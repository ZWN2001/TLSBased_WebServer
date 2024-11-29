#include "http_conn.h"
#include "../log/log.h"
#include <map>
#include <pqxx/pqxx>
#include <fstream>
#include <rapidjson/document.h>
#include <rapidjson/writer.h>
#include <rapidjson/stringbuffer.h>
#include <chrono>
#include <iomanip>
#include <ctime>

#include <stdio.h>
#include <string.h>
#include <unistd.h>

using namespace pqxx;

#define connfdET //边缘触发非阻塞
// #define connfdLT //水平触发阻塞

#define listenfdET //边缘触发非阻塞
// #define listenfdLT //水平触发阻塞

//定义http响应的一些状态信息
const char *ok_200_title = "OK";
const char *error_400_title = "Bad Request";
const char *error_400_form = "Your request has bad syntax or is inherently impossible to staisfy.\n";
const char *error_403_title = "Forbidden";
const char *error_403_form = "You do not have permission to get file form this server.\n";
const char *error_404_title = "Not Found";
const char *error_404_form = "The requested file was not found on this server.\n";
const char *error_500_title = "Internal Error";
const char *error_500_form = "There was an unusual problem serving the request file.\n";

locker m_lock;

void http_conn::initpostgres_result(connection_pool *connPool) {
    // 从连接池中获取一个 PostgreSQL 连接
    connection *conn = nullptr;
    connectionRAII postgrescon(&conn, connPool);
}

//对文件描述符设置非阻塞
int setnonblocking(int fd)
{
    int old_option = fcntl(fd, F_GETFL);
    int new_option = old_option | O_NONBLOCK;
    fcntl(fd, F_SETFL, new_option);
    return old_option;
}

//将内核事件表注册读事件，ET模式，选择开启EPOLLONESHOT
void addfd(int epollfd, int fd, bool one_shot)
{
    epoll_event event;
    event.data.fd = fd;

#ifdef connfdET
    event.events = EPOLLIN | EPOLLET | EPOLLRDHUP;
#endif

#ifdef connfdLT
    event.events = EPOLLIN | EPOLLRDHUP;
#endif

#ifdef listenfdET
    event.events = EPOLLIN | EPOLLET | EPOLLRDHUP;
#endif

#ifdef listenfdLT
    event.events = EPOLLIN | EPOLLRDHUP;
#endif

    if (one_shot)
        event.events |= EPOLLONESHOT;
    epoll_ctl(epollfd, EPOLL_CTL_ADD, fd, &event);
    setnonblocking(fd);
}

//从内核时间表删除描述符
void removefd(int epollfd, int fd)
{
    epoll_ctl(epollfd, EPOLL_CTL_DEL, fd, 0);
    close(fd);
}

//将事件重置为EPOLLONESHOT
void modfd(int epollfd, int fd, int ev)
{
    epoll_event event;
    event.data.fd = fd;

#ifdef connfdET
    event.events = ev | EPOLLET | EPOLLONESHOT | EPOLLRDHUP;
#endif

#ifdef connfdLT
    event.events = ev | EPOLLONESHOT | EPOLLRDHUP;
#endif

    epoll_ctl(epollfd, EPOLL_CTL_MOD, fd, &event);
}

int http_conn::m_user_count = 0;
int http_conn::m_epollfd = -1;

//关闭连接，关闭一个连接，客户总量减一
void http_conn::close_conn(bool real_close)
{
    if (real_close && (m_sockfd != -1))
    {
        removefd(m_epollfd, m_sockfd);
        m_sockfd = -1;
        m_user_count--;
        // ConcurrentFree(m_read_buf);
        // ConcurrentFree(m_write_buf);
        // ConcurrentFree(m_real_file);
    }
}

// void foo() {
//     int* ptr = nullptr;
//     *ptr = 42;  // 这会导致段错误
// }

//初始化连接,外部调用初始化套接字地址
void http_conn::init(int sockfd, const sockaddr_in &addr)
{
    m_sockfd = sockfd;
    m_address = addr;
    addfd(m_epollfd, sockfd, true);
    m_user_count++;
    // foo();
    init();
}

//初始化新接受的连接
//check_state默认为分析请求行状态
void http_conn::init()
{
    postgres_conn = nullptr;
    bytes_to_send = 0;
    bytes_have_send = 0;
    m_check_state = CHECK_STATE_REQUESTLINE;
    m_linger = false;
    m_method = GET;
    m_url = 0;
    m_version = 0;
    m_content_length = 0;
    m_host = 0;
    m_start_line = 0;
    m_checked_idx = 0;
    m_read_idx = 0;
    m_write_idx = 0;
    cgi = 0;
    m_read_buf = (char *)ConcurrentAlloc(sizeof(char) * READ_BUFFER_SIZE);
    m_write_buf = (char *)ConcurrentAlloc(sizeof(char) * WRITE_BUFFER_SIZE);
    m_real_file = (char *)ConcurrentAlloc(sizeof(char) * FILENAME_LEN);

    memset(m_read_buf, '\0', READ_BUFFER_SIZE);
    memset(m_write_buf, '\0', WRITE_BUFFER_SIZE);
    memset(m_real_file, '\0', FILENAME_LEN);
}

//从状态机，用于分析出一行内容
//返回值为行的读取状态，有LINE_OK,LINE_BAD,LINE_OPEN
http_conn::LINE_STATUS http_conn::parse_line()
{
    char temp;
    for (; m_checked_idx < m_read_idx; ++m_checked_idx)
    {
        temp = m_read_buf[m_checked_idx];
        if (temp == '\r')
        {
            if ((m_checked_idx + 1) == m_read_idx)
                return LINE_OPEN;
            else if (m_read_buf[m_checked_idx + 1] == '\n')
            {
                m_read_buf[m_checked_idx++] = '\0';
                m_read_buf[m_checked_idx++] = '\0';
                return LINE_OK;
            }
            return LINE_BAD;
        }
        else if (temp == '\n')
        {
            if (m_checked_idx > 1 && m_read_buf[m_checked_idx - 1] == '\r')
            {
                m_read_buf[m_checked_idx - 1] = '\0';
                m_read_buf[m_checked_idx++] = '\0';
                return LINE_OK;
            }
            return LINE_BAD;
        }
    }
    return LINE_OPEN;
}

//循环读取客户数据，直到无数据可读或对方关闭连接
//非阻塞ET工作模式下，需要一次性将数据读完
bool http_conn::read_once()
{
    if (m_read_idx >= READ_BUFFER_SIZE)
    {
        return false;
    }
    int bytes_read = 0;

#ifdef connfdLT

    bytes_read = recv(m_sockfd, m_read_buf + m_read_idx, READ_BUFFER_SIZE - m_read_idx, 0);
    m_read_idx += bytes_read;

    if (bytes_read <= 0)
    {
        return false;
    }

    return true;

#endif

#ifdef connfdET
    while (true)
    {
        bytes_read = recv(m_sockfd, m_read_buf + m_read_idx, READ_BUFFER_SIZE - m_read_idx, 0);
        if (bytes_read == -1)
        {
            if (errno == EAGAIN || errno == EWOULDBLOCK)
                break;
            return false;
        }
        else if (bytes_read == 0)
        {
            return false;
        }
        m_read_idx += bytes_read;
    }
    return true;
#endif
}

//解析http请求行，获得请求方法，目标url及http版本号
http_conn::HTTP_CODE http_conn::parse_request_line(char *text)
{
    m_url = strpbrk(text, " \t");
    if (!m_url)
    {
        return BAD_REQUEST;
    }
    *m_url++ = '\0';
    char *method = text;
    if (strcasecmp(method, "GET") == 0)
        m_method = GET;
    else if (strcasecmp(method, "POST") == 0)
    {
        m_method = POST;
        cgi = 1;
    }
    else
        return BAD_REQUEST;
    m_url += strspn(m_url, " \t");
    m_version = strpbrk(m_url, " \t");
    if (!m_version)
        return BAD_REQUEST;
    *m_version++ = '\0';
    m_version += strspn(m_version, " \t");
    if (strcasecmp(m_version, "HTTP/1.1") != 0)
        return BAD_REQUEST;
    if (strncasecmp(m_url, "http://", 7) == 0)
    {
        m_url += 7;
        m_url = strchr(m_url, '/');
    }

    if (strncasecmp(m_url, "https://", 8) == 0)
    {
        m_url += 8;
        m_url = strchr(m_url, '/');
    }

    if (!m_url || m_url[0] != '/')
        return BAD_REQUEST;
    m_check_state = CHECK_STATE_HEADER;
    return NO_REQUEST;
}

//解析http请求的一个头部信息
http_conn::HTTP_CODE http_conn::parse_headers(char *text)
{
    if (text[0] == '\0')
    {
        if (m_content_length != 0)
        {
            m_check_state = CHECK_STATE_CONTENT;
            return NO_REQUEST;
        }
        return GET_REQUEST;
    }
    else if (strncasecmp(text, "Connection:", 11) == 0)
    {
        text += 11;
        text += strspn(text, " \t");
        if (strcasecmp(text, "keep-alive") == 0)
        {
            m_linger = true;
        }
    }
    else if (strncasecmp(text, "Content-length:", 15) == 0)
    {
        text += 15;
        text += strspn(text, " \t");
        m_content_length = atol(text);
    }
    else if (strncasecmp(text, "Host:", 5) == 0)
    {
        text += 5;
        text += strspn(text, " \t");
        m_host = text;
    }
    else
    {
        //printf("oop!unknow header: %s\n",text);
        // LOG_INFO("oop!unknow header: %s", text);
        Log::get_instance()->flush();
    }
    return NO_REQUEST;
}

//判断http请求是否被完整读入
http_conn::HTTP_CODE http_conn::parse_content(char *text)
{
    if (m_read_idx >= (m_content_length + m_checked_idx))
    {
        text[m_content_length] = '\0';
        //POST请求中最后为输入的用户名和密码
        m_string = text;
        return GET_REQUEST;
    }
    return NO_REQUEST;
}

http_conn::HTTP_CODE http_conn::process_read()
{
    LINE_STATUS line_status = LINE_OK;
    HTTP_CODE ret = NO_REQUEST;
    char *text = 0;

    while ((m_check_state == CHECK_STATE_CONTENT && line_status == LINE_OK) || ((line_status = parse_line()) == LINE_OK))
    {
        text = get_line();
        m_start_line = m_checked_idx;
        // LOG_INFO("%s", text);
        Log::get_instance()->flush();
        switch (m_check_state)
        {
            case CHECK_STATE_REQUESTLINE:
            {
                ret = parse_request_line(text);
                if (ret == BAD_REQUEST)
                    return BAD_REQUEST;
                break;
            }
            case CHECK_STATE_HEADER:
            {
                ret = parse_headers(text);
                if (ret == BAD_REQUEST)
                    return BAD_REQUEST;
                else if (ret == GET_REQUEST)
                {
                    return do_request();
                }
                break;
            }
            case CHECK_STATE_CONTENT:
            {
                ret = parse_content(text);
                if (ret == GET_REQUEST)
                    return do_request();
                line_status = LINE_OPEN;
                break;
            }
            default:
                return INTERNAL_ERROR;
        }
    }
    return NO_REQUEST;
}

http_conn::HTTP_CODE http_conn::do_request()
{
    // ningmeng
    try {
        // pqxx::connection conn(conn_str);  // 创建数据库连接
        work txn(*postgres_conn);  // 创建事务
        // cout << m_url << endl;
        if (strcmp(m_url, "/ping") == 0) {
            const char *ping_response = "success";
            add_status_line(200, "OK");
            add_content_type("text/plain");
            add_headers(strlen(ping_response));
            add_content(ping_response);
            m_iv[0].iov_base = m_write_buf;
            m_iv[0].iov_len = m_write_idx;
            m_iv_count = 1;
            bytes_to_send = m_write_idx;
            return FILE_REQUEST;
        }

        // 处理 /api/bind
        else if (strcmp(m_url, "/api/bind") == 0 && m_method == POST) {
            // 解析 JSON 数据
            const char *json_data = m_string;
            rapidjson::Document doc;
            doc.Parse(json_data);

            if (!doc.HasMember("deviceid") || !doc["deviceid"].IsString()) {
                const char *response = R"({"code": 104})";
                add_status_line(200, "OK");
                add_content_type("application/json");
                add_headers(strlen(response));
                add_content(response);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv_count = 1;
                bytes_to_send = m_write_idx;
                return FILE_REQUEST;
            }

            std::string deviceid = doc["deviceid"].GetString();

            if (deviceid.length() != 36) {
                const char *response = R"({"code": 104})";
                add_status_line(200, "OK");
                add_content_type("application/json");
                add_headers(strlen(response));
                add_content(response);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv_count = 1;
                bytes_to_send = m_write_idx;
                return FILE_REQUEST;
            }

            // 查询 PostgreSQL 是否已存在此 deviceid
            std::string sql_query = "SELECT userid FROM user_info WHERE deviceid = " + txn.quote(deviceid);
            result res = txn.exec(sql_query);

            if (!res.empty()) {
                // deviceid 已存在，返回对应的 userid
                long userid = res[0][0].as<long>();
                char response[128];
                snprintf(response, sizeof(response), R"({"code": 102, "userid": %ld})", userid);
                // std::string response = "{\"code\": 102, \"userid\": " + std::to_string(userid) + "}";
                add_status_line(200, "OK");
                add_content_type("application/json");
                add_headers(strlen(response));
                add_content(response);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv_count = 1;
                bytes_to_send = m_write_idx;
                return FILE_REQUEST;
            }

            // 如果 deviceid 不存在，则创建新记录
            std::string sql_insert = "INSERT INTO user_info (deviceid) VALUES (" + txn.quote(deviceid) + ") RETURNING userid";
            m_lock.lock();
            result insert_res = txn.exec(sql_insert);
            txn.commit();
            m_lock.unlock();
            if (!insert_res.empty()) {
                long userid = insert_res[0][0].as<long>();
                char response[128];
                snprintf(response, sizeof(response), R"({"code": 100, "userid": %ld})", userid);
                add_status_line(200, "OK");
                add_content_type("application/json");
                add_headers(strlen(response));
                add_content(response);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv_count = 1;
                bytes_to_send = m_write_idx;
                return FILE_REQUEST;
            } else {
                // 数据库插入失败
                const char *response = R"({"code": 500})";
                add_status_line(500, "Internal Server Error");
                add_content_type("application/json");
                add_headers(strlen(response));
                add_content(response);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv_count = 1;
                bytes_to_send = m_write_idx;
                return FILE_REQUEST;
            }
        }

        // 处理 /api/upload
        else if (strcmp(m_url, "/api/upload") == 0 && m_method == POST) {
            // 解析 JSON 数据
            const char *json_data = m_string;
            rapidjson::Document doc;

            doc.Parse(json_data);
            // cout << doc["userid"].GetInt64() << endl;
            // cout << doc["data"].GetString() << endl;
            if (!doc.HasMember("userid") || !doc["userid"].IsInt64() ||
                !doc.HasMember("data") || !doc["data"].IsString()) {
                const char *response = R"({"code": 104})";
                add_status_line(200, "OK");
                add_content_type("application/json");
                add_headers(strlen(response));
                add_content(response);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv_count = 1;
                bytes_to_send = m_write_idx;
                return FILE_REQUEST;
            }

            long userid = doc["userid"].GetInt64();
            std::string data = doc["data"].GetString();

            if (data.length() > 256) {
                const char *response = R"({"code": 104})";
                add_status_line(200, "OK");
                add_content_type("application/json");
                add_headers(strlen(response));
                add_content(response);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv_count = 1;
                bytes_to_send = m_write_idx;
                return FILE_REQUEST;
            }

            // 检查 PostgreSQL 中是否存在该 userid
            // m_lock.lock();
            std::string sql_query = "INSERT INTO user_data (userid, data) VALUES (" 
                        + txn.quote(userid) + ", " + txn.quote(data) 
                        + ") ON CONFLICT (userid) DO UPDATE SET data = " 
                        + txn.quote(data);
            // std::string sql_query = "SELECT userid FROM user_data WHERE userid = " + txn.quote(userid);
            // result res = txn.exec(sql_query);
            // // m_lock.unlock();
            // bool user_exists = !res.empty();

            // std::string sql_update;
            // if (user_exists) {
            //     // 更新数据
            //     sql_update = "UPDATE user_data SET data = " + txn.quote(data) + " WHERE userid = " + txn.quote(userid);
            // } else {
            //     // 插入新数据
            //     sql_update = "INSERT INTO user_data (userid, data) VALUES (" + txn.quote(userid) + ", " + txn.quote(data) + ")";
            // }
            m_lock.lock();
            result update_res = txn.exec(sql_query);
            txn.commit();
            m_lock.unlock();
            if (update_res.affected_rows() > 0) {
                const char *response = R"({"code": 100})";
                add_status_line(200, "OK");
                add_content_type("application/json");
                add_headers(strlen(response));
                add_content(response);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv_count = 1;
                bytes_to_send = m_write_idx;
                return FILE_REQUEST;
            } else {
                // 更新或插入失败
                const char *response = R"({"code": 500})";
                add_status_line(500, "Internal Server Error");
                add_content_type("application/json");
                add_headers(strlen(response));
                add_content(response);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv_count = 1;
                bytes_to_send = m_write_idx;
                return FILE_REQUEST;
            }
        }

        // 其他请求处理
        else {
            const char *response = R"({"msg": "Wrong url! Please check the url!"})";
            add_status_line(200, "OK");
            add_content_type("application/json");
            add_headers(strlen(response));
            add_content(response);
            m_iv[0].iov_base = m_write_buf;
            m_iv[0].iov_len = m_write_idx;
            m_iv_count = 1;
            bytes_to_send = m_write_idx;
            return FILE_REQUEST;
        }

    } catch (const std::exception& e) {
        // 错误处理：数据库连接或查询失败
        std::cerr << "Error: " << e.what() << std::endl;
        const char *response = R"({"code": 500})";
        add_status_line(500, "Internal Server Error");
        add_content_type("application/json");
        add_headers(strlen(response));
        add_content(response);
        m_iv[0].iov_base = m_write_buf;
        m_iv[0].iov_len = m_write_idx;
        m_iv_count = 1;
        bytes_to_send = m_write_idx;
        return FILE_REQUEST;
    }
    return FILE_REQUEST;
}
void http_conn::unmap()
{
    if (m_file_address)
    {
        munmap(m_file_address, m_file_stat.st_size);
        m_file_address = 0;
    }
}

bool http_conn::write()
{
    int temp = 0;

    if (bytes_to_send == 0)
    {
        modfd(m_epollfd, m_sockfd, EPOLLIN);
        init();
        return true;
    }

    while (1)
    {
        temp = writev(m_sockfd, m_iv, m_iv_count);

        if (temp < 0)
        {
            if (errno == EAGAIN)
            {
                modfd(m_epollfd, m_sockfd, EPOLLOUT);
                return true;
            }
            unmap();
            return false;
        }

        bytes_have_send += temp;
        bytes_to_send -= temp;
        if (bytes_have_send >= m_iv[0].iov_len)
        {
            m_iv[0].iov_len = 0;
            m_iv[1].iov_base = m_file_address + (bytes_have_send - m_write_idx);
            m_iv[1].iov_len = bytes_to_send;
        }
        else
        {
            m_iv[0].iov_base = m_write_buf + bytes_have_send;
            m_iv[0].iov_len = m_iv[0].iov_len - bytes_have_send;
        }

        if (bytes_to_send <= 0)
        {
            unmap();
            modfd(m_epollfd, m_sockfd, EPOLLIN);

            if (m_linger)
            {
                init();
                return true;
            }
            else
            {
                return false;
            }
        }
    }
}

bool http_conn::add_response(const char *format, ...)
{
    if (m_write_idx >= WRITE_BUFFER_SIZE)
        return false;
    va_list arg_list;
    va_start(arg_list, format);
    int len = vsnprintf(m_write_buf + m_write_idx, WRITE_BUFFER_SIZE - 1 - m_write_idx, format, arg_list);
    if (len >= (WRITE_BUFFER_SIZE - 1 - m_write_idx))
    {
        va_end(arg_list);
        return false;
    }
    m_write_idx += len;
    va_end(arg_list);
    // LOG_INFO("request:%s", m_write_buf);
    Log::get_instance()->flush();
    return true;
}
bool http_conn::add_status_line(int status, const char *title)
{
    return add_response("%s %d %s\r\n", "HTTP/1.1", status, title);
}
bool http_conn::add_headers(int content_len)
{
    add_content_length(content_len);
    add_linger();
    add_blank_line();
}
bool http_conn::add_content_length(int content_len)
{
    return add_response("Content-Length:%d\r\n", content_len);
}
bool http_conn::add_content_type(const char *type = nullptr) {
    if (type) {
        return add_response("Content-Type:%s\r\n", type);
    }
    return add_response("Content-Type:%s\r\n", "text/html");
}
bool http_conn::add_linger()
{
    return add_response("Connection:%s\r\n", (m_linger == true) ? "keep-alive" : "close");
}
bool http_conn::add_blank_line()
{
    return add_response("%s", "\r\n");
}
bool http_conn::add_content(const char *content)
{
    return add_response("%s", content);
}
bool http_conn::process_write(HTTP_CODE ret)
{
    switch (ret)
    {
        case INTERNAL_ERROR:
        {
            add_status_line(500, error_500_title);
            add_headers(strlen(error_500_form));
            if (!add_content(error_500_form))
                return false;
            break;
        }
        case BAD_REQUEST:
        {
            add_status_line(404, error_404_title);
            add_headers(strlen(error_404_form));
            if (!add_content(error_404_form))
                return false;
            break;
        }
        case FORBIDDEN_REQUEST:
        {
            add_status_line(403, error_403_title);
            add_headers(strlen(error_403_form));
            if (!add_content(error_403_form))
                return false;
            break;
        }
        case FILE_REQUEST:
        {
            add_status_line(200, ok_200_title);
            if (m_file_stat.st_size != 0)
            {
                add_headers(m_file_stat.st_size);
                m_iv[0].iov_base = m_write_buf;
                m_iv[0].iov_len = m_write_idx;
                m_iv[1].iov_base = m_file_address;
                m_iv[1].iov_len = m_file_stat.st_size;
                m_iv_count = 2;
                bytes_to_send = m_write_idx + m_file_stat.st_size;
                return true;
            }
            else
            {
                // char client_ip[INET_ADDRSTRLEN];
                // auto now = std::chrono::system_clock::now();
                // std::time_t now_time = std::chrono::system_clock::to_time_t(now);
                // inet_ntop(AF_INET, &m_address.sin_addr, client_ip, INET_ADDRSTRLEN);
                // cout << "Client IP: " << client_ip 
                //         << ", Time: " << std::put_time(std::localtime(&now_time), "%F %T")
                //         << ", URL: " << (m_url ? m_url : "/") 
                //         << ", Response Code: " << "200" 
                //         << endl;
                return true;
            }
        }
        default:
            return false;
    }
    m_iv[0].iov_base = m_write_buf;
    m_iv[0].iov_len = m_write_idx;
    m_iv_count = 1;
    bytes_to_send = m_write_idx;
    return true;
}
void http_conn::process()
{
    HTTP_CODE read_ret = process_read();
    if (read_ret == NO_REQUEST)
    {
        modfd(m_epollfd, m_sockfd, EPOLLIN);
        return;
    }
    bool write_ret = process_write(read_ret);
    if (!write_ret)
    {
        close_conn();
    }

    modfd(m_epollfd, m_sockfd, EPOLLOUT);
}

