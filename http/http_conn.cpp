#include "http_conn.h"
#include "../log/log.h"
#include <map>
#include <pqxx/pqxx>
#include <fstream>

#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <rapidjson/document.h>
#include <rapidjson/writer.h>
#include <rapidjson/stringbuffer.h>

using namespace pqxx;

#define connfdET //边缘触发非阻塞
//#define connfdLT //水平触发阻塞

#define listenfdET //边缘触发非阻塞
//#define listenfdLT //水平触发阻塞

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

//当浏览器出现连接重置时，可能是网站根目录出错或http响应格式出错或者访问的文件中内容完全为空
const char *doc_root = "/home/ningmeng/server/root";

//将表中的用户名和密码放入map
map<string, string> users;
locker m_lock;

void http_conn::initpostgres_result(connection_pool *connPool) {
    // 从连接池中获取一个 PostgreSQL 连接
    connection *conn = nullptr;
    connectionRAII postgrescon(&conn, connPool);

    try {
        // 执行 SQL 查询，检索 `username` 和 `passwd` 数据
        nontransaction txn(*conn);
        result res = txn.exec("SELECT username, passwd FROM user");

        // 遍历结果集，将用户名和密码存入 `users` map 中
        for (const auto &row : res) {
            std::string username = row["username"].c_str();
            std::string password = row["passwd"].c_str();
            users[username] = password;
        }
    } catch (const std::exception &e) {
        LOG_ERROR("PostgreSQL SELECT error: %s", e.what());
    }
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
    }
}

//初始化连接,外部调用初始化套接字地址
void http_conn::init(int sockfd, const sockaddr_in &addr)
{
    m_sockfd = sockfd;
    m_address = addr;
    addfd(m_epollfd, sockfd, true);
    m_user_count++;
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
    //当url为/时，显示判断界面
    if (strlen(m_url) == 1)
        strcat(m_url, "judge.html");
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
        LOG_INFO("oop!unknow header: %s", text);
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
        LOG_INFO("%s", text);
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
    strcpy(m_real_file, doc_root);
    int len = strlen(doc_root);
    const char *p = strrchr(m_url, '/');

    if (cgi == 1 && (*(p + 1) == '2' || *(p + 1) == '3')) {
        char flag = m_url[1];
        char *m_url_real = (char *)ConcurrentAlloc(sizeof(char) * 200);
        strcpy(m_url_real, "/");
        strcat(m_url_real, m_url + 2);
        strncpy(m_real_file + len, m_url_real, FILENAME_LEN - len - 1);
        ConcurrentFree(m_url_real);

        // 提取用户名和密码
        char name[100], password[100];
        int i;
        for (i = 5; m_string[i] != '&'; ++i)
            name[i - 5] = m_string[i];
        name[i - 5] = '\0';

        int j = 0;
        for (i = i + 10; m_string[i] != '\0'; ++i, ++j)
            password[j] = m_string[i];
        password[j] = '\0';

        // 注册逻辑
        if (*(p + 1) == '3') {
            try {
                if (users.find(name) == users.end()) {
                    // 插入新用户到数据库
                    work txn(*postgres_conn);
                    txn.exec("INSERT INTO user (username, passwd) VALUES (" +
                             txn.quote(name) + ", " + txn.quote(password) + ")");
                    txn.commit();

                    // 更新本地缓存
                    m_lock.lock();
                    users[name] = password;
                    m_lock.unlock();

                    strcpy(m_url, "/log.html");
                } else {
                    strcpy(m_url, "/registerError.html");
                }
            } catch (const std::exception &e) {
                LOG_ERROR("PostgreSQL INSERT error: %s", e.what());
                strcpy(m_url, "/registerError.html");
            }
        }

        // 登录逻辑
        if (*(p + 1) == '2') {
            if (users.find(name) != users.end() && users[name] == password) {
                strcpy(m_url, "/welcome.html");
            } else {
                strcpy(m_url, "/logError.html");
            }
        }
    }

    if (*(p + 1) == '0')
    {
        char *m_url_real = (char *)ConcurrentAlloc(sizeof(char) * 200);
        strcpy(m_url_real, "/register.html");
        strncpy(m_real_file + len, m_url_real, strlen(m_url_real));
        ConcurrentFree(m_url_real);
    }
    else if (*(p + 1) == '1')
    {
        char *m_url_real = (char *)ConcurrentAlloc(sizeof(char) * 200);
        strcpy(m_url_real, "/log.html");
        strncpy(m_real_file + len, m_url_real, strlen(m_url_real));
        ConcurrentFree(m_url_real);
    }
    else if (*(p + 1) == '5')
    {
        char *m_url_real = (char *)ConcurrentAlloc(sizeof(char) * 200);
        strcpy(m_url_real, "/picture.html");
        strncpy(m_real_file + len, m_url_real, strlen(m_url_real));
        ConcurrentFree(m_url_real);
    }
    else if (*(p + 1) == '6')
    {
        char *m_url_real = (char *)ConcurrentAlloc(sizeof(char) * 200);
        strcpy(m_url_real, "/video.html");
        strncpy(m_real_file + len, m_url_real, strlen(m_url_real));
        ConcurrentFree(m_url_real);
    }
    else if (*(p + 1) == '7')
    {
        char *m_url_real = (char *)ConcurrentAlloc(sizeof(char) * 200);
        strcpy(m_url_real, "/fans.html");
        strncpy(m_real_file + len, m_url_real, strlen(m_url_real));
        ConcurrentFree(m_url_real);
    }
    else if (strcmp(m_url, "/ping") == 0) {
        // cout << "it is ping!" << endl;
        const char *ping_response = "success";
        add_status_line(200, "OK");
        add_content_type("text/plain");
        add_headers(strlen(ping_response));
        if (!add_content(ping_response)) {
            return INTERNAL_ERROR;
        }
        m_iv[0].iov_base = m_write_buf;
        m_iv[0].iov_len = m_write_idx;
        m_iv_count = 1;
        bytes_to_send = m_write_idx;
        return FILE_REQUEST;
    }
    else if (strcmp(m_url, "/api/bind") == 0 && m_method == POST) {
        // 解析 POST 请求中的 JSON 数据
        const char *json_data = m_string;
        rapidjson::Document doc;
        doc.Parse(json_data);

        if (!doc.HasMember("deviceid") || !doc["deviceid"].IsString()) {
            // deviceid 为空或格式非法
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
            // deviceid 长度非法
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

        // 查询数据库是否已存在此 deviceid
        char sql_query[256];
        snprintf(sql_query, sizeof(sql_query), "SELECT userid FROM user_info WHERE deviceid='%s'", deviceid.c_str());
        m_lock.lock();
        int query_res = mysql_query(mysql, sql_query);
        MYSQL_RES *result = mysql_store_result(mysql);
        m_lock.unlock();

        if (query_res == 0 && result != NULL) {
            MYSQL_ROW row = mysql_fetch_row(result);
            if (row) {
                // deviceid 已存在，返回对应的 userid
                long userid = atol(row[0]);
                mysql_free_result(result);
                char response[128];
                snprintf(response, sizeof(response), R"({"code": 102, "userid": %ld})", userid);
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
            mysql_free_result(result);
        }

        // 如果 deviceid 不存在，则创建新记录
        char sql_insert[256];
        snprintf(sql_insert, sizeof(sql_insert), "INSERT INTO user_info (deviceid) VALUES ('%s')", deviceid.c_str());
        m_lock.lock();
        int insert_res = mysql_query(mysql, sql_insert);
        long userid = mysql_insert_id(mysql);  // 获取自增生成的 userid
        m_lock.unlock();

        if (insert_res == 0) {
            // 返回创建成功的响应
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
    else if (strcmp(m_url, "/api/upload") == 0 && m_method == POST) {
        // 解析 POST 请求中的 JSON 数据
        const char *json_data = m_string;
        rapidjson::Document doc;
        doc.Parse(json_data);

        if (!doc.HasMember("userid") || !doc["userid"].IsInt64() ||
            !doc.HasMember("data") || !doc["data"].IsString()) {
            // 参数缺失或格式非法
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

        // 提取参数
        long userid = doc["userid"].GetInt64();
        std::string data = doc["data"].GetString();

        if (data.length() > 256) {
            // data 长度非法
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

        // 检查数据库中是否存在该 userid
        char sql_query[256];
        snprintf(sql_query, sizeof(sql_query), "SELECT userid FROM user_data WHERE userid=%ld", userid);
        m_lock.lock();
        int query_res = mysql_query(mysql, sql_query);
        MYSQL_RES *result = mysql_store_result(mysql);
        m_lock.unlock();

        if (query_res != 0) {
            // 数据库查询失败
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

        MYSQL_ROW row = mysql_fetch_row(result);
        bool user_exists = (row != nullptr);
        mysql_free_result(result);

        char sql_update[512];
        if (user_exists) {
            // 更新数据
            snprintf(sql_update, sizeof(sql_update), "UPDATE user_data SET data='%s' WHERE userid=%ld", data.c_str(), userid);
        } else {
            // 插入新数据
            snprintf(sql_update, sizeof(sql_update), "INSERT INTO user_data (userid, data) VALUES (%ld, '%s')", userid, data.c_str());
        }

        m_lock.lock();
        int update_res = mysql_query(mysql, sql_update);
        m_lock.unlock();

        if (update_res == 0) {
            // 更新或插入成功
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

    else {
        const char *response = R"({"msg": Wrong url! Please check the url!})";
        add_status_line(200, "OK");
        add_content_type("application/json");
        add_headers(strlen(response));
        add_content(response);
        m_iv[0].iov_base = m_write_buf;
        m_iv[0].iov_len = m_write_idx;
        m_iv_count = 1;
        bytes_to_send = m_write_idx;
        return FILE_REQUEST;
        // strncpy(m_real_file + len, m_url, FILENAME_LEN - len - 1);
    }

    if (stat(m_real_file, &m_file_stat) < 0)
        return NO_RESOURCE;
    if (!(m_file_stat.st_mode & S_IROTH))
        return FORBIDDEN_REQUEST;
    if (S_ISDIR(m_file_stat.st_mode))
        return BAD_REQUEST;
    int fd = open(m_real_file, O_RDONLY);
    m_file_address = (char *)mmap(0, m_file_stat.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
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
    LOG_INFO("request:%s", m_write_buf);
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
                // 打印日志：客户端 IP、URL 和响应码
                char client_ip[INET_ADDRSTRLEN];
                inet_ntop(AF_INET, &m_address.sin_addr, client_ip, INET_ADDRSTRLEN);
                cout << "Client IP: " << client_ip
                     << ", URL: " << (m_url ? m_url : "/")
                     << ", Response Code: " << "200"
                     << endl;
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

