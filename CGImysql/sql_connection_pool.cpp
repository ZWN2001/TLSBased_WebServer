#include <pqxx/pqxx>
#include <stdio.h>
#include <string>
#include <string.h>
#include <stdlib.h>
#include <list>
#include <pthread.h>
#include <iostream>
#include "sql_connection_pool.h"

using namespace std;
using namespace pqxx;

// 构造函数
connection_pool::connection_pool() : CurConn(0), FreeConn(0), MaxConn(0) {}

// 析构函数
connection_pool::~connection_pool() {
    DestroyPool();
}

// 初始化连接池
void connection_pool::init(string url, string User, string PassWord, string DBName, int Port, unsigned int MaxConn) {
    this->url = url;
    this->User = User;
    this->PassWord = PassWord;
    this->DatabaseName = DBName;

    lock.lock();
    for (unsigned int i = 0; i < MaxConn; i++) {
        string connectionString = "dbname=" + DatabaseName + " user=" + User + " password=" + PassWord + " host=" + url + " port=" + to_string(Port);
        try {
            // 创建连接对象
            connection *conn = new connection(connectionString);
            if (conn->is_open()) {
                connList.push_back(conn);
                ++FreeConn;
            } else {
                cout << "Can't open database" << endl;
                exit(1);
            }
        } catch (const std::exception &e) {
            cerr << e.what() << endl;
            exit(1);
        }
    }

    reserve = sem(FreeConn);
    this->MaxConn = FreeConn;

    lock.unlock();
}

// 获取一个连接
connection *connection_pool::GetConnection() {
    connection *conn = nullptr;

    if (connList.empty())
        return nullptr;

    reserve.wait();

    lock.lock();

    conn = connList.front();
    connList.pop_front();

    --FreeConn;
    ++CurConn;

    lock.unlock();
    return conn;
}

// 释放一个连接
bool connection_pool::ReleaseConnection(connection *conn) {
    if (conn == nullptr)
        return false;
    
    lock.lock();
    connList.push_back(conn);
    ++FreeConn;
    --CurConn;
    lock.unlock();
    reserve.post();
    return true;
}

// 销毁连接池
void connection_pool::DestroyPool() {
    lock.lock();
    for (auto conn : connList) {
        delete conn; // 删除连接对象
    }
    CurConn = 0;
    FreeConn = 0;
    connList.clear();
    lock.unlock();
}

// 获取空闲连接数
int connection_pool::GetFreeConn() {
    return this->FreeConn;
}

// 获取实例（单例模式）
connection_pool *connection_pool::GetInstance() {
    static connection_pool connPool;
    return &connPool;
}

// RAII 构造函数
connectionRAII::connectionRAII(connection **SQL, connection_pool *connPool) {
    *SQL = connPool->GetConnection();
    conRAII = *SQL;
    poolRAII = connPool;
}

// RAII 析构函数
connectionRAII::~connectionRAII() {
    poolRAII->ReleaseConnection(conRAII);
}