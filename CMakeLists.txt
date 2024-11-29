cmake_minimum_required(VERSION 3.10)
project(JonyServer)

set(CMAKE_CXX_STANDARD 17)

# 设置构建类型为 Debug，这将启用调试符号
set(CMAKE_BUILD_TYPE Debug)

# 添加 CMake 查找库的路径
LINK_DIRECTORIES(/usr/lib/x86_64-linux-gnu)

# 查找 libpqxx
find_package(PkgConfig REQUIRED)
pkg_check_modules(PQXX REQUIRED libpqxx)

# 查找 libpq (PostgreSQL client library)
find_package(PostgreSQL REQUIRED)

find_library(LIBBFD_LIBRARY NAMES bfd)

# 添加头文件路径
include_directories(${PQXX_INCLUDE_DIRS} ${PostgreSQL_INCLUDE_DIRS})

# 创建可执行文件
add_executable(JonyServer main.cpp 
    CGImysql/sql_connection_pool.h CGImysql/sql_connection_pool.cpp
    http/http_conn.h http/http_conn.cpp 
    lock/locker.h 
    log/block_queue.h log/log.cpp log/log.h 
    threadpool/threadpool.h 
    ConcurrentMemoryPool/CentralCache.h ConcurrentMemoryPool/CentralCache.cpp
    ConcurrentMemoryPool/Common.h ConcurrentMemoryPool/ConcurrentAlloc.h
    ConcurrentMemoryPool/PageCache.h ConcurrentMemoryPool/PageCache.cpp
    ConcurrentMemoryPool/ThreadCache.h ConcurrentMemoryPool/ThreadCache.cpp
    timer/time_wheel_timer.h timer/time_wheel_timer.cpp)

add_subdirectory(/home/ningmeng/ningmeng_postgre/backward-cpp)

# Add Backward to your target (either Backward::Interface, Backward::Object, or Backward::Backward)
target_link_libraries(JonyServer PUBLIC Backward::Interface ${LIBBFD_LIBRARY})

# 链接 libpqxx 和 libpq 库
target_link_libraries(JonyServer PRIVATE ${PQXX_LIBRARIES} ${PostgreSQL_LIBRARIES} pthread)

# 如果找不到 libpq，则手动指定 libpq 库路径
# 如果 PostgreSQL 安装在非标准路径，使用下面的方式指定路径
# target_link_libraries(JonyServer PRIVATE ${PQXX_LIBRARIES} /path/to/libpq /path/to/libpqxx pthread)
