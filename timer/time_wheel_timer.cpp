#include <time.h>
#include "../http/http_conn.h"
#include "../log/log.h"
#include "time_wheel_timer.h"


time_wheel::~time_wheel() {
    locker my_lock;
    for (int i = 0; i < N; i++) {
        time_wheel_timer *tmp = slots[i];
        while (tmp) {
            slots[i] = tmp->next;
            my_lock.lock();
            delete tmp;
            my_lock.unlock();
            tmp = slots[i];
        }
    }
}

time_wheel_timer *time_wheel::add_timer(int timeout) {
    if (timeout < 0) {
        return NULL;
    }
    int ticks = 0;
    if (timeout < SI) {
        ticks = 1;
    }
    else {
        ticks = timeout / SI;
    }
    // 计算待插入的定时器在时间轮转动多少圈后被触发
    int rotation = ticks / N;
    // 计算待插入的定时器应该被插入哪个槽中
    int ts = (cur_slot + (ticks % N)) % N;
    // 创建新的定时器，它在时间轮转动rotation圈之后被触发，且位于第ts个槽上
    time_wheel_timer *timer = new time_wheel_timer(rotation, ts);
    // 如果第ts个槽中尚无任何定时器，则把新建的定时器插入其中，并将该定时器设置为该槽的头结点
    if (!slots[ts]) {
        slots[ts] = timer;
        // cur_slot = ts;
    }
    else {
        timer->next = slots[ts];
        slots[ts]->prev = timer;
        slots[ts] = timer;
        // cur_slot = ts;
    }
    return timer;
}

void time_wheel::del_timer(time_wheel_timer *timer) {
    locker my_lock;
    if (!timer) {
        return;
    }
    int ts = timer->time_slot;
    // slots[ts] 是目标定时器所在槽的头结点，如果目标定时器就是头结点，则需要重置第ts个槽的头结点
    if (timer == slots[ts]) {
        slots[ts] = slots[ts]->next;
        if (slots[ts]) {
            slots[ts]->prev = NULL;
        }
        my_lock.lock();
        delete timer;
        my_lock.unlock();
    }
    else {
        if (timer->prev) timer->prev->next = timer->next;
        // timer->prev->next = timer->next;
        if (timer->next) {
            timer->next->prev = timer->prev;
        }
        my_lock.lock();
        delete timer;
        my_lock.unlock();
    }
    
}

void time_wheel::tick() {
    // 获取当前槽中的定时器
    time_wheel_timer *timer = slots[cur_slot];
    // cout << cur_slot << endl;
    // 如果当前槽没有定时器，则直接返回
    if (!timer) {
        // std::cout << "No timer in current slot." << std::endl;
        return;
    }

    std::cout << "Tick: Processing timers in slot " << cur_slot << std::endl;

    // 遍历当前槽的所有定时器
    while (timer) {
        // 获取下一个定时器
        time_wheel_timer *next_timer = timer->next;

        // 如果定时器的旋转次数已经到达，调用其回调函数
        if (timer->rotation == 0) {
            // 执行定时器回调函数
            if (timer->cb_func) {
                timer->cb_func(timer->user_data);
            }
            // 删除该定时器
            del_timer(timer);
        } else {
            // 否则，减少旋转次数
            timer->rotation--;
        }

        // 移动到下一个定时器
        timer = next_timer;
    }

    // 当前槽处理完毕，向前滚动到下一个槽
    cur_slot = (cur_slot + 1) % N;
}