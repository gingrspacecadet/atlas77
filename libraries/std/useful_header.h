#ifndef PORTABLE_TIMER_H
#define PORTABLE_TIMER_H

/* Minimal uint64_t for old compilers */
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
#include <stdint.h>
#else
typedef unsigned long long uint64_t;
#endif

#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>

static uint64_t timer_now_ns(void)
{
    LARGE_INTEGER freq;
    LARGE_INTEGER cnt;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&cnt);
    return (uint64_t)((cnt.QuadPart * 1000000000ULL) / freq.QuadPart);
}

#else /* POSIX / macOS */

#include <time.h>

#if defined(__MACH__) && !defined(CLOCK_MONOTONIC)
/* macOS pre-10.12 fallback using mach_absolute_time */
#include <mach/mach_time.h>

static uint64_t timer_now_ns(void)
{
    static mach_timebase_info_data_t tb = {0, 0};
    if (tb.denom == 0)
        mach_timebase_info(&tb);
    uint64_t v = mach_absolute_time();
    return (v * (uint64_t)tb.numer) / (uint64_t)tb.denom;
}

#else
/* POSIX clock_gettime (Linux, modern macOS) */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 199309L
#endif
static uint64_t timer_now_ns(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}
#endif

#endif /* _WIN32 */

static uint64_t timer_elapsed_ns(uint64_t start_ns)
{
    return timer_now_ns() - start_ns;
}

static double timer_elapsed_s(uint64_t start_ns)
{
    return (timer_elapsed_ns(start_ns)) / 1e9;
}

#endif /* PORTABLE_TIMER_H */

#ifndef ATLAS77_USEFUL_HEADER_H
#define ATLAS77_USEFUL_HEADER_H
/* Minimal uint64_t for old compilers */
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 199901L
#include <stdint.h>
#else
typedef unsigned long long uint64_t;
#endif
// Should this be conditionally included?
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// TODO: Once size_of<T> is implemented in Atlas77, we can make this more general
// because we will know the size at compile time.
static inline void __atlas77_c_swap(void *a, void *b)
{
    uint64_t temp = *(uint64_t *)a;
    *(uint64_t *)a = *(uint64_t *)b;
    *(uint64_t *)b = temp;
}

static inline void panic(const char *message)
{
    fprintf(stderr, "PANIC: %s\n", message);
    exit(1);
}

int64_t fib(int64_t arg_0);
void main();

typedef struct
{
    uint64_t len;
    char *data;
} string;

const uint64_t string_size = sizeof(string);

extern inline uint64_t __atlas77_c_str_len(const string str)
{
    return str.len;
}

extern inline string __atlas77_c_trim(const string str)
{
}

extern inline string __atlas77_c_to_upper(const string str)
{
}

extern inline string __atlas77_c_to_lower(const string str)
{
}

extern inline string __atlas77_c_split(string str, const string separator)
{
}

extern inline uint64_t __atlas77_c_str_cmp(const string str_1, const string str2)
{
    return strcmp(str_1.data, str2.data);
}

/* NB: Returns a null terminated string */
extern inline const char *__atlas77_c_to_chars(const string s)
{
    // Later to_chars() will return a slice e.g. `[char]`
    // And the string type will be a bit more defined
    return s.data;
}

/* NB: This is an array of char with a null terminated string for now */
extern inline string __atlas77_c_from_chars(const char *chars)
{
    uint64_t length = strlen(chars);
    char *my_str = (char *)malloc((length + 1) * sizeof(char));
    strcpy(my_str, chars);

    string my_string;
    my_string.len = length;
    my_string.data = my_str;

    return my_string;
}

#endif /* ATLAS77_USEFUL_HEADER_H */
