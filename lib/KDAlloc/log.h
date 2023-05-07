#pragma once

#include <limits>
#include <string_view>
#include <utility>

#define KDALLOC_LOG 0

namespace util {
#if defined(KDALLOC_LOG) && KDALLOC_LOG
void log(std::string_view s) noexcept;

void log(void *p) noexcept;

template <typename T>
std::enable_if_t<std::numeric_limits<T>::is_integer> log(T n) noexcept {
  using namespace std::string_view_literals;

  if (n == 0) {
    log("0"sv);
  } else {
    char str[std::numeric_limits<T>::digits10 + 1];
    char *p = str + sizeof(str);
    while (n) {
      --p;
      *p = (n % 10) + '0';
      n /= 10;
    }
    log(std::string_view(p, (str + sizeof(str)) - p));
  }
}

template <typename T, typename U, typename... V>
void log(T &&arg1, U &&arg2, V &&...args) noexcept {
  ((log(std::forward<T>(arg1)), log(std::forward<U>(arg2))), ...,
   log(std::forward<V>(args)));
}
#else
template <typename... V> void log(V &&...) {}
#endif
} // namespace util