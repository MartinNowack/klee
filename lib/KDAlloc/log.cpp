#include "log.h"

#include <cstdint>

#include <errno.h>
#include <unistd.h>

namespace util {
void log(std::string_view s) noexcept {
  std::size_t pos = 0;
  while (pos < s.length()) {
    auto written = write(2, s.data() + pos, s.length() - pos);
    if (written < 0) {
      if (errno == EINTR) {
        // nop
      } else {
        break;
      }
    } else if (written == 0) {
      break;
    } else {
      pos += written;
    }
  }
}

void log(void* p) noexcept {
  static_assert(std::numeric_limits<std::uintptr_t>::radix == 2);
  static_assert(std::numeric_limits<std::uintptr_t>::digits % 8 == 0);
  static constexpr const auto hexdigits = std::numeric_limits<std::uintptr_t>::digits / 4;

  using namespace std::string_view_literals;

  char str[hexdigits + 2];
  str[0] = '0';
  str[1] = 'x';

  auto n = reinterpret_cast<std::uintptr_t>(p);
  for(std::size_t i = 0; i < hexdigits; ++i) {
    str[i + 2] = "0123456789ABCDEF"[(n >> ((hexdigits - 1 - i) * 4)) & 0xF];
  }
  log(std::string_view(str, sizeof(str)));
}
}