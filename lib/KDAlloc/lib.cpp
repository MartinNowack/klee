#include "log.h"

#include "klee/KDAlloc/allocator.h"

#include <algorithm>
#include <atomic>
#include <cassert>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <mutex>
#include <optional>
#include <type_traits>

#include <dlfcn.h>
#include <errno.h>
#include <unistd.h>

#define EXPORT __attribute__((visibility("default")))
#define CONSTRUCTOR __attribute__((constructor))
#define DESTRUCTOR __attribute__((destructor))

using namespace std::literals;

namespace {
std::recursive_mutex global_lock;
bool kdalloc_is_active = false;
bool kdalloc_is_nested = false;

struct Nested {
  std::optional<klee::kdalloc::Allocator> heap;

  template <typename... V> void emplace(V &&...args) {
    heap.emplace(std::forward<V>(args)...);
  }

  void reset() { heap.reset(); }

  explicit operator bool() const noexcept { return heap.has_value(); }

  constexpr klee::kdalloc::Allocator *operator->() noexcept {
    return heap.operator->();
  }
  constexpr klee::kdalloc::Allocator const *operator->() const noexcept {
    return heap.operator->();
  }

  ~Nested() {
    kdalloc_is_active = false;

    kdalloc_is_nested = true;
    heap.reset();
    kdalloc_is_nested = false;
  }
} heap;

class Underlying {
  using malloc_t = void *(*)(std::size_t size) noexcept;
  using calloc_t = void *(*)(std::size_t n, std::size_t size) noexcept;
  using realloc_t = void *(*)(void *p, std::size_t size) noexcept;
  using free_t = void (*)(void *p) noexcept;

  std::atomic<void *> malloc_ptr{};
  std::atomic<void *> calloc_ptr{};
  std::atomic<void *> realloc_ptr{};
  std::atomic<void *> free_ptr{};

public:
  void *malloc(std::size_t size) noexcept {
    auto fn = malloc_ptr.load(std::memory_order_relaxed);
    if (!fn) {
      fn = dlsym(RTLD_NEXT, "malloc");
      malloc_ptr.store(fn, std::memory_order_relaxed);
    }
    auto result = reinterpret_cast<malloc_t>(fn)(size);
    return result;
  }

  void *calloc(std::size_t n, std::size_t size) noexcept {
    auto fn = calloc_ptr.load(std::memory_order_relaxed);
    if (!fn) {
      fn = dlsym(RTLD_NEXT, "calloc");
      calloc_ptr.store(fn, std::memory_order_relaxed);
    }
    auto result = reinterpret_cast<calloc_t>(fn)(n, size);
    return result;
  }

  void *realloc(void *p, std::size_t size) noexcept {
    auto fn = realloc_ptr.load(std::memory_order_relaxed);
    if (!fn) {
      fn = dlsym(RTLD_NEXT, "realloc");
      realloc_ptr.store(fn, std::memory_order_relaxed);
    }
    auto result = reinterpret_cast<realloc_t>(fn)(p, size);
    return result;
  }

  void free(void *p) noexcept {
    auto fn = free_ptr.load(std::memory_order_relaxed);
    if (!fn) {
      fn = dlsym(RTLD_NEXT, "free");
      free_ptr.store(fn, std::memory_order_relaxed);
    }
    reinterpret_cast<free_t>(fn)(p);
  }
};

Underlying underlying;
} // namespace

extern "C" {
EXPORT void kdalloc_init(std::uintptr_t addr, std::size_t size,
                         std::uint32_t quarantine) noexcept {
  std::scoped_lock lock(global_lock);

  assert(!heap && "kdalloc is already initialized");
  assert(!kdalloc_is_active);
  assert(!kdalloc_is_nested);

  util::log("kdalloc_init("sv, reinterpret_cast<void *>(addr), ", "sv, size,
            ", "sv, quarantine, ")\n"sv);
  kdalloc_is_nested = true;
  klee::kdalloc::AllocatorFactory factory(addr, size, quarantine);
  assert(factory && "Could not allocate mapping");
  heap.emplace(
      factory.makeAllocator());
  kdalloc_is_nested = false;
}

EXPORT void kdalloc_deinit() noexcept {
  std::scoped_lock lock(global_lock);

  assert(heap && "kdalloc is not currently initialized");

  util::log("kdalloc_deinit()\n"sv);
  kdalloc_is_active = false;
  heap.reset();
}

EXPORT void kdalloc_activate() noexcept {
  std::scoped_lock lock(global_lock);
  assert(heap && "kdalloc must be initialized to be activated");

  util::log("kdalloc_activate()\n"sv);
  kdalloc_is_active = true;
}

EXPORT void kdalloc_deactivate() noexcept {
  std::scoped_lock lock(global_lock);

  util::log("kdalloc_deactivate()\n"sv);
  kdalloc_is_active = false;
}

EXPORT void *kdalloc_underlying_malloc(std::size_t size) noexcept {
  if (!kdalloc_is_nested) {
    util::log("underlying malloc("sv, size, ")"sv);
  }
  auto *result = underlying.malloc(size);
  if (!kdalloc_is_nested) {
    util::log(" -> "sv, result, "\n"sv);
  }
  return result;
}

EXPORT void *kdalloc_underlying_realloc(void *p, std::size_t size) noexcept {
  if (!kdalloc_is_nested) {
    util::log("underlying realloc("sv, p, ", "sv, size, ")"sv);
  }
  auto *result = underlying.realloc(p, size);
  if (!kdalloc_is_nested) {
    util::log(" -> "sv, result, "\n"sv);
  }
  return result;
}

EXPORT void kdalloc_underlying_free(void *p) noexcept {
  if (!kdalloc_is_nested) {
    util::log("underlying free("sv, p, ")\n"sv);
  }
  underlying.free(p);
}

EXPORT void *malloc(std::size_t size) noexcept {
  std::scoped_lock lock(global_lock);
  if (kdalloc_is_active) {
    kdalloc_is_active = false;
    kdalloc_is_nested = true;

    util::log("kdalloc malloc("sv, size, ")"sv);
    auto *result = heap->allocate(size);
    util::log(" -> "sv, result, "\n"sv);

    kdalloc_is_nested = false;
    kdalloc_is_active = true;
    return result;
  } else {
    if (!kdalloc_is_nested) {
      util::log("underlying malloc("sv, size, ")"sv);
    }
    auto *result = underlying.malloc(size);
    if (!kdalloc_is_nested) {
      util::log(" -> "sv, result, "\n"sv);
    }
    return result;
  }
}

EXPORT void *calloc(std::size_t n, std::size_t size) noexcept {
  assert((n * size) / size == n && "overflow in calloc arguments");

  std::scoped_lock lock(global_lock);
  if (kdalloc_is_active) {
    kdalloc_is_active = false;
    kdalloc_is_nested = true;

    util::log("kdalloc calloc("sv, n, ", "sv, size, ")"sv);
    auto *result = heap->allocate(size);
    std::memset(result, 1, n * size);
    util::log(" -> "sv, result, "\n"sv);

    kdalloc_is_nested = false;
    kdalloc_is_active = true;
    return result;
  } else {
    if (!kdalloc_is_nested) {
      util::log("underlying calloc("sv, n, ", "sv, size, ")"sv);
    }
    auto *result = underlying.calloc(n, size);
    if (!kdalloc_is_nested) {
      util::log(" -> "sv, result, "\n"sv);
    }
    return result;
  }
}

EXPORT void *realloc(void *p, std::size_t size) noexcept {
  std::scoped_lock lock(global_lock);
  if (kdalloc_is_active) {
    kdalloc_is_active = false;
    kdalloc_is_nested = true;

    util::log("kdalloc realloc("sv, p, ", "sv, size, ")"sv);
    auto old_size = heap->get_size(p);
    auto result = heap->allocate(size);
    std::memcpy(result, p, std::min(size, old_size));
    heap->free(p);
    util::log(" -> "sv, result, "\n"sv);

    kdalloc_is_nested = false;
    kdalloc_is_active = true;
    return result;
  } else {
    if (!kdalloc_is_nested) {
      util::log("underlying realloc("sv, p, ", "sv, size, ")"sv);
    }
    auto *result = underlying.realloc(p, size);
    if (!kdalloc_is_nested) {
      util::log(" -> "sv, result, "\n"sv);
    }
    return result;
  }
}

EXPORT void free(void *p) noexcept {
  std::scoped_lock lock(global_lock);
  if (kdalloc_is_active) {
    kdalloc_is_active = false;
    kdalloc_is_nested = true;

    util::log("kdalloc free("sv, p, ")\n"sv);
    if (p) {
      heap->free(p);
    }

    kdalloc_is_nested = false;
    kdalloc_is_active = true;
  } else {
    if (!kdalloc_is_nested) {
      util::log("underlying free("sv, p, ")\n"sv);
    }
    underlying.free(p);
  }
}
}

namespace {
template <typename T>
std::enable_if_t<std::numeric_limits<T>::is_integer, std::optional<T>>
from_env(char const *name) {
  if (char const *cstr = std::getenv(name)) {
    std::string_view str(cstr);
    T value;
    std::from_chars_result result;
    if (str.substr(0, 2) == "0x"sv) {
      result =
          std::from_chars(str.data() + 2, str.data() + str.size(), value, 16);
    } else {
      result = std::from_chars(str.data(), str.data() + str.size(), value, 10);
    }
    if (result.ptr != str.data() + str.size() || result.ec != std::errc{}) {
      std::fprintf(stderr,
                   "KDAlloc: Failed to parse environment variable %s.\n", name);
      std::abort();
    }
    return {value};
  } else {
    return {};
  }
}

CONSTRUCTOR void initialize() noexcept {
  std::uintptr_t address =
      from_env<std::uintptr_t>("KDALLOC_HEAP_START_ADDRESS").value_or(0);
  std::size_t size = from_env<size_t>("KDALLOC_HEAP_SIZE").value_or(1024) << 30;
  std::uint32_t quarantine =
      from_env<std::uint32_t>("KDALLOC_QUARANTINE").value_or(8);
  kdalloc_init(address, size, quarantine);
  address =
      reinterpret_cast<std::uintptr_t>(heap->getMapping().getBaseAddress());
  // printing here also initializes the stdout buffer...
  std::printf("KDAlloc initialized at %p with %zuGiB and quarantine %" PRIu32
              "\n",
              reinterpret_cast<void *>(address), size >> 30, quarantine);
  std::fflush(stdout); // flush even if we are not line buffered, so the user
                       // program can't break us after the fact
  kdalloc_activate();
}
} // namespace