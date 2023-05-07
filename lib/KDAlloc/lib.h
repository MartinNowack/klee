#pragma once

#ifdef __cplusplus

#define KDALLOC_NOEXCEPT noexcept
#define KDALLOC_SIZE_T std::size_t
#define KDALLOC_UINTPTR_T std::uintptr_t
#define KDALLOC_UINT32_T std::uint32_t

#include <cstddef>
#include <cstdint>

#else

#define KDALLOC_NOEXCEPT
#define KDALLOC_SIZE_T size_t
#define KDALLOC_UINTPTR_T uintptr_t
#define KDALLOC_UINT32_T uint32_t

#include <stddef.h>
#include <stdint.h>

#endif

#ifdef __cplusplus
extern "C" {
#endif

void kdalloc_init(KDALLOC_UINTPTR_T addr, KDALLOC_SIZE_T size, KDALLOC_UINT32_T quarantine) KDALLOC_NOEXCEPT;
void kdalloc_deinit(void) KDALLOC_NOEXCEPT;
void kdalloc_activate(void) KDALLOC_NOEXCEPT;
void kdalloc_deactivate(void) KDALLOC_NOEXCEPT;

void* kdalloc_underlying_malloc(KDALLOC_SIZE_T size) KDALLOC_NOEXCEPT;
void* kdalloc_underlying_realloc(void* p, KDALLOC_SIZE_T size) KDALLOC_NOEXCEPT;
void kdalloc_underlying_free(void* p) KDALLOC_NOEXCEPT;

#ifdef __cplusplus
}
#endif