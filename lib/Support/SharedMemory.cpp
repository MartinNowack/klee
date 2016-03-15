/*
 * SharedMemory.cpp
 *
 *  Created on: Aug 14, 2015
 *      Author: seadmin
 */

#include "klee/util/SharedMemory.h"

#include <assert.h>
#include <fcntl.h> /* Defines O_* constants */
#include <string>
#include <sys/mman.h>
#include <sys/stat.h> /* Defines mode constants */
#include <sys/types.h>
#include <pthread.h>
#include <unistd.h>

#include <time.h>
#include <sys/time.h>
#include <mutex>

#include "llvm/Support/raw_ostream.h"
namespace {

struct Sync {
  int init;
  struct SyncItem {
    pthread_mutex_t mutex;
    pthread_cond_t cv;
    volatile bool condition;
  };
  SyncItem syncs[2];
  volatile bool terminate;

  size_t usedSize;

  klee::SharedMem::command command;
};

pthread_mutexattr_t attrmutex;
pthread_condattr_t attrcond;

static bool attributeInitialized = false;

void initAttributes() {
  static std::mutex m;
  std::lock_guard<std::mutex> lock(m);
  if (!attributeInitialized) {
    // Initialize mutex
    pthread_mutexattr_init(&attrmutex);
    pthread_mutexattr_setpshared(&attrmutex, PTHREAD_PROCESS_SHARED);

    // Initialize condition variable
    pthread_condattr_init(&attrcond);
    pthread_condattr_setpshared(&attrcond, PTHREAD_PROCESS_SHARED);

    attributeInitialized = true;
  }
}

void destroyAttributes() {
  static std::mutex m;
  std::lock_guard<std::mutex> lock(m);
  if (attributeInitialized) {
    pthread_mutexattr_destroy(&attrmutex);
    pthread_condattr_destroy(&attrcond);
    attributeInitialized = false;
  }
}
}

#define ALIGNMENT 0x8 // We want word based alignment

namespace klee {

SharedMem::SharedMem(size_t _size, std::string _name)
    : // Allocated memory should be aligned. Make sure we align it word based
      size(_size + sizeof(Sync) + ALIGNMENT - 1),
      size_orig(_size), addr(nullptr), name(_name) {
  initAttributes();
  initMemory();
}

void SharedMem::initMemory() {
  // Auto generate new file name if none is given
  if (name == "")
    name = "klee_" + std::to_string(getpid());

  // Allocate shared memory descriptor
  auto fd = shm_open(name.c_str(), O_CREAT | O_RDWR, S_IRUSR | S_IWUSR);
  assert(fd >= 0 && "Couldn't open shared memory");
  // Truncate to appropriate size (requested + meta data Sync)
  auto res = ftruncate(fd, size);
  assert(res == 0);
  addr = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  assert((void *)-1 != addr);
  // Check for three cases:
  //   1) we have to initialize the memory,
  //   2) somebody else is doing it already, so wait
  //   3) all set
  switch (__sync_val_compare_and_swap(&((Sync *)(addr))->init, 0, 1)) {
  case 0:
    // Initialize mutex
    for (auto &citem : ((Sync *)(addr))->syncs) {
      pthread_mutex_init(&citem.mutex, &attrmutex);
      pthread_cond_init(&citem.cv, &attrcond);
      citem.condition = false;
    }
    ((Sync *)(addr))->init = 2;
    break;
  case 1:
    while (__sync_val_compare_and_swap(&((Sync *)(addr))->init, 0, 1) < 2) {
    }
    break;
  default:
    break;
  }
}

void SharedMem::resetSync() {
  for (auto &citem : ((Sync *)(addr))->syncs) {
    citem.condition = false;
  }
}

void *SharedMem::getAddr() {
  assert(addr);
  auto newAddr = (char *)addr + sizeof(Sync) + sizeof(uint64_t);
  return (void *)((intptr_t)newAddr & ~ALIGNMENT);
}

SharedMem::~SharedMem() {
  if (addr) {
    auto res = munmap(addr, size);
    assert(res != -1);

    addr = nullptr;

    shm_unlink(name.c_str());
  }
  destroyAttributes();
}

void SharedMem::lock() {
  assert(addr);
  pthread_mutex_lock(&((Sync *)addr)->syncs[SharedMem::PRODUCER].mutex);
}

void SharedMem::unlock() {
  assert(addr);
  pthread_mutex_unlock(&((Sync *)addr)->syncs[SharedMem::PRODUCER].mutex);
}

void SharedMem::wait(size_t id) {
  assert(addr);
  while (!((Sync *)addr)->syncs[id].condition) {
    pthread_cond_wait(&((Sync *)addr)->syncs[id].cv,
                      &((Sync *)addr)->syncs[SharedMem::PRODUCER].mutex);
  }
  // reset condition
  ((Sync *)addr)->syncs[id].condition = false;
}

bool SharedMem::waitTimeout(size_t id, uint64_t duration) {
  struct timespec now;
  assert(addr);

  if (!((Sync *)addr)->syncs[id].condition) {
    clock_gettime(CLOCK_REALTIME, &now);
    now.tv_sec += duration;

    int res = 0;
    while (!((Sync *)addr)->syncs[id].condition && res == 0) {
      res = pthread_cond_timedwait(
          &((Sync *)addr)->syncs[id].cv,
          &((Sync *)addr)->syncs[SharedMem::PRODUCER].mutex, &now);
    }
    assert(((Sync *)addr)->syncs[id].condition || res == ETIMEDOUT);

    if (res == ETIMEDOUT)
      return false;
  }

  // reset condition
  ((Sync *)addr)->syncs[id].condition = false;
  return true;
}

void SharedMem::signal(size_t id) {
  assert(addr);
  ((Sync *)addr)->syncs[id].condition = true;
  pthread_cond_signal(&((Sync *)addr)->syncs[id].cv);
}

bool SharedMem::exit() {
  assert(addr);
  return ((Sync *)addr)->terminate;
}

void SharedMem::signalExit() {
  assert(addr);
  ((Sync *)addr)->terminate = true;
  signal(SharedMem::CONSUMER);
}

size_t SharedMem::getSize() {
  assert(addr);
  return size_orig;
}

size_t SharedMem::getUsedSize() {
  assert(addr);
  return ((Sync *)addr)->usedSize;
}

void SharedMem::setUsedSize(size_t size) {
  assert(addr);
  ((Sync *)addr)->usedSize = size;
}

void SharedMem::clearMemory() {
  assert(addr);

  // clear
  memset(getAddr(), 0, ((Sync *)addr)->usedSize);

  // reset counter
  ((Sync *)addr)->usedSize = 0;
}

void SharedMem::setCommand(command c) {
  assert(addr);
  ((Sync *)addr)->command = c;
}

SharedMem::command SharedMem::getCommand() {
  assert(addr);
  return ((Sync *)addr)->command;
}

} // namespace klee
