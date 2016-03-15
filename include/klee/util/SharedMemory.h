/*
 * SharedMemory.h
 *
 *  Created on: Aug 14, 2015
 *      Author: seadmin
 */

#ifndef INCLUDE_KLEE_UTIL_SHAREDMEMORY_H_
#define INCLUDE_KLEE_UTIL_SHAREDMEMORY_H_

#include <cstdlib>
#include <string>

namespace klee {

class SharedMem {
public:
  /// size in byte
  SharedMem(size_t size, std::string name = "");
  ~SharedMem();

  void *getAddr();

  void lock();
  void unlock();
  void wait(size_t id);
  // wait for signal or timeout
  // Returns true if condition set or false if timeout
  bool waitTimeout(size_t id, uint64_t duration);
  void signal(size_t id);

  bool exit();
  void signalExit();

  /// Returns the size of the whole allocation
  size_t getSize();

  /// Returns the size of the used part of the memory in byte.
  /// The allocation is consecutive from the beginning
  size_t getUsedSize();

  /// Set size of the used part
  void setUsedSize(size_t size);

  /// Initializes used memory with zero
  void clearMemory();

  /// Reset synchronization variables of SharedMem
  /// Attention, the reset happens unprotected
  void resetSync();

  enum role { PRODUCER = 0, CONSUMER = 1 };

  constexpr static size_t defaultSize = 40 * 1024 * 1024;

  /// TODO move me to descending class
  enum command {
    INITIAL_VALUE = 0,
    CONSTRAINT_LOG = 1,
    COMPUTE_TRUTH = 2,
    COMPUTE_VALUE = 3
  };

  void setCommand(command c);
  command getCommand();

  class Locker {
  public:
    ~Locker() { memory.unlock(); }
    Locker(SharedMem &mem) : memory(mem) { memory.lock(); }

  private:
    SharedMem &memory;
  };

private:
  size_t size;
  size_t size_orig;
  void *addr;
  std::string name;

  void initMemory();
};
}
#endif /* INCLUDE_KLEE_UTIL_SHAREDMEMORY_H_ */
