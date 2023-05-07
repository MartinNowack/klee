#include "cli.h"

#include <filesystem>

#if defined(__APPLE__)
#include <cassert>

#include <libproc.h>
#include <unistd.h>
#endif

#if defined(__FreeBSD__)
#include <array>
#include <cstddef>

#include <sys/sysctl.h>
#endif

static std::filesystem::path executablePath() {
#if defined(__APPLE__)
  char pathbuf[PROC_PIDPATHINFO_MAXSIZE];
  [[maybe_unused]] int rc = proc_pidpath(getpid(), pathbuf, sizeof(pathbuf));
  assert(rc > 0);
  return std::filesystem::canonical(pathbuf);
#elif defined(__FreeBSD__)
  std::array<int, 4> mib = {CTL_KERN, KERN_PROC, KERN_PROC_PATHNAME, -1};

  std::size_t length = 0;
  [[mabye_unused]] int rc =
      sysctl(mib.data(), mib.size(), NULL, &length, NULL, 0);
  assert(rc == 0);

  std::string path(length, '\0');
  rc = sysctl(mib.data(), mib.size(), path.data(), &length, NULL, 0);
  assert(rc == 0);
  path.resize(length);
  return std::filesystem::canonical(path.data());
#else
  return std::filesystem::canonical("/proc/self/exe");
#endif
}

#include <cstdlib>
#include <iostream>

namespace cli {
static llvm::cl::OptionCategory kleeReplayCategory("General Options");

llvm::cl::opt<std::string>
    chrootToDir("chroot-to-dir",
                llvm::cl::desc("use chroot jail (requires CAP_SYS_CHROOT)"),
                llvm::cl::value_desc("DIR"), llvm::cl::cat(kleeReplayCategory));
static llvm::cl::alias
    chrootToDirShort("r", llvm::cl::desc("Alias for --chroot-to-dir"),
                     llvm::cl::aliasopt(chrootToDir));

llvm::cl::opt<bool>
    keepReplayDir("keep-replay-dir",
                  llvm::cl::desc("do not delete replay directory"),
                  llvm::cl::cat(kleeReplayCategory));
static llvm::cl::alias
    keepReplayDirShort("k", llvm::cl::desc("Alias for --keep-replay-dir"),
                       llvm::cl::aliasopt(keepReplayDir));

llvm::cl::opt<bool>
    createFilesOnly("create-files-only",
                    llvm::cl::desc("only create the input files"),
                    llvm::cl::cat(kleeReplayCategory));

llvm::cl::opt<std::string>
    libKDAlloc("libkdalloc", llvm::cl::desc("location of libKDAlloc.so"),
               llvm::cl::init(executablePath().parent_path() / ".." / "lib" /
                              "libKDAlloc.so"),
               llvm::cl::cat(kleeReplayCategory));

llvm::cl::opt<bool> kdalloc("kdalloc", llvm::cl::desc("run with kdalloc"),
                            llvm::cl::cat(kleeReplayCategory));

llvm::cl::opt<std::string> ktest(llvm::cl::Positional, llvm::cl::Required,
                                 llvm::cl::desc("ktest-file"),
                                 llvm::cl::cat(kleeReplayCategory));

llvm::cl::opt<std::string> program(llvm::cl::Positional, llvm::cl::Required,
                                   llvm::cl::desc("program"),
                                   llvm::cl::cat(kleeReplayCategory));

void parse(int argc, char **argv) {
  for (auto &elem : llvm::cl::getRegisteredOptions()) {
    if (std::all_of(elem.second->Categories.begin(),
                    elem.second->Categories.end(),
                    [](llvm::cl::OptionCategory *cat) {
                      return cat != &cli::kleeReplayCategory;
                    })) {
      elem.second->setHiddenFlag(llvm::cl::Hidden);
    }
  }

  llvm::cl::ParseCommandLineOptions(argc, argv,
                                    "Use KLEE_REPLAY_TIMEOUT environment "
                                    "variable to set a timeout (in seconds).");
}
} // namespace cli