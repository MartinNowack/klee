#include <llvm/Support/CommandLine.h>

namespace cli {
extern llvm::cl::opt<std::string> chrootToDir;
extern llvm::cl::opt<bool> keepReplayDir;
extern llvm::cl::opt<bool> createFilesOnly;

extern llvm::cl::opt<std::string> libKDAlloc;
extern llvm::cl::opt<bool> kdalloc;

extern llvm::cl::opt<std::string> ktest;
extern llvm::cl::opt<std::string> program;

void parse(int argc, char **argv);
} // namespace cli