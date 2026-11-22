#include "Frontend.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/FileUtilities.h"
#include "llvm/Support/InitLLVM.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"

extern "C" void LLVMInitializeX86TargetInfo();
extern "C" void LLVMInitializeX86Target();
extern "C" void LLVMInitializeX86TargetMC();
extern "C" void LLVMInitializeX86AsmPrinter();
using namespace llvm;
using namespace cpn;
static std::string read(StringRef Path) {
  auto B = MemoryBuffer::getFile(Path);
  if (!B)
    fail({}, B.getError().message());
  return (*B)->getBuffer().str();
}
int main(int argc, char **argv) {
  InitLLVM Init(argc, argv);
  Options O;
  std::string Path;
  try {
    bool Edition = false, Mode = false;
    for (int I = 1; I < argc; ++I) {
      StringRef A(argv[I]);
      auto arg = [&](StringRef Flag) {
        if (A.starts_with((Flag + "=").str()))
          return A.drop_front(Flag.size() + 1).str();
        if (I + 1 >= argc)
          fail({}, "missing argument to " + Flag.str());
        return std::string(argv[++I]);
      };
      if (A == "--help" || A == "-h") {
        outs() << "Usage: cpnc --std=CPN26 [--check|-S|-c] [-o output] "
                  "source.cpn\n";
        return 0;
      }
      if (A == "--std" || A.starts_with("--std=")) {
        if (arg("--std") != "CPN26")
          fail({}, "--std requires CPN26");
        Edition = true;
      } else if (A == "-o")
        O.Output = arg("-o");
      else if (A == "--root-id" || A.starts_with("--root-id="))
        O.RootID = arg("--root-id");
      else if (A == "--config" || A.starts_with("--config="))
        O.Config = arg("--config");
      else if (A == "--identifiers" || A.starts_with("--identifiers=")) {
        Node N;
        N.Settings["source.identifiers"] = arg("--identifiers");
        configure(O, N);
      } else if (A == "--preset" || A.starts_with("--preset=")) {
        Node N;
        N.Settings["preset"] = arg("--preset");
        configure(O, N);
      } else if (A == "--check" || A == "-c" || A == "-S" ||
                 A == "--emit-llvm") {
        if (Mode)
          fail({}, "conflicting output modes");
        Mode = true;
        O.Check = A == "--check";
        O.IR = A == "-S" || A == "--emit-llvm";
      } else if (A.starts_with("-"))
        fail({}, "unknown option " + A.str());
      else if (!O.Input.empty())
        fail({}, "expected one root source unit");
      else
        O.Input = A.str();
    }
    if (!Edition)
      fail({}, "--std=CPN26 is required");
    if (O.Input.empty())
      fail({}, "missing input");
    Path = O.Config;
    if (!Path.empty()) {
      if (sys::path::filename(Path) != "cpn.config")
        fail({}, "project configuration must be named cpn.config");
      auto Config = parse(read(Path), O);
      if (Config.empty())
        fail({}, "empty project configuration");
      for (auto &N : Config) {
        if (N.K != Node::Config)
          fail(N.At, "expected configuration declaration");
        configure(O, N);
      }
    }
    Path = O.Input;
    auto Source = read(Path);
    auto AST = parse(Source, O);
    if (!AST.empty() && AST.front().K == Node::Config &&
        AST.front().Settings.count("source.identifiers")) {
      auto File = O;
      configure(File, AST.front());
      if (File.ASCII != O.ASCII)
        AST = parse(Source, File);
    }
    LLVMInitializeX86TargetInfo();
    LLVMInitializeX86Target();
    LLVMInitializeX86TargetMC();
    LLVMInitializeX86AsmPrinter();
    Triple TT("x86_64-unknown-linux-gnu");
    std::string Reason;
    auto *Target = TargetRegistry::lookupTarget(TT, Reason);
    if (!Target)
      fail({}, Reason);
    TargetOptions TO;
    std::unique_ptr<TargetMachine> TM(
        Target->createTargetMachine(TT, "generic", "", TO, Reloc::PIC_));
    LLVMContext C;
    Module M(O.RootID.empty() ? Path : O.RootID, C);
    M.setTargetTriple(TT);
    M.setDataLayout(TM->createDataLayout());
    compile(M, AST, O);
    if (verifyModule(M, &errs()))
      fail({}, "invalid generated LLVM module");
    if (O.Check)
      return 0;
    if (O.Output.empty()) {
      SmallString<256> P(Path);
      sys::path::replace_extension(P, O.IR ? "ll" : "o");
      O.Output = P.str().str();
    }
    if (sys::fs::equivalent(O.Output, Path))
      fail({}, "output would overwrite the source");
    int FD;
    SmallString<256> Temp;
    if (auto EC = sys::fs::createUniqueFile(O.Output + ".tmp-%%%%%%", FD, Temp))
      fail({}, EC.message());
    FileRemover Cleanup(Temp);
    bool Failed = false;
    {
      raw_fd_ostream Out(FD, true);
      if (O.IR)
        M.print(Out, nullptr);
      else {
        legacy::PassManager PM;
        Failed = TM->addPassesToEmitFile(PM, Out, nullptr,
                                         CodeGenFileType::ObjectFile);
        if (!Failed)
          PM.run(M);
      }
      Out.close();
      Failed |= Out.has_error();
      Out.clear_error();
    }
    if (Failed)
      fail({}, "cannot emit requested output");
    if (auto EC = sys::fs::rename(Temp, O.Output))
      fail({}, EC.message());
    Cleanup.releaseFile();
    return 0;
  } catch (const Diagnostic &D) {
    errs() << (Path.empty() ? "cpnc" : Path) << ":" << D.At.Line << ":"
           << D.At.Column << ": ERROR: " << D.Message << "\n";
    return 1;
  }
}
