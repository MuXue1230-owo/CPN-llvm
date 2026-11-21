// REQUIRES: x86-registered-target
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -x cpn -std=cpn26 -emit-llvm -o - %s | FileCheck %s --check-prefix=IR
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -x cpn -std=cpn26 -emit-obj -o %t.o %s
// RUN: llvm-readobj --file-headers --symbols %t.o | FileCheck %s --check-prefix=ELF
// RUN: %clang_cc1 -triple x86_64-pc-windows-msvc -x cpn -std=cpn26 -emit-obj -o %t.obj %s
// RUN: llvm-readobj --file-headers --symbols %t.obj | FileCheck %s --check-prefix=COFF

// Exercise real preprocessing and assembly stages, not just -### forwarding.
// RUN: cp %s %t.cpn
// RUN: %clang --target=x86_64-unknown-linux-gnu -std=cpn26 -save-temps=obj -c %t.cpn -o %t.saved.o
// RUN: llvm-readobj --file-headers --symbols %t.saved.o | FileCheck %s --check-prefix=ELF

// This common CPN26/Clang subset uses no C++ runtime or unimplemented CPN
// integer semantics. The source defines one C symbol and references another.
extern "C" void host_callback();

extern "C" void cpn_entry() {
  host_callback();
}

// IR-LABEL: define{{.*}} void @cpn_entry()
// IR: call void @host_callback()
// IR: ret void
// IR: declare void @host_callback()

// ELF: Format: elf64-x86-64
// ELF: Type: Relocatable (0x1)
// ELF: Machine: EM_X86_64 (0x3E)
// ELF: Name: cpn_entry
// ELF: Binding: Global
// ELF: Type: Function
// ELF: Section: .text
// ELF: Name: host_callback
// ELF: Section: Undefined

// COFF: Format: COFF-x86-64
// COFF: Machine: IMAGE_FILE_MACHINE_AMD64 (0x8664)
// COFF: Name: cpn_entry
// COFF: Section: .text
// COFF: StorageClass: External
// COFF: Name: host_callback
// COFF: Section: IMAGE_SYM_UNDEFINED
// COFF: StorageClass: External
