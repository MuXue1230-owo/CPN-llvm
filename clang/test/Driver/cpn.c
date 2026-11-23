// A CPN input keeps its language identity through the driver and saved
// preprocessed output. The .c test suffix is only for lit discovery.
// RUN: cp %s %t.cpn
// RUN: %clang --target=x86_64-unknown-linux-gnu -### -c %t.cpn 2>&1 | FileCheck %s --check-prefix=CPN
// RUN: %clang --target=x86_64-unknown-linux-gnu --driver-mode=g++ -### -c %t.cpn 2>&1 | FileCheck %s --check-prefix=CPN
// RUN: %clang --target=x86_64-unknown-linux-gnu -### -c -x cpn %s 2>&1 | FileCheck %s --check-prefix=CPN
// RUN: %clang --target=x86_64-unknown-linux-gnu -### -c -x cpn -std=cpn26 %s 2>&1 | FileCheck %s --check-prefix=EXPLICIT
// RUN: %clang --target=x86_64-unknown-linux-gnu -### -c -x cpn -std=cpn26 - 2>&1 | FileCheck %s --check-prefix=STDIN
// RUN: %clang --target=x86_64-unknown-linux-gnu -fsyntax-only %t.cpn
// RUN: %clang --target=x86_64-unknown-linux-gnu -fsyntax-only -x cpn -std=cpn26 - < %s
// CPN: "-cc1"
// CPN-SAME: "-x" "cpn"
// EXPLICIT: "-cc1"
// EXPLICIT-SAME: "-std=cpn26"
// EXPLICIT-SAME: "-x" "cpn"
// STDIN: "-cc1"
// STDIN-SAME: "-std=cpn26"
// STDIN-SAME: "-x" "cpn" "-"

// RUN: cp %s %t.cpni
// RUN: %clang --target=x86_64-unknown-linux-gnu -### -c %t.cpni 2>&1 | FileCheck %s --check-prefix=PREPROCESSED
// RUN: %clang --target=x86_64-unknown-linux-gnu -fsyntax-only %t.cpni
// RUN: %clang --target=x86_64-unknown-linux-gnu -fsyntax-only -x cpn-cpp-output -std=cpn26 %s
// PREPROCESSED: "-cc1"
// PREPROCESSED-SAME: "-x" "cpn-cpp-output"

// RUN: %clang --target=x86_64-unknown-linux-gnu -### -save-temps=obj -std=cpn26 -c %t.cpn -o %t.o 2>&1 | FileCheck %s --check-prefix=SAVE
// SAVE: "-cc1"
// SAVE-SAME: "-E"
// SAVE-SAME: "-o" "{{[^"]+}}.cpni"
// SAVE-SAME: "-x" "cpn"
// SAVE: "-cc1"
// SAVE-SAME: "-emit-llvm-bc"
// SAVE-SAME: "-x" "cpn-cpp-output"

// The MSVC C++ default must not override CPN's default edition.
// RUN: %clang --target=x86_64-pc-windows-msvc -### -c %t.cpn 2>&1 | FileCheck %s --check-prefix=WINDOWS
// RUN: %clang --target=x86_64-pc-windows-msvc -fsyntax-only %t.cpn
// WINDOWS-NOT: "-std=c++
// WINDOWS: "-cc1"
// WINDOWS-NOT: "-std=c++
// WINDOWS: "-x" "cpn"
// WINDOWS-NOT: "-std=c++

// Explicit source language continues to take precedence over the suffix.
// RUN: %clang --target=x86_64-unknown-linux-gnu -### -c -x c++ -std=c++26 %t.cpn 2>&1 | FileCheck %s --check-prefix=CXX
// CXX: "-cc1"
// CXX-SAME: "-std=c++26"
// CXX-SAME: "-x" "c++"

// RUN: not %clang -std=c++26 -fsyntax-only %t.cpn 2>&1 | FileCheck %s --check-prefix=WRONG-STANDARD
// RUN: not %clang -x c++ -std=cpn26 -fsyntax-only %s 2>&1 | FileCheck %s --check-prefix=WRONG-LANGUAGE
// WRONG-STANDARD: error: invalid argument '-std=c++26' not allowed with 'CPN'
// WRONG-LANGUAGE: error: invalid argument '-std=cpn26' not allowed with 'C++'

extern "C" void cpn_entry() {}
