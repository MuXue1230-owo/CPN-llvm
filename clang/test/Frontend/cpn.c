// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -x cpn -fsyntax-only %s
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -x cpn -std=cpn26 -fsyntax-only %s
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -x cpn-cpp-output -std=cpn26 -fsyntax-only %s
// RUN: cp %s %t.cpn
// RUN: cp %s %t.cpni
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -fsyntax-only %t.cpn
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -fsyntax-only %t.cpni

// Reject another language's standard instead of silently changing languages.
// RUN: not %clang_cc1 -x cpn -std=c++26 -fsyntax-only %s 2>&1 | FileCheck %s --check-prefix=CPN-CXX
// RUN: not %clang_cc1 -x cpn -std=c17 -fsyntax-only %s 2>&1 | FileCheck %s --check-prefix=CPN-C
// RUN: not %clang_cc1 -x c -std=cpn26 -fsyntax-only %s 2>&1 | FileCheck %s --check-prefix=C-CPN
// RUN: not %clang_cc1 -x c++ -std=cpn26 -fsyntax-only %s 2>&1 | FileCheck %s --check-prefix=CXX-CPN
// RUN: not %clang_cc1 -x cpn -cl-std=CL3.0 -fsyntax-only %s 2>&1 | FileCheck %s --check-prefix=CPN-CL
// RUN: not %clang_cc1 -x cpn -std=cpn27 -fsyntax-only %s 2>&1 | FileCheck %s --check-prefix=UNKNOWN
// CPN-CXX: error: invalid argument '-std=c++26' not allowed with 'CPN'
// CPN-C: error: invalid argument '-std=c17' not allowed with 'CPN'
// C-CPN: error: invalid argument '-std=cpn26' not allowed with 'C'
// CXX-CPN: error: invalid argument '-std=cpn26' not allowed with 'C++'
// CPN-CL: error: invalid argument '-cl-std=CL3.0' not allowed with 'CPN'
// UNKNOWN: error: invalid value 'cpn27' in '-std=cpn27'
// UNKNOWN-NEXT: note: use 'cpn26' for 'CPN26 experimental bootstrap' standard

// Reparse the serialized invocation, including the distinct preprocessed kind.
// RUN: %clang_cc1 -x cpn -std=cpn26 -fsyntax-only -round-trip-args -Rround-trip-cc1-args %s 2>&1 | FileCheck %s --check-prefix=ROUNDTRIP
// RUN: %clang_cc1 -x cpn-cpp-output -std=cpn26 -fsyntax-only -round-trip-args -Rround-trip-cc1-args %s 2>&1 | FileCheck %s --check-prefix=ROUNDTRIP-PP
// ROUNDTRIP: remark: generated arguments #{{.*}} in round-trip:
// ROUNDTRIP-DAG: "-std=cpn26"
// ROUNDTRIP-DAG: "-x" "cpn"
// ROUNDTRIP-PP: remark: generated arguments #{{.*}} in round-trip:
// ROUNDTRIP-PP-DAG: "-std=cpn26"
// ROUNDTRIP-PP-DAG: "-x" "cpn-cpp-output"

extern "C" void host_callback();
extern "C" void cpn_entry() { host_callback(); }
