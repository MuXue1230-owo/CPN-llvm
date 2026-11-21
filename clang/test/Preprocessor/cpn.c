// These are implementation identifiers for the experimental bootstrap, not
// CPN26 conformance macros. C++ predefines describe its current parser baseline.
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -x cpn -E -dM %s | FileCheck %s --check-prefix=CPN
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -x cpn -std=cpn26 -E -dM %s | FileCheck %s --check-prefix=CPN
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -x c++ -std=c++26 -E -dM %s | FileCheck %s --check-prefix=CXX --implicit-check-not=__CPN
// RUN: %clang_cc1 -triple x86_64-unknown-linux-gnu -x c -std=c17 -E -dM %s | FileCheck %s --check-prefix=C --implicit-check-not=__CPN
// CPN-DAG: #define __CPN__ 26
// CPN-DAG: #define __CPN_BOOTSTRAP__ 1
// CPN-DAG: #define __cplusplus 202400L
// CXX: #define __cplusplus 202400L
// C: #define __STDC_VERSION__ 201710L

// A .cpni file preserves CPN identity after the bootstrap preprocessing stage.
// RUN: %clang_cc1 -x cpn -std=cpn26 -E -P %S/../Frontend/cpn.c -o %t.cpni
// RUN: %clang_cc1 -std=cpn26 -fsyntax-only %t.cpni
// RUN: %clang_cc1 -x cpn-cpp-output -std=cpn26 -fsyntax-only %t.cpni
