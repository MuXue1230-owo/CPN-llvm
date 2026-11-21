# CPN26 frontend bootstrap

CPN-llvm provides an experimental language entry for CPN26, the single current
edition of [CPN](https://github.com/MuXue1230-owo/CPN/tree/CPN26). This stage
establishes language selection, frontend identity, and the path from source to
ordinary native object files.

The implementation uses Clang's existing C++26 parser and lowering. The tested
CPN subset consists of basic foreign function declarations, definitions, and
calls with `void` signatures. CPN26 Core conformance requires further language
implementation, including native numeric types and policies, declaration
classification, configuration, and lifetime semantics. Accepted C++ syntax is
bootstrap behavior and supplies no additional CPN26 semantic guarantee.

## Selecting the language

| Input or option | Behavior |
| --- | --- |
| `file.cpn` | Selects CPN source and defaults to CPN26. |
| `-x cpn` | Selects CPN for a named input or standard input. |
| `-std=cpn26` | Explicitly selects the CPN26 bootstrap standard for CPN input. |
| `file.cpni` or `-x cpn-cpp-output` | Selects preprocessed CPN input. |

Both `clang` and `clang++` preserve the CPN input kind. The frontend keeps a
distinct CPN language identity through invocation regeneration and serialized
language options. A C or C++ input paired with `-std=cpn26` receives an
incompatible-standard diagnostic; CPN input paired with a C or C++ standard
receives the corresponding diagnostic. An unknown CPN edition receives an
invalid-standard diagnostic.

Preprocessing and the `.cpni` form are implementation facilities for this
bootstrap. CPN26 Core does not specify C-style macro replacement as its lexical
mechanism. The ordinary `-E`, `-save-temps`, `-S`, `-emit-llvm`, `-c`, and
`-fsyntax-only` paths retain the selected CPN language identity.

## Compiling a native component

Save this source as `entry.cpn`:

```cpp
extern "C" void host_callback();

extern "C" void cpn_entry() {
    host_callback();
}
```

With a compiler built from this repository:

```sh
build/bin/clang -std=cpn26 -fsyntax-only entry.cpn
build/bin/clang -std=cpn26 -c entry.cpn -o entry.o
build/bin/clang -x cpn -std=cpn26 -S -emit-llvm entry.cpn -o entry.ll
build/bin/clang -E entry.cpn -o entry.cpni
build/bin/clang -c entry.cpni -o entry-preprocessed.o
```

The host defines `host_callback` and calls `cpn_entry`. Compile the foreign
translation units under their own C or C++ standards, then link their objects
with the CPN object using a matching target and ABI. Use the C++ link driver when
the foreign program requires its C++ runtime.

For an x86-64 Windows target, the same CPN source can produce a COFF object:

```sh
build/bin/clang --target=x86_64-pc-windows-msvc -std=cpn26 \
  -c entry.cpn -o entry.obj
```

The matching Windows toolchain supplies final linking and execution. Producing
an ELF or COFF object establishes the tested native component path; general C++
class layout, exceptions, runtime interoperability, and CPN provider contracts
need their own implementations and tests.

## Implementation identification

CPN mode defines these compiler-extension macros:

| Macro | Value | Meaning |
| --- | --- | --- |
| `__CPN__` | `26` | The selected CPN edition. |
| `__CPN_BOOTSTRAP__` | `1` | This implementation uses the experimental bootstrap. |

`__cplusplus` and the existing C++ feature macros continue to describe the
inherited parser baseline for compatibility with the reused frontend. These
macros are implementation identification, separate from a CPN26 conformance
claim. Ordinary C and C++ language modes keep their existing predefines.

## Building and checking

Build the Clang frontend with the targets needed by your application. For the
x86-64 ELF/COFF checks in this slice:

```sh
cmake -S llvm -B build -G Ninja -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS=clang -DLLVM_TARGETS_TO_BUILD=X86 \
  -DLLVM_ENABLE_ASSERTIONS=ON
cmake --build build --target clang FileCheck llvm-readobj split-file
```

The focused tests are in `clang/test/Driver`, `clang/test/Frontend`,
`clang/test/Preprocessor`, and `clang/test/CodeGen/CPN`. The native interoperability
check builds and runs C and C++ host programs against a CPN-generated object:

```sh
python3 clang/utils/cpn-smoke-test.py --clang build/bin/clang
```

The smoke check requires a working native linker and host C/C++ runtime setup.
Its callback verifies execution across the foreign boundary. The CPN source
uses `void` signatures so this check remains independent of native CPN integer
types and the hosted `i32 main()` entry, which belong to subsequent language
implementation.
