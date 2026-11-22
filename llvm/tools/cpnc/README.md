# cpnc

`cpnc` compiles one CPN26 root source unit to LLVM IR or an ordinary x86-64 Linux ELF object. Its C++ frontend constructs and verifies a module with the LLVM C++ API. The linked X86 target emits machine code in-process. It implements a subset of the [CPN26 standard](https://github.com/MuXue1230-owo/CPN/blob/CPN26/CPN26.md). The grammar reference is chapter 15. Chapter 21 §6.1 defines the requirements for a Core conformance claim.

## Build and run

Build from the LLVM checkout using its CMake, Ninja, Python and host C++ toolchain requirements.

```sh
cmake -S llvm -B build -G Ninja -DCMAKE_BUILD_TYPE=Release -DLLVM_TARGETS_TO_BUILD=X86
cmake --build build --target cpnc
build/bin/cpnc --std=CPN26 -c example.cpn -o example.o
cc example.o -o example
./example
```

For example, this program returns 42:

```cpn
generic<const i32 N>
i32 repeat(i32 value) {
    i32 sum;
    for (i32 n(0); n < N; ++n) {
        sum += value;
    }
    return sum;
}

i32 main() {
    return repeat<6>(7);
}
```

Use `--check` to bind and check the source or `-S` to emit textual IR. The built `cpnc` executable runs independently of Python and `llc`. Python generates immutable Unicode tables during the build and runs the test harness. Run `cmake --build build --target check-cpnc` on x86-64 Linux to verify the driver, IR, diagnostics and native execution.

## CPN26 Core implementation status

The conformance boundary is [chapter 21 §6.1](https://github.com/MuXue1230-owo/CPN/blob/CPN26/spec/21_abstract_machine_and_conformance.md). The frontend implements the features below on x86-64 Linux. Core conformance is **incomplete**.

| Area | Implemented and exercised |
| --- | --- |
| Source and declarations (ch. 10, 12, 15, 21) | Explicit edition, UTF-8, nested comments, Unicode 17.0.0 XID/NFC or ASCII identifiers, character and UTF-8 string literals, aliases, namespaces, incomplete nominal declarations, ordinary functions, argument-by-argument overload ranking, reference-category and receiver matching, selected-declaration access and deletion checks, prototypes, declaration-site trailing parameter defaults (including references to earlier parameters), locals and file-scope objects. |
| Numbers and configuration (ch. 2, 4, 7, 8) | Exact integer literal expressions, the 8/16/32/64-bit catalogue, platform integers, mathematical mixed-sign comparisons, Native/Checked/Wrapping/Saturating integer policies, scoped integer overrides, decimal and hexadecimal real literals rounded directly to f32/f64, IEEE binary32/binary64 storage, arithmetic and comparisons, project and file configuration, diagnostic filtering and promotion. |
| Types and control (ch. 10, 12, 15) | Arrays, basic object pointers and references, ordinary native function pointers with target-typed overload selection, indirect calls and noexcept weakening, closed integer enums, tagged unions with scalar payloads and exhaustive match, synchronous closures with explicit copy, reference, initializer and this captures and mutable receivers, nominal records with nonvirtual bases, virtual member dispatch across nonvirtual bases, final records and slots, receiver-category overloads, inherited member lookup, unambiguous base-pointer and base-reference conversions, control-flow statements, short circuiting, switch arms, explicit fallthrough, labels, restricted goto, labeled break/continue, and scalar constexpr/consteval function evaluation. |
| Generics (ch. 10, 15, 27) | Type/value function and record families, explicit applications, direct-family defaults, deduction for simple values, references and pointers, ordinary type and constant packs, ordered call-argument expansions, forwarding references, compile-time array extents, and nondependent name checks. Implemented requirements include Boolean predicates, SameType and ordinary object predicates, simple structural expression requirements and selected if constexpr branches. |
| Lifetime and storage (ch. 6, 12) | Field initialization, authored constructors and member functions, acyclic same-class constructor delegation with canonical ordering of deferred init producers, authored and explicitly defaulted copy/move construction and assignment, memberwise operations on bases and arrays, parameter and return value construction, scoped destruction and temporary cleanup, ordered array-element construction and reverse destruction, direct first-assignment construction and field-order checks across tested straight-line, branching, delegation and loop cases, virtual destructors and active-layer virtual calls, local Manual/Complete barriers, direct base initialization, cleanup bodies and direct base-only requests within the current destructor, and typed construction tails on local and file-scope objects, and local whole-object destroy, abandon, storage_of and construct_at. Registered storage tracks generation and the current destructor across same-storage replacement. |
| Static lifetime (ch. 8, 11) | Root ownership, file-scope and block-local static objects, serial dynamic initialization, direct reads checked for publication, reverse shutdown, static_id and init_after metadata, duplicate identity and dependency-cycle errors. |
| Native output (ch. 9, 20, 21) | LLVM IR, ELF64 relocatable objects, a hosted i32 main(), C-linked scalar functions, C linkage blocks and nested namespaces, compatible declarations sharing one external symbol, and scalar external object declarations and definitions. |

The executable tests in [tests/test_cpnc.py](tests/test_cpnc.py) compile source, verify the IR with llvm-as, link the object with the host C compiler and check the result. Negative cases test parser rejection, binding rules, numeric domains, lifetime violations and initializer-skipping transfers.

### Outstanding Core coverage

* Declaration binding and grammar are partial. Remaining work includes full closure borrowing and effect-bearing callable types, nontrivial union payloads, richer qualified declarations, and the full rules for overloads, nested pack patterns, structural witnesses, and definition-time proof of dependent operations across the entire parameter domain.
* Record lifetime support still needs shared virtual-base layouts, complete access checking and final-storage identity across calls, first-assignment analysis through arbitrary transfers and interprocedural initializes contracts, construction tails on subobjects and rollback, virtual-base Owner responsibilities, Whole propagation across helper calls and layers, and individually ended or replaced array-element generations.
* Local whole-object replacement is implemented. Subobject replacement, full pointer provenance and escape analysis across calls, storage transfer and allocator ownership remain incomplete.
* Constant expressions, configuration scopes, diagnostic codes, thread-local storage, indirect access to objects during initialization, and frozen boundary checking cover a subset of their normative rules. Floating-point arithmetic covers f32 and f64. Full floating status, trap delivery, provider controls and the named numeric operation catalogue need additional implementation.
* The supported ABI is x86-64 System V for the tested scalar boundary. C++ ABI features, separate compilation, module imports, reflection, exceptions and concurrent execution are unimplemented capabilities.

### Target and invocation

The driver defaults to the Unicode identifier profile and the Debug integer policy. Use `--preset Release` for Native arithmetic, `--identifiers ascii` for the ASCII profile, or `--config path/to/cpn.config` to supply project configuration. A supplied project file must contain configuration declarations. The project and source use the same CPN26 configuration syntax.

The LLVM module identifier defaults to the input path. Use `--root-id ID` to assign it an explicit root identity. CPN-internal symbols have module-local linkage. File-scope startup and shutdown use the ELF constructors and destructors emitted by LLVM.

The target has eight-bit bytes and 64-bit platform integers. Native addition, subtraction, multiplication and negation use modulo arithmetic. Exceptional Native division or remainder and invalid variable shift counts terminate through a target trap. Known invalid ordinary division or shift domains produce a source diagnostic. Direct object creation writes an ELF object suitable for the ordinary system linker.

The build compiles the Unicode tables into the driver. [utils/build_ucd.py](utils/build_ucd.py) reproduces them from the pinned Unicode 17.0.0 data files. Their license is included in [unicode/LICENSE.txt](unicode/LICENSE.txt).
