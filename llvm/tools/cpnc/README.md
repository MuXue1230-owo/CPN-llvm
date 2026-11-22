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
| Source and declarations (ch. 10, 12, 15, 21) | Explicit edition, UTF-8, nested comments, Unicode 17.0.0 XID/NFC or ASCII identifiers, character and UTF-8 string literals, reserved and contextual words, file, class and block type aliases, block-scoped nominal declarations and forward declarations, nested class, union and enum identities (including members of applied type families), parenthesized types, lexical shadowing and the ordinary declaration-name namespace, namespace and module-root name lookup, separate qualified definitions of previously declared functions, methods, constructors and destructors, incomplete nominal declarations, ordinary functions, static members, nominal member and nonmember operator overloads (including prefix/postfix increment, indexing and calls), argument-by-argument overload ranking, reference-category and receiver matching, selected-declaration access and deletion checks, prototypes, declaration-site trailing parameter defaults (including references to earlier parameters), ordered value-parameter construction before subsequent argument evaluation, locals and file-scope objects. |
| Numbers and configuration (ch. 2, 4, 7, 8) | Exact integer literal expressions, declaration-scoped subsets of the 8/16/32/64-bit catalogue with availability checked after common-type derivation, platform integers, mathematical mixed-sign comparisons, Native/Checked/Wrapping/Saturating integer policies, scoped integer overrides, decimal and hexadecimal real literals rounded directly to f32/f64, IEEE binary32/binary64 storage, arithmetic and comparisons, scoped rounding and subnormal controls, per-operation floating trap masks, sticky-event merging, Strict NaN selection and payload mapping, and constant arithmetic under the selected rounding mode, project and file configuration, diagnostic thresholds, code-based suppression and promotion. |
| Types and control (ch. 10, 12, 15) | Idempotent const qualification of objects, array elements and referents, canonical by-value parameter types, arrays including addressable zero-extent arrays, object pointers with checked offsets, one-past arithmetic and element distance when extent information is available, basic reference and named borrow-parameter contracts, unevaluated decltype queries retaining reference categories and callable contracts, native function pointers with positional noescape, returns_borrowed_from and consumes contracts, target-typed overload selection, indirect calls, noexcept weakening and lifecycle_effect(whole) checking, closed integer enums, tagged unions with discriminant-selected aligned payload storage, scalar and class-valued fields, authored and defaulted active-case copy and move construction, ordinary authored constructors on unions with a default case, static union members, default-case payload validation, and exhaustive match with owning or borrowed bindings, synchronous closures with explicit copy, reference, initializer and this captures and mutable receivers, explicit captureless-closure initialization of native function pointers with signature and effect checking, nominal records with nonvirtual and shared virtual bases, virtual member dispatch with receiver adjustment across both, final records and slots, receiver-category overloads, inherited member lookup, unambiguous base-pointer and base-reference conversions, control-flow statements, short circuiting, switch arms, explicit fallthrough, labels, restricted goto with reverse destruction on outward and backward jumps, labeled break/continue, and scalar constexpr/consteval function evaluation. |
| Generics (ch. 10, 15, 27) | Type/value function, record and tagged union families, inherited and static generic methods, qualified generic function and method definitions on ordinary owners, out-of-line ordinary member, constructor and destructor definitions on primary type/value families, accessible nested type requirements, explicit and partial ordinary type specializations, explicit applications, direct-family defaults, deduction for simple values, references and pointers, ordinary type and constant packs, ordered call-argument expansions, forwarding references, compile-time array extents, and definition-site binding of free overload sets, parameter defaults and numeric configuration. Ordinary and generic overloads compete by conversion rank, supported structural pattern specificity and conjunction subsumption. Implemented requirements include Boolean predicates, SameType, object and copy/move predicates, structural expression result categories and noexcept, and selected if constexpr branches. Generic definitions check dependent data-member access, method calls, indexing, callable objects, arithmetic, comparisons, unary and increment/decrement operations on direct type parameters using structural requirements, SameType bindings and if constexpr branch facts. This check also runs on unused definitions. The compiler enforces normalization, solver and instantiation budgets for supported operations. |
| Lifetime and storage (ch. 6, 12) | Final-storage initialization of positional fields in canonical order after bases, authored constructors and member functions, acyclic same-class constructor delegation with canonical ordering of deferred init producers, authored and explicitly defaulted copy/move construction and assignment, memberwise operations on bases and arrays, final-storage construction for native aggregate parameters and results across direct, virtual and indirect calls, conditional prvalues and owning closure captures, scoped destruction and temporary cleanup, ordered array-element construction with a counted loop for trailing defaults and reverse destruction, source-bound first-assignment construction through branches, switch, match, loops, delegation and goto, requires_initialized and initializes method contracts with normal-return checks, and immediate evaluation of the next available producer at a helper’s write, virtual destructors and active-layer virtual calls, local Manual/Complete barriers, canonical shared virtual-base initialization and destruction once per complete object, dormant virtual-base initializer arguments in embedded layers, direct base initialization, cleanup bodies, declarative virtual-base destruction owners and per-object owner transfer during construction and live use with frozen bindings on destruction entry, type and base_path selectors, Whole propagation through direct and indirect helpers and early requests on live complete objects, typed construction tails on local, file-scope and member objects, and destroy, abandon, storage_of and construct_at for complete objects, members and array elements. A sparse registration table retains each element’s cleanup rank, generation, capacity, and current destructor across replacement. Checked array pointers and element references retain bounds and generation metadata across local assignments, record fields, array elements, tagged payload storage, closure capture, conditionals, offsets, direct calls, virtual dispatch and indirect calls. C entry points retain their native signatures. |
| Static lifetime (ch. 8, 11) | Root ownership, file-scope and block-local static objects, serial dynamic initialization, static references bound once to a designated generation, constexpr pointer/reference designations of static objects and subobjects, constant pointer offsets and differences within a single extent, direct reads checked for publication, reverse shutdown, static_id and init_after metadata, duplicate identity and dependency-cycle errors. |
| Native output (ch. 9, 20, 21) | LLVM IR, ELF64 relocatable objects, a hosted i32 main(), C-linked scalar functions, C linkage blocks and nested namespaces, compatible declarations sharing one external symbol, and scalar external object declarations and definitions. |

The executable tests in [tests/test_cpnc.py](tests/test_cpnc.py) compile source, verify the IR with llvm-as, link the object with the host C compiler and check the result. Negative cases test parser rejection, binding rules, numeric domains, lifetime violations and initializer-skipping transfers.

### Outstanding Core coverage

* Declaration binding and grammar are partial. Remaining work includes full closure borrowing and the remaining callable effect contracts, full union active-case replacement contracts, qualified definitions on nested, packed or specialized generic owners, and the full rules for overloads, nested pack patterns, structural witnesses, and proof of dependent operations across the entire parameter domain.
* Record lifetime support still needs complete access checking, construction-state contracts across aliased receivers and inherited layers, construction rollback and complete lifecycle checking during construction and Cleanup.
* Complete objects and individually selected member and array-element extents support replacement, including by another fitting type. Pointer provenance after untracked foreign writes or raw storage reinterpretation, whole-program escape checking, storage transfer, and allocator ownership remain incomplete.
* Constant construction of aggregate values, the never result type, configuration scopes, diagnostic codes, thread-local storage, indirect access to objects during initialization, and frozen boundary checking cover a subset of their normative rules. Floating-point arithmetic covers f32 and f64. Status-bearing numerical result interfaces, FP context APIs, provider controls and the named numeric operation catalogue need additional implementation.
* The supported ABI is x86-64 System V for the tested scalar boundary. C++ ABI features, separate compilation, module imports, reflection, exceptions and concurrent execution are unimplemented capabilities.

### Target and invocation

The driver defaults to the Unicode identifier profile and the Debug integer policy. Use `--preset Release` for Native arithmetic, `--identifiers ascii` for the ASCII profile, or `--config path/to/cpn.config` to supply project configuration. A supplied project file must contain configuration declarations. The project and source use the same CPN26 configuration syntax.

The LLVM module identifier defaults to the input path. Use `--root-id ID` to assign it an explicit root identity. CPN-internal symbols have module-local linkage. File-scope startup and shutdown use the ELF constructors and destructors emitted by LLVM.

The target has eight-bit bytes and 64-bit platform integers. Native addition, subtraction, multiplication and negation use modulo arithmetic. Exceptional Native division or remainder and invalid variable shift counts terminate through a target trap. Known invalid ordinary division or shift domains produce a source diagnostic. Direct object creation writes an ELF object suitable for the ordinary system linker.

The build compiles the Unicode tables into the driver. [utils/build_ucd.py](utils/build_ucd.py) reproduces them from the pinned Unicode 17.0.0 data files. Their license is included in [unicode/LICENSE.txt](unicode/LICENSE.txt).
