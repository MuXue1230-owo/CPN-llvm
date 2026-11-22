"""Exercise the command line, LLVM verifier, native linker, and generated programs."""

import os
from pathlib import Path
import subprocess
import shutil
import tempfile
import unittest


DRIVER = [os.environ.get("CPNC") or shutil.which("cpnc") or "cpnc"]


class CompilerTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.dir = Path(temp.name)
        self.src = self.dir / "example.cpn"

    def compile(self, source, *options, edition=True):
        self.src.write_text(source, encoding="utf-8")
        standard = ["--std=CPN26"] if edition else []
        return subprocess.run(
            [*DRIVER, *standard, *options, self.src], capture_output=True, text=True
        )

    def program(self, source, *options, host=None):
        ir = self.compile(source, "-S", *options)
        self.assertEqual(ir.returncode, 0, ir.stderr)
        subprocess.run(
            ["llvm-as", self.src.with_suffix(".ll"), "-o", os.devnull], check=True
        )
        obj = self.compile(source, "-c", *options)
        self.assertEqual(obj.returncode, 0, obj.stderr)
        cmd = ["cc", self.src.with_suffix(".o")]
        if host:
            cfile = self.dir / "host.c"
            cfile.write_text(host, encoding="utf-8")
            cmd.append(cfile)
        exe = self.dir / "program"
        subprocess.run([*cmd, "-o", exe], check=True)
        return subprocess.run([exe], cwd=self.dir).returncode

    def test_empty_arrays_and_extent_pointer_arithmetic(self):
        self.assertEqual(
            self.program("""
            i32 drops;struct Item{~Item(){++drops;}};
            i32 main(){
                {Item[0] empty;if(sizeof(empty)<1 || alignof(Item[0])!=alignof(Item)){return 1;}}
                i32[4] a(1,2,3,4);i32[2] b(11,12);
                i32* p(&a[1]);i32* end(p+3);if(end-p!=3 || *(end-2)!=3){return 2;}
                p=&b[0]; if(*(1+p)!=12 || drops!=0){return 3;}return 42;
            }"""),
            42,
        )
        for body in (
            "return *(p+2);",
            "return *(p-1);",
            "return (p-&b[0])==0 ? 1 : 2;",
        ):
            self.assertLess(
                self.program(
                    "i32 main(){i32[2] a;i32[2] b;i32* p(&a[0]);" + body + "}"
                ),
                0,
            )
        self.assertNotEqual(
            self.compile("i32 main(){i32[0] a;return a[0];}", "--check").returncode, 0
        )

    def test_goto_drops_only_exited_objects_in_reverse(self):
        self.assertEqual(
            self.program("""
            i32 trace;struct Item{i32 n;~Item(){trace=trace*10+n;}};
            i32 main(){i32 loops;Item keep(4);
              start: {++loops;}
              Item a(1);
              {Item b(2);if(loops==1){goto start;}goto done;}
              done: {if(trace==212){return 42;}return 1;}
            }"""),
            42,
        )

    def test_type_specialization_order_and_ambiguity(self):
        self.assertEqual(
            self.program("""
            generic<type T> struct Tag{i32 value(1);};
            generic<type U> requires(ObjectType<U>) specialize struct Tag<U*>{i32 value(2);};
            specialize struct Tag<i32*>{i32 value(3);};
            generic<const i32 N> struct Amount{i32 n(N);};
            specialize struct Amount<6>{i32 n(30);};
            i32 main(){Tag<i32*> a;Tag<u8*> b;Tag<i64> c;Amount<6> d;Amount<6+0> e;
              if(a.value==3 && b.value==2 && c.value==1 && d.n==e.n){return d.n+12;}return 1;}
            """),
            42,
        )
        r = self.compile(
            """
            generic<type A,type B> struct Pair{};
            generic<type A> specialize struct Pair<A,i32>{};
            generic<type B> specialize struct Pair<i32,B>{};
            void f(){Pair<i32,i32> ambiguous;}
            """,
            "--check",
        )
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("ambiguous type specialization", r.stderr)

    def test_required_integer_evaluation_and_abandon_diagnostics(self):
        for src in (
            "constexpr i8 x(i8(127)+1);",
            "void f(){constexpr i8 x(i8(127)+1);}",
            "i32 f(u8 a,i8 b){return a|b;}",
            "i32 f(u8 a,u16 b){return a^b;}",
        ):
            self.assertNotEqual(self.compile(src, "--check").returncode, 0)
        body = (
            "struct D{~D(){}};struct Holder{D member;};void f(){Holder h;abandon(h);}"
        )
        for config, code, msg in [
            ("", 0, "ANOMALY: LIFE004"),
            ("diagnostics.promote=[LIFE004];", 1, "ERROR: LIFE004"),
            ("diagnostics.suppress=[LIFE004];", 0, ""),
        ]:
            r = self.compile(
                ("configuration {" + config + "};" if config else "") + body, "--check"
            )
            self.assertEqual(r.returncode, code, r.stderr)
            if msg:
                self.assertIn(msg, r.stderr)
            else:
                self.assertEqual(r.stderr, "")

    def test_borrow_parameter_contract_bindings(self):
        for src in (
            "[[noescape(x)]] void f(i32 x){}",
            "[[returns_borrowed_from(y)]] i32& f(i32& x){return x;}",
            "[[noescape(x)]] i32* f(i32* x){return x;}",
            "i32* retained;[[noescape(x)]] void f(i32* x){retained=x;}",
            "[[returns_borrowed_from(x)]] i32& f(i32& x,i32& y){return y;}",
        ):
            self.assertNotEqual(self.compile(src, "--check").returncode, 0)
        self.assertEqual(
            self.program("""
            [[noescape(x),returns_borrowed_from(x)]] i32& f(i32[2]& x){return x[1];}
            i32 main(){i32[2] a(0,40);f(a)+=2;return a[1];}
        """),
            42,
        )

    def test_generic_loop_and_exact_literals(self):
        self.assertEqual(
            self.program("""
            generic<type T, const i32 N> requires (SameType<T, i32>) T repeat(T x) {
                T sum;
                for (i32 i(0); i < N; i++) { sum += x; }
                return sum;
            }
            i32 main() {
                const u8 a(0b1010_1010);
                auto b(repeat<i32, (3 + 3)>(7));
                if (a < 300 && b == 42 && -7 % 3 == -1) { return b; }
                return 1;
            }"""),
            42,
        )

    def test_binding_calls_and_evaluation_order(self):
        self.assertEqual(
            self.program("""
            i32 state(1);
            declare i32 mutate();
            i32 first(i32 a, i32 b) { return a; }
            i32 go() {
                state += mutate();
                return first(state, mutate());
            }
            i32 mutate() { state = 10; return 2; }
            i32 main() {
                i32 n(go());
                if (false && mutate() == 2) { return 90; }
                if (true || (state = 7) == 7) { return n + state; }
                return 0;
            }"""),
            13,
        )

    def test_native_wrap_and_comparison(self):
        self.assertEqual(
            self.program("""
            configuration { preset = Release; };
            i32 main() {
                /* outer /* nested */ ok */
                i64 low(-9223372036854775808);
                u64 high(0xffff_ffff_ffff_ffff);
                i8 s(127);
                s++;
                if (low < high && s == -128 && high > -1) { return 42; }
                return 0;
            }"""),
            42,
        )

    def test_checked_runtime_trap(self):
        self.assertLess(
            self.program("""
            i8 increment(i8 n) { return n + 1; }
            i32 main() { return increment(127); }
        """),
            0,
        )

    def test_saturation_and_unsigned_subtraction(self):
        self.assertEqual(
            self.program("""
            configuration { numeric.integer.overflow = saturating; };
            i32 main() {
                i8 a(120); u8 b(3); u8 c(20);
                a += 40; b -= c;
                if (b == 0 && a == 127) { return a; }
                return 0;
            }"""),
            127,
        )

    def test_control_flow_and_selected_lvalue(self):
        self.assertEqual(
            self.program("""
            i32 main() {
                i32 x; i32 y; bool flag(true);
                (flag ? x : y) = 3;
                do {
                    switch (x) {
                        case 3: { y += 7; fallthrough; }
                        case 4: { y += 5; break; }
                        default: { return 1; }
                    }
                    ++x;
                } while (x < 5);
                while (true) { if (x == 5) { break; } continue; }
                return y;
            }"""),
            17,
        )

    def test_overload_and_deduction(self):
        self.assertEqual(
            self.program("""
            alias Small = i8;
            i32 select(Small x) { return 10; }
            i32 select(i32 x) { return 20; }
            generic<type T> T identity(T x) { return x; }
            i32 main() { return select(identity(Small(7))) + select(7); }
        """),
            30,
        )

    def test_argumentwise_overload_ranking(self):
        declarations = [
            "i32 pick(i8 a, i32 b, i32 c) { return 1; }",
            "i32 pick(i32 a, i8 b, i8 c) { return 2; }",
        ]
        main = "i32 main() { i8 x(1); return pick(x,x,x); }"
        for order in (declarations, declarations[::-1]):
            r = self.compile("\n".join([*order, main]), "--check")
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("ambiguous overload", r.stderr)
            best = "i32 pick(i8 a, i8 b, i8 c) { return 42; }"
            for i in range(3):
                self.assertEqual(
                    self.program("\n".join([*order[:i], best, *order[i:], main])),
                    42,
                )

    def test_viable_reference_pointer_and_numeric_bindings(self):
        self.assertEqual(
            self.program("""
            struct Base { i32 value(38); };
            struct Derived : Base {};
            i32 pick(Base* p) { return p->value; }
            i32 pick(i32 n) { return 0; }
            i32 get(i32& n) { return 1; }
            i32 get(const<i32>& n) { return 2; }
            i32 get(i32&& n) { return 3; }
            i32 width(i32 n) { return 100; }
            i32 width(i64 n) { return 1; }
            i32 main() {
                Derived d; u32 u; i32 v; const i32 c(2);
                return pick(&d) + get(v) + get(c) + get(5) + width(u) - 3;
            }"""),
            42,
        )
        r = self.compile(
            "i32 f(i32&& n){return n;} i32 main(){i32 x(2);return f(x);}",
            "--check",
        )
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("no viable overload", r.stderr)

    def test_definition_site_overloads_and_policies(self):
        self.assertEqual(
            self.program("""
            i32 choose(i64 n) {return 40;}
            generic<type T> i32 bound(T n) {return choose(n);}
            declare i32 defaulted(i32 n(choose(i8(0))));
            i32 choose(i8 n) {return 2;}
            i32 defaulted(i32 n){return n;}
            configured(numeric.integer.overflow=saturating)
            generic<type T> requires(SameType<T,i8>) T increment(T n){return n+1;}
            configured(numeric.integer.overflow=saturating)
            generic<type T> requires(SameType<T,i8>) struct Counter {T increment(T n){return n+1;}};
            i32 main(){
                Counter<i8> c;
                if(increment(i8(127))==127 && c.increment(i8(127))==127 &&
                   defaulted()==40) {return bound(i8(0))+choose(i8(0));}
                return 0;
            }"""),
            42,
        )

    def test_generic_and_nongeneric_candidates(self):
        self.assertEqual(
            self.program("""
            generic<type T> i32 which(T v){return 1;}
            generic<type T> i32 which(T* v){return 2;}
            i32 which(i32 v){return 4;}
            generic<type T> requires (SameType<T,u8>) i32 width(T v){return 8;}
            i32 width(i64 v){return 16;}
            generic<type T> requires (ObjectType<T>) i32 size(T n){return 9;}
            generic<type U> requires (ObjectType<U> && SameType<U,i8>) i32 size(U n){return 11;}
            i32 main(){i32 x; return which(x)+which<>(&x)+which<i32>(x)+
                                      width(u8(0))+width(i32(0))+size(i8(0));}
            """),
            42,
        )
        for source, diagnostic in (
            (
                "generic<const i32 N> requires(N>0) i32 a(){return 1;} "
                "generic<const i32 M> requires(M>=1) i32 a(){return 2;} "
                "i32 main(){return a<2>();}",
                "ambiguous",
            ),
            (
                "generic<type T> i32 a(T x){return 1;} "
                "generic<type U> i32 a(U x){return 2;}",
                "duplicate generic signature",
            ),
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_generic_resource_limits_and_constant_parameter_domains(self):
        for source, diagnostic in (
            (
                "configuration {generic.max_instantiations=1;}; "
                "generic<type T> i32 value(T n){return 1;} "
                "i32 main(){return value(i8(2))+value(i16(3));}",
                "instantiation resource exhausted",
            ),
            (
                "configuration {generic.max_solver_steps=1;}; "
                "generic<type T> requires(ObjectType<T> && CompleteType<T>) "
                "i32 f(T n){return 1;} i32 main(){return f(1);}",
                "solver step resource exhausted",
            ),
            (
                "configuration {generic.max_normalization_nodes=1;}; "
                "generic<type T> requires(ObjectType<T> && CompleteType<T>) "
                "i32 f(T n){return 1;}",
                "normalization resource exhausted",
            ),
            ("generic<const f64 X> i32 f(){return 0;}", "constant parameter type"),
            (
                "generic<type T, const T N> i32 f(){return 0;} "
                "i32 main(){return f<f32,2.0>();}",
                "constant parameter type",
            ),
            (
                "constraint Broken<type T> {requires(unknown());};",
                "unknown name",
            ),
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_structural_result_categories_effects_and_special_members(self):
        self.assertEqual(
            self.program("""
            namespace checks {
                constraint Borrow<type T>{
                    expression(T& v){v.get()->i32& noexcept;}
                };
                generic<type T> requires(Borrow<T>) i32 get(T& v){return v.get();}
            }
            i32 n(42);
            struct Good{i32& get() noexcept {return n;}};
            struct Throws{i32& get(){return n;}};
            struct Value{i32 get() noexcept {return n;}};
            struct Only{Only(Only&& x)=default;};
            struct Nested{Only x; Nested(const<Nested>& x)=default;};
            i32 main(){
                Good x;
                if(!checks::Borrow<Throws> && !checks::Borrow<Value> &&
                   !CopyConstructible<Nested> && MoveConstructible<Only> &&
                   CopyConstructible<i32>){return checks::get<Good>(x);}
                return 0;
            }
            """),
            42,
        )

    def test_uninstantiated_dependent_arithmetic_requires_evidence(self):
        for definition in (
            "generic<type T> T plus(T a, T b){return a+b;}",
            "generic<type T> requires(ObjectType<T>) T plus(T a,T b){return a+b;}",
            "generic<type T> T bad(T n){if constexpr(SameType<T,i32>){return n;}"
            "else{return n+1;}}",
        ):
            with self.subTest(definition=definition):
                r = self.compile(definition, "--check")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn("not established", r.stderr)
        self.assertEqual(
            self.program("""
            constraint Sum<type T>{expression(const<T>& a,const<T>& b){a+b->T;}};
            generic<type X> requires(Sum<X>) X plus(X a,X b){return a+b;}
            generic<type T> i32 guarded(T x){
                if constexpr(SameType<T,i32> || SameType<T,i16>){return x+2;}
                else{return 0;}
            }
            i32 main(){return guarded(plus(20,20));}
        """),
            42,
        )

    def test_linkage_regions_and_external_symbol_identity(self):
        self.assertEqual(
            self.program(
                """
                extern "C" {
                    namespace first { i32 counter; i32 apply(i32 v); }
                    namespace second {
                        define i32 counter(40);
                        i32 apply(i32 v) { return counter + v; }
                    }
                }
                extern "C" i32 probe() {
                    return first::apply(1) + first::counter - second::counter;
                }""",
                host="""
                extern int counter, apply(int), probe(void);
                int main(void) {
                    return counter == 40 && apply(2) == 42 ? probe() + 1 : 0;
                }""",
            ),
            42,
        )
        for source in (
            "define i32 x(5);",
            'extern "C" declare i32 f();',
            'extern "C" i32 x(10);',
            'extern "C" i32 f(i32 x); extern "C" i32 f(u32 x);',
            'extern "C" i32 x; extern "C" i32 x();',
            'extern "C" i32 x(); extern "C" i32 x;',
            'extern "C" { define i32 x(1); define i32 x(2); }',
            'extern "C" { i32 x; u32 x; }',
        ):
            with self.subTest(source=source):
                self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_selected_deleted_or_inaccessible_overload(self):
        self.assertEqual(
            self.program("""
            class Base {
            protected:
                i32 read() const { return 40; }
            };
            struct Derived : Base { i32 go() { return read() + 2; } };
            i32 choose(i32 n) = delete;
            i32 choose(i8 n) { Derived d; return d.go(); }
            i32 main() { return choose(i8(0)); }"""),
            42,
        )
        for source, message in (
            (
                "i32 f(i8 n)=delete; i32 f(i32 n){return 0;} "
                "i32 main(){return f(i8(2));}",
                "deleted",
            ),
            (
                "class T { i32 f(i8 n){return 1;} public: i32 f(i32 n){return 0;} }; "
                "i32 main(){T t;return t.f(i8(2));}",
                "inaccessible",
            ),
            ("class T { T() {} }; i32 main(){T t;return 0;}", "inaccessible"),
            ("struct T { T() = delete; }; i32 main(){T t;return 0;}", "deleted"),
            ("struct T { T() = later; };", "default or delete"),
            ("struct T { ~T(i32 x) {} };", "no parameters"),
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_native_c_link(self):
        self.assertEqual(
            self.program(
                """
            extern "C" i32 host_value(i32 n);
            extern "C" i32 compute(i32 x) { return host_value(x) + 2; }
        """,
                host="""
            extern int compute(int);
            int host_value(int n) { return n * 2; }
            int main(void) { return compute(20); }
        """,
            ),
            42,
        )

    def test_manual_storage_generation(self):
        self.assertEqual(
            self.program("""
            i32 main() {
                i64 old(3);
                auto storage(storage_of(old));
                destroy(old);
                auto replacement(construct_at<i32>(storage, 40));
                *replacement += 2;
                return *replacement;
            }"""),
            42,
        )

    def test_record_lifetime(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            struct Item {
                i32 id;
                Item(i32 n) { init id(n); }
                ~Item() { trace = trace * 10 + id; }
            };
            void populate() { Item a(2); Item b(4); return; }
            i32 main() { populate(); return trace; }
        """),
            42,
        )

    def test_generic_record_and_references(self):
        self.assertEqual(
            self.program("""
            generic<type T, const usize N> struct Buffer { T[N] data; };
            void add(i32& dst, const i32& value) { dst += value; }
            i32 main() {
                Buffer<i32, 3> buffer;
                i32 delta(2);
                buffer.data[1] = 40;
                add(buffer.data[1], delta);
                return buffer.data[1];
            }"""),
            42,
        )

    def test_constant_expressions_in_types(self):
        self.assertEqual(
            self.program("""
            generic<type T, const usize N> struct Buffer { T[N + 1] data; };
            generic<const bool Select, type T> T pick(T x, T y) {
                if (Select) { return x; }
                return y;
            }
            consteval usize extent(usize n) { return n + 1; }
            i32 main() {
                constexpr usize limit(extent(7));
                Buffer<Buffer<i32, (limit >> 1)>, limit & 1> outer;
                outer.data[0].data[4] = 40;
                i32[limit / 4] tail(1, 2);
                return pick<limit >= 8>(outer.data[0].data[4], i32(0)) + tail[1];
            }"""),
            42,
        )

    def test_pack_expansion_and_forwarding(self):
        self.assertEqual(
            self.program("""
            i32 sum(){return 0;}
            i32 sum(i32 a, i32 b, i32 c){return a+b+c;}
            generic<type... Ts> i32 relay(Ts... values){return sum(values...);}
            generic<const i32... Ns> i32 constants(){return sum(Ns...);}
            generic<type... Ts> i32 nested(Ts... x){return relay<Ts...>(x...);}
            struct R {
                i32 kind() & {return 1;}
                i32 kind() && {return 2;}
            };
            generic<type T> i32 kind(forward T v){return std::forward<T>(v).kind();}
            i32 main(){
                R r;
                return nested(10,11,12)+constants<1,2,3>()+relay()+kind(r)+kind(R());
            }
        """),
            42,
        )
        for source, diagnostic in [
            ("generic<type... Ts,type U> void f(){}", "last parameter"),
            ("generic<type... Ts=i32> void f(){}", "cannot have a default"),
            ("generic<type... Ts> i32 f(Ts... xs){return xs;}", "unexpanded pack"),
            ("void f(i32... xs){}", "requires a generic pack"),
            ("void f(forward i32 x){}", "forward requires"),
        ]:
            with self.subTest(source=source):
                r = self.compile(source, "--check")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn(diagnostic, r.stderr)

    def test_compile_time_branch_and_definition_lookup(self):
        self.assertEqual(
            self.program("""
            generic<const bool Field, type T> i32 read(T value) {
                if constexpr (Field) { return value.n; }
                else { return value; }
            }
            struct Box { i32 n; };
            i32 main() { return read<true>(Box(40)) + read<false>(i32(2)); }
            """),
            42,
        )
        for source in [
            "generic<type T> i32 bad(T x) { return undefined(x); }",
            "generic<type T> i32 bad(T x) {if constexpr(true){return 0;}else{return missing;}}",
            "i32 f(){if constexpr(false){return unknown();}return 1;}",
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("unknown name", result.stderr)

    def test_array_construction_and_reverse_destruction(self):
        self.assertEqual(
            self.program("""
            i32 order;
            i32 serial;
            struct Entry {
                i32 id;
                Entry() { init id(++serial); }
                Entry(i32 n) { init id(n); }
                ~Entry() { order = order * 10 + id; }
            };
            struct Row { Entry[2] entries; };
            void take(Row) {}
            i32 main() {
                take(Row());
                if (order != 21) {return 1;}
                order = 0;
                {
                    Entry[3] entries(Entry(7));
                    if (entries[2].id != 4) {return 2;}
                }
                if (order != 437) {return 3;}
                return 42;
            }"""),
            42,
        )

    def test_root_static_initialization_and_shutdown(self):
        self.assertEqual(
            self.program(
                """
            extern "C" void note(i32 n);
            extern "C" i32 observed();
            i32 count;
            struct Item {
                i32 n;
                Item() {init n(++count); note(n);}
                ~Item(){note(n);}
            };
            [[static_id("first-item")]] Item first;
            [[init_after(first), static_id("second-item")]] static Item second;
            static i32 total(first.n + second.n);
            i32 main(){if(total == 3 && observed() == 12){return 42;} return 1;}
        """,
                host="""
            #include <stdlib.h>
            static int trace;
            void note(int n){trace = trace*10+n;}
            int observed(void){return trace;}
            __attribute__((destructor(101))) static void verify(void){
                if(trace != 1221) _Exit(2);
            }
        """,
            ),
            42,
        )

        self.assertLess(
            self.program("""
            declare i32 early();
            i32 first(early());
            i32 make(){return 7;}
            i32 later(make());
            i32 early(){return later;}
            i32 main(){return 0;}
        """),
            0,
        )

    def test_incomplete_type_identity(self):
        self.assertEqual(
            self.program("""
            declare struct Cell;
            alias Link = Cell*;
            declare i32 read(const<Cell>& c);
            struct Cell { i32 value; Link next; };
            declare enum Kind:u8;
            enum Kind:u8 {case A(1)};
            i32 read(const<Cell>& c) {return c.value;}
            i32 main(){Cell c(42,nullptr); return read(c);}
        """),
            42,
        )
        for source, diagnostic in [
            ("declare struct T; void f(){T x;}", "complete object type"),
            ("declare struct T; void f(){auto n(sizeof(T));}", "complete object type"),
            ("declare class T; union T{case A;};", "conflicting nominal"),
            ("declare enum E:i32; enum E:u32{case A(0)};", "incompatible enum"),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_binary_floating_literals_operations_and_native_abi(self):
        self.assertEqual(
            self.program(
                """
            configuration { preset=Release; numeric.float.formats=[f32,f64]; };
            extern "C" f32 host(f32 n, f64 k);
            f32 add(f32 x){return x+0x1.8p+1;}
            i32 main(){
                f32 a(16_777_217.0); f32 b(16_777_216.0);
                f64 c(1.0/8.0);
                if(a==b && c==1.25e-1 && host(add(4.0),c)==7.125){return 42;}
                return 1;
            }
        """,
                host="float host(float n,double k){return (float)(n+k);}",
            ),
            42,
        )
        self.assertEqual(
            self.program("""
            configuration {numeric.literal.real_rounding=toward_negative_infinity;};
            f32 signed_literal(){return -1.00000001;}
            i32 main(){f32 n(signed_literal());if(n < -1.0){return 42;}return 1;}
        """),
            42,
        )
        for source, msg in [
            ("void f(){f32 n(0x1.8);}", "binary exponent"),
            ("void f(){f64 n(1.25e+_2);}", "malformed numeric"),
            ("void f(){f32 n(1e1000);}", "overflows"),
            (
                "configuration {numeric.float.formats=[f64];};void f(){f32 n;}",
                "disabled",
            ),
            ("f32 f(f64 n){return n;}", "lossless"),
        ]:
            r = self.compile(source, "--check")
            self.assertNotEqual(r.returncode, 0)
            self.assertIn(msg, r.stderr)

    def test_closure_captures_and_mutable_receiver(self):
        self.assertEqual(
            self.program("""
            generic<type F> i32 invoke(F& fn,i32 v){return fn(v);}
            struct Seed {
              i32 seed;
              i32 read() const {
                auto get([this] i32() {return this->seed;});
                return get();
              }
            };
            i32 main(){
                i32 x(4);i32 count;
                auto fn([x,&count,y(x+1)] i32(i32 n) mutable noexcept {
                    ++x; ++count; return x+y+n;
                });
                x=30;
                Seed base(7);
                return invoke(fn,3)+invoke(fn,9)+count+base.read();
            }
        """),
            42,
        )
        for source, message in [
            (
                "i32 f(){i32 x(2);auto g([] i32(){return x;});return g();}",
                "unknown name",
            ),
            ("void f(){i32 x;auto g([x] void(){++x;});}", "writable lvalue"),
            ("void f(){i32 a;auto g([a,a] void(){});}", "duplicate closure capture"),
        ]:
            r = self.compile(source, "--check")
            self.assertNotEqual(r.returncode, 0)
            self.assertIn(message, r.stderr)

    def test_captureless_closure_explicit_function_pointer(self):
        self.assertEqual(
            self.program("""
            struct Box{Box* self;i32 n;Box(i32 v){init self(this);init n(v);}};
            function<i32(i32) noexcept>* factory(){
                function<i32(i32) noexcept>* p([] i32(i32 n) noexcept {return n+1;});
                return p;
            }
            i32 main(){
                auto make([] Box(i32 n){return Box(n);});
                function<Box(i32)>* p(make);
                Box v(p(40));
                function<i32(Box)>* f([] i32(Box b){if(b.self!=&b){return 0;}return b.n;});
                if(v.self==&v && f(p(40))==40){return factory()(41);}return 0;
            }"""),
            42,
        )
        for body, diagnostic in [
            ("i32 x;function<void()>* p([x] void(){});", "captureless"),
            ("function<i32(i32)>* p([] i64(i32 n){return n;});", "signature"),
            ("function<void() noexcept>* p([] void(){});", "signature"),
            (
                "function<void(D&)>* p([] void(D& d){abandon_base<B>(d);});",
                "lifecycle_effect",
            ),
            ("take([] void(){});", "no viable overload"),
        ]:
            with self.subTest(body=body):
                r = self.compile(
                    "struct B{};struct D:B{Complete base<B>;};"
                    "void take(function<void()>* p){}void f(){" + body + "}",
                    "--check",
                )
                self.assertNotEqual(r.returncode, 0)
                self.assertIn(diagnostic, r.stderr)

    def test_static_local_initializes_at_startup(self):
        self.assertEqual(
            self.program("""
            i32 calls;
            i32 start(){++calls;return 19;}
            i32 next(){static i32 n(start());return ++n;}
            i32 main(){if(calls!=1){return 1;}return next()+next()+calls;}
        """),
            42,
        )
        r = self.compile("i32 f(i32 x){static i32 n(x);return n;}", "--check")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("unknown name", r.stderr)

    def test_replacement_destroys_current_type_and_invalidates_old_borrows(self):
        self.assertEqual(
            self.program("""
            i32 log;
            struct A{i32 n;~A(){log=log*10+n;}};
            struct B{i32 n;~B(){log=log*10+n+1;}};
            void work(bool change){
                A a(4);auto storage(storage_of(a));
                if(change){destroy(a);construct_at<B>(storage,1);}
            }
            i32 main(){work(true);return log;}
        """),
            42,
        )
        self.assertLess(
            self.program("""
            i32 main(){i32 a(1);auto old(&a);auto storage(storage_of(a));
                destroy(a);construct_at<i32>(storage,42);return *old;}
        """),
            0,
        )

    def test_first_assignment_construction_frontier(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            i32 mark(i32 n, i32 value){trace=trace*10+n;return value;}
            struct Child {
                i32 value;
                Child(){mark(8,0);}
                Child(i32 n){init value(n);}
            };
            struct Pair {
                Child first; i32 second;
                Pair(i32 n, bool flag){
                    init second(mark(3,first.value));
                    if(flag){this->first=Child(mark(1,n));}
                    else{first=Child(mark(2,n+1));}
                    mark(4,0);
                }
            };
            i32 main(){
                Pair a(20,true); Pair b(21,false);
                if(trace==134234){return a.second+b.second;}return 1;
            }
        """),
            42,
        )
        self.assertEqual(
            self.program("""
            i32 count;
            i32 next(){return ++count;}
            struct Item {
                i32 a; i32 b;
                Item(i32 n){
                    init b(next());
                    for(i32 i; i<n; ++i){a=i;}
                    a=40;
                }
            };
            i32 main(){Item i(2); return i.a+i.b;}
        """),
            41,
        )
        for body in [
            "this->second=2;this->first=1;",
            "if(flag){second=1;first=2;}else{first=3;second=4;}",
        ]:
            r = self.compile(
                "struct Pair{i32 first;i32 second;Pair(bool flag){" + body + "}};",
                "--check",
            )
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("initialization frontier", r.stderr)

    def test_construction_tail_shares_frontier_and_final_storage(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            i32 mark(i32 n) { trace = trace * 10 + n; return n; }
            struct S {
                i32 first; i32 second;
                S(i32& a) { ++a; mark(1); delegate(a,0); mark(4); }
                S(i32 a, i32 tag) { init first(a + mark(2)); mark(3); }
            };
            struct P { i32 x; i32 y; };
            P global -> { init y(2); this->x = y; };
            i32 main() {
                i32 a(17);
                S s(a) -> { init second(first + a); mark(5); this->second += 2; };
                P p(global.x) -> { init y(x + s.second); };
                if (trace == 12345 && s.first == 20 && s.second == 40) { return p.y; }
                return 1;
            }
        """),
            42,
        )
        self.assertEqual(
            self.program("""
            struct R { i32 a; R() {} };
            i32 main() {
                i32 x(5);
                R one -> { init a(x + 5); };
                R two -> { init a(x + 27); };
                return one.a + two.a;
            }
        """),
            42,
        )

    def test_construction_tail_diagnostics(self):
        for source, message in [
            ("void f(){auto x(1) -> {};}", "typed declaration"),
            (
                "struct R{i32 a;}; void f(){R r -> {init b(1);};}",
                "unknown initialization",
            ),
            (
                "struct R{i32 a;R(){init a(1);}}; void f(){R r -> {init a(1);};}",
                "duplicate initialization",
            ),
            (
                "struct R{i32 a;}; void f(){R r(1) -> {init a(2);};}",
                "duplicate aggregate",
            ),
            (
                "struct R{i32 a; i32 b;}; void f(){R r -> {init a(this->b);};}",
                "before initialization",
            ),
            (
                "struct R{i32 a; R(){}}; void f(){R r -> {i32 x(1); init a(x);};}",
                "unknown name",
            ),
            (
                "struct R{R(){return; delegate(1);} R(i32 x){}};",
                "bypasses required delegation",
            ),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_unified_delegation_frontier(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            i32 mark(i32 digit,i32 value){trace=trace*10+digit;return value;}
            struct Pair {
                i32 a;
                i32 b;
                Pair(i32 x) {
                    init b(mark(3,x));
                    mark(1,0);
                    ++x;
                    { delegate(x + 2,0); }
                    mark(5,0);
                }
                Pair(i32 x,i32 tag) {
                    init a(mark(2,x));
                    mark(4,0);
                }
            };
            i32 main(){
                Pair pair(19);
                if(trace==12345 && pair.a==22 && pair.b==20){return 42;}
                return 1;
            }
        """),
            42,
        )
        for source, diagnostic in [
            ("struct A{A(){delegate();}};", "cyclic"),
            ("struct A{A(){delegate(1);} A(i32 x){delegate();}};", "cyclic"),
            ("struct A{A(){if(true){delegate(1);}} A(i32 x){}};", "unconditional"),
            (
                "struct A{i32 x; A(){init x(1);delegate(1);} A(i32 n){init x(n);}};",
                "duplicate initialization",
            ),
            ("void f(){delegate();}", "requires a constructor"),
        ]:
            with self.subTest(source=source):
                r = self.compile(source, "--check")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn(diagnostic, r.stderr)

    def test_shared_virtual_base_identity_and_lifetime(self):
        self.assertEqual(
            self.program("""
            i32 trace; i32 producers; i32 last;
            i32 note(){++producers;return 7;}
            struct Root {
                i32 n;
                Root(i32 x){init n(x);trace=trace*10+1;}
                virtual i32 read() const {return n;}
                virtual ~Root(){trace=trace*10+7;}
            };
            i32 call(const<Root>* p){return p->read();}
            struct Left : virtual Root {
                Left(){init virtual_base<Root>(note());trace=trace*10+2;}
                i32 read() const override {return n+1;}
                ~Left() {last=call(this);trace=trace*10+6;}
            };
            struct Right : virtual Root {
                Right(){init virtual_base<Root>(note());trace=trace*10+3;}
                ~Right(){trace=trace*10+5;}
            };
            struct Both : Left, Right {
                Both(){init virtual_base<Root>(37);trace=trace*10+4;}
                i32 read() const override {return n+5;}
            };
            Root* fromLeft(Left* p){return p;}
            Root* fromRight(Right* p){return p;}
            i32 main(){
                { Both b;
                  Root* a(fromLeft(&b)); Root* c(fromRight(&b));
                  if(a!=c || b.n!=37 || call(c)!=42 || trace!=1234 || producers!=0){return 1;}
                }
                if(trace!=1234567 || last!=38){return 2;}
                trace=0;
                { Left alone; if(producers!=1 || call(&alone)!=8){return 3;} }
                return 42;
            }"""),
            42,
        )

    def test_virtual_base_copy_and_nested_boundaries(self):
        self.assertEqual(
            self.program("""
            i32 copies; i32 drops;
            struct V {
                i32 n;
                V(const<V>& src){init n(src.n);++copies;}
                ~V(){++drops;}
            };
            struct A:virtual V {A(const<A>& src)=default;};
            struct B:virtual V {B(const<B>& src)=default;};
            struct D:A,B {D(const<D>& src)=default;};
            struct Top:virtual D {Top(const<Top>& src)=default;};
            struct Nested {Top[2] items;};
            i32 take(A a){return a.n;}
            i32 main(){
                {Nested s; s.items[0].n=20; s.items[1].n=22;
                 Top t(s.items[0]);
                 if(copies!=1 || t.n!=20 || &t.n==&s.items[0].n){return 1;}
                 A& a(s.items[1]);
                 if(take(a)+t.n!=42 || copies!=2){return 2;}
                }
                if(drops==4){return 42;} return 3;
            }
        """),
            42,
        )

    def test_virtual_base_tail_aggregate_and_diagnostics(self):
        self.assertEqual(
            self.program("""
            struct V{i32 n;}; struct A:virtual V{}; struct B:virtual V{};
            struct D:A,B{i32 inc(2);};
            i32 main(){D x -> {init virtual_base<V>(40);};
                       return x.n+x.inc;}
            """),
            42,
        )
        for src, msg in (
            (
                "struct V{};struct A:V{A(){init virtual_base<V>();}};",
                "unknown initialization target",
            ),
            (
                "struct V{};struct A:virtual V{A(){init base<V>();}};",
                "unknown initialization target",
            ),
            (
                "struct V{virtual i32 f(){return 0;}};struct A:virtual V{i32 f() override{return 1;}};"
                "struct B:virtual V{i32 f() override{return 2;}};struct D:A,B{};",
                "ambiguous final overrider",
            ),
        ):
            with self.subTest(src=src):
                result = self.compile(src, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(msg, result.stderr)

    def test_virtual_slots_and_active_layers(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            struct Left { i64 pad; };
            struct Base {
                virtual i32 read(i32 x(3)) const noexcept { return x; }
                Base() { trace = read(); }
                virtual ~Base() noexcept { trace = trace * 10 + read(1); }
            };
            struct Derived : Left, Base {
                i32 n;
                Derived(){ init n(7); trace = trace*10 + read(0); }
                i32 read(i32 x) const noexcept override final { return n + x; }
                ~Derived() noexcept override { trace = trace*10+read(0); }
            };
            i32 invoke(const<Base>& b){return b.read();}
            i32 main(){
                Derived d;
                Base* p(&d);
                if(invoke(d)!=10 || p->read(2)!=9 || trace!=37){return 1;}
                destroy(*p);
                if(trace==3771){return 42;}return 2;
            }
        """),
            42,
        )

    def test_virtual_slot_diagnostics_and_receiver_category(self):
        self.assertEqual(
            self.program("""
            struct R {
                i32 which() & { return 40; }
                i32 which() && { return 2; }
            };
            i32 main(){ R r; return r.which()+R().which(); }
        """),
            42,
        )
        for source, diagnostic in [
            (
                "struct B{virtual i32 f(){return 1;}};struct D:B{i32 f(){return 2;}};",
                "invalid override",
            ),
            (
                "struct B{virtual i32 f() noexcept{return 1;}};struct D:B{i32 f() override{return 2;}};",
                "invalid override",
            ),
            (
                "struct B{virtual i32 f() final{return 1;}};struct D:B{i32 f() override{return 2;}};",
                "invalid override",
            ),
            ("struct B{i32 f() override{return 1;}};", "no matching inherited"),
            ("struct B{i32 f(){return 1;}i32 f() & {return 2;}};", "duplicate"),
        ]:
            with self.subTest(source=source):
                r = self.compile(source, "--check")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn(diagnostic, r.stderr)

    def test_nonvirtual_bases_and_subobject_addresses(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            struct Left {
                i32 left;
                Left() {init left(2); trace = trace * 10 + 1;}
                ~Left() {trace = trace * 10 + 6;}
            };
            struct Right {
                i32 right;
                Right(i32 v){init right(v); trace = trace * 10 + 2;}
                i32 get() const {return right;}
                ~Right(){trace = trace * 10 + 5;}
            };
            struct Both final : Left, Right {
                Both(){init base<Right>(40); trace = trace * 10 + 3;}
                i32 sum() const {return left + get();}
                ~Both(){trace = trace * 10 + 4;}
            };
            i32 read(const<Right>& base){return base.get();}
            i32 main(){
                {
                    Both b;
                    Right* r(&b);
                    if (b.sum() != 42 || b.right != 40 || r->get() != 40 || read(b) != 40) {return 1;}
                }
                if (trace == 123456){return 42;}
                return 2;
            }
        """),
            42,
        )
        for source, diagnostic in [
            ("struct A final {}; struct B:A {};", "complete non-final"),
            ("struct A {}; struct B:A,A {};", "duplicate direct base"),
            (
                "struct A{i32 n;};struct B:A{};struct C:A{};struct D:B,C{};i32 f(D& d){return d.n;}",
                "ambiguous inherited",
            ),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_whole_unwinds_direct_and_indirect_helpers(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            void note(i32 n){trace=trace*10+n;}
            struct Marker {i32 n; Marker(i32 v){init n(v);} ~Marker(){note(n);}};
            struct Base {~Base(){note(2);}};
            declare struct Derived;
            declare void inner(Derived& d);
            declare void outer(Derived& d);
            struct Derived:Base {
                Complete base<Base>; Marker field(6);
                ~Derived(){note(1);outer(*this);note(9);}
                cleanup {note(7);}
            };
            void inner(Derived& d){ Marker local(3);
                destroy_base<Base>(d);note(9); }
            void outer(Derived& d){ Marker local(4);
                function<void(Derived&) [[lifecycle_effect(whole)]]>* fn(&inner);fn(d);note(9); }
            i32 main(){{Derived d;}if(trace==123467){return 42;}return 1;}
            """),
            42,
        )

    def test_whole_effect_pointer_contract(self):
        for qualifier in ("", " noexcept"):
            source = """
                struct Base{};struct D:Base{Complete base<Base>;};
                void end(D& d) QUAL {abandon_base<Base>(d);}
                void forward_request(D& d) QUAL {end(d);}
                void f(){function<void(D&) QUAL EFFECT>* p(&forward_request);}
            """.replace("QUAL", qualifier)
            valid = self.compile(
                source.replace("EFFECT", "[[lifecycle_effect(whole)]]"), "--check"
            )
            self.assertEqual(valid.returncode, 0, valid.stderr)
            invalid = self.compile(source.replace("EFFECT", ""), "--check")
            self.assertNotEqual(invalid.returncode, 0)
            self.assertIn("preserve lifecycle_effect", invalid.stderr)

    def test_alive_base_path_request_skips_containing_layers(self):
        for request, expected in [("destroy_base", 232456), ("abandon_base", 32456)]:
            with self.subTest(request=request):
                self.assertEqual(
                    self.program(
                        """
                    i32 trace; void note(i32 n){trace=trace*10+n;}
                    struct B {~B(){note(2);}};
                    struct Left:B {Complete base<B>;~Left(){note(9);}cleanup {note(5);}};
                    struct Right:B {~Right(){note(3);}cleanup {note(4);}};
                    struct D:Left,Right {~D(){note(9);}cleanup {note(6);}};
                    i32 main(){D d;
                        REQUEST<base_path<Left,B>>(d);
                        if(trace==EXPECTED){return 42;}return 1;}
                    """.replace("REQUEST", request).replace("EXPECTED", str(expected))
                    ),
                    42,
                )

    def test_virtual_owner_preserves_one_shared_obligation(self):
        self.assertEqual(
            self.program("""
            i32 trace; void note(i32 n){trace=trace*10+n;}
            struct V{~V(){note(2);}};
            struct Left:virtual V {Complete virtual_base<V>;
                ~Left(){note(1);destroy_base<V>(this);note(9);} cleanup {note(3);}};
            struct Right:virtual V {~Right(){note(4);}};
            struct D:Right,Left {destruction_owner<V> = Left;};
            i32 main(){{D d;}if(trace==123){return 42;}return 1;}
            """),
            42,
        )
        for source, message in [
            (
                "struct V{};struct L:V{};struct D:L{destruction_owner<V> = L;};",
                "shared virtual base",
            ),
            (
                "struct V{};struct L:virtual V{};struct X{};"
                "struct D:L,X{destruction_owner<V> = X;};",
                "must contain",
            ),
            (
                "struct V{};struct L:virtual V{};struct D:L{"
                "destruction_owner<V> = L;destruction_owner<V> = L;};",
                "competing",
            ),
            (
                "struct V{};struct L:V{};struct R:V{};struct D:L,R{};"
                "void f(D& d){destroy_base<V>(d);}",
                "ambiguous base",
            ),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_owner_transfer_commits_per_object_and_freezes_at_destruction(self):
        source = """
            i32 trace; bool early;
            struct V{~V(){trace=trace*10+2;}};
            struct L:virtual V{Complete virtual_base<V>;
                ~L(){if(early){destroy_base<V>(this);}trace=trace*10+1;}
                cleanup {trace=trace*10+3;}};
            struct R:virtual V{};
            struct D:L,R{destruction_owner<V> = R;};
            void change(L& layer){transfer_destruction<V>(layer);}
        """
        self.assertEqual(
            self.program(
                source
                + """
            i32 main(){{D d;change(d);early=true;}
                      if(trace!=23){return 1;}trace=0;early=false;
                      {D other;}if(trace!=132){return 2;}return 42;}
            """
            ),
            42,
        )
        self.assertLess(
            self.program(
                source
                + """
            i32 main(){early=true;D d;return 0;}
            """
            ),
            0,
        )
        self.assertLess(
            self.program("""
            struct V{};struct Layer:virtual V{~Layer(){transfer_destruction<V>(this);}};
            i32 main(){Layer d;return 0;}
            """),
            0,
        )
        invalid = self.compile(
            "struct V{};struct L:V{};void f(L& l){transfer_destruction<V>(l);}",
            "--check",
        )
        self.assertNotEqual(invalid.returncode, 0)
        self.assertIn("virtual base", invalid.stderr)

    def test_direct_base_request_exits_the_destructor_body(self):
        for request in ("destroy_base<Parent>(this);", "this->Parent::~Parent();"):
            with self.subTest(request=request):
                self.assertEqual(
                    self.program(
                        """
                    i32 trace;
                    void note(i32 n){trace=trace*10+n;}
                    struct Parent {~Parent(){note(2);}};
                    struct Member {~Member(){note(3);}};
                    struct Child:Parent {
                        Complete base<Parent>;
                        Member m;
                        ~Child(){note(1); REQUEST note(9);}
                        cleanup {note(4);}
                    };
                    i32 main(){{Child c;} if(trace==1234){return 42;} return 1;}
                """.replace("REQUEST", request)
                    ),
                    42,
                )

    def test_generic_defaults_and_literal_deduction(self):
        self.assertEqual(
            self.program("""
            constexpr usize count(3);
            generic<type T = i32, const usize N = count, const usize M = N + 1>
            struct Buffer { T[M] data; };
            generic<type A, type B = A, const B N = B(2)>
            requires(SameType<A,i32> && SameType<B,i32>) B add(A x) { return x + N; }
            i32 main() {
                constexpr usize count(20);
                Buffer<> buf;
                buf.data[3] = 40;
                if (sizeof(buf.data) == 16) { return add<>(buf.data[3]); }
                return add(0);
            }"""),
            42,
        )

    def test_structural_and_constant_requirements(self):
        definitions = """
            constraint Addable<type T> {
                expression(const<T>& a, const<T>& b) { a + b -> T; }
            };
            generic<type T> requires (ObjectType<T> && Addable<T>)
            T sum(const<T>& x, const<T>& y) { return x + y; }
            generic<type T, const usize N> requires (CompleteType<T> && N > 0)
            struct Buffer { T[N] data; };
            struct Empty {};
        """
        self.assertEqual(
            self.program(
                definitions
                + """
            i32 main() {
                Buffer<i32,2> storage;
                storage.data[0] = 40;
                if constexpr (!Addable<Empty> && SameType<i32,i32>) {
                    return sum(storage.data[0], 2);
                }
                return 0;
            }"""
            ),
            42,
        )
        for extra in [
            "void f(){ Buffer<i32,0> b; }",
            "void f(){ sum(Empty(), Empty()); }",
        ]:
            result = self.compile(definitions + extra, "--check")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("constraint is not satisfied", result.stderr)

    def test_function_pointer_binding_and_indirect_calls(self):
        self.assertEqual(
            self.program("""
            i32 increment(i32 n) noexcept { return n+1; }
            i64 increment(i64 n) { return n+2; }
            alias Transform = function<i32(i32 value)>*;
            Transform from(function<i32(i32) noexcept>* op) { return op; }
            i32 apply(Transform op, i32 n) { return op(n); }
            i32 main(){
                function<i32(i32) noexcept>* fp(&increment);
                Transform relaxed(from(fp));
                return apply(&increment, (*relaxed)((fp)(39)));
            }
            """),
            42,
        )
        for source, message in [
            (
                "i32 op(i32 x){return x;} void f(){auto p(&op);}",
                "target function-pointer",
            ),
            (
                "i32 op(i32 x){return x;} void f(){function<i32(i32) noexcept>* p(&op);}",
                "no unique compatible",
            ),
            ("i32 f(function<i32(i32)>* p){return p();}", "wrong argument count"),
            ("void f(){function<i32(i32)> x;}", "requires a pointer"),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_default_argument_ownership_and_order(self):
        self.assertEqual(
            self.program("""
            i32 state(1);
            i32 next(){ return ++state; }
            declare i32 compute(i32 first, i32 second(++first), i32 third(second + next()));
            i32 invoke() { i32 state(100); return compute(next()); }
            i32 compute(i32 a, i32 b, i32 c){ return a * 10 + b + c; }
            consteval i32 plus(i32 a, i32 b(a+1)){return a+b;}
            i32 main(){constexpr i32 three(plus(1)); return invoke() + three;}
            """),
            42,
        )
        self.assertEqual(
            self.program(
                """
            extern "C" i32 sum(i32 n, i32 m(n * 2));
            struct C { i32 v; C(i32 n(7)){init v(n);} i32 add(i32 x(14)){return v+x;} };
            i32 main() { C c; return c.add() + sum(7); }
            """,
                host="int sum(int n,int m) {return n+m;}",
            ),
            42,
        )
        for source, message in [
            ("declare i32 f(i32 a(2), i32 b);", "trailing suffix"),
            ("declare i32 f(i32 a = 2);", "expected ')'"),
            ("declare i32 f(i32 a(later));", "unknown name"),
            (
                "declare i32 f(i32 a(2)); i32 f(i32 a(2)){return a;}",
                "canonical declaration",
            ),
            (
                "alias F = function<i32(i32 a(3))>*;",
                "cannot contain a parameter default",
            ),
            ("i32 f(i32 a(true)){return a;}", "cannot convert"),
            ("declare i32 f(i32 a(true));", "cannot convert"),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_unicode_source_and_literals(self):
        self.assertEqual(
            self.program(r"""
            i32 求值() {
                byte[2] values(40,42);
                if ('🙂' == '\u{1F642}' && sizeof("β") == 3 && "A"[1] == 0) {
                    return values[1];
                }
                return 0;
            }
            i32 main() { return 求值(); }
        """),
            42,
        )
        r = self.compile(
            "i32 café(){return 42;} i32 main(){return cafe\u0301();}", "--check"
        )
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("WARNING: identifier spelling is not NFC", r.stderr)

    def test_scoped_configuration(self):
        self.assertEqual(
            self.program("""
            configuration { preset = Release; };
            i32 main() {
                i8 x(127);
                configured(numeric.integer.overflow = saturating) { ++x; }
                if (x != 127) { return 1; }
                ++x;
                if (x != -128) { return 2; }
                return configured(numeric.integer.overflow = wrapping) (x + i8(-86));
            }
        """),
            42,
        )

    def test_conditional_reconstruction(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            struct Item { i32 id; ~Item() { trace = trace * 10 + id; } };
            void replace_if(bool change) {
                Item a(4);
                auto view(storage_of(a));
                if (change) {
                    destroy(a);
                    construct_at<Item>(view, 2);
                }
            }
            i32 main() { replace_if(true); return trace; }
        """),
            42,
        )

    def test_namespaces_enum_and_methods(self):
        self.assertEqual(
            self.program("""
            enum Mode : u8 { case Keep(0), case Increment(1) };
            namespace app {
                class Counter {
                    i32 n;
                public:
                    Counter(i32 v) { init n(v); }
                    i32 read() const { return this->n; }
                    void update(Mode m) {
                        switch (m) {
                            case Mode::Increment: { ++n; }
                            default: {}
                        }
                    }
                };
            }
            i32 main() {
                app::Counter c(41);
                c.update(Mode::Increment);
                return c.read();
            }
        """),
            42,
        )

    def test_full_expression_destruction(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            struct Item {
                i32 id;
                ~Item() { trace = trace * 10 + id; }
                bool check() const { return true; }
            };
            i32 main() {
                if (false && Item(7).check()) { return 1; }
                Item(4).check();
                { Item x(Item(2)); }
                return trace;
            }
        """),
            42,
        )

    def test_constant_calls_and_control_transfers(self):
        self.assertEqual(
            self.program("""
            constexpr i32 sum(i32 n) {
                i32 result;
                for (i32 i(1); i <= n; ++i) { result += i; }
                return result;
            }
            consteval i32 answer(i32 n) { return sum(n) * 2; }
            i32 main() {
                constexpr i32 max(answer(6));
                i32 i;
                again: { ++i; }
                if (i < max - 2) { goto again; }
                outer: while (true) { while (true) { i += 2; break outer; } }
                return i;
            }
        """),
            42,
        )

    def test_project_config_and_c_objects(self):
        config = self.dir / "cpn.config"
        config.write_text(
            """configuration {
            preset = Release;
            target = "x86_64-linux-gnu";
            source.identifiers = ascii;
            numeric.integer.widths = [8, 16, 32, 64];
        };""",
            encoding="utf-8",
        )
        self.assertEqual(
            self.program(
                """
            extern "C" { i32 total; define i32 total(40); void bump(){ total += 2; } }
            i32 main(){ bump(); return total; }
        """,
                "--config",
                str(config),
            ),
            42,
        )
        config.write_text(
            "configuration { diagnostics.promote = [WARNING]; };", encoding="utf-8"
        )
        r = self.compile(
            "i32 main(){bool x; if(x = true){return 1;} return 2;}",
            "--config",
            str(config),
            "--check",
        )
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("assignment used directly", r.stderr)

    def test_union_active_payload_operations(self):
        self.assertEqual(
            self.program("""
            i32 copies; i32 moves; i32 drops;
            struct Cell {
                i32 n(3);
                Cell() = default;
                Cell(i32 v) { init n(v); }
                Cell(const<Cell>& other) { init n(other.n); ++copies; }
                Cell(Cell&& other) { init n(other.n); other.n=0; ++moves; }
                ~Cell() { ++drops; }
            };
            union U {
                default case Item(Cell c);
                case Pair(Cell left, Cell right);
                case None;
                U(const<U>&) = default;
                U(U&&) = default;
                i32 number() const {
                    match (*this) {
                        case U::Item(ref c) { return c.n; }
                        case _ { return 0; }
                    }
                }
            };
            i32 main(){
                { U initial; if(initial.number()!=3){return 1;}
                  U p(U::Pair(Cell(10),Cell(32)));
                  U copied(p); U moved(std::move(p));
                  if(copies!=2 || moves!=2 || drops!=0){return 2;}
                  match (std::move(moved)) {
                      case U::Pair(value a, move b) {
                          if(a.n+b.n!=42){return 3;}
                      }
                      case _ {return 4;}
                  }
                  if(copies!=3 || moves!=3 || drops!=2){return 5;}
                  match (moved) {
                      case U::Pair(_, ref b){if(b.n!=0){return 6;}}
                      case _ {return 7;}
                  }
                }
                if(drops!=9){return 8;}
                return 42;
            }"""),
            42,
        )

    def test_union_payload_destruction_order_and_early_return(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            struct T { i32 n; T(i32 x){init n(x);}
                       T(const<T>& b){init n(b.n);}
                       ~T(){trace=trace*10+n;} };
            union U { case Pair(T a, T b); case Empty; };
            i32 take(){match(U::Pair(T(1),T(2))){
                case U::Pair(value a, _){return a.n;}
                case _ { return 0; }
            }}
            i32 main(){if(take()!=1 || trace!=121){return 1;}
                       return 42;}
            """),
            42,
        )

    def test_union_payload_uses_final_address(self):
        self.assertEqual(
            self.program("""
            struct Self { Self* saved; Self(){init saved(this);} };
            union Inner { case A(Self object); };
            union Outer { case Wrap(Inner data); };
            i32 main(){
                Outer o(Outer::Wrap(Inner::A(Self())));
                match(o){case Outer::Wrap(ref inner){
                    match(inner){case Inner::A(ref s){
                        if(s.saved==&s){return 42;}
                    }}
                }}
                return 0;
            }"""),
            42,
        )

    def test_registered_static_and_borrowed_extent(self):
        self.assertEqual(
            self.program("""
            struct Item{i32 n;}; Item global;
            void end(Item& object){destroy(object);}
            i32 use(Item object){end(object);
                auto p(construct_at<Item>(storage_of(object),40));
                return p->n;}
            i32 main(){Item item(1);end(global);
                auto p(construct_at<Item>(storage_of(global),2));
                return use(Item(1))+p->n;}"""),
            42,
        )
        self.assertLess(
            self.program("""
            struct Pair{i32 n;};i32 main(){
                Pair p; auto inner(storage_of(p.n)); auto outer(storage_of(p));
                destroy(p);construct_at<Pair>(outer);
                construct_at<i32>(inner,42);return 1;}"""),
            0,
        )

    def test_nullable_virtual_base_conversion(self):
        self.assertEqual(
            self.program("""
            struct A{i32 x;}; struct B:virtual A{};
            A* convert(B* b){return b;}
            i32 main(){B* empty;if(convert(empty)==nullptr){return 42;}return 1;}
            """),
            42,
        )

    def test_element_storage_replacement_and_reverse_registration_order(self):
        self.assertEqual(
            self.program("""
            i32 trace; i32 calls;
            i32 index(){++calls;return 1;}
            struct Item {i32 n;Item(i32 v){init n(v);}~Item(){trace=10*trace+n;}};
            struct Other {i32 n;Other(i32 v){init n(v);}~Other(){trace=10*trace+n;}};
            void change(Item[3]& items){
                destroy(items[index()]);
                auto view(storage_of(items[1]));
                auto replacement(construct_at<Other>(view,7));
                if(replacement->n!=7){trace=9;}
            }
            i32 main(){
                { Item[3] items(Item(1),Item(2),Item(3));
                  change(items); abandon(items[0]); }
                if(trace==237 && calls==1){return 42;}return 1;
            }"""),
            42,
        )

    def test_member_replacement_in_aggregate_and_authored_destructor(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            struct A {i32 n;A(i32 v){init n(v);}~A(){trace=trace*10+n;}};
            struct B {i32 n;B(i32 v){init n(v);}~B(){trace=trace*10+n;}};
            struct Pair {A first(1);A last(2);~Pair(){trace=trace*10+3;}
                         cleanup {trace=trace*10+4;}};
            i32 main(){
                {Pair p; abandon(p.first); auto view(storage_of(p.first));
                 construct_at<B>(view,7);}
                if(trace==3274){return 42;}return 1;
            }"""),
            42,
        )
        for expr in ("*old", "values[0]"):
            with self.subTest(expr=expr):
                self.assertLess(
                    self.program(
                        "i32 main(){i32[2] values(10,20);auto old(&values[0]);"
                        "destroy(values[0]);construct_at<i32>(storage_of(values[0]),42);"
                        "return " + expr + ";}"
                    ),
                    0,
                )

    def test_storage_view_after_ending_complete_object(self):
        self.assertEqual(
            self.program("""
            i32 main(){i32 n(5);destroy(n);
                       auto replacement(construct_at<i32>(storage_of(n),42));
                       return *replacement;}"""),
            42,
        )

    def test_static_members_and_modifier_order(self):
        self.assertEqual(
            self.program("""
            struct Counter {
                static i32 value(39);
                declare static void step();
                static i32 read(){return value;}
                i32 next(){step();return read();}
            };
            void Counter::step(){++value;}
            i32 main(){
                Counter x; Counter::step(); x.next();
                function<i32()>* p(&Counter::read);
                if(sizeof(Counter)!=1 || p()!=41){return 0;}
                return ++Counter::value;
            }"""),
            42,
        )
        for source in [
            "struct S{static i32 f() const{return 0;}};",
            "struct S{static constexpr i32 f(){return 0;}};",
            "struct S{static i32 operator+(i32 n){return n;}};",
            "struct S{virtual i32 x;};",
            "struct S{i32 n; static i32 f(){return n;}};",
            "struct S{static i32 f(){return this->n;}i32 n;};",
            "struct S{declare i32 f();};i32 main(){return S::f();}",
            "i32 f(){i32 x;return i32(alignof(x));}",
            "const constexpr i32 x(1);",
        ]:
            with self.subTest(source=source):
                self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_operator_names_categories_and_native_execution(self):
        self.assertEqual(
            self.program("""
            struct Number {
                i32 n;
                Number(i32 v){init n(v);}
                i32 operator+(i32 r) const {return n+r;}
                bool operator!() const {return n==0;}
                Number& operator+=(i32 r) {n+=r;return *this;}
                Number& operator prefix ++(){++n;return *this;}
                Number operator postfix ++(){Number old(n);++n;return Number(old.n);}
                i32& operator[](i32 index){return n;}
                i32 operator()(i32 scale) const {return scale*n;}
            };
            i32 operator-(i32 l, const<Number>& r){return l-r.n;}
            i32 main(){
                Number n(4);
                i32 old(n++.n);
                ++n; n+=1; n[0]=10;
                if(old!=4 || !n || n.operator+(2)!=12 || (12-n)!=2){return 1;}
                return n(4)+(n+2)-10;
            }"""),
            42,
        )

    def test_operator_selection_competes_across_receiver_and_free_candidates(self):
        self.assertEqual(
            self.program("""
            struct N{ i32 n(1); i32 operator+(i64 x) const{return 0;} };
            i32 operator+(const<N>& n,i32 x){return x+n.n;}
            N& operator prefix --(N& n){--n.n; return n;}
            i32 main(){N n;--n;return n+i32(42);}
            """),
            42,
        )
        for source, diagnostic in [
            ("i32 operator+(i32 x,i32 y){return x;}", "nominal operand"),
            ("struct T {void operator++(){} };", "overloadable operator"),
            ("struct T {void operator&&(T& r){} };", "overloadable operator"),
            ("struct T {i32 operator prefix ++(){return 0;} };", "writable nominal"),
            ("struct T {i32 operator[](i32 x,i32 y){return 0;} };", "operand count"),
            ("struct T {}; i32 operator[](T& o,i32 n){return n;}", "nonstatic member"),
            (
                "struct T {i32 operator+(i32 n) const{return n;}};"
                "i32 operator+(const<T>& t,i32 n){return n;}i32 f(T& t){return t+i32(1);}",
                "ambiguous overload",
            ),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_qualified_definitions_and_root_lookup(self):
        self.assertEqual(
            self.program("""
            i32 destroyed; i32 offset(2); i32 add(){return 10;}
            namespace ns {
                i32 offset(1); i32 add(){return 20;}
                declare i32 sum(i32 n(9));
                class Box {
                    i32 n;
                public:
                    declare Box(i32 v);
                    declare Box(const<Box>&);
                    declare ~Box();
                    declare i32 read() const noexcept;
                };
            }
            ns::Box::Box(i32 v){init n(v);}
            ns::Box::Box(const<ns::Box>&) = default;
            ns::Box::~Box(){++destroyed;}
            i32 ns::Box::read() const noexcept{return n+::offset;}
            i32 ns::sum(i32 n){return ::add()+add()+offset+n;}
            i32 main(){
                { ::ns::Box x(38); ::ns::Box y(x);
                  if(y.read()!=40 || ::ns::sum()!=40){return 1;} }
                return 40+destroyed;
            }
            """),
            42,
        )
        for source, diagnostic in [
            ("struct R{}; i32 R::extra(){return 1;}", "existing declaration"),
            (
                "struct R{declare i32 f(i32);};i32 R::f(bool x){return 0;}",
                "existing declaration",
            ),
            (
                "struct R{declare i32 f() const noexcept;};i32 R::f() const{return 1;}",
                "incompatible redeclaration",
            ),
            (
                "class R{declare i32 f();};i32 R::f(){return 1;}i32 g(R& r){return r.f();}",
                "inaccessible",
            ),
            ("struct R{declare R();};R::Other(){}", "owning record"),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_nested_generic_names_and_union_alternatives(self):
        self.assertEqual(
            self.program("""
            generic<type T> struct Box{T item;};
            generic<type T> union Maybe{case Some(T item);case None;};
            alias MaybeInt = Maybe<i32>;
            i32 main() {
                Box<Box<i32>> nested;
                nested.item.item=40;
                MaybeInt sample(Maybe<i32>::Some(nested.item.item));
                match(sample) {
                    case MaybeInt::Some(ref n){return n+2;}
                    case ::Maybe<i32>::None{return 1;}
                }
            }"""),
            42,
        )

    def test_reserved_and_contextual_identifiers(self):
        for word in (
            "associated",
            "declaration",
            "destruction_owner",
            "emit",
            "export",
            "generate",
            "module",
            "partial_typefn",
            "quote",
            "reflect_type",
            "satisfy",
            "specialize",
            "splice_expr",
        ):
            with self.subTest(word=word):
                result = self.compile("i32 " + word + ";", "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("identifier", result.stderr)
        words = (
            "Manual",
            "Complete",
            "aggregate",
            "base",
            "base_path",
            "expression",
            "final",
            "move",
            "override",
            "postfix",
            "prefix",
            "ref",
            "type",
            "value",
            "virtual_base",
        )
        result = self.compile(" ".join("i32 " + w + ";" for w in words), "--check")
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_union_payload_rules(self):
        for source, message in [
            ("union U{case A(i32);};", "identifier"),
            ("union U{case A();};", "type"),
            ("union U{case A(i32 x, i32 x);};", "duplicate union payload"),
            ("union U{case A(i32 x(1));};", "expected ')'"),
            ("union U{case A; i32 x;};", "common fields"),
            ("union U{case A;}; struct R:U {};", "complete record"),
            ("union U{case A;}; void f(){U x(U::A()); U y(x);}", "copy constructor"),
            (
                "struct T {}; union U{case A;case B(T t); U(const<U>&)=default;};"
                "void f(){U x(U::A());U y(x);}",
                "copy constructor",
            ),
            (
                "union U{case A;};void f(U x){match(x){case _{}case U::A{}}}",
                "final match arm",
            ),
            (
                "union U{case A(const i32 n);};void f(U x){"
                "match(x){case U::A(ref n){n=1;}}}",
                "writable lvalue",
            ),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_tagged_union_and_match(self):
        self.assertEqual(
            self.program("""
            union Reading { default case Missing; case Sample(i32 value); };
            i32 main() {
                Reading r(Reading::Sample(40));
                match(r) {
                    case Reading::Missing { return 1; }
                    case Reading::Sample(ref n) { n += 2; return n; }
                }
            }
        """),
            42,
        )

    def test_declared_copy_move_and_assignment(self):
        self.assertEqual(
            self.program("""
            struct Point {
                i32 x; i32 y;
                Point(const<Point>& source) = default;
                Point(Point&& source) = default;
                Point& operator=(const<Point>& source) = default;
            };
            i32 main() {
                Point a(40,2); Point b(a); Point c(std::move(b));
                a = c;
                return a.x + a.y;
            }
        """),
            42,
        )

    def test_memberwise_operations_call_authored_members_in_order(self):
        self.assertEqual(
            self.program("""
            i32 calls;
            struct Element {
                i32 n;
                Element(i32 v){init n(v);}
                Element(const<Element>& v){init n(v.n); calls=calls*10+n;}
                Element(Element&& v){init n(v.n); v.n=0; calls=calls*10+n;}
                Element& operator=(const<Element>& v){n=v.n; calls=calls*10+n; return *this;}
                Element& operator=(Element&& v){n=v.n; v.n=0; calls=calls*10+n; return *this;}
            };
            struct Pair {
                Element[2] value;
                Pair(){init value(Element(1),Element(2));}
                Pair(const<Pair>& p)=default;
                Pair(Pair&& p)=default;
                Pair& operator=(const<Pair>& p)=default;
                Pair& operator=(Pair&& p)=default;
            };
            i32 main(){
                Pair first;
                Pair second(first);
                Pair third(std::move(first));
                second = third;
                third = std::move(second);
                if (calls==12121212 && first.value[0].n==0 &&
                    second.value[1].n==0 && third.value[1].n==2) {return 42;}
                return 0;
            }"""),
            42,
        )

    def test_parameter_construction_precedes_the_next_argument(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            struct Box {
                i32 n;
                Box(i32 a){init n(a);}
                Box(const<Box>& b){init n(b.n); trace=trace*10+n;}
            };
            i32 change(Box& b){b.n=7; trace=trace*10+7; return 0;}
            i32 first(Box b, i32 unused){return b.n;}
            struct Hold {i32 n; Hold(Box b, i32 unused){init n(b.n);} };
            i32 main(){
                Box a(3);
                if(first(a,change(a))!=3 || trace!=37){return 1;}
                a.n=4; trace=0;
                Hold h(a,change(a));
                if(h.n!=4 || trace!=47){return 2;}
                a.n=5; trace=0;
                auto read([] i32(Box b,i32 unused){return b.n;});
                if(read(a,change(a))==5 && trace==57){return 42;}
                return 3;
            }"""),
            42,
        )

    def test_final_storage_through_calls_and_indirect_aggregate_abi(self):
        self.assertEqual(
            self.program("""
            i32 copies; i32 moves;
            struct Self {
                Self* address; i32 n;
                Self(i32 v){init address(this);init n(v);}
                Self(const<Self>& other){init address(this);init n(other.n);++copies;}
                Self(Self&& other){init address(this);init n(other.n);++moves;}
                bool same() const {return address==this;}
            };
            Self make(i32 n){return Self(n);}
            Self local(){Self a(10);return a;}
            Self moved(){Self a(12);return std::move(a);}
            i32 read(Self s){if(!s.same()){return 0;}return s.n;}
            struct Factory{virtual Self get(){return Self(1);}};
            struct Derived:Factory{Self get() override{return make(20);}};
            i32 main(){
                function<Self(i32)>* f(&make); Self s(f(10));
                if(!s.same() || read(s)!=10 || copies!=1 || moves!=0){return 1;}
                function<i32(Self)>* take(&read); if(take(make(30))!=30){return 2;}
                Self a(local()); Self b(moved());
                Derived d; Factory& factory(d);
                Self c(factory.get());
                if(!a.same() || !b.same() || !c.same() || copies!=2 || moves!=1){return 3;}
                return a.n+b.n+c.n;
            }"""),
            42,
        )

    def test_conditional_results_and_owning_captures_use_final_storage(self):
        self.assertEqual(
            self.program("""
            i32 drops; i32 copies;
            struct S {S* addr;i32 n;
                S(i32 v){init addr(this);init n(v);}
                S(const<S>& s){init addr(this);init n(s.n);++copies;}
                ~S(){++drops;}
                bool valid() const{return this==addr;}
            };
            S make(i32 n){return S(n);}
            S choose(bool b, S& other){return b ? make(10) : other;}
            i32 main(){
                { S local(32);S a(choose(true,local));S b(choose(false,local));
                  if(!a.valid() || !b.valid() || drops!=0 || copies!=1){return 1;}
                  auto fn([local,k(make(10))] i32(){
                      if(!local.valid() || !k.valid()){return 0;} return local.n+k.n;
                  });
                  if(fn()!=42 || copies!=2){return 2;}
                  auto selected(false ? make(1) : make(7));
                  if(!selected.valid() || selected.n!=7){return 3;}
                }
                if(drops!=6){return 4;}return 42;
            }"""),
            42,
        )

    def test_returned_union_and_array_fields_keep_their_addresses(self):
        self.assertEqual(
            self.program("""
            struct T{T* self; T(){init self(this);}};
            union U{case A(T value);};
            U build(){return U::A(T());}
            T make(){return T();}
            struct Holder{T[2] array(make(),make());U item(build());};
            i32 main(){Holder h;
                if(h.array[0].self!=&h.array[0] || h.array[1].self!=&h.array[1]){return 1;}
                match(h.item){case U::A(ref v){if(v.self==&v){return 42;}}}
                return 0;}
            """),
            42,
        )

    def test_value_parameters_returns_and_elided_results(self):
        self.assertEqual(
            self.program("""
            i32 copies; i32 moves; i32 drops;
            struct Item {
                i32 v;
                Item(i32 x){init v(x);}
                Item(const<Item>& s){init v(s.v); ++copies;}
                Item(Item&& s){init v(s.v); s.v=0; ++moves;}
                ~Item(){++drops;}
            };
            Item by_copy(Item arg){ return arg; }
            Item by_move(Item arg){ return std::move(arg); }
            void use(){
                Item a(42);
                auto b(by_copy(a));
                Item c(by_move(Item(7)));
                auto d(b);
                by_move(Item(0));
            }
            i32 main(){use(); if(copies==3 && moves==2 && drops==8){return 42;}
                       return 0;}
            """),
            42,
        )
        for statements, diagnostic in (
            ("Only a; Only b(a);", "copy constructor"),
            ("Only a; auto b(a);", "copy constructor"),
            ("Only a; accept(a);", "copy constructor"),
            ("Only a; Only b; a=b;", "copy assignment"),
            ("Only a; Only b; a=std::move(b);", "move assignment"),
        ):
            with self.subTest(statements=statements):
                result = self.compile(
                    "struct Only { Only(Only&& v)=default; }; "
                    "void accept(Only v){} i32 main(){" + statements + "return 0;}",
                    "--check",
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)
        result = self.compile(
            "struct Only { Only(Only&& v)=default; }; Only f(){ Only a; return a; }",
            "--check",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("copy constructor", result.stderr)

    def test_small_integer_domains_with_c_caller(self):
        source = """
            configuration { numeric.integer.overflow = saturating; };
            extern "C" i8 product(i8 a, i8 b) { return a*b; }
            extern "C" u8 difference(u8 a, u8 b) { return a-b; }
            extern "C" i8 quotient(i8 a, i8 b) { return a/b; }
            extern "C" bool less(i8 a, u8 b) { return a < b; }
        """
        host = """
            #include <stdint.h>
            #include <stdbool.h>
            extern int8_t product(int8_t,int8_t), quotient(int8_t,int8_t);
            extern uint8_t difference(uint8_t,uint8_t);
            extern bool less(int8_t,uint8_t);
            static int clamp(int n) { return n < -128 ? -128 : n > 127 ? 127 : n; }
            int main(void) {
                for (int a = -128; a < 128; ++a)
                    for (int b = -128; b < 128; ++b) {
                        if (product(a,b) != clamp(a*b)) return 1;
                        if (b && quotient(a,b) != clamp(a/b)) return 2;
                        if (difference(a+128,b+128) != (a>b ? a-b : 0)) return 3;
                        if (less(a,b+128) != (a < b+128)) return 4;
                    }
                return 42;
            }
        """
        self.assertEqual(self.program(source, host=host), 42)

    def test_cleanup_manual_member_barrier(self):
        self.assertEqual(
            self.program("""
            i32 trace;
            struct Item { i32 id; ~Item(){ trace = trace*10 + id; } };
            class Manual Pair {
            public:
                Item first; Item second;
                Pair(){ init first(2); init second(4); }
                ~Pair() {} cleanup { destroy(second); }
            };
            i32 main(){ { Pair p; } return trace; }
        """),
            42,
        )

    def test_source_errors(self):
        bad = [
            (
                "union R { case A; case B; }; i32 f(R r){ match(r){case R::A{return 1;}} }",
                "non-exhaustive",
            ),
            (
                "struct P { i32 x; }; i32 f(){P a; P b(a); return 1;}",
                "copy constructor",
            ),
            (
                "struct P { P(const<P>&) = delete; }; i32 f(){P a; P b(a); return 1;}",
                "copy constructor",
            ),
            ("i32 f(){ u8 n(-1); return n; }", "outside the range"),
            ("i32 f(){ return 0b102; }", "malformed"),
            ("i32 f(){ return 1__0; }", "malformed"),
            ("i32 f(){ /*", "unterminated"),
            ("i32 f(){ if (1) { return 2; } return 0; }", "requires bool"),
            ("i8 f(i32 x){ return x; }", "lossless conversion"),
            ("i32 f(){ i32 a(a); return a; }", "before initialization"),
            ("i32 f(){ const i32 a(0); a++; return a; }", "writable lvalue"),
            ("i32 f(i32 x){ return x / (2 - 2); }", "division by zero"),
            ("i32 f(bool c){ if (c) { return 1; } }", "without returning"),
            ("i32 f(){ return late(); } i32 late(){return 1;}", "unknown name"),
            ("declare i32 f(); i32 main(){return f();}", "needs a definition"),
            ("i32 f(){ switch(3){case 3:{} case 3:{}} return 1; }", "duplicate case"),
            ("i32 f(){ i32 a = 3; return a; }", "expected ';'"),
            ("i32 f(){ u64 a; i64 b; auto c(a+b); return 0; }", "i128 is unavailable"),
            ("i32 f(){ goto end; i32 x; end: return x; }", "unexecuted initializer"),
            (
                "consteval i32 f(i32 a){return a;} i32 g(i32 x){return f(x);}",
                "constant argument required",
            ),
            ("struct A{ A[1] array; };", "incomplete record"),
            ("void f(){ void[1] array; }", "complete object element"),
            ("void f(){ i32[1 - 2] a; }", "outside the range"),
            ("void f(usize n){ i32[n + 1] a; }", "constant expression"),
            ("configuration {diagnostics.promote=[[WARNING]];};", "CFG001"),
            ("configuration {diagnostics.suppress=[LIFE002];};", "CFG001"),
            ("configuration {compilation.modules=true;};", "CFG002"),
            ('[[static_id("a")]] i32 x; [[static_id("a")]] i32 y;', "STAT001"),
            ("[[init_after(b)]] i32 a; i32 b;", "cyclic static initialization"),
            ("[[init_after(missing)]] i32 a;", "unknown static dependency"),
            ("generic<type T> void f(T a){auto bad('ab');}", "one Unicode scalar"),
            ("generic<const void* P> struct B {};", "invalid generic constant"),
            ("generic<const i32 N = missing> struct B {};", "unknown name"),
            ("struct S{i32 x;}; void f(){ S[2] a; S[2] b(a); }", "copy constructor"),
            (
                "enum E:i32{case A(1)}; void f(){ E[2] xs(E::A); }",
                "zero-valued default",
            ),
            ("generic<const i32 N> struct B{}; void f(){ B<1>=v; }", "expected"),
            ("enum E:u8 {case A(0),case B(0)};", "duplicate enum"),
            (
                "i32 f(){ i32 x; if (true) { destroy(x); } return x; }",
                "ended object generation",
            ),
            ("i32 f(){ int x = 0; return x; }", "expected"),
            ("i32 f(){ for(int i=0;i<2;i++){ } return 1;}", "expected"),
            ("i32 f(){ i32 a; destroy(a); return a; }", "ended object generation"),
            (
                "i32 f(){ i32 a; auto p(&a); destroy(a); return *p; }",
                "ended object generation",
            ),
            (
                "i32 f(){ i32 x; auto s(storage_of(x)); construct_at<i32>(s,4); return 0; }",
                "live generation",
            ),
            (
                "i32 f(){ i8 x; auto s(storage_of(x)); destroy(x); construct_at<i64>(s,4); return 0; }",
                "insufficient storage",
            ),
            ("i32 f(){ i32[2] a; return a[2]; }", "outside extent"),
            ("i32 f(){ i32 x[2]; return 0; }", "expected ';'"),
            ("i32 f(){ if (true) return 2; return 0; }", "expected '{'"),
            ("i32 f(void){return 1;}", "void parameter"),
            ("i32 f(){ i32 x(1); i32 x(2); return x; }", "duplicate declaration"),
            ("#define N 42\ni32 f(){return N;}", "unsupported or unknown type"),
            ("i32 f(){ return 42UL; }", "malformed"),
            ("i32 f(){ char c('ab'); return 1; }", "one Unicode scalar"),
            ("i32 f(){ auto c('\\u{D800}'); return 1; }", "Unicode scalar"),
            (
                "class Locked { i32 n; }; i32 f(){ Locked v; return v.n; }",
                "inaccessible member",
            ),
        ]
        for source, msg in bad:
            with self.subTest(source=source):
                r = self.compile(source, "--check")
                self.assertNotEqual(r.returncode, 0)
                self.assertRegex(r.stderr, r"example\.cpn:\d+:\d+: ERROR:")
                self.assertIn(msg, r.stderr)

    def test_edition_and_output_integrity(self):
        for args in ([], ["--std=CPN25"]):
            r = self.compile("i32 main(){ return 42; }", *args, edition=False)
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("--std", r.stderr)
        output = self.dir / "kept.o"
        output.write_bytes(b"kept")
        r = self.compile("i32 main(){ return invalid; }", "-o", output)
        self.assertNotEqual(r.returncode, 0)
        self.assertEqual(output.read_bytes(), b"kept")
        self.src.write_text("i32 main(){ return 42; }", encoding="utf-8")
        driver = shutil.which(DRIVER[0]) or DRIVER[0]
        result = subprocess.run(
            [driver, "--std=CPN26", "-c", self.src, "-o", output],
            env={**os.environ, "PATH": ""},
            capture_output=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output.read_bytes()[:4], b"\x7fELF")


if __name__ == "__main__":
    unittest.main()
