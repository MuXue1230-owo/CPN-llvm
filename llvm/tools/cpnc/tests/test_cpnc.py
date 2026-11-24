"""Exercise the command line, LLVM verifier, native linker, and generated programs."""

import os
import signal
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

    def test_construction_callbacks_with_whole_tracking_and_unevaluated_calls(self):
        self.assertEqual(
            self.program("""
          [[lifecycle_effect(whole)]] void unused(){}
          i32 drops;
          struct Guard {~Guard(){++drops;}};
          struct Box{
            i32 a; i32 b; i32 c(b+1);
            [[initializes(a)]] i32 start(i32 n){a=n;return a;}
            Box(i32 b){Guard guard;init b(a+1);i32 got(start(b));}
          };
          i32 main(){Box x(40);
            if(sizeof(x.start(9))!=sizeof(i32) || x.a!=40 || drops!=1){return 1;}
            return x.c;}
        """),
            42,
        )

    def test_source_bound_construction_under_analysis_modes(self):
        body = """
          i32 defaults;struct Cell{i32 n;Cell(){++defaults;}Cell(i32 v){init n(v);}
              Cell& operator=(const<Cell>& c)=delete;};
          struct Root {Cell cell;[[initializes(cell)]] void build(){cell=Cell(42);}
              Root(){usize size(sizeof(cell));build();}};
          i32 main(){Root r;return defaults==0?r.cell.n:0;}
        """
        for mode in ("local", "interprocedural"):
            config = (
                "configuration { construction.analysis="
                + mode
                + "; effects.inference="
                + mode
                + "; };"
            )
            self.assertEqual(self.program(config + body), 42)
        for source in (
            "void f(){configured(construction.analysis=local){}}",
            "configuration {effects.inference=invalid;};",
        ):
            r = self.compile(source, "--check")
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("CFG001", r.stderr)

    def test_minimal_unit_and_diagnostic_operations(self):
        self.assertEqual(
            self.program("""
                i32 count;
                bool bump(){++count;return true;}
                i32 main(){
                    std::Unit value;
                    std::Unit copy(value);
                    std::Unit moved(::std::move(copy));
                    copy=moved;
                    constexpr bool single(std::Unit()==std::Unit());
                    if(!single || copy!=value || !(moved==value)){return 0;}
                    configured(library.debug_assertions=false) (std::debug_assert(bump()));
                    std::ensure(bump());
                    std::discard(bump());
                    return count+40;
                }
            """),
            42,
        )
        assertions = """
            i32 count;
            bool check(){++count;return true;}
            i32 main(){::std::debug_assert(check());return count;}
        """
        self.assertEqual(self.program(assertions, "--preset", "Debug"), 1)
        self.assertEqual(self.program(assertions, "--preset", "Release"), 0)
        self.assertEqual(
            self.program(
                "i32 main(){std::ensure(false);return 0;}", "--preset", "Release"
            ),
            -signal.SIGILL,
        )
        wrong = self.compile(
            "i32 main(){std::debug_assert(i32(1));return 0;}",
            "--preset",
            "Release",
            "--check",
        )
        self.assertEqual(wrong.returncode, 1, wrong.stderr)
        self.assertIn("condition requires bool", wrong.stderr)
        self.assertEqual(
            self.program("""
                struct Part {
                    i32 number;
                    Part(i32 n){init number(n);}
                    Part& operator=(Part&& other)=delete;
                };
                struct Parent {
                    Part part;
                    Parent(){
                        configured(library.debug_assertions=false) {
                            std::debug_assert(part.number==0);
                        }
                        part=Part(42);
                    }
                };
                i32 main(){Parent p;return p.part.number;}
            """),
            42,
        )

    def test_nested_type_scopes_and_structural_requirements(self):
        self.assertEqual(
            self.program("""
          namespace lib {
            struct Box {
              alias Count=i32;
              declare struct Cell;
              struct Cell { Count value; };
              enum State:i8 { case Ready(0),case Full(1) };
              union Payload {default case Empty; case Number(Count n);};
              Cell data;
              Count read(){return data.value;}
            };
          }
          constraint HasCount<type T> {type T::Count; expression(T& x){x.read() -> T::Count;}};
          class Hidden { alias Count=i8; };
          generic<type T> requires(HasCount<T>) T::Count read(T& value){
            return value.read();}
          i32 main(){lib::Box::Cell cell(39);
            lib::Box box(lib::Box::Cell(cell.value));lib::Box::State state(lib::Box::State::Full);
            lib::Box::Payload p(lib::Box::Payload::Number(3));
            if(HasCount<Hidden> || state!=lib::Box::State::Full){return 1;}
            match(p){case lib::Box::Payload::Number(value n){return read(box)+n;}
                     case lib::Box::Payload::Empty{return 0;}}
          }
        """),
            42,
        )
        for source in (
            "class A{alias Private=i32;};A::Private data;",
            "struct A{alias X=i32; i32 X;};",
            "struct A{struct X{}; union X{case V;};};",
            "struct A{struct X{};}; X outside;",
        ):
            self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_nested_nominals_complete_in_layout_dependency_order(self):
        self.assertEqual(
            self.program("""
                struct Envelope {
                    struct Cell {
                        Envelope* owner;
                        Payload payload;
                        Number number;
                        i32 read(){
                            return owner->id + payload.get()
                                + i32(std::to_underlying(number));
                        }
                    };
                    union Payload {
                        case Number(i32 data);
                        i32 get() const {
                            match(*this){case Payload::Number(value i){return i;}}
                        }
                    };
                    alias Number=Scalar;
                    enum Scalar:i32 { case Answer(2) };
                    i32 id;
                    Cell cell;
                };
                i32 main(){
                    Envelope env(20,Envelope::Cell(nullptr,
                        Envelope::Payload::Number(20),Envelope::Scalar::Answer));
                    env.cell.owner=&env;
                    return env.cell.read();
                }
            """),
            42,
        )
        recur = self.compile(
            "struct Graph{struct Left{Right r;};struct Right{Left l;};};",
            "--check",
        )
        self.assertEqual(recur.returncode, 1, recur.stderr)
        self.assertIn("field requires a complete object type", recur.stderr)

    def test_nested_sibling_pointer_cycles_and_qualified_calls(self):
        self.assertEqual(
            self.program("""
                struct Graph {
                    struct Left {
                        Right* right;
                        i32 number;
                        i32 read(){return right->read() + Right::add<2>();}
                    };
                    struct Right {
                        Left* left;
                        i32 read(){return left->number;}
                        generic<const i32 N> static i32 add(){return N;}
                    };
                };
                i32 main(){Graph::Left lhs;Graph::Right rhs(&lhs);
                    lhs.right=&rhs;lhs.number=40;return lhs.read();}
            """),
            42,
        )

    def test_generic_methods_inherit_and_keep_owner_substitutions(self):
        self.assertEqual(
            self.program("""
          generic<type A> struct Holder {
            A value;
            generic<type B> A get(B unused) const {return value;}
            generic<const i32 N> i32 number(){return N;}
            generic<type B> static B identity(B x){return x;}
          };
          struct Derived:Holder<i32>{};
          i32 main(){Derived d;d.value=39;
            return d.get<bool>(true)+d.number<1>()+Holder<i32>::identity<i32>(2);}
        """),
            42,
        )
        for source in (
            "class A{generic<type T> T f(T n){return n;}};void g(){A a;a.f(1);}",
            "struct A{generic<type T> T f(T n){return n+n;}};",
        ):
            self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_qualified_generic_definitions_and_early_calls(self):
        self.assertEqual(
            self.program("""
          namespace lib{
            struct S{i32 seed;
              generic<type T> declare T take(T n,T previous(n)) const;
              generic<type T> requires(SameType<T,i32>) declare T combine(T n) const;
            };
          }
          i32 before(lib::S& s){return s.take(20);}
          generic<type U> U lib::S::take(U a,U b) const{return b;}
          generic<type V> requires(SameType<V,i32>) V lib::S::combine(V v) const{return seed+v;}
          i32 main(){lib::S s(20);
            if(before(s)!=20){return 1;}return s.combine(s.take<i32>(1,22));}
        """),
            42,
        )
        for source in (
            "struct S{};generic<type T> T S::missing(T x){return x;}",
            "struct S{generic<type T> declare T f(T x) const;};generic<type T> T S::f(T x){return x;}",
            "struct S{generic<type T> declare T f(T x);};generic<type T> i32 S::f(T x){return 1;}",
            "struct S{generic<type T> declare T f(T n);};generic<type T> T S::f(T n(4)){return n;}",
        ):
            self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_dependent_assignment_requires_matching_category_evidence(self):
        requirements = """
            constraint Copies<type A> {
                expression (A& left, const<A>& right) {left = right -> A&;}
            };
            constraint Moves<type A> {
                expression (A& left, A& right) {left = std::move(right) -> A&;}
            };
        """
        self.assertEqual(
            self.program(
                requirements
                + """
                generic<type T> requires(Copies<T>)
                void copy_to(T& left,T& right){left=right;}
                generic<type T> requires(Moves<T>)
                void move_to(T& left,T&& right){left=std::move(right);}
                generic<type T> void guarded(T& left,const<T>& right){
                    if constexpr(Copies<T>){left=right;}
                }
                generic<type T> requires(CopyConstructible<T>)
                struct Box {T item; Box(const<T>& source){item=source;} };
                i32 main(){
                    i32 left; i32 right(18); copy_to(left,right);
                    i32 first(left); right=24; move_to(left,std::move(right));
                    guarded(left,right); Box<i32> box(left); return first+box.item;
                }
            """
            ),
            42,
        )
        for definition in (
            "generic<type T> void f(T& a,const<T>& b){a=b;}",
            "generic<type T> requires(Copies<T>) void f(T& a,T& b){a=std::move(b);}",
            "generic<type T> requires(Moves<T>) void f(T& a,T& b){a=b;}",
            "generic<type T> void f(T& a,const<T>& b){"
            "if constexpr(!SameType<T,const<T>>){a=b;}}",
            "generic<type T> struct Copier {Copier(T& a,const<T>& b){a=b;}};",
            "generic<type T> struct Copier {T item;"
            "Copier(T& item,const<T>& source){item=source;}};",
        ):
            with self.subTest(definition=definition):
                result = self.compile(requirements + definition, "--check")
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn(
                    "dependent operation '=' is not established", result.stderr
                )

    def test_generic_contracts_keep_declaration_parameter_positions(self):
        self.assertEqual(
            self.program("""
            [[ensures(return_value==limit)]]
            generic<const i32 limit> declare i32 pick(const<i32>& data)
                [[effects(read(data))]];
            i32 early_pick(const<i32>& n) {return pick<20>(n);}
            [[ensures(return_value==bound)]]
            generic<const i32 bound> i32 pick(const<i32>& source)
                [[effects(read(source))]] {return source;}

            generic<const i32 limit> struct Box {
                i32 data;
                [[ensures(return_value==limit)]]
                declare i32 get() const [[effects(read(this))]];
            };
            [[ensures(return_value==bound)]]
            generic<const i32 bound> i32 Box<bound>::get() const
                [[effects(read(this))]] {return data;}

            generic<type... Ts> i32 pack(Ts... args)
                [[effects(read(args))]] {return 1;}
            i32 main() {
                Box<20> box(20);
                i32 n(20);
                return box.get()+early_pick(n)+pack()+pack(n,42);
            }
            """),
            42,
        )
        for source, diagnostic in (
            (
                "[[requires(missing)]] generic<type T> T id(T x) {return x;}",
                "unknown name 'missing' in contract predicate",
            ),
            (
                "[[requires(late())]] generic<const i32 N> i32 f() {return N;} "
                "[[effects(none)]] bool late() {return true;}",
                "unknown name 'late' in contract predicate",
            ),
            (
                "[[requires(x>0)]] generic<type T> void f(T x) {}",
                "dependent operation '>' is not established",
            ),
            (
                "generic<type T> i32 f(T x) [[effects(read(missing))]] {return 0;}",
                "unknown effect region",
            ),
            (
                "generic<type T> declare i32 f(T x,T y) [[effects(read(x))]]; "
                "generic<type U> i32 f(U a,U b) [[effects(read(b))]] {return 0;}",
                "incompatible generic effect contract",
            ),
            (
                "[[ensures(return_value==N)]] generic<const i32 N> declare i32 f(); "
                "[[ensures(return_value!=M)]] generic<const i32 M> i32 f(){return 0;}",
                "incompatible generic value contract",
            ),
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_nested_types_of_applied_families(self):
        self.assertEqual(
            self.program("""
          generic<type T> struct Outer {
            alias Value=T;
            struct Inner{T data;};
            generic<type U> struct Pair{T left;U right;};
          };
          i32 main(){Outer<i32>::Inner a(40);
            Outer<i32>::Pair<i8> pair(a.data,2);
            Outer<i32>::Value result(pair.left+pair.right);
            return result;}
        """),
            42,
        )

    def test_member_construction_tails_and_scalar_tail_cleanup(self):
        self.assertEqual(
            self.program("""
            i32 drops; struct Count{~Count(){++drops;}};
            struct Inner {i32 a; i32 b; Inner(){a=2;}};
            struct Aggregate {i32 seed(39);
                Inner child -> {init b(a+seed);this->b+=1;};
            };
            struct Authored {i32 seed(39);
                Inner child -> {init b(a+seed);this->b+=1;};Authored(){}
            };
            i32 main(){Aggregate first;Authored second;
                i32 x(1) -> {Count c;*this=4;};
                i32[2] items(1,2) -> {(*this)[0]=x;};
                if(first.child.b!=42 || drops!=1 || items[0]!=4){return 0;}
                return second.child.b;}
        """),
            42,
        )
        for source in (
            "void f(){i32 x -> {init missing(1);};}",
            "struct S{i32 x -> {init missing(1);};};void f(){S s;}",
        ):
            self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_dependent_member_index_and_call_witnesses(self):
        self.assertEqual(
            self.program("""
          struct View {i32 n; i32 operator[](i32 i){return n+i;} i32 plus(i32 x){return n+x;}};
          constraint Readable<type T> {
            expression(T& v,i32 i) {v.n -> i32&; v[i] -> i32; v.plus(i) -> i32;}
          };
          generic<type T> requires(Readable<T>) i32 read(T& v,i32 i) {
            return v.n + v[i] + v.plus(i);
          }
          i32 main(){View v(12);return read(v,3);}
        """),
            42,
        )
        for expr in ("x.missing", "x.missing(1)", "x[i]", "x(i)", "p->missing"):
            r = self.compile(
                "generic<type T> i32 bad(T& x,T* p,i32 i){return " + expr + ";}",
                "--check",
            )
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("declared constraints", r.stderr)
        r = self.compile(
            """
          constraint WithMember<type T>{expression(T& v){v.n -> i32&;}};
          generic<type T> requires(WithMember<T>) i32 wrong(T& x){return x.other;}
        """,
            "--check",
        )
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("declared constraints", r.stderr)

    def test_authored_union_copy_move_default_and_static_member(self):
        self.assertEqual(
            self.program("""
            i32 copies; i32 moves; i32 dropped;
            struct Cell {i32 n; Cell(i32 v){init n(v);}
              Cell(const<Cell>& c){init n(c.n);++copies;}
              Cell(Cell&& c){init n(c.n);++moves;} ~Cell(){++dropped;}};
            union U {default case Empty;case Data(Cell c);
              static i32 visits;
              U(i32 n){visits+=n;}
              U(const<U>& other){++visits;} declare U(U&& other);
              i32 get() const {match(*this){case U::Empty{return 0;}
                                            case U::Data(ref v){return v.n;}}}
            };
            U::U(U&& other){++visits;}
            i32 main(){i32 got;
              {U d(1); U a(U::Data(Cell(42))); U b(a); U c(std::move(b));U empty(d);
               got=c.get();if(d.get()!=0 || empty.get()!=0){return 0;}}
              return copies==1 && moves==1 && dropped==3 && U::visits==4 ? got : 1;}
        """),
            42,
        )
        for source in (
            "enum E:i8{case One(1)};union U{default case Missing(E e);};",
            "struct X{X(const<X>& o)=delete;};union U{case D(X x);U(const<U>& y){}};",
        ):
            self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_conditional_construction_and_pointer_state(self):
        self.assertEqual(
            self.program("""
          i32 defaults;
          struct Item {i32 n;Item(){++defaults;}Item(i32 x){init n(x);}
                       Item& operator=(const<Item>& x)=delete;};
          struct One {Item item;
            [[initializes(item)]] i32 fill(i32 x){item=Item(x);return x;}
            One(bool flag){i32 k(flag?fill(20):fill(22));}
          };
          i32 main(){One a(true);One b(false);return defaults==0?a.item.n+b.item.n:0;}
        """),
            42,
        )
        for choice, expected in (("true", 42), ("false", -4)):
            self.assertEqual(
                self.program(
                    """
              i32* pick(bool choose,i32* a,i32* b){return choose?a:b;}
              i32 main(){i32[2] a(1,42);i32[1] b(2);
                auto p(pick(CHOICE,&a[0],&b[0]));return *(p+1);}
            """.replace("CHOICE", choice)
                ),
                expected,
            )

    def test_special_member_attribute_positions(self):
        self.assertEqual(
            self.program("""
          struct X{[[lifecycle_effect(whole)]] X(){} [[lifecycle_effect(whole)]] ~X(){}};
          i32 main(){X value;return 42;}
        """),
            42,
        )
        for source in (
            "[[lifecycle_effect(whole)]] configured(numeric.integer.overflow=checked) void f(){}",
            "struct X{[[initializes(x)]] X(){}i32 x;};",
        ):
            self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_block_nominal_declarations_and_distinct_owners(self):
        self.assertEqual(
            self.program("""
            i32 main(){
              alias Number=i32;
              declare struct Local;
              alias Before=Local*;
              struct Local{Number n;Local* self;Local(Number v){init n(v);init self(this);}
                Number read() const{return n;}};
              enum State:i8{case Ready(0),case Other(1)};
              union Value{case Some(Number n);default case None;};
              Local l(40);Before pointer(&l);
              State s(State::Ready);Value v(Value::Some(2));
              {struct Local{i8 n;};Local inner(1);if(inner.n!=1){return 1;}}
              if(s!=State::Ready || pointer!=l.self){return 0;}
              match(v){case Value::Some(value x){return pointer->read()+x;}
                       case Value::None{return 1;}}
            }
        """),
            42,
        )
        for source in (
            "void f(){{struct A{};}A out;}",
            "void f(){struct A{};i32 A;}",
            "void f(){declare struct A; union A{case Empty;};}",
        ):
            self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_reference_arguments_and_results_preserve_element_extent(self):
        self.assertEqual(
            self.program("""
          [[returns_borrowed_from(x)]] i32& ref(i32& x){return x;}
          i32 next(i32& x){return *(&x+1);}
          i32 main(){i32[3] a(4,5,42);return next(ref(a[1]));}
        """),
            42,
        )
        for last in ("return next(ref(a[1]));", "return read(a[0],replace(a[0]));"):
            self.assertEqual(
                self.program(
                    """
              [[returns_borrowed_from(x)]] i32& ref(i32& x){return x;}
              i32 next(i32& x){return *(&x+1);}
              i32 read(i32& x,i32 ignored){return x;}
              i32 replace(i32& x){auto cap(storage_of(x));destroy(x);
                construct_at<i32>(cap,42);return 0;}
              i32 main(){i32[2] a(7,8);BODY}
            """.replace("BODY", last)
                ),
                -4,
            )

    def test_construction_state_contracts_and_deferred_producers(self):
        self.assertEqual(
            self.program("""
            i32 log;
            struct Item {
              i32 value;
              Item() {log=log*10+9;}
              Item(i32 n){init value(n);log=log*10+n;}
              Item& operator=(const<Item>& other)=delete;
            };
            struct Box {
              i32 seed; Item a; Item mid; Item b; Item tail;
              Box(i32 n) {
                init seed(n);
                init mid(seed+1);
                init tail(seed+3);
                i32 ret(this->fill(n));
                if(ret!=42){log=0;}
              }
              [[initializes(a,b),requires_initialized(seed)]] i32 fill(i32 n) {
                a=Item(n);
                if(mid.value==2){b=Item(n+2);return 42;}
                b=Item(7);return 1;
              }
            };
            i32 main(){Box x(1);
              if(log==1234 && x.a.value==1 && x.b.value==3 && x.tail.value==4){return 42;}return 1;}
        """),
            42,
        )
        self.assertEqual(
            self.program("""
            struct Count{
              i32 a; i32 b;
              [[initializes(a)]] void one(i32 n){a=n;}
              [[initializes(a,b)]] void both(i32 n){one(n);b=n+1;}
              [[requires_initialized(a,b)]] i32 sum(){return a+b;}
              Count(i32 n){both(n);if(sum()!=41){b=0;}}
            };
            i32 main(){Count c(20);return c.sum()+1;}
        """),
            42,
        )

    def test_constructor_contract_control_flow_and_overloads(self):
        self.assertEqual(
            self.program("""
            union Choice {case A(i32 n);case B;};
            i32 resets; i32 drops;
            struct Cell {
              i32 n;
              Cell(){++resets;}
              Cell(i32 v){init n(v);}
              Cell& operator=(const<Cell>& o)=delete;
              ~Cell(){++drops;}
            };
            struct S{
              Cell a; Cell b; Cell c;
              [[initializes(a)]] void choose(i32 n){a=Cell(n);}
              [[initializes(b)]] void choose(bool n){b=Cell(n?2:4);}
              [[initializes(c)]] void last(i32 v){
                switch(v){case 2:{c=Cell(3);break;}default:{c=Cell(4);}}
              }
              S(Choice& q){
                match(q){case Choice::A(value n){choose(n);}
                         case Choice::B{choose(1);}}
                goto next; next: {bool flag(true); choose(flag);}
                last(b.n);
              }
            };
            i32 main(){Choice q(Choice::A(37));i32 n;
              {S s(q);n=s.a.n+s.b.n+s.c.n;}
              return resets==0 && drops==3 ? n : 1;}
        """),
            42,
        )
        self.assertEqual(
            self.program("""
          struct Retry {
            i32 x;
            [[initializes(x)]] void fill(i32 n) {
              again: {if(n==0){x=42;return;}--n;goto again;}
            }
            Retry(i32 n){fill(n);}
          }; i32 main(){Retry r(4);return r.x;}
        """),
            42,
        )
        for fragment in (
            "goto skip;x=1;skip:{return;}",
            "switch(n){case 1:{x=2;}default:{}}",
            "while(n>0){x=1;break;}",
        ):
            r = self.compile(
                "struct S{i32 x;[[initializes(x)]] void bad(i32 n){" + fragment + "}};",
                "--check",
            )
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("postcondition", r.stderr)

    def test_out_of_line_and_recursive_construction_contract(self):
        self.assertEqual(
            self.program("""
          struct Box {
            i32 a; i32 b;
            [[initializes(a)]] declare i32 fill(i32 n);
            Box(i32 n){init b(a+1);i32 value(fill(n));if(value!=b){b=0;}}
          };
          i32 Box::fill(i32 n){if(n>0){return fill(n-1);} a=41; return 42;}
          i32 main(){Box b(3);return b.b;}
        """),
            42,
        )

    def test_construction_contract_rejections(self):
        cases = [
            (
                "struct S{i32 a;[[initializes(a)]] void bad(bool yes){if(yes){a=1;}}};",
                "postcondition",
            ),
            (
                "struct S{i32 a;[[initializes(a)]] void bad(bool yes){if(yes){return;}a=1;}};",
                "postcondition",
            ),
            (
                "struct S{i32 a;[[initializes(a)]] void bad(){a=a+1;}};",
                "before initialization",
            ),
            (
                "struct S{i32 a;i32 b;[[initializes(a,b)]] void bad(){b=2;a=1;}};",
                "frontier",
            ),
            (
                "struct S{i32 a;[[initializes(a),requires_initialized(a)]] void f(){a=1;}};",
                "entry requirements",
            ),
            (
                "struct S{i32 a;[[initializes(x)]] void f(){a=1;}};",
                "unknown construction-state slot",
            ),
            (
                "struct S{i32 a;[[initializes(a)]] static void f(){}};",
                "instance method",
            ),
            ("[[initializes(x)]] void f(){}", "instance method"),
            (
                "struct S{i32 a;[[initializes(a)]] void f(){a=1;}};void g(){S s;s.f();}",
                "Pending",
            ),
            (
                "struct S{i32 a(4);S(){f();}[[initializes(a)]] void f(){a=1;}};",
                "Pending",
            ),
        ]
        for source, message in cases:
            with self.subTest(source=source):
                r = self.compile(source, "--check")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn(message, r.stderr)

    def test_construction_state_through_immutable_receiver_views(self):
        source = """
            i32 checkpoints;
            struct Part {
                i32 n;
                Part() { checkpoints = 9; }
                Part(i32 value) { init n(value); checkpoints = checkpoints * 10 + value; }
                Part& operator=(const<Part>& other) = delete;
            };
            struct Box {
                Part first; Part second;
                [[initializes(first)]] void fill(i32 n) { first = Part(n); }
                Box() {
                    init second(2);
                    const<Box*> view(this);
                    Box& self_ref(*view);
                    self_ref.fill(1);
                }
            };
            struct ByReference {
                Part item;
                ByReference(){ByReference& view(*this);view.item=Part(3);}
            };
            i32 main(){Box box;ByReference other;
                return checkpoints==123 && box.first.n==1 && box.second.n==2 &&
                       other.item.n==3 ? 42 : 1;}
        """
        for mode in ("local", "interprocedural"):
            with self.subTest(mode=mode):
                self.assertEqual(
                    self.program(
                        "configuration {construction.analysis=" + mode + ";};" + source
                    ),
                    42,
                )

    def test_construction_state_rejects_inherited_reads_before_base_entry(self):
        base = """
          struct Parent {
            i32 seed;
            Parent(i32 n){init seed(n);}
            [[requires_initialized(seed)]] i32 read(){return seed;}
          };
        """
        for pending in ("seed", "read()"):
            with self.subTest(pending=pending):
                result = self.compile(
                    base
                    + "struct Child : Parent {Child(){init base<Parent>("
                    + pending
                    + ");}};",
                    "--check",
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("LIFE002", result.stderr)
        self.assertEqual(
            self.program(
                base
                + """
                struct Child : Parent { i32 value;
                    Child(){init base<Parent>(42);init value(read());}
                };
                i32 main(){Child item;return item.value;}
            """
            ),
            42,
        )

    def test_construction_state_uses_canonical_immutable_receiver_aliases(self):
        source = """
            i32 trace;
            struct Part {
                i32 number;
                Part(){trace=9;}
                Part(i32 n){init number(n);trace=trace*10+n;}
                Part& operator=(const<Part>& other)=delete;
            };
            namespace example {
                struct Box {
                    Part first; Part second;
                    [[initializes(first)]] void fill(i32 n){first=Part(n);}
                    Box(bool choose){
                        init second(2);
                        alias Handle=const<Box*>;
                        Handle view(choose?this:&*this);
                        (*view).fill(1);
                    }
                };
                struct Direct {
                    Part first;
                    Direct(){(*this).first=Part(3);}
                };
                struct Inferred {
                    Part first;
                    Inferred(){const auto view(this);view->first=Part(4);}
                };
            }
            i32 main(){
                example::Box box(false);example::Direct direct;
                example::Inferred inferred;
                return trace==1234&&box.second.number==2&&direct.first.number==3&&
                    inferred.first.number==4?42:1;
            }
        """
        for mode in ("local", "interprocedural"):
            with self.subTest(mode=mode):
                self.assertEqual(
                    self.program(
                        "configuration {construction.analysis=" + mode + ";};" + source
                    ),
                    42,
                )
        shadowed = self.compile(
            """
            struct Box {
                i32 field;
                Box(){const<Box*> view(this);{alias view=i32;view->field=1;}field=42;}
            };
        """,
            "--check",
        )
        self.assertEqual(shadowed.returncode, 1)
        self.assertIn("type alias", shadowed.stderr)

    def test_construction_state_admits_only_valid_borrowed_call_arguments(self):
        prefix = """
            declare struct Box;
            declare i32 read_field(const<Box>* view);
            alias Reader=function<i32(const<Box>* view)>*;
        """
        for ctor in (
            "Box(){init value(read_field(this));}",
            "Box(Reader read){init value(read(this));}",
        ):
            with self.subTest(ctor=ctor):
                result = self.compile(
                    prefix + "struct Box{i32 value;" + ctor + "};"
                    "i32 read_field(const<Box>* view){return view->value;}",
                    "--check",
                )
                self.assertEqual(result.returncode, 1)
                self.assertIn("LIFE002", result.stderr)
        self.assertEqual(
            self.program("""
                declare struct Base;
                [[effects(read(view))]] declare i32 read_base(const<Base>* view);
                struct Base{i32 seed;Base(i32 n){init seed(n);}};
                [[effects(read(view))]] i32 read_base(const<Base>* view){return view->seed;}
                declare struct Box;
                [[effects(none)]] declare i32 inert(const<Box>* view);
                [[effects(read(source))]] declare i32 read_other(const<Box>* view,const<i32>& source);
                alias Inert=function<i32(const<Box>* view) [[effects(none)]]>*;
                struct Box:Base {
                    i32 value; i32 tail;
                    Box(Inert make){
                        init base<Base>(make(this));
                        init value(read_base(this));
                        init tail(read_other(this,value));
                    }
                };
                [[effects(none)]] i32 inert(const<Box>* view){return 42;}
                [[effects(read(source))]] i32 read_other(const<Box>* view,const<i32>& source){return source;}
                i32 main(){Box value(&inert);return value.tail;}
            """),
            42,
        )
        pending_base = self.compile(
            """
            struct Base{i32 seed;Base(i32 n){init seed(n);}};
            [[effects(read(view))]] i32 read_base(const<Base>* view){return view->seed;}
            struct Box:Base{Box(){init base<Base>(read_base(this));}};
        """,
            "--check",
        )
        self.assertEqual(pending_base.returncode, 1)
        self.assertIn("LIFE002", pending_base.stderr)

    def test_construction_checks_exact_returned_pointer_aliases(self):
        source = """
            declare struct Box;
            [[effects(read(view))]] declare i32 read_box(const<Box>* view);
            [[effects(none),returns_borrowed_from(ptr)]]
            Box* identity(Box* ptr){return ptr;}
            struct Box {
                i32 field;
                i32 result;
                Box(){ CTOR }
            };
            [[effects(read(view))]] i32 read_box(const<Box>* view){return view->field;}
            i32 main(){Box box;return box.result;}
        """
        pending = self.compile(
            source.replace("CTOR", "init field(read_box(identity(this)));"),
            "--check",
        )
        self.assertEqual(pending.returncode, 1)
        self.assertIn("LIFE002", pending.stderr)
        for mode in ("local", "interprocedural"):
            with self.subTest(mode=mode):
                self.assertEqual(
                    self.program(
                        "configuration {construction.analysis="
                        + mode
                        + ";};"
                        + source.replace(
                            "CTOR",
                            "init field(42);init result(0);result=read_box(identity(this));",
                        )
                    ),
                    42,
                )

    def test_construction_checks_conditional_aliases_before_access(self):
        source = """
            declare struct Box;
            [[effects(read(view))]] declare i32 read_box(const<Box>* view);
            struct Box {
                i32 field;
                Box(i32 n){init field(n);}
                i32 read() const {return field;}
                Box(bool select_self, Box* other){init field(EXPRESSION);}
            };
            [[effects(read(view))]] i32 read_box(const<Box>* view) {
                return view->field;
            }
            i32 main(){Box alive(42);Box chosen(SELECT_SELF,&alive);return chosen.field;}
        """
        for expression in (
            "read_box(select_self?this:other)",
            "(select_self?this:other)->field",
            "(select_self?this:other)->read()",
        ):
            with self.subTest(expression=expression):
                program = source.replace("EXPRESSION", expression)
                good = program.replace("SELECT_SELF", "false")
                result = self.compile(good, "--check")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("LIFE003", result.stderr)
                self.assertEqual(self.program(good), 42)
                self.assertEqual(
                    self.program(program.replace("SELECT_SELF", "true")),
                    -signal.SIGILL,
                )

    def test_construction_checks_opaque_aliases_and_whole_value_copies(self):
        source = """
            declare struct Box;
            [[effects(none),returns_borrowed_from(self,other)]]
            Box* choose(bool use_self, Box* self, Box* other) {
                return use_self?self:other;
            }
            [[effects(read(view))]] declare i32 read_box(const<Box>* view);
            struct Box {
                i32 field;
                Box(i32 n){init field(n);}
                Box(bool use_self, Box* other){init field(EXPRESSION);}
            };
            [[effects(read(view))]] i32 read_box(const<Box>* view){return view->field;}
            i32 main(){Box alive(42);Box chosen(SELECT_SELF,&alive);return chosen.field;}
        """
        opaque = source.replace("EXPRESSION", "read_box(choose(use_self,this,other))")
        for preset in ("Debug", "Release"):
            with self.subTest(preset=preset):
                self.assertEqual(
                    self.program(
                        opaque.replace("SELECT_SELF", "false"), "--preset", preset
                    ),
                    42,
                )
        self.assertEqual(
            self.program(opaque.replace("SELECT_SELF", "true")), -signal.SIGILL
        )
        constant_alias = source.replace("EXPRESSION", "read_box(true?this:other)")
        result = self.compile(constant_alias.replace("SELECT_SELF", "false"), "--check")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("LIFE002", result.stderr)

        copied = self.compile(
            """
                declare struct Box;
                declare i32 consume(Box item);
                struct Box {
                    i32 field;
                    Box(){init field(consume(*this));}
                    Box(const<Box>& other)=default;
                };
                i32 consume(Box item){return item.field;}
            """,
            "--check",
        )
        self.assertEqual(copied.returncode, 1, copied.stderr)
        self.assertIn("LIFE002", copied.stderr)

    def test_construction_state_respects_closed_nonaccessing_call_contracts(self):
        source = """
            struct PureMethod {
                i32 number;
                [[effects(none)]] i32 constant_value() const {return 42;}
                PureMethod(){init number(constant_value());}
            };
            struct Item {
                i32 number;
                Item(){} Item(i32 n){init number(n);}
                Item& operator=(const<Item>& other)=delete;
            };
            declare struct Box;
            [[effects(none)]] declare void inert(Box* view);
            alias Observer=function<void(Box* view) [[effects(none)]]>*;
            struct Box {
                Item field;
                Box(Observer observe){inert(this);observe(this);field=Item(42);}
            };
            [[effects(none)]] void inert(Box* view){}
            struct LocalType {
                i32 number(42);
                LocalType(){
                    struct Holder{Holder(LocalType* view){}};
                    Holder keep(this);
                }
            };
            i32 main(){
                PureMethod method;Box value(&inert);LocalType local;
                return method.number==42&&value.field.number==42&&local.number==42?42:1;
            }
        """
        for mode in ("local", "interprocedural"):
            with self.subTest(mode=mode):
                self.assertEqual(
                    self.program(
                        "configuration {construction.analysis=" + mode + ";};" + source
                    ),
                    42,
                )
        for contract in ("requires(value>=0),effects(none)", "effects(read(this))"):
            with self.subTest(contract=contract):
                body = "return 42;" if "requires" in contract else "return value;"
                result = self.compile(
                    "struct Box{i32 value;[["
                    + contract
                    + "]] i32 helper() const{"
                    + body
                    + "}"
                    "Box(){init value(helper());}};",
                    "--check",
                )
                self.assertEqual(result.returncode, 1)
                self.assertIn("LIFE002", result.stderr)

    def test_canonical_const_type_construction_and_parameters(self):
        self.assertEqual(
            self.program("""
            alias Immutable=const<const<i32>>;alias Ref=i32&;
            declare i32 twice(i32 n);
            i32 twice(Immutable n){return n+n;}
            i32 drops;struct R {const<i32> v(20); ~R(){++drops;}};
            const<R> make(){return R();}
            const<i32> id(i32 n){return n;}
            i32 main(){R r;const<i32[2]> a(1,2); Immutable v(20);
              const<Ref> frozen(v); const<i32*> ptr(nullptr);
              {const<R[2]> arr; if(arr[0].v!=id(20)){return 1;}}
              if(make().v!=20){return 2;}
              if(drops!=3){return 3;}
              if(SameType<const<i32[2]>,const<i32>[2]> &&
                 SameType<const<Ref>,const<i32>&> &&
                 SameType<function<i32(Immutable)>,function<i32(i32)>> &&
                 sizeof(Immutable)==4 && ptr==nullptr && r.v==frozen){
                return twice(v)+a[1];}return 0;}
        """),
            42,
        )
        for source in [
            "void f(const<i32> n){++n;}",
            "alias I=const<i32>;void f(){I x;x=1;}",
            "void f(){const<i32[2]> a;a[0]=1;}",
            "struct R{const<i32> x;};void f(){R r;r.x=1;}",
            "void f(){i32 x;const<i32*> p(&x);p=nullptr;}",
        ]:
            with self.subTest(source=source):
                self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_out_of_line_members_of_applied_owners(self):
        self.assertEqual(
            self.program("""
          namespace lib {
            generic<type T,const usize N> struct Box {
              T[N] a;declare T get(usize index) const;
              declare Box(T first);
            };
            declare i32 early();
          }
          i32 lib::early(){lib::Box<i32,2> box(20);return box.get(0);}
          generic<type X,const usize K> X lib::Box<X,K>::get(usize pos) const {
            return a[pos];}
          generic<type X,const usize K> lib::Box<X,K>::Box(X n){a[0]=n;}
          i32 main(){lib::Box<i16,1> second(22);
            return lib::early()+i32(second.get(0));}
        """),
            42,
        )
        for source in (
            "generic<type T> struct B{declare T get();};"
            "generic<type X> X B<X>::other(){return X();}",
            "generic<type T> struct B{declare T get(T p);};"
            "generic<type X> X B<X>::get(X v){return v+v;}",
            "generic<type T> struct B{declare T get(T p);};"
            "generic<type X> X B<X>::get(X v(X())){return v;}",
            "generic<type T> struct B{declare T get() const;};"
            "generic<type X> X B<X>::get(){return X();}",
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_packed_nested_and_specialized_member_definitions(self):
        self.assertEqual(
            self.program("""
          i32 add(){return 0;}i32 add(i32 a,i32 b){return a+b;}
          generic<const i32... Ns> struct Values{declare i32 sum();};
          generic<const i32... Vs> i32 Values<Vs...>::sum(){return add(Vs...);}
          generic<type T> struct Outer{struct Inner{T n;declare T get() const;};};
          generic<type X> X Outer<X>::Inner::get() const{return n;}
          generic<type A,type B> struct Pair{declare i32 read();};
          generic<type X> specialize struct Pair<X,i32>{X n;declare X get();};
          specialize struct Pair<i32,i16>{declare i32 value();};
          generic<type Y> Y Pair<Y,i32>::get(){return n;}
          i32 Pair<i32,i16>::value(){return 7;}
          i32 main(){Values<4,6> v;Values<> z; Outer<i32>::Inner n(17);
            Pair<i32,i32> s(8);Pair<i32,i16> explicitPair;
            return v.sum()+z.sum()+n.get()+s.get()+explicitPair.value();}
        """),
            42,
        )
        for source in (
            "generic<type... Ts> struct P{declare i32 f();};generic<type... Us> i32 P<Us>::f(){return 0;}",
            "generic<type T> struct P{declare i32 f();};i32 P<i32>::f(){return 0;}",
            "generic<type T> struct P{struct I{declare T f();};};generic<type U> U P<U>::I::other(){return U();}",
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_compound_specialized_owner_patterns(self):
        self.assertEqual(
            self.program("""
            namespace lib {
                generic<const i32 A,const i32 B> struct Table {
                    i32 query(){return 1;}
                };
                generic<const i32 N> specialize struct Table<N+1,N> {
                    i32 offset;
                    declare i32 query() const;
                    generic<type T> struct Inner{T value;declare T get() const;};
                };
            }
            i32 early(){lib::Table<21,20> tab(2);return tab.query();}
            generic<const i32 Count> i32 lib::Table<(Count+0x1),Count>::query() const {
                return offset+Count;
            }
            generic<const i32 M,type U> (U) ::lib::Table<M+1,M>::Inner<U>::get() const {
                return value;
            }
            i32 main(){
                lib::Table<11,10>::Inner<i32> entry(19);
                lib::Table<22,20> ordinary;
                return early()+entry.get()+ordinary.query();
            }
            """),
            42,
        )
        result = self.compile(
            """
            generic<const i32 A,const i32 B> struct Grid{};
            generic<const i32 N> specialize struct Grid<N+1,N>{declare i32 get();};
            generic<const i32 M> i32 Grid<M+2,M>::get(){return M;}
            """,
            "--check",
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("declared family or specialization", result.stderr)

    def test_nested_pack_patterns_and_array_extent_deduction(self):
        self.assertEqual(
            self.program("""
            generic<type... Ts> struct Types{};
            generic<type T> struct Box{};
            generic<const i32... Ns> struct Values{};
            i32 add(){return 0;}
            i32 add(i32 a,i32 b){return a+b;}
            i32 bytes(){return 0;}
            i32 bytes(usize a,usize b){
                return a==4 && b==8 ? 12 : a==2 && b==4 ? 6 : 0;
            }
            generic<type... Ts> i32 widths(const<Box<Types<Ts...>>>& box) {
                return bytes(sizeof(Ts)...);
            }
            generic<const i32... Ns>
            i32 shifted(const<Values<(Ns+1)...>>& shifted,
                        const<Values<Ns...>>& basis) {
                return add(Ns...);
            }
            generic<type T,const usize N> i32 extent(T[N]& array) {
                return i32(N);
            }
            generic<type... Ts> Types<Ts...> make(Ts... args) {
                return Types<Ts...>();
            }
            generic<type... Ts> i32 paired(const<Types<Ts...>>& t,Ts... args) {
                return bytes(sizeof(Ts)...);
            }
            i32 main(){
                Box<Types<i32,i64>> sized;
                Box<Types<>> empty;
                Values<11,13> adjusted;
                Values<10,12> basis;
                i32[2] number(23,31);
                auto types(make(i16(2),i32(9)));
                return widths(sized)+widths(empty)+shifted(adjusted,basis)
                       +extent(number)+paired(types,i16(2),i32(9));
            }
            """),
            42,
        )
        for left, right, diagnostic in (
            ("i32", "i32,i16", "conflicting deduced pack lengths"),
            ("i32,i16", "i32,i64", "conflicting deduction"),
        ):
            with self.subTest(left=left, right=right):
                result = self.compile(
                    f"""
                    generic<type... Ts> struct Types{{}};
                    generic<type... Ts> i32 same(const<Types<Ts...>>& a,
                                                  const<Types<Ts...>>& b)
                        {{return 42;}}
                    i32 main(){{Types<{left}> x;Types<{right}> y;return same(x,y);}}
                    """,
                    "--check",
                )
                self.assertEqual(result.returncode, 1)
                self.assertIn(diagnostic, result.stderr)

    def test_specializations_of_packed_and_nested_family_shapes(self):
        self.assertEqual(
            self.program("""
            i32 bytes(usize a,usize b){return a==2 && b==4?6:12;}
            generic<type... Ts> struct Row{};
            specialize struct Row<>{i32 result(){return 5;}};
            generic<type... Ts> specialize struct Row<i32,Ts...> {
                declare i32 result() const;
            };
            generic<type... Items> i32 Row<i32,Items...>::result() const {
                return bytes(sizeof(Items)...);
            }
            generic<type T> struct Outer{i32 result(){return 19;}};
            generic<type... Tail> specialize struct Outer<Row<i8,Tail...>> {
                i32 result(){return bytes(sizeof(Tail)...);}
            };
            i32 main(){
                Row<> empty;
                Row<i32,i16,i32> packed;
                Outer<Row<i8,i32,i64>> fitted;
                Outer<Row<i16,i32>> plain;
                return empty.result()+packed.result()+fitted.result()+plain.result();
            }
            """),
            42,
        )

    def test_callable_type_pack_deduction_and_contract_positions(self):
        self.assertEqual(
            self.program("""
            [[noescape(a,b,out), effects(read(a),read(b),read(out),write(out))]]
            i32 set(const<i32>& a,const<i16>& b,i32& out) noexcept {
                out=a==20 && b==22 ? 42 : 0;
                return out;
            }
            alias Writer=function<i32(const<i32>& a,const<i16>& b,i32& out)
                noexcept [[noescape(a,b,out),
                effects(read(a),read(b),read(out),write(out))]]>*;
            generic<type... Ts>
            i32 invoke(function<i32(const<Ts>&... args,i32& out) noexcept
                       [[noescape(args,out),effects(read(args),read(out),write(out))]]>*
                       writer,i32& out,const<Ts>&... values) {
                return writer(values...,out);
            }
            [[effects(none)]] i32 identity(i32 value) noexcept{return value;}
            [[effects(none)]] i32 zero() noexcept{return 0;}
            generic<type... Ts>
            i32 defaults(function<i32(Ts...) noexcept [[effects(none)]]>* fn) {
                return fn(Ts()...);
            }
            generic<type... Ts>
            i32 preferred(function<i32(Ts...) noexcept>* fn){return 1;}
            generic<type... Ts>
            i32 preferred(function<i32(i32,Ts...) noexcept>* fn){return 0;}
            i32 main(){
                i32 a(20);i16 b(22);i32 out;
                Writer writer(&set);
                function<i32(i32) noexcept [[effects(none)]]>* id(&identity);
                function<i32() noexcept [[effects(none)]]>* empty(&zero);
                return invoke(writer,out,a,b)+defaults(id)+defaults(empty)+preferred(id);
            }
            """),
            42,
        )
        result = self.compile(
            """
            i32 one(i32 x){return x;}
            i32 zero(){return 0;}
            generic<type... Ts> void same(function<i32(Ts...)>* a,
                                           function<i32(Ts...)>* b){}
            i32 main(){
                function<i32(i32)>* a(&one);
                function<i32()>* b(&zero);
                same(a,b); return 0;
            }
            """,
            "--check",
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("conflicting deduced pack lengths", result.stderr)
        result = self.compile(
            "generic<type T> i32 invalid(function<i32(T)>* f,i32 n){return f(n);}",
            "--check",
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn(
            "function pointer argument type is not established", result.stderr
        )

    def test_pack_deduction_through_applied_owner_scopes(self):
        self.assertEqual(
            self.program("""
            namespace lib {
                generic<type... Ts> struct Outer {
                    struct Item{};
                    generic<type U> struct Nested{};
                };
            }
            i32 sizes(usize a,usize b){return a==1 && b==2 ? 20 : 0;}
            generic<type... Ts>
            i32 score(const<lib::Outer<Ts...>::Item>& item) {
                return sizes(sizeof(Ts)...);
            }
            generic<type U,type... Ts>
            i32 nested(const<lib::Outer<Ts...>::Nested<U>>& item) {
                return sizeof(U)==4 ? sizes(sizeof(Ts)...)+2 : 0;
            }
            i32 main(){
                lib::Outer<i8,i16>::Item a;
                lib::Outer<i8,i16>::Nested<i32> b;
                return score(a)+nested(b);
            }
            """),
            42,
        )
        result = self.compile(
            """
            generic<type... Ts> struct Outer{struct Item{};};
            generic<type... Ts> struct Other{struct Item{};};
            generic<type... Ts> i32 take(const<Outer<Ts...>::Item>& item){return 1;}
            i32 main(){Other<i8>::Item n;return take(n);}
            """,
            "--check",
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("no viable overload", result.stderr)

    def test_nested_owner_packs_expand_in_their_own_scope(self):
        self.assertEqual(
            self.program("""
            generic<type... Ts> struct List{};
            generic<const i32... Ns> struct Values{};
            generic<type... Outer> struct Layer {
                generic<type... Inner> struct Nested {
                    alias Combined=List<Outer...,Inner...>;
                    generic<type... Args>
                    i32 call(function<i32(Args...)>* fn,Args... values) {
                        return fn(values...);
                    }
                };
            };
            generic<const i32... Outer> struct NumberLayer {
                generic<const i32... Inner> struct Nested {
                    alias Combined=Values<Outer...,Inner...>;
                };
            };
            i32 combine(i8 a,i16 b){return i32(a)+i32(b);}
            i32 main(){
                Layer<i32>::Nested<i8,i16> object;
                alias Types=Layer<i32>::Nested<i8,i16>::Combined;
                alias Numbers=NumberLayer<3>::Nested<5,8>::Combined;
                function<i32(i8,i16)>* fn(&combine);
                if constexpr(SameType<Types,List<i32,i8,i16>> &&
                             SameType<Numbers,Values<3,5,8>>) {
                    return object.call(fn,i8(20),i16(22));
                } else {return 1;}
            }
            """),
            42,
        )

    def test_coexpansion_of_captured_and_local_packs(self):
        declarations = """
            generic<type A,type B> struct Pair{};
            generic<type... Ts> struct Types{};
            generic<const i32... Ns> struct Values{};
            i32 add(i32 a,i32 b){return a+b;}
            generic<type... Outer> struct Layer {
                generic<type... Inner> struct Nested {
                    alias Zipped=Types<Pair<Outer,Inner>...>;
                };
            };
            generic<type... Outer> struct SeparateLayer {
                generic<type... Inner> struct Nested {
                    alias Separate=Types<Pair<Types<Outer...>,Inner>...>;
                };
            };
            generic<const i32... Outer> struct NumberLayer {
                generic<const i32... Inner> struct Nested {
                    alias Zipped=Values<(Outer+Inner)...>;
                    i32 sum() {return add((Outer+Inner)...);}
                };
            };
        """
        self.assertEqual(
            self.program(
                declarations
                + """
            i32 main(){
                alias First=Layer<i8,i16>::Nested<i32,i64>::Zipped;
                alias Second=SeparateLayer<i8>::Nested<i32,i64>::Separate;
                alias Empty=Layer<>::Nested<>::Zipped;
                alias Numbers=NumberLayer<3,5>::Nested<14,20>::Zipped;
                NumberLayer<3,5>::Nested<14,20> nums;
                if constexpr(SameType<First,Types<Pair<i8,i32>,Pair<i16,i64>>>
                    && SameType<Second,Types<Pair<Types<i8>,i32>,
                                              Pair<Types<i8>,i64>>>
                    && SameType<Empty,Types<>>
                    && SameType<Numbers,Values<17,25>>) {
                    return nums.sum();
                } else {return 1;}
            }
            """
            ),
            42,
        )
        for type_name in (
            "Layer<i8>::Nested<i32,i64>",
            "NumberLayer<3,5>::Nested<14>",
        ):
            with self.subTest(type_name=type_name):
                result = self.compile(
                    declarations + f"i32 main(){{{type_name} value;return 0;}}",
                    "--check",
                )
                self.assertEqual(result.returncode, 1)
                self.assertIn(
                    "packs expanded together have different lengths", result.stderr
                )

    def test_symbolic_computed_specialization_ordering(self):
        self.assertEqual(
            self.program("""
            generic<const i32 A,const i32 B> struct Table {
                i32 get(){return 0;}
            };
            generic<const i32 N> specialize struct Table<N+1,N> {
                i32 get(){return 1;}
            };
            generic<const i32 M> requires(M>0)
            specialize struct Table<M+0x1,M> {i32 get(){return 2;}};
            specialize struct Table<3,2>{i32 get(){return 40;}};
            i32 main(){Table<3,2> exact;Table<5,4> constrained;
                return exact.get()+constrained.get();}
            """),
            42,
        )
        result = self.compile(
            """
            generic<const i32 A,const i32 B> struct Table{};
            generic<const i32 N> specialize struct Table<N+0,N>{};
            generic<const i32 M> specialize struct Table<M,M+0>{};
            i32 main(){Table<2,2> tied;return 0;}
            """,
            "--check",
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("ambiguous type specialization", result.stderr)

    def test_qualified_definition_with_multiple_applied_owner_scopes(self):
        self.assertEqual(
            self.program("""
          generic<type T> struct Outer{
            generic<type U> struct Inner{T a;U b;declare U get(T arg) const;};
          };
          i32 early(){Outer<i16>::Inner<i32> item(2,20);return item.get(4);}
          generic<type A,type B> B Outer<A>::Inner<B>::get(A ignored) const{return b;}
          i32 main(){Outer<i32>::Inner<i16> item(1,22);return early()+i32(item.get(2));}
        """),
            42,
        )
        for definition in (
            "generic<type A,type B> B Outer<B>::Inner<A>::get(A ignored) const{return b;}",
            "generic<type A> A Outer<A>::Inner::get(A ignored) const{return b;}",
        ):
            with self.subTest(definition=definition):
                source = (
                    "generic<type T> struct Outer{generic<type U> struct Inner{T a;U b;declare U get(T arg) const;};};"
                    + definition
                )
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_out_of_line_generic_members_keep_owner_and_member_bindings(self):
        self.assertEqual(
            self.program("""
            namespace library {
                generic<type T> struct Outer {
                    generic<type U> struct Box {
                    private:
                        T first;
                        U second;
                    public:
                        Box(T a, U b) { init first(a); init second(b); }
                        generic<type W>
                        requires(SameType<W,i32> && SameType<T,W> && SameType<U,W>)
                        declare W total(W bias) const;
                        generic<const i32 N>
                        declare static i32 offset(i32 n(N));
                    };
                };
            }
            alias Box=library::Outer<i32>::Box<i32>;
            i32 early(const<Box>& box){
                return box.total(3) + library::Outer<i32>::Box<i32>::offset<4>();
            }
            i32 between(i32 n){return n;}
            generic<type X,type Result,type Y>
            Result library::Outer<X>::Box<Y>::total(Result n) const {
                return between(first+second+n);
            }
            generic<const i32 Bias,type O,type I>
            i32 library::Outer<O>::Box<I>::offset(i32 arg){return arg+Bias;}
            i32 main(){Box box(11,20);return early(box);}
            """),
            42,
        )

    def test_out_of_line_generic_member_and_owner_packs_expand_separately(self):
        self.assertEqual(
            self.program("""
            i32 add(){return 0;}
            i32 add(i32 a,i32 b){return a+b;}
            generic<const i32... Ns> struct Values {
                generic<const i32 N> declare i32 total() const;
            };
            generic<const i32 Bias,const i32... Vs>
            i32 Values<Vs...>::total() const { return add(Vs...) + Bias; }

            generic<type T> struct Box {
                T first;
                generic<type... Ps> declare i32 sum(Ps... arguments) const;
            };
            generic<type Owner,type... Args>
            i32 Box<Owner>::sum(Args... values) const { return add(values...); }
            i32 main(){
                Values<5,6> full;
                Values<> empty;
                Box<i8> box;
                return full.total<2>() + empty.total<3>() + box.sum(7,19) + box.sum();
            }
            """),
            42,
        )

    def test_out_of_line_generic_members_reject_incompatible_definitions(self):
        declarations = """
            generic<type T> struct Box {
                generic<type U> requires(SameType<U,i32>) declare U get(U n) const;
                generic<type U> requires(SameType<U,i16>) declare U get(U n) const;
            };
        """
        for definition, diagnostic in (
            (
                "generic<type O,type F> F Box<O>::get(F n) const{return n;}",
                "member is ambiguous",
            ),
            (
                "generic<type O,type F> requires(SameType<F,i8>) F Box<O>::get(F n) const{return n;}",
                "previously declared family member",
            ),
            (
                "generic<type O,type F> requires(SameType<F,i32>) F Box<O>::get(F n(3)) const{return n;}",
                "defaults belong to the canonical declaration",
            ),
            (
                "generic<type O,type F> requires(SameType<F,i32>) F Box<O>::get(F n) const{return missing;}",
                "unknown name 'missing'",
            ),
        ):
            with self.subTest(diagnostic=diagnostic):
                result = self.compile(declarations + definition, "--check")
                self.assertEqual(result.returncode, 1)
                self.assertIn(diagnostic, result.stderr)

    def test_static_generic_members_through_qualified_type_aliases(self):
        declarations = """
            namespace library {
                generic<type T> struct Maker {
                    generic<const i32 N> static i32 value(){return N;}
                    generic<type U> static U copy(U source){return source;}
                };
                alias Default=Maker<i8>;
            }
            alias Pick=library::Default;
            alias Chain=(Pick);
            struct Alternative {
                generic<type U> static U value(U number){return number;}
            };
        """
        self.assertEqual(
            self.program(
                declarations
                + """
                i32 main(){
                    i32 first(Chain::value<8>());
                    {
                        alias Pick=Alternative;
                        first += Pick::value<i32>(10) + ::Pick::value<13>();
                    }
                    return first + Pick::copy<i32>(11);
                }
                """
            ),
            42,
        )
        for expression in ("Pick::value<i32>()", "Pick::copy<42>(11)"):
            with self.subTest(expression=expression):
                source = declarations + f"i32 main(){{return {expression};}}"
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_instance_generic_arguments_follow_the_typed_receiver(self):
        source = """
            struct Counts {
                generic<const i32 N> i32 take() const { return N; }
            };
            namespace lib {
                enum Tag:i32 { case Answer(7) };
                struct Arg { i32 n; };
                struct Tags {
                    generic<const Tag K> i32 take() const {
                        return K==Tag::Answer ? 7 : 0;
                    }
                };
                struct Types {
                    generic<type T> i32 take(const<T>& item) const {
                        return sizeof(T)==4 ? 3 : 0;
                    }
                };
            }
            struct Mixed { Counts count; lib::Types typed; };
            struct Plain { i32 take; };
            alias CountPtr=const<Counts>*;
            i32 select(const<Counts>& source, CountPtr ptr, const<lib::Tags>& tags){
                return source.take<9>() + ptr->take<10>() + tags.take<lib::Tag::Answer>();
            }
        """
        self.assertEqual(
            self.program(
                source
                + """
                i32 main(){
                    Mixed mixed;
                    Counts[2] items;
                    lib::Tags tags;
                    lib::Arg argument;
                    Plain plain(1);
                    if(plain.take < 2){
                        return select(mixed.count,&mixed.count,tags) +
                               mixed.typed.take<lib::Arg>(argument) + items[0].take<13>();
                    }
                    return 0;
                }
                """
            ),
            42,
        )
        for expression in (
            "mixed.count.take<lib::Arg>()",
            "mixed.typed.take<13>(argument)",
        ):
            with self.subTest(expression=expression):
                invalid = (
                    source
                    + f"i32 main(){{Mixed mixed;lib::Arg argument;return {expression};}}"
                )
                self.assertEqual(self.compile(invalid, "--check").returncode, 1)

    def test_deferred_generic_member_arguments_follow_the_bound_owner(self):
        source = """
            enum Tag:i32 {case Answer(11)};
            constraint Selectable<type T> {
                expression(T& item){item.take<Tag::Answer>() -> i32;}
            };
            generic<type T> requires(Selectable<T>) i32 through(T& item) {
                return item.take<Tag::Answer>();
            }
            struct Values {
                generic<const Tag K> i32 take() const {
                    return K==Tag::Answer ? 11 : 0;
                }
            };
            struct Types {
                generic<type T> i32 take(const<T>& item) const {
                    return sizeof(T)==4 ? 9 : 0;
                }
            };
            struct Inherited:Values {};
            Values make_values(){return Values();}
        """
        self.assertEqual(
            self.program(
                source
                + """
                i32 main(){
                    auto inferred(make_values());
                    auto types(Types());
                    Inherited inherited;
                    i32 number(0);
                    return inferred.take<Tag::Answer>() +
                           types.take<decltype(i32(0))>(number) +
                           inherited.take<Tag::Answer>() + through(inferred);
                }
                """
            ),
            42,
        )
        for expression, diagnosis in (
            ("types.take<13>(number)", "expected a type argument"),
            ("inherited.take<const<i32>>()", "expected a constant argument"),
        ):
            with self.subTest(expression=expression):
                result = self.compile(
                    source
                    + "i32 main(){auto types(Types());Inherited inherited;i32 number;"
                    + "return "
                    + expression
                    + ";}",
                    "--check",
                )
                self.assertEqual(result.returncode, 1)
                self.assertIn(diagnosis, result.stderr)

    def test_calls_and_inferred_objects_bind_member_syntax_from_result_types(self):
        self.assertEqual(
            self.program("""
                struct Range {bool operator>(i32 n) const {return n==0;}};
                struct Less {Range operator<(i32 n) const {return Range();}};
                struct Holder {Less get;};
                struct Reader {generic<const i32 N> i32 get() const {return N;}};
                generic<type T> struct GenericHolder {Less get;};
                namespace lib {
                    Holder holder(){return Holder();}
                    Reader reader(){return Reader();}
                    Holder pick(i32 first,i32 second(0)){return Holder();}
                    Reader pick(){return Reader();}
                    Holder select(i32 value){return Holder();}
                    Reader select(bool value){return Reader();}
                    struct More {
                        Reader get_reader() const {return Reader();}
                        static Holder make(){return Holder();}
                        static Holder pick(i32 first,i32 second(0)){return Holder();}
                        static Reader pick(){return Reader();}
                    };
                    struct Inherited:Holder {};
                    struct GenericInherited:GenericHolder<i32> {};
                }
                i32 exercise(bool choose){
                    auto object(lib::holder());
                    lib::More more;
                    lib::Inherited inherited;
                    lib::GenericInherited generic_inherited;
                    alias Factory=function<Holder()>*;
                    Factory make(&lib::holder);
                    decltype(lib::holder()) other;
                    if (!(object.get < 1 > (0)) || !(lib::holder().get < 2 > (0)) ||
                        !(make().get < 3 > (0)) || !(inherited.get < 4 > (0)) ||
                        !((choose ? object : other).get < 5 > (0)) ||
                        !(generic_inherited.get < 6 > (0)) ||
                        !(lib::More::make().get < 7 > (0)) ||
                        !(lib::pick(0).get < 8 > (0)) ||
                        !(lib::More::pick(0).get < 9 > (0)) ||
                        !(lib::select(i32(0)).get < 10 > (0))) {return 0;}
                    return more.get_reader().get<11>() + lib::reader().get<10>() +
                           lib::pick().get<7>() + lib::More::pick().get<9>() +
                           lib::select(true).get<5>();
                }
                i32 main(){return exercise(true);}
            """),
            42,
        )

    def test_reference_and_receiver_overloads_bind_following_member_syntax(self):
        self.assertEqual(
            self.program("""
                struct Range {bool operator>(i32 n) const {return n==0;}};
                struct Less {Range operator<(i32 n) const {return Range();}};
                struct Relation {Less get;};
                struct Generic {generic<const i32 N> i32 get() const {return N;}};
                alias Count=i32;
                Relation pick(Count& value){return Relation();}
                Generic pick(const<Count>& value){return Generic();}
                Generic pick(Count&& value){return Generic();}
                Relation computation(i32 value){return Relation();}
                Generic computation(bool value){return Generic();}
                generic<type T> T& identity(T& value) [[returns_borrowed_from(value)]] {
                    return value;
                }
                struct Input {};
                Relation nominal(Input& value){return Relation();}
                Generic nominal(Input&& value){return Generic();}
                Relation pointer(Input* value){return Relation();}
                Generic pointer(bool value){return Generic();}
                Relation scalar_pointer(i32* value){return Relation();}
                Generic scalar_pointer(bool* value){return Generic();}
                struct Maker {
                    Relation read() & {return Relation();}
                    Generic read() const & {return Generic();}
                    Generic read() && {return Generic();}
                };
                i32 main(){
                    Count n; const Count fixed(0); Input input; bool checked(true);
                    Relation relation; Generic generic_value;
                    Maker maker; const Maker readonly;
                    Maker* mutable_ptr(&maker); const<Maker>* readonly_ptr(&readonly);
                    auto copy([n] i32(){return pick(n).get<4>();});
                    auto borrow([&n] bool(){return pick(n).get < 1 > (0);});
                    auto init_copy([captured(i32(0))] i32(){return pick(captured).get<5>();});
                    if (!(pick(n).get < 1 > (0)) || !(nominal(input).get < 2 > (0)) ||
                        !(maker.read().get < 3 > (0)) || !(mutable_ptr->read().get < 4 > (0)) ||
                        !(computation(n + 1).get < 5 > (0)) ||
                        !(computation(n == 0).get<1>() == 1) ||
                        !(identity(relation).get < 6 > (0)) ||
                        !(identity(generic_value).get<1>() == 1) ||
                        !(pointer(&input).get < 7 > (0)) ||
                        !(scalar_pointer(&n).get < 8 > (0)) ||
                        !(scalar_pointer(&checked).get<1>() == 1) ||
                        !borrow()) {return 0;}
                    return pick(fixed).get<3>() + pick(i32(0)).get<5>() +
                           pick(std::move(n)).get<7>() + nominal(Input()).get<2>() +
                           readonly.read().get<8>() + readonly_ptr->read().get<6>() +
                           std::move(maker).read().get<2>() + copy() + init_copy();
                }
            """),
            42,
        )

    def test_constrained_overload_results_bind_member_syntax(self):
        self.assertEqual(
            self.program("""
                struct Range { bool operator>(i32 n) const {return n==0;} };
                struct Less { Range operator<(i32 n) const {return Range();} };
                struct Relation { Less get; };
                struct Generic { generic<const i32 N> i32 get() const {return N;} };
                namespace number {
                    alias Wide=i32;
                    constraint Integer<type A> { requires(SameType<A,Wide>); };
                    constraint Toggle<type A,const bool Enabled> {
                        requires(Enabled);
                        requires(Integer<A>);
                    };
                    generic<type A> requires(Toggle<A,true>) Relation choose(const<A>& a) {
                        return Relation();
                    }
                    generic<type A> requires(!Toggle<A,true>) Generic choose(const<A>& a) {
                        return Generic();
                    }
                    generic<type A,const bool Flag> requires(Flag && SameType<A,Wide>)
                    Relation direct(A a){return Relation();}
                    generic<type A,const bool Flag> requires(!Flag || !SameType<A,Wide>)
                    Generic direct(A a){return Generic();}
                    generic<type A> requires(Integer<A> || SameType<A,bool>)
                    Generic ranked(A a){return Generic();}
                    generic<type B> requires(Integer<B> && ObjectType<B>)
                    Relation ranked(B a){return Relation();}
                }
                generic<type T> requires(
                    (SameType<T,bool> && 1/0==0) || SameType<T,i32>)
                Relation protected_division(T arg){return Relation();}
                generic<type T> requires(!SameType<T,i32>)
                Generic protected_division(T arg){return Generic();}
                i32 main(){
                    const number::Wide value(0);
                    if (!(number::choose(value).get < 1 > (0)) ||
                        !(number::direct<i32,true>(0).get < 2 > (0)) ||
                        !(protected_division(i32(0)).get < 3 > (0)) ||
                        !(number::ranked(i32(0)).get < 4 > (0))) {return 0;}
                    return number::choose(true).get<24>() +
                           number::direct<i32,false>(0).get<11>() +
                           number::ranked(true).get<7>();
                }
            """),
            42,
        )
        bad = self.compile(
            "generic<type T> requires(SameType<T,bool> && 1/0==0) i32 f(T x){return 1;}"
            "generic<type T> requires(SameType<T,i32>) i32 f(T x){return 2;}"
            "i32 main(){return f(true);}",
            "--check",
        )
        self.assertEqual(bad.returncode, 1, bad.stderr)
        self.assertIn("division by zero", bad.stderr)

    def test_free_overloads_bind_type_and_constant_template_arguments(self):
        self.assertEqual(
            self.program("""
                generic<type T> i32 size_or_value(){return i32(sizeof(T));}
                generic<const i32 N> i32 size_or_value(){return N;}
                namespace lib {
                    alias Wide=i64;
                    generic<const i32 N> i32 size_or_value(){return N;}
                    generic<type T> i32 size_or_value(){return i32(sizeof(T));}
                }
                i32 main(){
                    return size_or_value<i32>() + size_or_value<10>() +
                           lib::size_or_value<lib::Wide>() + lib::size_or_value<20>();
                }
            """),
            42,
        )

    def test_consteval_constraints_confirm_relational_member_binding(self):
        source = """
            struct Range {bool operator>(i32 v) const {return v==0;}};
            struct Less {Range operator<(i32 v) const {return Range();}};
            struct Relation {Less get;};
            struct Generic {generic<const i32 N> i32 get() const {return N;}};
            consteval bool odd(i32 x) {return x%2!=0;}
            consteval bool odd(i64 x) {return x%3==0;}
            generic<const i32 N> requires(!odd(N)) Relation choose(){return Relation();}
            generic<const i32 N> requires(odd(N)) Generic choose(){return Generic();}
            generic<type T> bool from_generic(T argument){
                return choose<6>().get < 3 > (0);
            }
            i32 main(){
                auto selected(choose<4>());
                if (!(choose<2>().get < 1 > (0)) || !(selected.get < 2 > (0)) ||
                    !from_generic(i32(0))) {return 0;}
                return choose<3>().get<42>();
            }
        """
        checked = self.compile(source, "--check")
        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.assertEqual(checked.stderr.count("chained relational comparison"), 3)
        self.assertEqual(self.program(source), 42)

    def test_generic_definition_facts_bind_member_syntax_across_instantiations(self):
        declarations = """
            struct Range {bool operator>(i32 v) const {return v==0;}};
            struct Less {Range operator<(i32 v) const {return Range();}};
            struct Relation {Less get;};
            struct Generic {generic<const i32 N> i32 get() const {return N;}};
            consteval bool odd(i32 x) {return x%2!=0;}
            consteval bool odd(i64 x) {return x%3==0;}
            generic<const i32 N> requires(!odd(N)) Relation choose(){return Relation();}
            generic<const i32 N> requires(odd(N)) Generic choose(){return Generic();}
        """
        self.assertEqual(
            self.program(
                declarations
                + """
                namespace proof {
                    alias Number=i32;
                    constraint Even<const Number Value> {requires(!::odd(Value));};
                }
                generic<const i32 Input> requires(proof::Even<Input>)
                bool declared(){return ::choose<Input>().get < 1 > (0);}
                constraint IsRelation<type X> {requires(SameType<Relation,X>);};
                generic<type T> requires(IsRelation<T>) bool known_type(T& value,T* ptr){
                    return (value.get < 3 > (0)) && (ptr->get < 4 > (0));
                }
                generic<type T,type U> requires(SameType<T,U> && IsRelation<U>)
                bool known_type_chain(T& value,U& other){return value.get < 8 > (0);}
                generic<const i32 N> requires(N%2==0) Relation arithmetic(){return Relation();}
                generic<const i32 N> requires(!(N%2==0)) Generic arithmetic(){return Generic();}
                generic<const i32 N> requires(N%2==0) bool known_parity(){
                    return arithmetic<N>().get < 5 > (0);
                }
                generic<const i32 N> requires(!odd(N+2)) bool known_argument(){
                    return choose<N+2>().get < 6 > (0);
                }
                consteval bool positive(i64 value){return value > 0;}
                constraint Filter<const i32 N>{
                    requires(((~N >> 1)&1)==0);
                    requires(positive(N));
                };
                generic<const i32 N> requires(((~N >> 1)&1)==0) Relation bits(){
                    return Relation();
                }
                generic<const i32 N>
                requires(!(((~N >> 1)&1)==0) && positive(N)) Generic bits(){
                    return Generic();
                }
                generic<const i32 N> requires(Filter<N>) bool known_bits(){
                    return bits<N>().get < 9 > (0);
                }
                struct Witness {i32 item;};
                constraint HasItem<type T>{expression(T& x){x.item -> i32&;}};
                generic<type T> requires(HasItem<T>) Relation by_field(T& x){return Relation();}
                generic<type T> requires(!HasItem<T>) Generic by_field(T& x){return Generic();}
                generic<type U> requires(HasItem<U>) bool known_requirement(U& x){
                    return by_field(x).get < 7 > (0);
                }
                generic<const i32 A> i32 guarded(){
                    if constexpr (::odd(A)) {
                        return choose<A>().get<21>();
                    } else {
                        return choose<A>().get < 2 > (0) ? 21 : 0;
                    }
                }
                i32 main(){
                    Relation object; Witness witness;
                    if(!known_type(object,&object) || !known_type_chain(object,object)){return 2;}
                    if(!known_parity<2>() || !known_argument<4>()){return 3;}
                    if(!known_bits<2>() || !known_bits<6>()){return 5;}
                    if(!known_requirement(witness)){return 4;}
                    if(!declared<2>() || !declared<8>()){return 1;}
                    return guarded<4>()+guarded<5>();
                }
            """
            ),
            42,
        )
        different = self.compile(
            declarations
            + """
            namespace other {
                consteval bool odd(i32 x) {return x%3==0;}
                generic<const i32 A> requires(!odd(A))
                bool use(){return ::choose<A>().get < 1 > (0);}
            }
            i32 main(){return other::use<2>() ? 42 : 0;}
        """,
            "--check",
        )
        self.assertEqual(different.returncode, 1, different.stderr)
        disjunction = self.compile(
            declarations
            + """
            consteval bool positive(i64 value){return value>0;}
            generic<const i32 A> requires(!odd(A) || positive(A))
            bool use(){return choose<A>().get < 1 > (0);}
            i32 main(){return use<3>() ? 42 : 0;}
            """,
            "--check",
        )
        self.assertEqual(disjunction.returncode, 1, disjunction.stderr)
        different_policy = self.compile(
            declarations
            + """
            configured(numeric.integer.overflow=wrapping)
            generic<const i8 N> requires(N+1>0) Relation limit(){return Relation();}
            configured(numeric.integer.overflow=wrapping)
            generic<const i8 N> requires(!(N+1>0)) Generic limit(){return Generic();}
            configured(numeric.integer.overflow=saturating)
            generic<const i8 N> requires(N+1>0) bool use(){
                return limit<N>().get < 1 > (0);
            }
            i32 main(){return use<1>() ? 42 : 0;}
        """,
            "--check",
        )
        self.assertEqual(different_policy.returncode, 1, different_policy.stderr)

    def test_candidate_result_types_can_agree_on_member_syntax(self):
        self.assertEqual(
            self.program("""
                struct Range {bool operator>(i32 n) const {return n==0;}};
                struct Less {Range operator<(i32 n) const {return Range();}};
                struct A {Less get;}; struct B {Less get;};
                struct First {A box;}; struct Second {B box;};
                struct G1 {generic<const i32 N> i32 get() const {return N;}};
                struct G2 {generic<const i32 N> i32 get() const {return N+1;}};
                consteval bool odd(i32 n){return n%2!=0;}
                generic<const i32 N> requires(!odd(N)) First boxes(){return First();}
                generic<const i32 N> requires(odd(N)) Second boxes(){return Second();}
                generic<const i32 N> requires(!odd(N)) G1 family(){return G1();}
                generic<const i32 N> requires(odd(N)) G2 family(){return G2();}
                generic<const i32 N> i32 use(){
                    auto value(boxes<N>());
                    if (!(value.box.get < 1 > (0))) {return 0;}
                    return family<N>().get<20>();
                }
                i32 main(){return use<2>()+use<3>()+1;}
            """),
            42,
        )

    def test_member_overload_argument_kinds_follow_caller_declarations(self):
        source = """
            enum Tag:i32 {case Answer(11)};
            generic<type A> struct Both {
                generic<type T> declare i32 get() const;
                generic<const i32 N> declare i32 get() const;
                generic<type T> static i32 choose(){return i32(sizeof(T));}
                generic<const Tag K> static i32 choose(){return K==Tag::Answer ? 11 : 0;}
            };
            generic<type Owner,type Item> i32 Both<Owner>::get() const {
                return i32(sizeof(Item));
            }
            generic<type Owner,const i32 Key> i32 Both<Owner>::get() const {
                return Key;
            }
            struct Range { bool operator>(i32 x) const {return x==0;} };
            struct Box { Range operator<(i32 x) const {return Range();} };
            struct Relation { Box get; };
            alias Applied=Both<i8>;
        """
        self.assertEqual(
            self.program(
                source
                + """
                i32 main(){
                    Applied both;
                    Relation relation;
                    if (relation.get < 1 > (0)) {
                        return both.get<i32>() + both.get<23>() +
                               Applied::choose<Tag>() + Applied::choose<Tag::Answer>();
                    }
                    return 0;
                }
                """
            ),
            42,
        )
        for expression in ("both.get<1 > 0>()", "both.get<i32,23>()", "both.get<>()"):
            with self.subTest(expression=expression):
                result = self.compile(
                    source + "i32 main(){Applied both;return " + expression + ";}",
                    "--check",
                )
                self.assertEqual(result.returncode, 1)

    def test_implicit_member_overloads_respect_lexical_value_shadowing(self):
        self.assertEqual(
            self.program("""
                generic<const i32 N> i32 global_value(){return N;}
                struct Range {bool operator>(i32 x) const {return x==0;}};
                struct Needle {Range operator<(i32 x) const {return Range();}};
                struct Both {
                    generic<type T> i32 get() const {return i32(sizeof(T));}
                    generic<const i32 N> i32 get() const {return N;}
                    i32 use() const {
                        {Needle get;if (!(get < 1 > (0))) {return 1;}}
                        return get<i32>()+get<37>()+global_value<1>();
                    }
                };
                i32 main(){Both both;return both.use();}
            """),
            42,
        )

    def test_complete_record_index_binds_forward_member_applications(self):
        self.assertEqual(
            self.program("""
                generic<type T> i32 needle(){return -1;}
                struct Range {bool operator>(i32 x) const {return x==0;}};
                struct Needle {Range operator<(i32 x) const {return Range();}};
                struct Both {
                    generic<type T> i32 get() const {return i32(sizeof(T));}
                    i32 use() const {
                        if (!(needle < 1 > (0))) {return 1;}
                        {Needle get;if (!(get < 1 > (0))) {return 2;}}
                        return get<i32>() + this->get<38>();
                    }
                    generic<const i32 N> i32 get() const {return N;}
                    Needle needle;
                };
                i32 main(){Both both;return both.use();}
            """),
            42,
        )

    def test_forward_field_receiver_selects_its_nested_record_schema(self):
        self.assertEqual(
            self.program("""
                struct Both {
                    i32 use() const {
                        Local local;
                        return child.get<i32>() + this->child.get<34>() + local.get<i32>();
                    }
                    struct Node {
                        generic<type T> i32 get() const {return i32(sizeof(T));}
                        generic<const i32 N> i32 get() const {return N;}
                    };
                    alias Local=Node;
                    Node child;
                };
                i32 main(){Both both;return both.use();}
            """),
            42,
        )

    def test_nested_type_family_binds_before_its_definition(self):
        self.assertEqual(
            self.program("""
                struct Owner {
                    Item<type_of> item(type_of n) const {return Item<type_of>(n);}
                    alias type_of=i32;
                    generic<type T> struct Item { T value; };
                };
                i32 main(){Owner owner;return owner.item(42).value;}
            """),
            42,
        )

    def test_nested_type_binds_in_earlier_field_and_payload_layout(self):
        self.assertEqual(
            self.program("""
                struct Outer {
                    Node stored;
                    struct Node { i32 n; };
                };
                union Response {
                    case Good(Payload value);
                    struct Payload { i32 n; };
                };
                i32 main(){
                    Outer outer(Outer::Node(12));
                    Response value(Response::Good(Response::Payload(30)));
                    match(value){
                        case Response::Good(ref found) {return outer.stored.n + found.n;}
                    }
                }
            """),
            42,
        )

    def test_record_aliases_bind_forward_dependencies_and_reject_cycles(self):
        self.assertEqual(
            self.program("""
                struct Box {
                    alias Payload=Box::Stored;
                    Payload field;
                    struct Stored { Number n; };
                    alias Number=Word;
                    alias Word=i32;
                };
                i32 main(){Box box(Box::Payload(42));return box.field.n;}
            """),
            42,
        )
        cycle = self.compile(
            "struct Box { alias First=Second; alias Second=Box::First; };",
            "--check",
        )
        self.assertEqual(cycle.returncode, 1)
        self.assertIn("cyclic nested type alias", cycle.stderr)
        chain = "".join(f"alias T{i}=T{i + 1};" for i in range(1024))
        self.assertEqual(
            self.program(
                "struct Box {"
                + chain
                + "alias T1024=i32; T0 field; };"
                + "i32 main(){Box box(42);return box.field;}"
            ),
            42,
        )

    def test_chained_relational_comparison_warns_unless_grouped(self):
        source = """
            struct Bound {i32 mark;};
            bool operator<(bool lower,const<Bound>& bound){
                return lower && bound.mark==42;
            }
            bool inside(const<Bound>& bound){return EXPRESSION;}
            i32 main(){Bound bound(42);return inside(bound) ? 42 : 1;}
        """
        for expression, warning in (
            ("1 < 2 < bound", True),
            ("(1 < 2) < bound", False),
        ):
            with self.subTest(expression=expression):
                program = source.replace("EXPRESSION", expression)
                result = self.compile(program, "--check")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(
                    "WARNING: chained relational comparison" in result.stderr,
                    warning,
                )
                self.assertEqual(self.program(program), 42)

    def test_never_paths_and_nullptr_object_representation(self):
        program = """
          never diverge(){for(;;){}}
          never stop_now(){return diverge();}
          alias F=function<never() >*;
          i32 choose(bool ok,F stop){return ok ? 40 : stop();}
          i32& choose_ref(bool ok,i32& n){return ok ? n : diverge();}
          struct Layout{nullptr_t n;u8 tag;};
          i32 main(){F f(&stop_now);i32 n(2);nullptr_t empty;auto value(nullptr);
            Layout v(empty,9);i32* p(value);nullptr_t[3] array;
            if(sizeof(v)!=2 || sizeof(nullptr)!=1 || sizeof(array)!=3 ||
               p!=nullptr || empty!=value || v.tag!=9){return 0;}
            return choose(true,f)+choose_ref(true,n);}
        """
        self.assertEqual(self.program(program), 42)
        for source in (
            "never f(){}",
            "never f(bool x){if(x){while(true){}}}",
            "never f(){return;}",
            "never f(){return 7;}",
            "never value;",
            "void f(void p){}",
            "bool f(){return nullptr==u8(0);}",
            "bool f(){return nullptr==false;}",
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_constant_aggregate_values_fields_and_array_extents(self):
        self.assertLess(
            self.program("""
          struct Holder{i32* p;};struct Data{i32[2] a;i32 after;};
          Data d;constexpr Holder saved(&d.a[0]);
          i32 main(){d.after=12;return *(saved.p+2);}
        """),
            0,
        )
        self.assertEqual(
            self.program("""
          constexpr i32[3] a(4,5,6);
          struct Pair{i32 x;i32 y(x+2);};
          struct Box{Pair p;i32[2] v;};
          constexpr Pair pair(a[1]);
          constexpr i32[2] a2(3,9);constexpr Box box(Pair(8),a2);
          constexpr i32 score(){Box b(Pair(8),a2);i32 ix(0);
            b.v[ix++]+=b.p.y;b.v[0]=b.v[0]+(b.v[1]=2);
            return ix+b.v[0]+b.v[1];}
          constexpr i32 altered(score());
          constexpr i32 n(pair.y+box.p.y+box.v[1]+a[0]);
          i32 main(){constexpr Pair local(10);return altered==18?n+local.y:0;}
        """),
            42,
        )
        for source in (
            "struct P{i32 x;};i32 n;constexpr P point(n);",
            "constexpr i32[1] bad(1,2);",
            "constexpr i32[1] a(3);constexpr i32 n(a[1]);",
            "struct P{i32 a(b);i32 b(2);};constexpr P p;",
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_constexpr_constructor_uses_canonical_plan(self):
        self.assertEqual(
            self.program("""
            struct Number {
                i32 first; i32 second(first + 2); i32 third;
                Number(i32 v, bool choose) {
                    init third(v + second);
                    if(choose) {first = v;} else {first = 1;}
                    this->third += 2;
                }
                Number(i32 v) {delegate(v,true);}
            };
            constexpr Number n(8);
            constexpr Number m(1,false) -> {third += 2;};
            i32 main(){Number runtime(8);return runtime.third == n.third ?
                n.first+n.second+n.third+m.first+m.second : 0;}
            """),
            42,
        )
        for source in (
            "i32 global; struct S{i32 n;S(i32 v){init n(v);global=v;}};constexpr S bad(2);",
            "i32 run(i32 v){return v;} struct S{i32 n;S(i32 x){init n(run(x));}};constexpr S bad(2);",
            "struct S{i32 a;i32 b;S(i32 n){init a(b);init b(n);}};constexpr S bad(3);",
            "struct S{i32 x;S(i32 n){init x(n);}};constexpr S bad(2)->{init x(3);};",
            "struct S{i32 n;S(i32 x){for(;;){}}};constexpr S bad(1);",
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_constexpr_call_targets_argument_order_and_reference_results(self):
        self.assertEqual(
            self.program("""
          constexpr i32 select(i32 a,i32 b){return a*10+b;}
          constexpr i32 select(bool a,bool b){return 7;}
          constexpr i32 via(function<i32(i32,i32)>* f,i32& n){return f(n,++n);}
          constexpr function<i32(i32,i32)>* fp(&select);
          [[returns_borrowed_from(n)]] constexpr i32& borrow(i32& n){return n;}
          constexpr i32 compute(){
            i32 n(1);i32 a(select(n,++n));i32 b(via(fp,n));
            i32& r(borrow(n));r+=4;return a+b+n;
          }
          constexpr i32 answer(compute());
          i32 main(){return compute()==answer?answer:0;}
        """),
            42,
        )
        for source in (
            'extern "C" i32 external(i32);constexpr function<i32(i32)>* p(&external);constexpr i32 n(p(1));',
            "constexpr function<i32(i32)>* p(nullptr);constexpr i32 n(p(1));",
            "constexpr i32& invalid(){i32 n(7);return n;}constexpr i32 n(invalid());",
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_constexpr_temporary_destruction_and_final_destination(self):
        declarations = """
          i32 calls;
          struct Guard {i32 value;~Guard(){if(value!=42){++calls;}}};
          constexpr i32 get(const<Guard>& g){return g.value;}
          constexpr Guard make(i32 n){return Guard(n);}
        """
        self.assertEqual(
            self.program(
                declarations
                + """
          constexpr i32 valid(){Guard(42);return get(make(42));}
          constexpr Guard staticGuard(make(1));
          constexpr i32 answer(valid());
          i32 main(){return calls==0 && staticGuard.value==1?answer:0;}
        """
            ),
            42,
        )
        for body in (
            "Guard(1);return 42;",
            "return get(Guard(1));",
            "if(get(Guard(1))==1){return 42;}return 0;",
            "Guard g(make(1));return 42;",
        ):
            with self.subTest(body=body):
                result = self.compile(
                    declarations
                    + "constexpr i32 invalid(){"
                    + body
                    + "}constexpr i32 bad(invalid());",
                    "--check",
                )
                self.assertEqual(result.returncode, 1)
                self.assertIn("writable local", result.stderr)

    def test_constexpr_goto_resumes_lexical_control(self):
        self.assertEqual(
            self.program("""
            constexpr i32 branch() {
                i32 n(0);
                goto warm;
                if(false) {warm: {n=1;}}
                goto tick;
                while(++n<40) {tick: {n+=20;}}
                return n-1;
            }
            constexpr i32 switches() {
                i32 n(0);
                outer: for(i32 i(0);i<10;++i) {
                    switch(i) {
                        case 0: {goto next;}
                        case 1: {next: {n+=20;continue outer;}}
                        case 2: {n+=2;break outer;}
                    }
                }
                return n;
            }
            constexpr i32 no_dispatch() {
                i32 n(1);
                goto chosen;
                switch(++n) {
                    case 0: {chosen: {n+=20;} fallthrough;}
                    default: {n+=21;break;}
                }
                return n;
            }
            constexpr i32 aliases() {
                i32 n;
                again: {if(n==42){goto done;}}
                alias Number=i32;
                n=Number(n+1);
                goto again;
                done: return Number(n);
            }
            constexpr i32 selected() {
                goto then;
                if constexpr(true) {then: {return 42;}}
                else {return 1;}
            }
            constexpr void fill(i32& n) {
                goto entered;
                if(false) {entered: {n=42;}}
            }
            constexpr i32 continuation() {
                i32 n;
                fill(n);
                return n;
            }
            constexpr i32 a(branch());
            constexpr i32 b(switches());
            constexpr i32 c(no_dispatch());
            constexpr i32 d(aliases());
            constexpr i32 e(selected());
            constexpr i32 f(continuation());
            i32 main(){
                return a==42 && b==42 && c==42 && d==42 && e==42
                       && f==42 && continuation()==42
                       && branch()==42 && switches()==42 && no_dispatch()==42
                       && aliases()==42 && selected()==42 ? 42 : 1;
            }
            """),
            42,
        )

    def test_constexpr_goto_checks_lifetimes_and_budget(self):
        declarations = """
            i32 invalid_cleanup;
            struct Item {
                i32 safe;
                ~Item(){if(safe==0){++invalid_cleanup;}}
            };
        """
        self.assertEqual(
            self.program(
                declarations
                + """
                constexpr i32 f(){
                    Item before(0);
                    i32 trips;
                    retry: {++trips;}
                    Item first(1);
                    {Item second(1);if(trips<2){goto retry;}}
                    before.safe=1;
                    return 42;
                }
                constexpr i32 answer(f());
                i32 main(){return invalid_cleanup==0?answer:1;}
            """
            ),
            42,
        )
        for source, diagnostic in (
            (
                declarations + "constexpr i32 f(){i32 n;retry:{++n;}Item out(n-1);"
                "if(n<2){goto retry;}return 42;} constexpr i32 bad(f());",
                "writable local",
            ),
            (
                "constexpr i32 f(){goto enter;for(i32 i(0);i<2;++i)"
                "{enter: {return 42;}}return 1;}",
                "unexecuted initializer",
            ),
            (
                "union U{case A;}; constexpr i32 f(){U u(U::A());goto enter;"
                "match(u){case U::A {enter: {return 42;}}}return 1;}",
                "unexecuted initializer",
            ),
            (
                "constexpr i32 f(){again: goto again;}constexpr i32 bad(f());",
                "constant evaluation step budget exhausted",
            ),
            (
                "struct Child{~Child(){}};"
                "struct Owner{Child c;~Owner(){goto skip;}cleanup{skip: {}}};",
                "goto crosses a destructor phase boundary",
            ),
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn(diagnostic, result.stderr)

    def test_constexpr_references_special_members_and_switch(self):
        self.assertEqual(
            self.program("""
          struct N {
            i32 n;
            N(const<N>& other){init n(other.n+1);}
            constexpr i32 add(i32 v){n+=v;return n;}
          };
          constexpr i32 bump(i32& n){return ++n;}
          constexpr i32 run(i32 n){
            N obj(n); N copy(obj);
            i32& field(copy.n);
            switch(n){case 8:{bump(field);fallthrough;}
              case 9:{copy.add(2);break;} default:{return 1;}}
            return 2*copy.n+2*obj.n+2;
          }
          constexpr i32 result(run(8));
          i32 main(){return run(8)==result?result:0;}
        """),
            42,
        )
        for source in (
            "struct X{~X(){i32 n(1);}};i32 global;struct Y{~Y(){global=1;}};"
            "constexpr i32 f(){Y[2] y;return 3;}constexpr i32 n(f());",
            'struct Y{~Y(){i32 n(4);}};extern "C" void effect();'
            "struct Z{Y y;~Z(){return;}cleanup{effect();}};"
            "constexpr i32 f(bool cond){if(cond){Z z;}return 1;}constexpr i32 n(f(true));",
            "constexpr void change(const<i32>& x){x=5;}constexpr i32 f(){i32 a(2);change(a);return a;}constexpr i32 n(f());",
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_constexpr_tagged_union_payloads_and_match(self):
        self.assertEqual(
            self.program("""
            struct Pair{i16 a; i32 b; Pair(const<Pair>& p)=default;};
            union U{default case Empty;case Small(i8 b);case PairOf(Pair p, i8 t);case Ptr(const<i32>* p);U(const<U>& v)=default;};
            constexpr i32 base(14);
            constexpr U pointer(U::Ptr(&base));
            constexpr U pair(U::PairOf(Pair(6,10),2));
            constexpr U empty;
            constexpr i32 sum(U v){
                match(v){case U::PairOf(ref p,value t){p.b+=t;return p.a+p.b;}
                    case U::Small(value b){return b;} case U::Empty{return 0;}
                    case U::Ptr(value p){return *p;}}
            }
            constexpr i32 a(sum(pair)+sum(empty)+sum(U::Small(10)));
            i32 main(){return a+sum(pointer);}
            """),
            42,
        )
        for source in (
            "union U{case A(i32 v);};constexpr U bad;",
            "union U{case A(i32 v);};constexpr U bad(U::A());",
            "union U{case A(i32 v);};constexpr U u(U::A(2));constexpr i32 f(){match(u){case U::A(ref n){n+=1;return n;}}}constexpr i32 bad(f());",
            "union U{case A;case B;};constexpr i32 f(){match(U::A()){case U::A{return 1;}}}constexpr i32 bad(f());",
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_static_reference_binding_and_symbolic_pointer_constants(self):
        self.assertEqual(
            self.program("""
          struct Pair{i32 unused; i32[3] a;};
          Pair box;constexpr i32 n(16);
          constexpr const<i32>* c(&n);constexpr i32 value(*c);
          constexpr i32* begin(&box.a[0]);constexpr i32* mid(begin+1);
          constexpr isize distance(mid-begin);
          constexpr i32& ref(box.a[1]);
          i32 picks; i32& pick(){++picks;return box.a[2];} i32& selected(pick());
          i32 main(){*mid=20;selected=5;
            constexpr i32* last(&box.a[2]);
            return value+ref+*last+i32(distance)*picks;}
        """),
            42,
        )
        self.assertLess(
            self.program("""
          i32 item(42);i32& old(item);i32 main(){auto s(storage_of(item));
            destroy(item);construct_at<i32>(s,12);return old;}
        """),
            0,
        )
        self.assertLess(
            self.program("""
          i32[2] a;constexpr i32* p(&a[0]);
          i32 main(){auto s(storage_of(a[0]));destroy(a[0]);
            construct_at<i32>(s,12);return *p;}
        """),
            0,
        )
        for src in [
            "i32 main(){i32 n(7);constexpr i32* p(&n);return 0;}",
            "i32 main(){i32 n(7);constexpr i32& ref(n);return 0;}",
            "i32[2] a;constexpr i32* invalid(&a[0]+3);",
            "constexpr i32 i(7);constexpr const<i32>* end(&i+1);constexpr i32 n(*end);",
            "i32 x(3);constexpr i32* p(&x);constexpr i32 bad(*p);",
        ]:
            with self.subTest(src=src):
                result = self.compile(src, "--check")
                self.assertEqual(result.returncode, 1, result.stderr)

    def test_capture_preserves_element_lifetime_and_extent(self):
        self.assertLess(
            self.program("""
          struct D{i32[2] a;i32 next;};
          i32 main(){D d;auto p(&d.a[0]);
            auto call([p] i32(){return *(p+2);});return call();}
        """),
            0,
        )
        self.assertLess(
            self.program("""
          i32 main(){i32 n(3);i32& r(n);auto read([&r] i32(){return r;});
            auto cap(storage_of(n));destroy(n);construct_at<i32>(cap,17);
            return read();}
        """),
            0,
        )

    def test_pointer_fields_preserve_array_bounds_and_generations(self):
        types = """
          struct Data{i32[2] a; i32 next;};
          struct Handle{i32* p;Handle(const<Handle>& h)=default;
             Handle& operator=(const<Handle>& h)=default;
             Handle& operator=(Handle&& h)=default;};
          struct Pair{i64 padding;Handle[2] h;Pair(const<Pair>& b)=default;};
          Handle saved;
          Handle copy(Handle h){return h;}
          i32 read(const<Handle>& h,isize i){return *(h.p+i);}
        """
        setup = """
          i32 main(){Data d;d.a[0]=10;d.a[1]=32;d.next=19;
            Handle first(&d.a[0]);Pair box;
            box.h[0]=copy(first);box.h[1].p=&d.a[1];
            saved=box.h[0];Pair other(box);"""
        self.assertEqual(
            self.program(types + setup + "return read(saved,1)+read(other.h[1],-1);}"),
            42,
        )
        for tail in (
            "return read(saved,2);",
            "return read(other.h[1],1);",
            "auto s(storage_of(d.a[0]));destroy(d.a[0]);"
            "construct_at<i32>(s,7);return *other.h[0].p;",
        ):
            with self.subTest(tail=tail):
                self.assertLess(self.program(types + setup + tail + "}"), 0)

    def test_consuming_parameter_position_and_indirect_lifetime(self):
        source = """
          alias Release=function<void(i32& arg) [[consumes(arg)]]>*;
          [[consumes(x)]] declare void end(i32& x);
          [[consumes(value)]] void end(i32& value){destroy(value);}
        """
        self.assertEqual(
            self.program(
                source
                + """
              i32 main(){i32 x(3);auto s(storage_of(x));Release release(&end);
                release(x);return *construct_at<i32>(s,42);}
            """
            ),
            42,
        )
        self.assertLess(
            self.program(
                source
                + """
              i32 main(){i32 x(3);Release release(&end);release(x);return x;}
            """
            ),
            0,
        )
        for extra in (
            "void test(){function<void(i32&)>* p(&end);}",
            "void keep(i32& value){} void test(){Release p(&keep);}",
            "[[consumes(unknown)]] void broken(i32& x){}",
            "[[consumes(x)]] declare void f(i32& x);void f(i32& x){}",
            "alias Bad=function<void(i32& x) [[consumes(y)]]>*;",
        ):
            with self.subTest(extra=extra):
                self.assertNotEqual(
                    self.compile(source + extra, "--check").returncode, 0
                )

    def test_aliases_in_borrow_contract_signatures(self):
        self.assertEqual(
            self.program("""
          alias Ref=i32&;
          [[returns_borrowed_from(x),noescape(x)]] Ref forward_ref(Ref x){return x;}
          alias F=function<Ref(Ref p) [[noescape(p),returns_borrowed_from(p)]]>*;
          i32 main(){i32 x(41);F f(&forward_ref);++f(x);return x;}
        """),
            42,
        )
        for source in [
            "alias I=i32; [[noescape(x)]] void f(I x){}",
            "alias I=i32;alias P=function<I(i32& x)[[returns_borrowed_from(x)]]>*;",
            "alias I=i32;alias P=function<void(I x)[[noescape(x)]]>*;",
        ]:
            self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_ordinary_names_and_lexical_type_aliases(self):
        self.assertEqual(
            self.program("""
          alias Number=i32;
          generic<type T> T copy(T x){alias Local=T;return Local(x);}
          i32 main(){Number n(39);alias Ptr=Number*;Ptr p(&n);
            {alias Number=i8;Number v(2);n+=v;}
            {alias Count=i32;auto get([] Count(){return Count(1);});n+=get();}
            return copy(*p);}
        """),
            42,
        )
        rejected = [
            "alias A=i32; alias A=i32;",
            "alias A=i32; i32 A;",
            "i32 f(){return 1;} struct f{};",
            "enum E:i32{case A(0),case A(1)};",
            "enum E:i32{case A(0)};enum E:i32{case B(1)};",
            "void f(){alias T=i32;i32 T;}",
            "void f(){i32 T;alias T=i32;}",
            "void f(){{alias T=i32;}T x;}",
            "i32 g(){return 42;} i32 f(){i32 g;return g();}",
        ]
        for source in rejected:
            with self.subTest(source=source):
                self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_parenthesized_type_and_expression_disambiguation(self):
        self.assertEqual(
            self.program("""
          alias T=i64; i32 calls;
          struct Small{i8 v;Small(i32 n){calls+=n;}};
          i32 size_value(i8 T){return sizeof(T)==1 && sizeof(::T)==8 ? 42 : 0;}
          i32 main(){((i32)) n(42);(i32)* p(&n);
            if(sizeof((i32(1)+1))!=4 || sizeof(Small(1))!=1 ||
               alignof(((i32)))!=4 || calls!=0 || (*p)!=42){return 1;}
            return size_value(1);}
        """),
            42,
        )

    def test_configured_widths_and_scope(self):
        self.assertEqual(
            self.program("""
          configuration { numeric.integer.widths=[0x20,0b1000,6_4]; };
          configured(numeric.integer.widths=[16,32]) i16 pair(i16 x){return x+x;}
          i32 main(){i8 n(39);usize pos(1);
            configured(numeric.integer.widths=[16,32]) i16 v(pair(1));
            if(pos==1 && v==2){return n+3;}return 0;}
        """),
            42,
        )
        cases = [
            (
                "configuration {numeric.integer.widths=[8,32,64];};"
                "i32 f(i8 a,u8 b){return a+b;}",
                "i16 is unavailable",
            ),
            (
                "configuration {numeric.integer.widths=[32];};void f(){::u8 a;}",
                "u8 is disabled",
            ),
            (
                "configuration {numeric.integer.widths=[32];};void f(){byte a;}",
                "u8 is disabled",
            ),
            (
                "configuration {numeric.float.formats=[f64];};void f(){::f32 a;}",
                "f32 is disabled",
            ),
            ("void f(){configured(numeric.integer.widths=[32]) {}}", "CFG001"),
            ("i32 f(){return configured(numeric.float.formats=[f32])(1);}", "CFG001"),
            ("configuration {source.identifiers=ascii;};", "CFG001"),
            ('configured(target="x86_64-linux-gnu") void f(){}', "CFG001"),
            (
                "configured(numeric.literal.integer_default=isize) i32 f(){return 0;}",
                "CFG001",
            ),
            (
                "configuration {numeric.integer.widths=[8,32];numeric.literal.integer_default=i16;};",
                "CFG002",
            ),
            ("configuration {numeric.integer.widths=[3 2];};", "expected"),
            ("configured() void f(){}", "CFG001"),
            (
                "void f(){i32 n;configured(numeric.integer.overflow=wrapping)n+=1;}",
                "parenthesized",
            ),
        ]
        for source, message in cases:
            with self.subTest(source=source):
                r = self.compile(source, "--check")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn(message, r.stderr)

    def test_member_defaults_retain_bound_numeric_policy(self):
        self.assertEqual(
            self.program("""
            i8 maximum(){return 127;}
            struct Generated {
              configured(numeric.integer.overflow=wrapping) i8 delta(maximum()+1);
            };
            configured(numeric.integer.overflow=saturating) struct Authored {
              i8 delta(maximum()+1);
              Authored(i32 unused) {}
            };
            i32 main(){Generated a; Authored b(42);
              if(a.delta == -128 && b.delta == 127){return 42;}return 0;}
        """),
            42,
        )
        r = self.compile(
            "configured(diagnostics.promote=[WARNING]) void f(){"
            "bool flag; if((flag=true)){} }",
            "--check",
        )
        self.assertEqual(r.returncode, 0, r.stderr)
        for source in (
            "void f(){switch(1){case 1:{fallthrough xyz;}default:{}}}",
            "void f(){goto;}",
        ):
            self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_configured_diagnostic_threshold_and_artifact(self):
        config = self.dir / "cpn.config"
        config.write_text(
            "configuration {compilation.modules=false;compilation.separate=false;"
            'tooling.contract_export=false;source.unicode_version="17.0.0";};',
            encoding="utf-8",
        )
        body = "bool x; if(x=true){}"
        for level, emitted in [
            ("INFO", True),
            ("WARNING", True),
            ("ANOMALY", False),
            ("ERROR", False),
            ("none", False),
        ]:
            r = self.compile(
                "void f(){configured(diagnostics.minimum=" + level + "){" + body + "}}",
                "--config",
                str(config),
                "--check",
            )
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual("WARNING" in r.stderr, emitted)
        r = self.compile(
            "configured(diagnostics.minimum=none,diagnostics.promote=[WARNING])"
            "void f(){" + body + "}",
            "--check",
        )
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("ERROR", r.stderr)
        r = self.compile(
            "configured(diagnostics.minimum=none) i32 f(){return unknown;}", "--check"
        )
        self.assertNotEqual(r.returncode, 0)

    def test_decltype_uses_lexical_binding_and_preserves_category(self):
        self.assertEqual(
            self.program("""
            i32 calls; i32 next(){++calls;return 10;}
            struct S{i32 n;};generic<type T> struct Box{T value;};
            generic<type T> i32 query(T& v){
              decltype(v) ref(v);ref+=1;
              return SameType<decltype(std::move(v)),T&&> ? 1 : 0;
            }
            i32 main(){i32 v(40);const i32 c(0);S item(1);
              decltype(next()) result(0);Box<decltype(next())> box(0);
              decltype(item.n) field(item.n);++field;
              if(!SameType<decltype(c),const<i32>&> || field!=2 || calls!=0){return 1;}
              if(query(v)!=1 || calls!=0){return 2;}return v+1;
            }"""),
            42,
        )

    def test_effect_bounds_bind_canonical_callable_regions(self):
        self.assertEqual(
            self.program("""
            [[effects(read(source))]] declare i32 inspect(const<i32>& source);
            i32 inspect(const<i32>& item) [[effects(read(item))]] { return item; }
            alias Reader = function<i32(const<i32>& observed) [[effects(read(observed))]]>*;
            alias Broad = function<i32(const<i32>& observed) [[effects(read(any))]]>*;
            [[effects(none)]] i32 local(Reader read) {
                i32 object(42);
                return read(object);
            }
            i32 main() {
                Reader read(&inspect);
                Broad broad(read);
                i32 object(42);
                if (!SameType<Reader,decltype(&inspect)> || broad(object)!=42) {return 1;}
                return local(read);
            }
            """),
            42,
        )

    def test_effect_bounds_include_direct_calls_arguments_and_cleanup(self):
        self.assertEqual(
            self.program("""
            i32 trace(0);
            [[effects(write(global))]] void publish(i32 input){trace=input;}
            struct Guard {
                ~Guard() [[effects(write(global))]] {publish(42);}
            };
            [[effects(none)]] i32 identity(i32 input){return input;}
            [[effects(write(global))]] void run(){Guard local;identity(0);}
            i32 main(){run();return trace;}
            """),
            42,
        )
        for body in ("Guard local;", "identity(update());"):
            with self.subTest(body=body):
                result = self.compile(
                    """
                    i32 trace;
                    [[effects(write(global))]] i32 update(){trace=1;return 1;}
                    [[effects(none)]] i32 identity(i32 input){return input;}
                    struct Guard{~Guard() [[effects(write(global))]] {update();}};
                    [[effects(none)]] void run(){"""
                    + body
                    + "}",
                    "--check",
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("effect", result.stderr)

    def test_effect_bounds_track_selected_integer_failure_policy(self):
        self.assertEqual(
            self.program("""
            [[effects(trap(any))]] i32 checked_increment(i32 n){return n+1;}
            configured(numeric.integer.overflow=wrapping)
            [[effects(none)]] i32 wrapped_increment(i32 n){return n+1;}
            i32 main(){return checked_increment(wrapped_increment(40));}
            """),
            42,
        )
        result = self.compile(
            "[[effects(none)]] i32 unchecked_bound(i32 n){return n+1;}", "--check"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("effect", result.stderr)

    def test_effect_bounds_reject_invalid_regions_and_callable_substitution(self):
        cases = {
            "unknown parameter": "[[effects(read(missing))]] declare i32 f(i32& actual);",
            "receiver without instance": "[[effects(read(this))]] declare i32 f();",
            "noexcept contradiction": "[[effects(throw)]] declare void f() noexcept;",
            "mixed empty bound": "[[effects(none,io)]] declare void f();",
            "unknown trap kind": "[[effects(trap(memory))]] declare void f();",
            "write does not cover independent read": (
                "[[effects(write(x))]] i32 f(i32& x){return x;}"
            ),
            "wrong parameter region": (
                "[[effects(read(x))]] i32 f(i32& x,i32& y){return y;}"
            ),
            "unbounded target": (
                "i32 f(i32 x){return x;}void g(){"
                "function<i32(i32) [[effects(none)]]>* p(&f);}"
            ),
            "incompatible redeclaration": (
                "[[effects(read(x))]] declare i32 f(i32& x);"
                "[[effects(none)]] i32 f(i32& y){return y;}"
            ),
            "incompatible override": (
                "i32 global_state;"
                "struct B{virtual i32 f() [[effects(none)]] {return 0;}};"
                "struct D:B{i32 f() [[effects(read(global))]] override{return global_state;}};"
            ),
        }
        for case, source in cases.items():
            with self.subTest(case=case):
                self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_effect_bounds_include_registered_storage_cleanup(self):
        declarations = """
            i32 trace;
            struct Plain {i32 n;};
            struct Item {
                i32 n;
                ~Item() [[effects(write(global))]] {trace=42;}
            };
            """
        replace = """
            auto extent(storage_of(object));
            destroy(object);
            construct_at<Item>(extent, 0);
            """
        declarations += (
            "[[effects(read(object), write(object))]] void install(Plain& object){"
            + replace
            + "}"
        )
        reconstructed = "Plain object(0);" + replace
        through_call = "Plain object(0); install(object);"
        for body in (reconstructed, through_call):
            with self.subTest(admitted=body):
                self.assertEqual(
                    self.program(
                        declarations
                        + "[[effects(write(global))]] void run(){"
                        + body
                        + "}i32 main(){run();return trace;}"
                    ),
                    42,
                )
        for body in (
            reconstructed,
            "Item object(0); destroy(object);",
            "Item object(0); auto extent(storage_of(object));",
            through_call,
        ):
            with self.subTest(body=body):
                result = self.compile(
                    declarations + "[[effects(none)]] void run(){" + body + "}",
                    "--check",
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("write(global)", result.stderr)
        self.assertEqual(
            self.program(
                declarations
                + """
                [[effects(none)]] void run(){
                    Item object(0);
                    auto extent(storage_of(object));
                    abandon(object);
                    construct_at<Plain>(extent,0);
                }
                i32 main(){run();return trace;}
                """
            ),
            0,
        )

    def test_explicit_storage_generation_writes_actual_parameter_region(self):
        source = """
            [[effects(read(x), write(x))]] i32 replace(i32& x) {
                auto extent(storage_of(x));
                destroy(x);
                return *construct_at<i32>(extent,42);
            }
            i32 main(){i32 n(1);return replace(n);}
            """
        self.assertEqual(self.program(source), 42)
        for body in (
            source.replace("read(x), write(x)", "read(x)"),
            "[[effects(none)]] void retire(i32& x){abandon(x);}",
        ):
            with self.subTest(body=body):
                result = self.compile(body, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("write(parameter 0)", result.stderr)

    def test_effect_inference_and_opaque_diagnostics_follow_configuration(self):
        body = """
        i32 state;
        void leaf(){state=42;}
        [[effects(none)]] void entry(){leaf();}
        """
        inferred = self.compile(body, "--check")
        self.assertNotEqual(inferred.returncode, 0)
        self.assertIn("write(global)", inferred.stderr)
        unresolved = self.compile(
            "configuration {effects.inference=local;};" + body, "--check"
        )
        self.assertEqual(unresolved.returncode, 0, unresolved.stderr)
        self.assertIn("ANOMALY", unresolved.stderr)
        strict = self.compile(
            """
            configuration {
                effects.inference=local;
                effects.opaque_default=conservative;
                effects.diagnostics=strict;
            };
            void leaf(){}
            void entry(){leaf();}
            """,
            "--check",
        )
        self.assertEqual(strict.returncode, 0, strict.stderr)
        self.assertIn("ANOMALY", strict.stderr)

    def test_effect_regions_follow_pointers_in_value_parameters(self):
        declarations = """
        struct Holder {i32* ptr;};
        [[effects(write(box))]] void set(Holder box){*box.ptr=42;}
        alias Setter = function<void(Holder box) [[effects(write(box))]]>*;
        """
        self.assertEqual(
            self.program(
                declarations
                + """
                [[effects(none)]] i32 invoke(Setter setter){
                    i32 local(0);
                    setter(Holder(&local));
                    return local;
                }
                i32 main(){return invoke(&set);}
                """
            ),
            42,
        )
        for callee in ("set", "setter"):
            result = self.compile(
                declarations
                + "i32 state;"
                + "[[effects(none)]] void invoke(Setter setter){"
                + callee
                + "(Holder(&state));}",
                "--check",
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("write(global)", result.stderr)

    def test_indirect_calls_preserve_selected_contract_checks(self):
        source = """
            [[effects(none), requires(n != 0)]]
            i32 checked(i32 n) noexcept {return n;}
            [[effects(none)]]
            i32 identity(i32 n) noexcept {return n;}
            alias Exact = decltype(&checked);
            alias Callback =
                function<i32(i32) noexcept [[effects(trap(contract))]]>*;
            struct Slot {Callback action;};
            Exact selected(bool guarded) {
                Exact a(&checked);
                Exact b(&identity);
                return guarded ? a : b;
            }
            [[effects(trap(contract))]]
            i32 invoke(Callback callback, i32 n) {
                Slot slot(callback);
                Callback copy(slot.action);
                return copy(n);
            }
            i32 main(){return invoke(selected(true), 42);}
            """
        self.assertEqual(self.program(source), 42)
        self.assertEqual(
            self.program(source.replace("selected(true), 42", "selected(true), 0")),
            -signal.SIGILL,
        )
        self.assertEqual(
            self.program(source.replace("selected(true), 42", "selected(false), 0")),
            0,
        )
        for alias in ("Exact", "Callback"):
            with self.subTest(alias=alias):
                result = self.compile(
                    source
                    + f"[[effects(none)]] i32 reject({alias} cb){{return cb(42);}}",
                    "--check",
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("trap(contract)", result.stderr)

    def test_pointer_conversion_preserves_checked_predicate_read_regions(self):
        source = """
            [[effects(none), requires(p > 0)]]
            i32 checked(const<i32>& p) noexcept {return 42;}
            alias Callback = function<i32(const<i32>& subject) noexcept
                [[effects(read(subject), trap(contract))]]>*;
            i32 main(){Callback fn(&checked); i32 n(1); return fn(n);}
            """
        self.assertEqual(self.program(source), 42)
        for bound in ("none", "trap(contract)", "read(subject)"):
            with self.subTest(bound=bound):
                result = self.compile(
                    source.replace("read(subject), trap(contract)", bound), "--check"
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("function-pointer", result.stderr)
        self.assertEqual(
            self.program(
                "configured(contracts.validation=document)"
                + source.replace("read(subject), trap(contract)", "none")
            ),
            42,
        )

    def test_indirect_postcondition_preserves_borrowed_result_region(self):
        source = """
            [[effects(none), returns_borrowed_from(p), ensures(return_value > 0)]]
            const<i32>& checked(const<i32>& p) noexcept {return p;}
            alias Callback = function<const<i32>& (const<i32>& subject) noexcept
                [[returns_borrowed_from(subject),
                  effects(read(subject), trap(contract))]]>*;
            i32 main(){i32 n(42); Callback fn(&checked); return fn(n);}
            """
        self.assertEqual(self.program(source), 42)
        self.assertEqual(self.program(source.replace("n(42)", "n(0)")), -signal.SIGILL)
        result = self.compile(source.replace("read(subject), ", ""), "--check")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("function-pointer", result.stderr)

    def test_callable_type_queries_preserve_parameter_contracts(self):
        src = """
            [[noescape(a),returns_borrowed_from(a)]] i32& id(i32& a) noexcept{return a;}
            alias Pointer=decltype(id)*;
            alias Renamed=function<i32&(i32& value) noexcept [[returns_borrowed_from(value),noescape(value)]]>*;
            i32 main(){Pointer p(&id);i32 n(40);p(n)+=2;
              return SameType<decltype(&id),Renamed> && SameType<Pointer,Renamed> ? n : 1;}
        """
        self.assertEqual(self.program(src), 42)
        for src in (
            "i32& f(i32& x){return x;}void g(){function<i32&(i32& a) [[noescape(a)]]>* p(&f);}",
            "i32 f(i32 x){return x;}i64 f(i64 x){return x;}alias T=decltype(f);",
            "void f(){decltype(unknown()) x;}",
            "alias P=function<void(i32* a) [[noescape(missing)]]>*;",
            "[[noescape(x)]] i32* f(i32* x){return x;}",
        ):
            self.assertNotEqual(self.compile(src, "--check").returncode, 0, src)

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

    def test_pointer_call_bounds_and_returned_generations(self):
        calls = """
          [[returns_borrowed_from(p)]] i32* offset(i32* p,i32 n){return p+n;}
          [[returns_borrowed_from(p)]] i32* walk(i32* p,i32 n){
            if(n==0){return p;}return walk(p+1,n-1);}
          void advance(i32*& p){++p;}
          i32 read(i32* p,i32 n){return *(p+n);}
        """
        self.assertEqual(
            self.program(
                calls
                + """
          i32 main(){i32[3] a(4,5,42);i32* p(&a[0]);advance(p);
            i32* last(walk(p,1));return read(offset(last,-1),1);}
        """
            ),
            42,
        )
        for body in (
            "return read(p,2);",
            "auto end(walk(p,2));return *end;",
            "advance(p);return *(p+1);",
            "auto old(offset(p,1));auto slot(storage_of(a[1]));"
            "destroy(a[1]);construct_at<i32>(slot,42); return read(old,0);",
        ):
            self.assertEqual(
                self.program(
                    calls + "i32 main(){i32[2] a(7,8);i32* p(&a[0]);" + body + "}"
                ),
                -4,
            )

    def test_pointer_call_bounds_native_virtual_and_indirect(self):
        source = """
          struct Base {virtual i32 read(i32* p,i32 n){return *(p+n);}};
          struct Child:Base{i32 read(i32* p,i32 n) override{return *(p+n);}};
          i32 via(Base& b,i32* p,i32 n){return b.read(p,n);}
          extern "C" i32 inspect(i32* p,i32 n){return *(p+n);}
          extern "C" i32 host();
          i32 main(){i32[2] a(1,42);Child c;
            function<i32(i32*,i32)>* f(&inspect);
            function<i32(i32*,i32)>* lambda([] i32(i32* p,i32 n) {return *(p+n);});
            if(host()!=42 || via(c,&a[0],1)!=42){return 0;}
            BODY
          }
        """
        host = "extern int inspect(int *,int); int host(void){int a[2]={0,42};return inspect(a,1);}"
        for body, expected in (
            ("return f(&a[0],1);", 42),
            ("return via(c,&a[0],2);", -4),
            ("return f(&a[0],2);", -4),
            ("return lambda(&a[0],2);", -4),
        ):
            self.assertEqual(
                self.program(source.replace("BODY", body), host=host), expected
            )

    def test_pointer_offsets_track_selected_element_generation(self):
        self.assertEqual(
            self.program("""
          i32 main(){i32[3] a(40,7,42);i32* p(&a[0]);auto tail(p+3);
            destroy(a[0]);i32* q(tail-1); if(*q!=42){return 1;}
            auto slot(storage_of(a[0]));p=construct_at<i32>(slot,42);return *p;}
        """),
            42,
        )
        for body in (
            "auto q(p+1);destroy(a[1]);return *q;",
            "p++;destroy(a[1]);return *p;",
            "auto q(p+1);auto cap(storage_of(a[1]));destroy(a[1]);construct_at<i32>(cap,5);return *q;",
        ):
            self.assertLess(
                self.program("i32 main(){i32[2] a(7,8);i32* p(&a[0]);" + body + "}"), 0
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
                constraint Item<type T> {expression(T& x){x.item -> i32&;}};
                generic<type T> requires(Item<T>) i32 inspect(T& value){
                    alias Member=decltype(value.item);
                    if constexpr(SameType<Member,i32&>){return value.item;}
                    else{return 0;}
                }
                struct Value{i32 item(42);};
                i32 main(){Value value;return inspect(value);}
            """),
            42,
        )
        for usage in (
            "alias Member=decltype(value.item);",
            "if constexpr(SameType<decltype(value.item),i32&>){return 1;}",
        ):
            checked = self.compile(
                "generic<type T> i32 unused(T& value){" + usage + "return 0;}",
                "--check",
            )
            self.assertEqual(checked.returncode, 1, checked.stderr)
            self.assertIn("dependent operation", checked.stderr)
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

    def test_unary_and_comparison_constraint_witnesses(self):
        for definition in [
            "generic<type T> T neg(T v){return -v;}",
            "generic<type T> bool less(T a,T b){return a<b;}",
            "constraint Prefix<type T>{expression(T& a){++a->T&;}};"
            "generic<type T> requires(Prefix<T>) T next(T v){return v++;}",
        ]:
            r = self.compile(definition, "--check")
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("not established", r.stderr)
        self.assertEqual(
            self.program("""
            constraint Ordered<type X>{expression(X v,X w){v<w->bool;-v->X;}}
            ;
            generic<type T> requires(Ordered<T>) T positive(T v){
              if(v<T(0)){return -v;}return v;}
            i32 main(){return positive(i32(-42));}
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

    def test_c_abi_symbol_binds_imports_exports_and_distinct_overloads(self):
        source = """
            extern "C" {
                [[abi_symbol("llvm.test.foreign_count"), abi_cc("sysv-amd64-2018.lp64")]]
                i32 read();
                [[abi_symbol("cpn.upstream.adjust")]] i32 read(i8 amount);
                namespace host {
                    [[abi_symbol("host.shared")]] i32 shared;
                }
                [[abi_symbol("cpn.out")]] i32 dispatch(i32 amount);
                i32 dispatch(i32 amount) {
                    return read() + read(checked_cast<i8>(amount)) + host::shared;
                }
                [[abi_symbol("cpn.shared")]] i32 public_count;
                define i32 public_count(9);
            }
        """
        host = """
            #include <stdint.h>
            int read_count(void) __asm__("llvm.test.foreign_count");
            int read_count(void) { return 20; }
            int adjust(int8_t a) __asm__("cpn.upstream.adjust");
            int adjust(int8_t a) { return 10 + a; }
            int shared __asm__("host.shared") = 10;
            extern int out(int) __asm__("cpn.out");
            extern int result_count __asm__("cpn.shared");
            int main(void) { return result_count == 9 ? out(2) : 1; }
        """
        self.assertEqual(self.program(source, host=host), 42)
        for source, diagnostic in (
            (
                'extern "C" [[abi_symbol("one")]] i32 f(); '
                'extern "C" [[abi_symbol("two")]] i32 f();',
                "incompatible redeclaration",
            ),
            (
                'extern "C" [[abi_symbol("one")]] i32 object; '
                'extern "C" [[abi_symbol("two")]] i32 object;',
                "conflicting external object declaration",
            ),
            (
                'extern "C" [[abi_symbol("overlap")]] i32 a; '
                'extern "C" [[abi_symbol("overlap")]] i32 f();',
                "conflicting external symbol",
            ),
            (
                'extern "C" [[abi_symbol("cpn.slot.begin")]] void f(); '
                "i32 main(){i32 object;destroy(object);f();return 42;}",
                "conflicting external symbol",
            ),
            ('extern "C" [[abi_symbol("")]] i32 f();', "invalid raw"),
            (r'extern "C" [[abi_symbol("a\0b")]] i32 f();', "invalid raw"),
            ('extern "C" [[abi_cc("win64")]] i32 f();', "CFG002"),
            ('extern "C++" i32 example();', "CFG002"),
            ('struct Pair{i32 x;};extern "C" Pair pair;', "no C ABI transport"),
            ('extern "C" auto external;', "requires an explicit type"),
            ('extern "C" define auto external(2);', "requires an explicit type"),
            ('extern "C" constexpr i32 external;', "requires a definition"),
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertEqual(result.returncode, 1)
                self.assertIn(diagnostic, result.stderr)

    def test_native_symbols_use_logical_owner_and_signature(self):
        source = """
            i32 state(9);
            i32 sum(i32 a){return a+state;}
            i32 sum(i16 a){return i32(a)+state;}
            i32 main(){return sum(i32(10))+sum(i16(14));}
        """

        def symbols(prefix, root):
            result = self.compile(prefix + source, "-S", "--root-id=" + root)
            self.assertEqual(result.returncode, 0, result.stderr)
            module = self.src.with_suffix(".ll").read_text()
            functions = set()
            for line in module.splitlines():
                if line.startswith("define internal i32 @cpn.v1.fn."):
                    functions.add(line.split("@", 1)[1].split("(", 1)[0])
            owner = root.encode().hex()
            identifier = "sum".encode().hex()
            self.assertIn(f"@cpn.v1.obj.{owner}.{'state'.encode().hex()}.", module)
            return {name for name in functions if f".{owner}.{identifier}." in name}

        original = symbols("", "linked-root")
        self.assertEqual(len(original), 2)
        self.assertEqual(
            original, symbols("i32 unrelated(){return 8;}\n", "linked-root")
        )
        self.assertTrue(original.isdisjoint(symbols("", "other-root")))

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

    def test_foreign_import_checks_keep_c_scalar_abi(self):
        self.assertEqual(
            self.program(
                """
            extern "C" {
                [[requires(n < 0), ensures(return_value == n)]]
                i8 signed_echo(i8 n);
                [[requires(ok), ensures(return_value)]]
                bool echo_bool(bool ok);
                void set_value(i32* cell)
                    [[requires(cell != nullptr), ensures(*cell == 42)]];
                i32 call_echo(function<i8(i8)>* callback);
            }
            i32 main() {
                if (signed_echo(i8(-7)) != -7 || !echo_bool(true)) { return 1; }
                function<i8(i8)>* checked(&signed_echo);
                if (checked(i8(-7)) != -7) { return 2; }
                i32 cell;
                set_value(&cell);
                if (cell != 42) { return 3; }
                return call_echo(checked);
            }
        """,
                host="""
            #include <stdbool.h>
            #include <stdint.h>
            int8_t signed_echo(int8_t n) { return n; }
            bool echo_bool(bool ok) { return ok; }
            void set_value(int32_t *cell) { *cell = 42; }
            int call_echo(int8_t (*callback)(int8_t)) {
                return callback(-7) == -7 ? 42 : 4;
            }
        """,
            ),
            42,
        )

        ir = self.src.with_suffix(".ll").read_text()
        self.assertIn("call signext i8 @signed_echo(i8 signext ", ir)
        self.assertIn("call zeroext i1 @echo_bool(i1 zeroext ", ir)

    def test_foreign_import_contract_traps_and_bound_policy(self):
        before = """
            extern "C" {
                [[requires(n > 0)]]
                i32 must_not_call(i32 n);
            }
            i32 main() { return must_not_call(0); }
        """
        indirect = before.replace(
            "return must_not_call(0);",
            "function<i32(i32)>* call(&must_not_call); return call(0);",
        )
        host = "#include <stdlib.h>\nint must_not_call(int n) { _Exit(5); }"
        for source in (before, indirect):
            self.assertEqual(self.program(source, host=host), -signal.SIGILL)
        after = """
            extern "C" {
                [[ensures(return_value == expected)]]
                i32 returns_wrong(i32 expected);
            }
            i32 main() { return returns_wrong(42); }
        """
        host = "int returns_wrong(int expected) { return 5; }"
        self.assertEqual(self.program(after, host=host), -signal.SIGILL)
        self.assertEqual(self.program(after, "--preset", "Release", host=host), 5)

    def test_foreign_prototype_followed_by_local_definition_keeps_address(self):
        self.assertEqual(
            self.program(
                """
            extern "C" {
                [[requires(n > 0), ensures(return_value == n)]]
                i32 local_echo(i32 n);
                bool is_local_echo(function<i32(i32)>* callback);
            }
            alias Echo = function<i32(i32)>*;
            constexpr Echo callback(&local_echo);
            i32 call_before_definition() { return callback(42); }
            extern "C" i32 local_echo(i32 n) { return n; }
            i32 main() {
                return is_local_echo(callback) ? call_before_definition() : 1;
            }
        """,
                host="""
            #include <stdbool.h>
            extern int local_echo(int);
            bool is_local_echo(int (*callback)(int)) {
                return callback == local_echo;
            }
        """,
            ),
            42,
        )

    def test_foreign_import_contract_effect_composition(self):
        source = """
            extern "C" {
                [[requires(n > 0), effects(none)]]
                i32 imported(i32 n);
            }
            [[effects(BOUND)]] i32 caller(i32 n) { return imported(n); }
            i32 main() { return caller(42); }
        """
        rejected = self.compile(source.replace("BOUND", "none"), "--check")
        self.assertEqual(rejected.returncode, 1)
        self.assertIn("trap(contract)", rejected.stderr)
        self.assertEqual(
            self.program(
                source.replace("BOUND", "trap(contract)"),
                host="int imported(int n) { return n; }",
            ),
            42,
        )

    def test_foreign_import_prove_mode_uses_available_evidence(self):
        proved = """
            extern "C" {
                configured(contracts.validation=prove)
                [[requires(true), ensures(return_value == return_value)]]
                i32 imported(i32 n);
            }
            i32 main() { return imported(42); }
        """
        self.assertEqual(
            self.program(proved, host="int imported(int n) { return n; }"),
            42,
        )
        unproved = proved.replace("return_value == return_value", "return_value == n")
        rejected = self.compile(unproved, "--check")
        self.assertEqual(rejected.returncode, 1)
        self.assertIn("cannot establish imported ensures", rejected.stderr)

    def test_narrow_scalars_use_one_abi_for_c_and_native_function_pointers(self):
        self.assertEqual(
            self.program(
                """
            extern "C" {
                i32 signed_byte(i8 n);
                i32 signed_word(i16 n);
                i32 unsigned_byte(u8 n);
                i32 unsigned_word(u16 n);
                i32 boolean_value(bool n);
                i32 call_byte(function<i8(i8)>* callback);
            }
            i8 native_echo(i8 n) { return n; }
            i32 main() {
                function<i32(i8)>* s8(&signed_byte);
                function<i32(i16)>* s16(&signed_word);
                function<i32(u8)>* u8_reader(&unsigned_byte);
                function<i32(u16)>* u16_reader(&unsigned_word);
                function<i32(bool)>* bool_reader(&boolean_value);
                function<i8(i8)>* native(&native_echo);
                function<i8(i8)>* closure([] i8(i8 n) { return n; });
                if (s8(i8(-42)) != -42 || s16(i16(-321)) != -321) { return 1; }
                if (u8_reader(u8(250)) != 250 || u16_reader(u16(60000)) != 60000) {
                    return 2;
                }
                if (bool_reader(true) != 1 || bool_reader(false) != 0) { return 3; }
                if (call_byte(native) != -42 || call_byte(closure) != -42) {
                    return 4;
                }
                return native(i8(-7)) == -7 && closure(i8(-7)) == -7 ? 42 : 5;
            }
        """,
                host=r"""
            #include <stdbool.h>
            #include <stdint.h>
            // Observe all 32 bits of the designated SysV argument register,
            // including the extension beyond each parameter's source width.
            #define Observe(name, type) \
                __attribute__((naked)) int name(type n) { \
                    __asm__("movl %edi, %eax\n\tret"); \
                }
            Observe(signed_byte, int8_t)
            Observe(signed_word, int16_t)
            Observe(unsigned_byte, uint8_t)
            Observe(unsigned_word, uint16_t)
            Observe(boolean_value, bool)
            // The tail jump lets the ABI test observe the callback's full
            // result register through the caller's wider C return type.
            __attribute__((naked)) int call_byte(int8_t (*callback)(int8_t)) {
                __asm__("movq %rdi, %rax\n\tmovl $-42, %edi\n\tjmp *%rax");
            }
        """,
            ),
            42,
        )

    def test_narrow_scalar_abi_offsets_with_aggregate_results_and_receivers(self):
        self.assertEqual(
            self.program("""
                struct Packet { i8 code; };
                struct Base {
                    virtual Packet read(i8 n) { return Packet(n); }
                };
                struct Derived : Base {
                    Packet read(i8 n) override { return Packet(n); }
                };
                Packet through_virtual(Base& view, i8 n) { return view.read(n); }
                i32 main() {
                    Derived object;
                    Packet a(through_virtual(object, i8(-42)));
                    function<Packet(i8)>* f([] Packet(i8 n) { return Packet(n); });
                    Packet b(f(i8(-42)));
                    return a.code == -42 && b.code == -42 ? 42 : 1;
                }
            """),
            42,
        )
        ir = self.src.with_suffix(".ll").read_text()
        self.assertRegex(ir, r"call void %\w+\(ptr [^,]+, ptr [^,]+, i8 signext ")
        self.assertRegex(ir, r"call void %\w+\(ptr [^,]+, i8 signext ")

    def test_construction_tail_exit_retires_completed_subobjects(self):
        self.assertEqual(
            self.program("""
                i32 log;
                struct Child {i32 tag; ~Child(){log=log*10+tag;}};
                struct Parent {
                    Child first(1);
                    Child second(2);
                    ~Parent(){log=99;}
                };
                i32 returning() {
                    Parent value -> {Child local(3); return 42;};
                    return 0;
                }
                void jumping(){
                    {Parent value -> {Child local(3); goto done;};}
                    done:{}
                }
                void breaking(){
                    while(true){
                        Parent value -> {Child local(3); break;};
                    }
                }
                i32 main(){
                    if(returning()!=42 || log!=321){return 1;}
                    log=0;
                    jumping();
                    if(log!=321){return 2;}
                    log=0;
                    breaking();
                    return log==321?42:3;
                }
            """),
            42,
        )

    def test_constexpr_construction_tail_rolls_back_only_completed_subobjects(self):
        source = """
            i32 observed;
            struct Child {i32 tag; ~Child(){if(tag==0){++observed;}}};
            struct Parent {Child child(42); ~Parent(){++observed;}};
            consteval i32 evaluate(){
                {Parent value -> {goto done;};}
                done:{return 42;}
            }
            constexpr i32 computed(evaluate());
            i32 main(){return computed;}
        """
        self.assertEqual(self.program(source), 42)
        result = self.compile(source.replace("child(42)", "child(0)"), "--check")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("constant", result.stderr)

    def test_pointer_cell_storage_is_independent_of_its_referent(self):
        self.assertEqual(
            self.program("""
                i32 replace(i32* cell, i32* next) {
                    auto extent(storage_of(cell));
                    i32 before(*cell);
                    destroy(cell);
                    auto fresh(construct_at<i32*>(extent, next));
                    return before+**fresh;
                }
                i32 main(){
                    i32 first(2);i32 next(40);
                    i32* pointer(&first);i32*& viewRef(pointer);
                    auto extent(storage_of(viewRef));
                    destroy(viewRef);
                    auto fresh(construct_at<i32*>(extent,&next));
                    return replace(&first,*fresh);
                }
            """),
            42,
        )
        stale_cell = self.compile(
            """
                i32 main(){
                    i32 first(1);i32 second(42);
                    i32* pointer(&first);
                    auto extent(storage_of(pointer));
                    i32** bound(&pointer);
                    destroy(pointer);
                    auto fresh(construct_at<i32*>(extent,&second));
                    if(**fresh==42){return **bound;}
                    return 0;
                }
            """,
            "--check",
        )
        self.assertEqual(stale_cell.returncode, 1, stale_cell.stderr)
        self.assertIn("ended object generation", stale_cell.stderr)
        ended = self.compile(
            "i32 f(){i32 value(1); i32* p(&value); destroy(p); return *p;}",
            "--check",
        )
        self.assertNotEqual(ended.returncode, 0)
        self.assertIn("ended object generation", ended.stderr)

    def test_storage_view_does_not_shadow_a_source_type(self):
        self.assertEqual(
            self.program("""
                struct storage {i32 value;};
                i32 main(){
                    storage named(0);
                    auto view(storage_of(named));
                    destroy(named);
                    return construct_at<storage>(view,42)->value;
                }
            """),
            42,
        )

    def test_raw_validation_policy_preserves_mandatory_pointer_checks(self):
        source = """
            i32 read(i32* p){return *p;}
            i32 main(){i32* p(nullptr);return read(p);}
        """
        self.assertEqual(self.program(source), -signal.SIGILL)
        trap_counts = []
        for preset in ("Debug", "Release"):
            result = self.compile(source, "-S", "--preset", preset)
            self.assertEqual(result.returncode, 0, result.stderr)
            ir = self.src.with_suffix(".ll").read_text()
            trap_counts.append(ir.count("call void @llvm.trap("))
        self.assertEqual(trap_counts[0], trap_counts[1] + 1)
        with_override = """
            configured(memory.raw_validation=available)
            i32 read(i32* p){return *p;}
            i32 main(){i32* p(nullptr);return read(p);}
        """
        self.assertEqual(
            self.program(with_override, "--preset=Release"), -signal.SIGILL
        )

        known_null = self.compile(
            "constexpr i32* p(nullptr); i32 f(){return *p;}",
            "--check",
            "--preset=Release",
        )
        self.assertNotEqual(known_null.returncode, 0)
        self.assertIn("null pointer access", known_null.stderr)

    def test_pointer_receiver_calls_validate_the_bound_generation(self):
        checked = self.compile(
            """
                struct Cell {i32 read() const{return 42;}};
                i32 main(){
                    Cell old;
                    auto extent(storage_of(old));
                    auto previous(&old);
                    destroy(old);
                    auto current(construct_at<Cell>(extent));
                    if(current->read()==42){return previous->read();}
                    return 0;
                }
            """,
            "--check",
            "--preset=Release",
        )
        self.assertEqual(checked.returncode, 1, checked.stderr)
        self.assertIn("ended object generation", checked.stderr)

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

    def test_forward_preserves_const_reference_and_recorded_category(self):
        self.assertEqual(
            self.program("""
                struct Item {
                    constexpr i32 kind() & {return 13;}
                    constexpr i32 kind() const & {return 11;}
                    constexpr i32 kind() && {return 18;}
                };
                generic<type T> requires (SameType<T,Item&> ||
                    SameType<T,const<Item>&> || SameType<T,Item>)
                constexpr i32 kind(forward T item){
                    return ::std::forward<T>(item).kind();
                }
                constexpr i32 expiring(kind(Item()));
                i32 main(){Item item;const Item read_only;
                    return kind(item)+kind(read_only)+expiring;
                }
            """),
            42,
        )
        for source in (
            "i32 main(){i32 n(42);return std::forward<i32>(n);}",
            "generic<type T> i32 f(forward T n){return std::forward<i32>(n);}"
            "i32 main(){i32 n(42);return f(n);}",
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("std::forward", result.stderr)

    def test_constraint_order_expands_named_structural_requirements(self):
        self.assertEqual(
            self.program("""
                constraint Readable<type T> {
                    expression(const<T>& x){x.read()->i32;}
                };
                constraint SizedReadable<type T> {
                    requires(Readable<T>);
                    expression(const<T>& value){value.size()->usize;}
                };
                struct Data {
                    i32 read() const {return 40;}
                    usize size() const {return 2;}
                };
                generic<type Item> requires(Readable<Item>)
                i32 use(const<Item>& x){return 1;}
                generic<type Value> requires(SizedReadable<Value>)
                i32 use(const<Value>& x){return x.read();}
                generic<type T> struct Rank { i32 get() const {return 0;} };
                generic<type T> requires(Readable<T>)
                specialize struct Rank<T> {i32 get() const {return 1;}};
                generic<type T> requires(SizedReadable<T>)
                specialize struct Rank<T> {i32 get() const {return 2;}};
                i32 main(){ Data data; Rank<Data> rank; return use(data)+rank.get(); }
            """),
            42,
        )

    def test_constraint_order_uses_boolean_implication(self):
        self.assertEqual(
            self.program("""
                alias Word=i32;
                constraint EnabledWord<type T,const bool Enabled=true> {
                    requires(Enabled && SameType<T,Word>);
                };
                generic<type T> requires(SameType<T,i32> || SameType<T,i64>)
                i32 choose(T value){return 1;}
                generic<type T> requires(EnabledWord<T> && !SameType<T,bool>)
                i32 choose(T value){return 42;}
                i32 main(){return choose(i32(0));}
            """),
            42,
        )
        for source in (
            "generic<const i32 N> requires(N>0) i32 f(){return 1;}"
            "generic<const i32 N> requires(N>=1) i32 f(){return 2;}"
            "i32 main(){return f<2>();}",
            "generic<type T> requires(SameType<T,i32>) i32 f(T x){return 1;}"
            "generic<type T> requires((SameType<T,i32> && CompleteType<T>) ||"
            " (SameType<T,i32> && !CompleteType<T>)) i32 f(T x){return 2;}"
            "i32 main(){return f(i32(0));}",
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn("ambiguous overload", result.stderr)

    def test_constraint_order_preserves_short_circuit_evaluation(self):
        source = """
            constexpr bool recursive(){return recursive();}
            generic<type T> requires(SameType<T,i32> || recursive())
            i32 choose(T value){return 1;}
            generic<type T> requires(SameType<T,i32> && CompleteType<T>)
            i32 choose(T value){return 42;}
            i32 main(){return choose(TYPE(0));}
        """
        self.assertEqual(self.program(source.replace("TYPE", "i32")), 42)
        reached = self.compile(source.replace("TYPE", "i64"), "--check")
        self.assertEqual(reached.returncode, 1, reached.stderr)
        self.assertIn("constant invocation depth exhausted", reached.stderr)

    def test_required_constraint_evaluation_failure_is_not_false(self):
        source = """
            bool runtime_only(){return true;}
            constraint Gate<type T> {requires(CONDITION);};
            generic<type T> requires(Gate<T>) i32 pick(T value){return 1;}
            generic<type T> i32 pick(T value){return 42;}
            i32 main(){return pick(i32(0));}
        """
        self.assertEqual(
            self.program(source.replace("CONDITION", "false && runtime_only()")),
            42,
        )
        for condition, diagnostic in (
            ("true && runtime_only()", "constexpr function"),
            ("i32(1)", "Boolean type"),
        ):
            with self.subTest(condition=condition):
                result = self.compile(source.replace("CONDITION", condition), "--check")
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn(diagnostic, result.stderr)

    def test_core_type_predicates_exclude_nonobject_and_incomplete_enum_types(self):
        self.assertEqual(
            self.program("""
                declare enum State:i32;
                constexpr bool opaque(ObjectType<State> && !CompleteType<State>
                    && !CopyConstructible<State>);
                enum State:i32 {case Ready(1)};
                alias Signature=function<void()>;
                i32 main(){return opaque && CompleteType<State>
                    && CopyConstructible<State> && !ObjectType<never>
                    && !ObjectType<Signature> && !CompleteType<Signature> ? 42 : 0;}
            """),
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
            generic<type T> requires(SameType<T,R&> || SameType<T,R>)
            i32 kind(forward T v){return std::forward<T>(v).kind();}
            i32 main(){
                R r;
                return nested(10,11,12)+constants<1,2,3>()+relay()+kind(r)+kind(R());
            }
        """),
            42,
        )
        self.assertEqual(
            self.program("""
                generic<type T> T value(){return T();}
                generic<type... Ts> i32 result(){return 42;}
                generic<type... Ts> struct Types{};
                generic<type... Ts> struct Wrapped{
                    alias Result=decltype(result<Ts...>());
                    alias Elements=Types<decltype(value<Ts>())...>;
                };
                i32 sum(){return 0;}
                i32 sum(i32 left,i32 right){return left+right;}
                generic<type... Ts> i32 inspect(Ts... values){
                    alias Viewed=decltype(sum(values...));
                    if constexpr(SameType<Viewed,i32>){return sum(values...);}
                    else{return 1;}
                }
                i32 main(){
                    if constexpr(SameType<Wrapped<i8,i64>::Result,i32> &&
                                 SameType<Wrapped<i8,i64>::Elements,Types<i8,i64>> &&
                                 SameType<Wrapped<>::Elements,Types<>>){
                        return inspect(19,23)+inspect();
                    }else{return 2;}
                }
            """),
            42,
        )
        for source, diagnostic in [
            ("generic<type... Ts,type U> void f(){}", "last parameter"),
            ("generic<type... Ts=i32> void f(){}", "cannot have a default"),
            ("generic<type... Ts> i32 f(Ts... xs){return xs;}", "unexpanded pack"),
            ("void f(i32... xs){}", "requires a generic pack"),
            ("generic<type... Ts> void f(i32... xs){}", "requires a generic pack"),
            (
                "void sink(i32 x){} generic<type T> void f(T x){sink(x...);}",
                "pack expansion requires an unexpanded pack binding",
            ),
            (
                "generic<type... Ts> void sink(){} "
                "generic<type T> void f(){sink<T...>();}",
                "pack expansion requires an unexpanded pack binding",
            ),
            (
                "generic<type... Ts> struct Types{}; "
                "generic<type... Ts> void sink(){} "
                "generic<type... Ts> void f(){sink<Types<Ts...>...>();}",
                "pack expansion requires an unexpanded pack binding",
            ),
            (
                "generic<type... Ts> struct Types{}; "
                "generic<type T> struct Unused{alias Bad=Types<T...>;};",
                "pack expansion requires an unexpanded pack binding",
            ),
            (
                "generic<type... Ts> i32 result(){return 0;} "
                "generic<type T> struct Unused{alias Bad=decltype(result<T...>());};",
                "pack expansion requires an unexpanded pack binding",
            ),
            (
                "generic<type T> struct Unused{alias Bad=decltype(missing());};",
                "unknown name 'missing'",
            ),
            (
                "generic<type T> void f(function<void(T...)>* fn){}",
                "pack expansion requires an unexpanded pack binding",
            ),
            (
                "namespace lib{i32 values;} void sink(i32 x){} "
                "generic<const i32... values> void f(){sink(lib::values...);}",
                "pack expansion requires an unexpanded pack binding",
            ),
            (
                "struct R{i32 values;}; void sink(i32 x){} "
                "generic<type... Ts> void f(R r,Ts... values){sink(r.values...);}",
                "pack expansion requires an unexpanded pack binding",
            ),
            ("void f(forward i32 x){}", "forward requires"),
        ]:
            with self.subTest(source=source):
                r = self.compile(source, "--check")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn(diagnostic, r.stderr)

    def test_compile_time_branch_and_definition_lookup(self):
        self.assertEqual(
            self.program("""
            constraint HasN<type T>{expression(T& v){v.n -> i32&;}};
            generic<const bool Field, type T> requires(!Field || HasN<T>) i32 read(T value) {
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

    def test_constexpr_arms_bind_in_their_lexical_and_dependent_scopes(self):
        self.assertEqual(
            self.program("""
                struct Packet { i32 code; };
                union Selection { case One(i32 n); };
                i32 read(Packet value) {
                    struct Packet { i32 other; };
                    if constexpr (false) { return value.code; }
                    return 40;
                }
                i32 payload(Selection choice) {
                    match(choice) {
                        case Selection::One(value n) {
                            if constexpr (false) { return n + 1; }
                            return n;
                        }
                    }
                }
                generic<type T> i32 dependent() {
                    alias S = T;
                    if constexpr (false) { return S::member; }
                    return 0;
                }
                i32 main() {
                    auto f([] i32(i32 n) {
                        if constexpr (false) { return n + 1; }
                        return n;
                    });
                    if constexpr (false) {
                        union Hidden { case Value(i32 n); };
                        Hidden h(Hidden::Value(0));
                    }
                    return f(read(Packet(0))) + payload(Selection::One(2))
                         + dependent<i32>();
                }
            """),
            42,
        )

    def test_unemitted_definitions_still_bind_nondependent_names(self):
        for source, diagnostic in (
            (
                "struct C{C(){if constexpr(false){missing();}}};",
                "unknown name 'missing'",
            ),
            (
                "struct C{~C(){} cleanup {if constexpr(false){missing();}}};",
                "unknown name 'missing'",
            ),
            (
                "generic<type T> struct G{i32 f(){"
                "if constexpr(false){missing();}return 42;}};",
                "unknown name 'missing'",
            ),
            (
                "generic<type T> struct G{G(){if constexpr(false){this->missing;}}};",
                "unknown member 'missing'",
            ),
            (
                "struct C{i32 n;};i32 f(C o){"
                "if constexpr(false){return o.missing;}return o.n;}",
                "unknown member 'missing'",
            ),
            (
                "i32 f(){for(i32 i(0);i<1;++i){}"
                "if constexpr(false){return i;}return 42;}",
                "unknown name 'i'",
            ),
            (
                "void f(){i32 n; auto check([] void(){"
                "if constexpr(false){i32 use(n);} });}",
                "unknown name 'n'",
            ),
            (
                "generic<const bool B> requires(false && missing) i32 f(){return 0;}",
                "unknown name 'missing'",
            ),
            (
                "generic<const i32 A,const i32 B> struct Table{};"
                "generic<const i32 T> specialize struct Table<T+missing,T>{};",
                "unknown name 'missing'",
            ),
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertEqual(result.returncode, 1)
                self.assertIn(diagnostic, result.stderr)

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

    def test_static_publication_through_pointer_and_subobject(self):
        source = """
          struct Cell {i32 a; i32 b(a+2);Cell(i32 n){init a(n);}};
          declare i32 early();i32 read(i32* p){return *p;}
          i32 make(){return 40;}
        """
        self.assertLess(
            self.program(
                source
                + """
          i32 first(early());Cell later(make());
          i32 early(){return read(&later.b);}
          i32 main(){return first;}
        """
            ),
            0,
        )
        self.assertEqual(
            self.program(
                source
                + """
          Cell earlier(make());i32 after(early());
          i32 early(){return read(&earlier.b);}
          i32 main(){return after;}
        """
            ),
            42,
        )

    def test_automatic_borrows_in_returned_records_and_static_cells(self):
        for source in (
            "struct H{i32* p;};H f(){i32 a(42);return H(&a);}",
            "struct N{i32 n;};struct H{i32* p;};H f(N a){return H(&a.n);}",
            "i32* retained;void f(){i32 a;retained=&a;}",
            "struct H{i32* p;H(const<H>& h)=default;};H f(){i32 n;H h(&n);return h;}",
        ):
            with self.subTest(source=source):
                r = self.compile(source, "--check")
                self.assertEqual(r.returncode, 1, r.stderr)
                self.assertIn("automatic storage", r.stderr)
        self.assertEqual(
            self.program("""
          struct H{i32* p;}; i32* retained;i32 global(42);
          H wrap(i32& n){return H(&n);}
          void transient(){i32 n;retained=&n;retained=&global;}
          i32 main(){transient();H h(wrap(global));return *h.p;}
        """),
            42,
        )

    def test_opaque_and_indirect_calls_preserve_returned_borrow_origins(self):
        declarations = """
            extern "C" {
                [[noescape(a,b),returns_borrowed_from(a,b)]]
                i32* select_borrow(i32* a,i32* b);
            }
            alias Callback = function<i32*(i32* a,i32* b)
                [[noescape(a,b),returns_borrowed_from(a,b)]]>*;
            i32 static_value(1);
            """
        self.assertEqual(
            self.program(
                declarations
                + """
                i32* choose(Callback callback,i32& value){
                    return callback(&static_value,&value);
                }
                i32 main(){i32 n(42);return *choose(&select_borrow,n);}
                """,
                host="int *select_borrow(int *a,int *b){return b;}",
            ),
            42,
        )
        for body in (
            "return select_borrow(&static_value,&local);",
            "return callback(&static_value,&local);",
            "auto get([&local] i32*(){return select_borrow(&static_value,&local);});"
            "return get();",
        ):
            with self.subTest(body=body):
                result = self.compile(
                    declarations
                    + "i32* leak(Callback callback){i32 local(42);"
                    + body
                    + "}",
                    "--check",
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("automatic storage escapes", result.stderr)

    def test_unproved_opaque_retention_uses_memory_diagnostic_policy(self):
        for body in (
            "observe(&local);",
            "callback(&local);",
            "auto get([&local] void(){observe(&local);});get();",
        ):
            source = (
                'extern "C" {void observe(i32* p);}'
                "alias Callback=function<void(i32* p)>*;"
                "void test(Callback callback){i32 local;" + body + "}"
            )
            with self.subTest(body=body):
                result = self.compile(source, "--check")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn("ANOMALY: MEM002", result.stderr)
                promoted = self.compile(
                    "configuration {diagnostics.promote=[MEM002];};" + source,
                    "--check",
                )
                self.assertNotEqual(promoted.returncode, 0)
                self.assertIn("ERROR: MEM002", promoted.stderr)
                checked = self.compile(
                    "configuration {diagnostics.promote=[MEM002];};"
                    + source.replace(
                        "void observe", "[[noescape(p)]] void observe"
                    ).replace("void(i32* p)>", "void(i32* p) [[noescape(p)]]>"),
                    "--check",
                )
                self.assertEqual(checked.returncode, 0, checked.stderr)

    def test_known_indirect_and_closure_calls_cannot_publish_automatic_borrows(self):
        source = """
            i32* saved;
            i32 static_value(42);
            void retain(i32* n){saved=n;}
            """
        for body in (
            "retain(&local);",
            "function<void(i32*)>* callback(&retain);callback(&local);",
            "auto publish([&local] void(){saved=&local;});publish();",
        ):
            with self.subTest(body=body):
                result = self.compile(
                    source + "void leak(){i32 local;" + body + "}", "--check"
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("automatic storage escapes", result.stderr)
        self.assertEqual(
            self.program(
                source
                + """
                void use(){i32 local;retain(&local);saved=&static_value;}
                i32 main(){use();return *saved;}
                """
            ),
            42,
        )

    def test_root_static_dependency_lists_and_attributes(self):
        self.assertEqual(
            self.program("""
          namespace lib {
            [[static_id("lib.first")]] i32 first(8);
            [[init_after(first)]] i32 second(10);
            [[init_after(::lib::first,second),init_cancel(cooperative),init_effect(none)]]
            i32 sum(first+second);
          }
          [[init_after(lib::sum,lib::second),init_cancel(finish)]] i32 answer(lib::sum+24);
          i32 main(){return answer;}
        """),
            42,
        )
        for source in (
            "[[static_id(42)]] i32 n;",
            "[[init_after()]] i32 n;",
            "i32 a;[[init_after(a,b)]] i32 c;i32 b;",
            "i32 a;[[init_after(a,missing)]] i32 b;",
            "[[init_cancel(cooperative)]] i32 a;",
            "[[init_effect(other)]] i32 a;",
            'struct X{[[static_id("field")]] i32 a;};',
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

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

    def test_strict_floating_nan_order_and_payload_mapping(self):
        self.assertEqual(
            self.program(
                """
            extern "C" f32 cpn_add(f32 a,f32 b){return a+b;}
            extern "C" f32 cpn_div(f32 a,f32 b){return a/b;}
            extern "C" f32 narrow(f64 v){return f32(v);}
            extern "C" f64 widen(f32 v){return f64(v);}
        """,
                host="""
            #include <stdint.h>
            #include <string.h>
            #include <xmmintrin.h>
            extern float cpn_add(float,float),cpn_div(float,float),narrow(double);
            extern double widen(float);
            static float f(uint32_t x){float v;memcpy(&v,&x,4);return v;}
            static double d(uint64_t x){double v;memcpy(&v,&x,8);return v;}
            static uint32_t raw(float v){uint32_t x;memcpy(&x,&v,4);return x;}
            static uint64_t wide(double v){uint64_t x;memcpy(&x,&v,8);return x;}
            int main(void){
                unsigned old=_mm_getcsr();_mm_setcsr((old|0x1f80u)&~0x3fu);
                uint32_t a=raw(cpn_add(f(0x7f800001),f(0xffc00002)));
                unsigned invalid=_mm_getcsr()&1u;
                int ok=a==0xffc00002 && invalid &&
                  raw(cpn_add(f(0xffc00003),f(0x7fc00002)))==0xffc00003 &&
                  raw(cpn_add(f(0xff800004),f(0x7f800005)))==0xffc00004 &&
                  raw(cpn_div(0.f,0.f))==0x7fc00000 &&
                  raw(narrow(d(0xfffa100000000043ull)))==0xffc00043 &&
                  wide(widen(f(0xffc00021)))==0xfff8000000000021ull;
                _mm_setcsr(old);return ok?42:1;}
        """,
            ),
            42,
        )

    def test_floating_local_trap_mask_and_subnormal_controls(self):
        source = """
          extern "C" f32 calc(f32 x,f32 y){return configured(numeric.fp.trap_mask=[DivideByZero])(x/y);}
          extern "C" f32 keep(f32 x){return configured(numeric.fp.subnormal=preserve)(x+x);}
        """
        host = """
          #include <xmmintrin.h>
          #include <stdint.h>
          #include <string.h>
          extern float calc(float,float),keep(float);
          int main(void){unsigned saved=_mm_getcsr();
            _mm_setcsr(saved|0x1f80u|0x8040u|4u);
            uint32_t raw=1;float x;memcpy(&x,&raw,4);x=keep(x);memcpy(&raw,&x,4);
            int ok=raw==2 && calc(4.f,2.f)==2.f && (_mm_getcsr()&0x8044u)==0x8044u;
            _mm_setcsr(saved);return ok?42:1;}
        """
        self.assertEqual(self.program(source, host=host), 42)
        self.assertEqual(
            self.program(source, host=host.replace("4.f,2.f", "4.f,0.f")), -4
        )
        self.assertEqual(
            self.program("""
          configuration {numeric.fp.initial_trap_mask=[Inexact];};
          f32 ratio(f32 x,f32 y){return x/y;}
          i32 main(){return ratio(1.0,3.0)>0.0?1:0;}
        """),
            -4,
        )
        for config in (
            "numeric.fp.trap_mask=[bad]",
            "numeric.fp.trap_mask=[Invalid,Invalid]",
            "numeric.fp.initial_rounding=current",
        ):
            r = self.compile("configuration {" + config + ";};", "--check")
            self.assertNotEqual(r.returncode, 0)
            self.assertIn("CFG001", r.stderr)
        self.assertNotEqual(
            self.compile(
                "configuration {numeric.fp.trap_mask=[Inexact];}; constexpr f32 x(f32(1.0)/f32(3.0));",
                "--check",
            ).returncode,
            0,
        )

    def test_fp_rounding_and_ambient_status(self):
        result = self.program(
            """
          extern "C" f32 up(f32 a,f32 b) {
            return configured(numeric.fp.rounding=toward_positive_infinity)(a+b);
          }
          extern "C" f32 down(f32 a,f32 b) {
            return configured(numeric.fp.rounding=toward_negative_infinity)(a+b);
          }
          extern "C" f32 cpn_truncate(f32 a,f32 b) {
            return configured(numeric.fp.rounding=toward_zero)(a/b);
          }
          extern "C" f32 ambient(f32 a,f32 b) {return a+b;}
          constexpr f32 folded(configured(numeric.fp.rounding=toward_positive_infinity)(f32(1.0)+f32(0x1.0p-24)));
          extern "C" f32 constant_value(){return folded;}
        """,
            host="""
          #include <xmmintrin.h>
          extern float up(float,float), down(float,float), cpn_truncate(float,float);
          extern float ambient(float,float), constant_value(void);
          int main(void) {
            unsigned saved = _mm_getcsr();
            _mm_setcsr((saved & ~(0x6000u|0x3fu)) | 0x2000u | 1u);
            float a = 1.0f, half = 0x1p-24f, next = 0x1.000002p0f;
            int ok = up(a,half)==next && down(a,half)==a &&
                     ambient(a,half)==a && cpn_truncate(1.0f,3.0f)==0x1.555554p-2f &&
                     constant_value()==next;
            unsigned after = _mm_getcsr();
            _mm_setcsr(saved);
            return ok && (after & 0x6000u)==0x2000u && (after & 0x21u)==0x21u ? 42 : 1;
          }""",
        )
        self.assertEqual(result, 42)

    def test_floating_context_atomic_validation_and_native_status(self):
        source = """
            alias Control=std::numeric::FPControl;
            alias Status=std::numeric::FPStatus;
            alias Flag=std::numeric::FPFlag;
            alias Flags=std::numeric::FPFlagSet;
            alias Mode=std::numeric::RoundingMode;
            alias Policy=std::numeric::SubnormalPolicy;
            alias Error=std::numeric::FPControlError;
            alias Result=std::Result<void,Error>;
            [[effects(fp_control)]] Control read_control(){return std::numeric::get_fp_control();}
            [[effects(fp_status)]] Status read_status(){return std::numeric::get_fp_status();}
            [[effects(fp_control)]] Result install(Control control){return try_set_fp_control(control);}
            [[effects(fp_status)]] void clear(Flags selected){clear_fp_status(selected);}
            [[effects(fp_status)]] void merge(Status selected){merge_fp_status(selected);}
            extern "C" i32 inspect(f32 one,f32 half){
                Control defaults;
                if(defaults.rounding!=Mode::NearestTiesEven || !defaults.trap_mask.empty() ||
                   defaults.subnormal!=Policy::Preserve){return 1;}
                Control original(read_control());
                if(original.rounding!=Mode::TowardNegativeInfinity ||
                   !original.trap_mask.empty() || original.subnormal==Policy::Preserve){return 2;}
                Status before(read_status());
                if(!before.flags.contains(Flag::Invalid) || !before.flags.contains(Flag::Overflow)){
                    return 3;
                }
                Control attempt(original);
                attempt.rounding=Mode::NearestTiesAway;
                Result first(install(attempt));
                match(first){
                    case Result::Ok{return 4;}
                    case Result::Err(ref error){
                        match(error){case Error::UnsupportedRounding{} case _{return 5;}}
                    }
                }
                attempt.rounding=Mode::TowardPositiveInfinity;
                Result second(install(attempt));
                match(second){
                    case Result::Ok{return 6;}
                    case Result::Err(ref error){
                        match(error){case Error::UnsupportedSubnormal{} case _{return 7;}}
                    }
                }
                Control kept(read_control());
                Status flags(read_status());
                if(kept.rounding!=original.rounding || kept.subnormal!=original.subnormal ||
                   !(flags.flags==before.flags)){return 8;}
                attempt.subnormal=Policy::Preserve;
                attempt.trap_mask=Flags(Flag::DivideByZero);
                Result installed(install(attempt));
                if(!installed.has_value()){return 9;}
                Status updated(read_status());
                if(!(updated.flags==before.flags)){return 10;}
                clear(Flags(Flag::Invalid));
                Status add;
                add.flags=Flags(Flag::Underflow) | Flags(Flag::Inexact);
                merge(add);
                Status merged(read_status());
                Control now(read_control());
                if(merged.flags.contains(Flag::Invalid) || !merged.flags.contains(Flag::Overflow) ||
                   !merged.flags.contains(Flag::Underflow) || !merged.flags.contains(Flag::Inexact) ||
                   now.rounding!=Mode::TowardPositiveInfinity ||
                   !now.trap_mask.contains(Flag::DivideByZero) || now.subnormal!=Policy::Preserve){return 11;}
                return one+half>one ? 42 : 12;
            }
        """
        host = """
            #include <xmmintrin.h>
            extern int inspect(float,float);
            int main(void){
                unsigned old=_mm_getcsr();
                _mm_setcsr(((old|0x1f80u)&~0x603fu)|0xa00bu);
                int outcome=inspect(1.f,0x1p-24f);
                unsigned actual=_mm_getcsr();
                _mm_setcsr(old);
                return outcome==42 && (actual&0xe07fu)==0x403au &&
                       (actual&0x1f80u)==0x1d80u ? 42 : outcome==42 ? 13 : outcome;
            }
        """
        self.assertEqual(self.program(source, host=host), 42)

    def test_floating_context_initializes_only_the_observed_root(self):
        source = """
            configuration {numeric.fp.initial_rounding=toward_negative_infinity;};
            alias Control=std::numeric::FPControl;
            alias Status=std::numeric::FPStatus;
            alias Mode=std::numeric::RoundingMode;
            alias Policy=std::numeric::SubnormalPolicy;
            Mode startup(){Control c(get_fp_control());return c.rounding;}
            Mode first(startup());
            f32 current(f32 a,f32 b){return a+b;}
            f32 local(f32 a,f32 b){return configured(numeric.fp.rounding=toward_negative_infinity)(a+b);}
            constexpr bool defaults(){Control c;Status s;
                return c.rounding==Mode::NearestTiesEven && c.subnormal==Policy::Preserve &&
                       c.trap_mask.empty() && s.flags.empty();}
            constexpr bool folded(defaults());
            i32 main(){
                f32 a(1.0);f32 half(0x1p-24);
                if(!folded || first!=Mode::TowardNegativeInfinity || current(a,half)!=a){return 1;}
                Control c(get_fp_control());c.rounding=Mode::TowardPositiveInfinity;
                if(!try_set_fp_control(c).has_value()){return 2;}
                return current(a,half)>a && local(a,half)==a && current(a,half)>a ? 42 : 3;
            }
        """
        self.assertEqual(self.program(source), 42)
        host = """
            #include <xmmintrin.h>
            extern int inspect(void);
            int main(void){unsigned old=_mm_getcsr();
              _mm_setcsr((old&~0x6000u)|0x4000u);int result=inspect();
              _mm_setcsr(old);return result;}
        """
        self.assertEqual(
            self.program(
                """
                configuration {numeric.fp.initial_rounding=toward_negative_infinity;};
                alias Mode=std::numeric::RoundingMode;
                extern "C" i32 inspect(){auto c(get_fp_control());
                    return c.rounding==Mode::TowardPositiveInfinity ? 42 : 1;}
                """,
                host=host,
            ),
            42,
        )
        for bad, diagnostic in (
            ("constexpr auto s(get_fp_status());", "require runtime evaluation"),
            (
                "void f(){configured(numeric.fp.initial_rounding=toward_zero){}}",
                "CFG001",
            ),
            ("[[effects(fp_control)]] void f(){get_fp_status();}", "fp_status"),
            ("void f(){clear_fp_status(0);}", "FPFlagSet"),
        ):
            with self.subTest(source=bad):
                result = self.compile(bad, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_floating_result_masks_local_flags_and_required_evaluation(self):
        source = """
            configuration {numeric.fp.trap_mask=[Invalid,DivideByZero,Overflow,Inexact];};
            alias Outcome=std::numeric::NumericResult<f32>;
            alias Code=std::numeric::NumericErrorCode;
            alias Flag=std::numeric::FPFlag;
            constexpr bool division(f32 divisor){
                Outcome outcome(std::numeric::try_div(f32(1.0),divisor));
                match(outcome){
                    case Outcome::Ok(value quotient,ref status){
                        return quotient==0.5 && status.fp_flags.empty();
                    }
                    case Outcome::Err(value code,ref status){
                        return code==Code::DivideByZero &&
                               status.fp_flags.contains(Flag::DivideByZero) &&
                               !status.value_inexact;
                    }
                }
            }
            constexpr bool folded(division(0.0) && division(2.0));
            extern "C" i32 inspect(f32 maximum){
                Outcome outcome(configured(numeric.fp.result_mask=[Inexact,Overflow])
                                (try_mul(maximum, f32(2.0))));
                match(outcome){
                    case Outcome::Ok(value product,ref status){return 1;}
                    case Outcome::Err(value code,ref status){
                        return folded && division(2.0) && division(0.0) &&
                            code==Code::Overflow && status.value_inexact &&
                            status.fp_flags.contains(Flag::Overflow) &&
                            status.fp_flags.contains(Flag::Inexact) ? 42 : 2;
                    }
                }
            }
            extern "C" i32 cpn_finite(f32 operand){
                Outcome outcome(configured(numeric.fp.require_finite=true)
                                (try_add(operand,f32(0.0))));
                match(outcome){
                    case Outcome::Ok(value sum,ref status){return 1;}
                    case Outcome::Err(value code,ref status){
                        return code==Code::NonFinite && status.fp_flags.empty() ? 42 : 2;
                    }
                }
            }
        """
        host = """
            #include <float.h>
            #include <math.h>
            #include <xmmintrin.h>
            extern int inspect(float),cpn_finite(float);
            int main(void){
                unsigned saved=_mm_getcsr();
                _mm_setcsr((saved | 0x1f80u) & ~0x3fu);
                _mm_setcsr(_mm_getcsr() | 0x4u);
                int ok=inspect(FLT_MAX)==42 && cpn_finite(NAN)==42;
                unsigned flags=_mm_getcsr() & 0x3du;
                _mm_setcsr(saved);
                return ok && flags==0x2cu ? 42 : 3;
            }
        """
        for preset in ("Debug", "Release"):
            with self.subTest(preset=preset):
                self.assertEqual(
                    self.program(source, "--preset=" + preset, host=host), 42
                )

    def test_checked_floating_uses_result_policy(self):
        self.assertEqual(
            self.program("""
                configuration {numeric.fp.trap_mask=[Inexact];};
                f32 divide(f32 x){return checked_div(x,f32(3.0));}
                i32 main(){return divide(1.0)>0.0 ? 42 : 1;}
            """),
            42,
        )
        self.assertEqual(
            self.program("""
                configuration {numeric.fp.trap_mask=[]; numeric.fp.result_mask=[Inexact];};
                f32 divide(f32 x){return checked_div(x,f32(3.0));}
                i32 main(){return divide(1.0)>0.0 ? 42 : 1;}
            """),
            -signal.SIGILL,
        )
        result = self.compile(
            "constexpr f32 bad(checked_div(f32(1.0), f32(0.0)));", "--check"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("floating operation traps in constant evaluation", result.stderr)

    def test_floating_reports_keep_the_default_value_when_result_would_fail(self):
        self.assertEqual(
            self.program("""
                configuration {numeric.fp.trap_mask=[DivideByZero];};
                alias Flag=std::numeric::FPFlag;
                constexpr f64 maximum(f64(0x1.fffffffffffffp1023));
                constexpr bool folded(){
                    auto report(report_div(f64(1.0),f64(0.0)));
                    return report.value > maximum &&
                           report.status.fp_flags.contains(Flag::DivideByZero);
                }
                constexpr bool observed(folded());
                bool divide(f64 divisor){
                    auto report(std::numeric::report_div(f64(1.0),divisor));
                    return report.value > maximum &&
                           report.status.fp_flags.contains(Flag::DivideByZero) &&
                           !report.status.value_inexact;
                }
                i32 main(){return observed && divide(0.0) ? 42 : 1;}
            """),
            42,
        )

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

    def test_named_floating_special_values_preserve_representation_and_flags(self):
        source = """
            configuration {numeric.fp.trap_mask=[Invalid];};
            alias Outcome=std::numeric::NumericResult<f32>;
            alias Code=std::numeric::NumericErrorCode;
            constexpr bool rejected(){
                Outcome r(try_signaling_nan<f32>(0));
                match(r){
                    case Outcome::Ok(value number,ref status){return false;}
                    case Outcome::Err(value code,ref status){
                        return code==Code::OutOfRange && status.fp_flags.empty();
                    }
                }
            }
            constexpr bool folded(rejected());
            extern "C" f32 signaling(u32 payload){return signaling_nan<f32>(payload,Negative);}
            extern "C" f64 quiet(u64 payload){return quiet_nan<f64>(payload);}
            extern "C" f64 negative_infinity(){return std::numeric::infinity<f64>(Negative);}
            extern "C" i32 rejects(i64 payload){
                Outcome r(try_quiet_nan<f32>(payload,Positive));
                match(r){
                    case Outcome::Ok(value number,ref status){return 1;}
                    case Outcome::Err(value code,ref status){
                        return folded && code==Code::OutOfRange && status.fp_flags.empty() ? 42 : 2;
                    }
                }
            }
        """
        host = """
            #include <stdint.h>
            #include <string.h>
            #include <xmmintrin.h>
            extern float signaling(uint32_t);
            extern double quiet(uint64_t), negative_infinity(void);
            extern int rejects(int64_t);
            int main(void) {
                unsigned saved=_mm_getcsr();
                _mm_setcsr((saved | 0x1f80u) & ~0x3fu);
                float s=signaling(0x3fffffu);
                double q=quiet(0x7ffffffffffffULL), i=negative_infinity();
                uint32_t sb; uint64_t qb, ib;
                memcpy(&sb,&s,sizeof s);
                memcpy(&qb,&q,sizeof q);
                memcpy(&ib,&i,sizeof i);
                int ok=sb==0xffbfffffu && qb==0x7fffffffffffffffULL &&
                       ib==0xfff0000000000000ULL && rejects(-1)==42 &&
                       rejects(0x400000)==42 && !(_mm_getcsr() & 0x3du);
                _mm_setcsr(saved);
                return ok ? 42 : 3;
            }
        """
        self.assertEqual(self.program(source, host=host), 42)
        self.assertEqual(
            self.program("""
                f32 make(u32 payload){return signaling_nan<f32>(payload);}
                i32 main(){make(0);return 42;}
            """),
            -signal.SIGILL,
        )
        for source in (
            "constexpr f32 wrong(signaling_nan<f32>(0));",
            "configuration {numeric.float.formats=[f64];}; f64 wrong(){return infinity<f32>();}",
            "f32 wrong(){return quiet_nan<f32>(1.5);}",
            "f32 wrong(){return infinity<f32>(true);}",
        ):
            with self.subTest(source=source):
                self.assertEqual(self.compile(source, "--check").returncode, 1)

    def test_closure_captures_and_mutable_receiver(self):
        self.assertEqual(
            self.program("""
            constraint Invocable<type F>{expression(F& fn,i32 arg){fn(arg) -> i32;}};
            generic<type F> requires(Invocable<F>) i32 invoke(F& fn,i32 v){return fn(v);}
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

    def test_constexpr_closure_owned_state_and_captureless_pointer(self):
        self.assertEqual(
            self.program("""
            alias Callback=function<i32(i32) noexcept>*;
            constexpr Callback callback([] i32(i32 n) noexcept {return n;});
            constexpr i32 compute() {
                i32 input(13);
                auto next([copy(input)] i32(i32 step) mutable {
                    copy += step;
                    return copy;
                });
                auto independent(next);
                i32 first(next(1));
                i32 second(next(2));
                return callback(first+second+independent(1)-2);
            }
            constexpr i32 total(compute());
            i32 main(){return total;}
            """),
            42,
        )

    def test_constexpr_closure_borrows_and_receiver(self):
        self.assertEqual(
            self.program("""
            struct Counter {
                i32 count;
                constexpr i32 advance() {
                    auto change([this] void(){this->count+=1;});
                    change();
                    return count;
                }
            };
            constexpr i32 compute() {
                i32 n(39);
                auto add([&n] void(){++n;});
                auto copy(add);
                add();
                copy();
                Counter C(n);
                return C.advance();
            }
            constexpr i32 total(compute());
            i32 main(){return total;}
            """),
            42,
        )

    def test_constexpr_closure_copy_runs_captured_copy_constructor(self):
        self.assertEqual(
            self.program("""
            struct Box {
                i32 value;
                Box(i32 n){init value(n);}
                Box(const<Box>& other){init value(other.value+1);}
            };
            constexpr i32 compute() {
                Box source(40);
                auto local([source] i32(){return source.value;});
                auto copy(local);
                return copy();
            }
            constexpr i32 folded(compute());
            i32 main(){return folded;}
            """),
            42,
        )

    def test_constexpr_closure_rejects_ended_and_published_addresses(self):
        for source in (
            """
            constexpr i32 compute() {
                const<i32>& ref(([n(42)] const<i32>&(){return n;})());
                return ref;
            }
            constexpr i32 bad(compute());
            """,
            """
            constexpr i32 compute() {
                i32* address(nullptr);
                {
                    i32 n(42);
                    auto view([&n] i32*(){return &n;});
                    address=view();
                }
                return *address;
            }
            constexpr i32 bad(compute());
            """,
            """
            constexpr i32 compute() {
                auto require_nonzero([] i32(i32 n)
                    [[requires(n!=0), ensures(return_value==n)]] {return n;});
                return require_nonzero(0);
            }
            constexpr i32 bad(compute());
            """,
            """
            consteval i32* expose() {
                i32 n(42);
                auto view([&n] i32*(){return &n;});
                return view();
            }
            constexpr i32* bad(expose());
            """,
            """
            constexpr i32 compute() {
                i32 n(42);
                auto invalid([n] i32(){++n;return n;});
                return invalid();
            }
            constexpr i32 bad(compute());
            """,
        ):
            with self.subTest(source=source):
                self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_closure_capture_borrow_lifetimes_across_calls(self):
        self.assertEqual(
            self.program("""
            i32 global(21);
            i32* address(i32& n) {
                auto get([&n] i32*(){return &n;});
                auto copy(get);
                return copy();
            }
            i32 main() {
                i32 local(21);
                return *address(local)+*address(global);
            }
            """),
            42,
        )
        for source in (
            """
            i32* leak() {
                i32 local(42);
                auto get([&local] i32*(){return &local;});
                auto copy(get);
                return copy();
            }
            """,
            """
            i32& leak() {
                i32 local(42);
                auto get([&local] i32&(){return local;});
                return get();
            }
            """,
            """
            const<i32>* leak() {
                i32 local(42);
                auto get([local] const<i32>*(){return &local;});
                return get();
            }
            """,
            """
            struct Box {
                i32 value;
                const<Box>* address() const {
                    auto get([this] const<Box>*(){return this;});
                    return get();
                }
            };
            const<Box>* leak() {Box local(42); return local.address();}
            """,
            """
            constraint Callback<type F> {
                expression(F& callback) { callback() -> i32*; }
            };
            generic<type F> requires(Callback<F>)
            i32* invoke(F& callback){return callback();}
            i32* leak() {
                i32 local(42);
                auto get([&local] i32*(){return &local;});
                return invoke(get);
            }
            """,
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("borrow of automatic storage escapes", result.stderr)

    def test_closure_captures_retain_checked_generation(self):
        source = """
            i32 main(){
                i32 n(42);
                auto get([&n] i32(){ return n; });
                auto copy(get);
                auto extent(storage_of(n));
                destroy(n);
                construct_at<i32>(extent,7);
                return copy();
            }
        """
        self.assertEqual(self.program(source), -signal.SIGILL)
        self.assertEqual(
            self.program("""
            i32 main(){
                i32* address(nullptr);
                {
                    i32 n(42);
                    auto get([&n] i32*(){return &n;});
                    address=get();
                }
                return *address;
            }
            """),
            -signal.SIGILL,
        )

    def test_closure_borrow_preserves_parameter_contracts(self):
        source = """
        [[noescape(n), returns_borrowed_from(n)]] i32* address(i32& n) {
            auto get([&n] i32*(){return &n;});
            return get();
        }
        i32 main(){i32 local(42); return *address(local);}
        """
        self.assertEqual(self.program(source), 42)
        retained = """
            i32* retained(nullptr);
            [[noescape(n)]] void bad(i32& n) {
                auto get([&n] i32*(){return &n;});
                retained=get();
            }
        """
        for rejected in (
            source.replace(", returns_borrowed_from(n)", ""),
            retained,
        ):
            result = self.compile(rejected, "--check")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("violates the declared parameter contract", result.stderr)
        cleared = retained.replace(
            "retained=get();", "retained=get();retained=nullptr;"
        )
        checked = self.compile(cleared, "--check")
        self.assertEqual(checked.returncode, 0, checked.stderr)

    def test_contract_predicate_type_binding(self):
        self.assertEqual(
            self.program("""
            alias item=i64;
            [[requires(sizeof(item)==sizeof(i32))]]
            i32 identity(i32 item){return item;}
            [[requires(sizeof(T)==alignof(T))]]
            generic<type T> i32 answer(T item)
                [[ensures(sizeof(item)==sizeof(T))]] {return 42;}
            i32 main(){return identity(answer(i32(0)));}
            """),
            42,
        )
        for source in (
            "alias F=function<void() [[requires(true)]]>*;",
            "[[requires(true,false)]] void f(){}",
            "struct S {[[invariant(true)]] Complete;};",
        ):
            with self.subTest(source=source):
                self.assertNotEqual(self.compile(source, "--check").returncode, 0)

    def test_closure_trailing_contract_attributes(self):
        source = """
            alias Identity=function<i32(i32) noexcept [[effects(none)]]>*;
            i32 main(){
                i32 captured(41);
                auto f([captured] i32(i32 n) mutable
                    [[effects(read(this),write(this)),requires(n!=captured),
                      ensures(return_value==captured)]] {
                    captured=n;
                    return captured;
                });
                Identity identity([] i32(i32 n) noexcept
                    [[effects(none),requires(true),ensures(true)]] {return n;});
                return identity(f(42));
            }"""
        self.assertEqual(self.program(source), 42)
        self.assertEqual(self.program(source.replace("f(42)", "f(41)")), -signal.SIGILL)
        for body, message in (
            ("auto f([] void() [[requires(missing)]] {});", "unknown name"),
            ("auto f([] i32() [[effects(none)]] {return trace;});", "effect"),
        ):
            with self.subTest(body=body):
                result = self.compile("i32 trace;void test(){" + body + "}", "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

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

    def test_eager_block_statics_bind_visible_static_objects_and_policies(self):
        self.assertEqual(
            self.program("""
                i32 trace;
                i32 first(i8 unused) { trace = trace * 10 + 1; return 40; }
                i32 second(i32 n) { trace = trace * 10 + 2; return n + 2; }
                i32 n(1);
                void never_called() {
                    alias Count = i32;
                    [[static_id("first")]] static Count n(first(i8(0)));
                    static Count& first_ref(n);
                    {
                        [[init_after(first_ref, n)]]
                        [[static_id("second")]]
                        static Count next(second(first_ref));
                        static i8 max(127);
                        configured(numeric.integer.overflow=wrapping)
                        [[init_after(max)]] static i8 wrapped(max + 1);
                        if (next == 0 || wrapped != -128) { return; }
                    }
                }
                i32 main() { return trace == 12 && n == 1 ? 42 : 1; }
            """),
            42,
        )

    def test_block_static_initializers_reject_hidden_globals_and_invalid_edges(self):
        for source, diagnostic in (
            (
                "i32 n(42);void f(i32 n){static i32 s(n);}",
                "automatic object is unavailable",
            ),
            (
                "i32 first(){return 42;} void f(i32 first){static i32 s(first());}",
                "automatic object is unavailable",
            ),
            (
                "i32 n(42);void f(i32 n){[[init_after(n)]] static i32 s;}",
                "does not name a static object",
            ),
            (
                "void f(){[[init_after(s)]] static i32 s;}",
                "cyclic static initialization",
            ),
            (
                'void f(){[[static_id("auto-object")]] i32 n;}',
                "require a storage modifier",
            ),
            (
                "void f(){static thread_local i32 n;}",
                "duplicate storage modifier",
            ),
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertEqual(result.returncode, 1)
                self.assertIn(diagnostic, result.stderr)

    def test_static_rank_uses_source_order_across_members_and_method_locals(self):
        self.assertEqual(
            self.program(
                """
                extern "C" { void note(i32 n); i32 observed(); }
                struct Item {
                    i32 n;
                    Item(i32 v) { init n(v); note(n); }
                    ~Item() { note(n); }
                };
                namespace lib {
                    struct Owner {
                        static Item first(1);
                        void never_called() {
                            [[init_after(first)]] static Item second(2);
                        }
                        static Item third(3);
                    };
                }
                i32 main() { return observed() == 123 ? 42 : 1; }
            """,
                host="""
                #include <stdlib.h>
                static int trace;
                void note(int n) { trace = trace * 10 + n; }
                int observed(void) { return trace; }
                __attribute__((destructor(101))) static void verify(void) {
                    if (trace != 123321) _Exit(2);
                }
            """,
            ),
            42,
        )
        rejected = self.compile(
            """
            struct Owner {
                void f() { [[init_after(later)]] static i32 local; }
                static i32 later;
            };
        """,
            "--check",
        )
        self.assertEqual(rejected.returncode, 1)
        self.assertIn("cyclic static initialization", rejected.stderr)

    def test_static_dependency_resolves_another_namespace_view_of_c_definition(self):
        self.assertEqual(
            self.program("""
                i32 seed() { return 40; }
                extern "C" {
                    namespace view { i32 shared; }
                    namespace owner { define i32 shared(seed()); }
                }
                [[init_after(view::shared)]] i32 answer(view::shared + 2);
                namespace lib {
                    generic<type T> i32 read() {
                        [[init_after(answer)]] static i32 saved(answer);
                        return saved;
                    }
                }
                namespace types { struct Argument {}; }
                i32 main() { return lib::read<types::Argument>(); }
            """),
            42,
        )

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
        for retirement in ("destroy(a);", "if(change){destroy(a);}else{abandon(a);}"):
            checked = self.compile(
                """
                i32 read(bool change){
                    i32 a(1);auto old(&a);auto storage(storage_of(a));
                    RETIRE
                    construct_at<i32>(storage,42);return *old;
                }
                """.replace("RETIRE", retirement),
                "--check",
            )
            self.assertEqual(checked.returncode, 1, checked.stderr)
            self.assertIn("ended object generation", checked.stderr)
        dynamic = """
            i32 read(bool change){
                i32 a(42);auto old(&a);auto storage(storage_of(a));
                if(change){destroy(a);construct_at<i32>(storage,1);}
                return *old;
            }
            i32 main(){return read(DECISION);}
        """
        self.assertEqual(self.program(dynamic.replace("DECISION", "false")), 42)
        self.assertEqual(
            self.program(dynamic.replace("DECISION", "true")), -signal.SIGILL
        )
        self.assertEqual(
            self.program("""
                i32 main(){
                    i32 a(1);auto old(&a);auto storage(storage_of(a));
                    destroy(a);old=construct_at<i32>(storage,42);return *old;
                }
            """),
            42,
        )
        self.assertEqual(
            self.program("""
                void redirect(i32*& cell,i32& target){cell=&target;}
                i32 main(){
                    i32 a(1);i32 next(42);auto old(&a);
                    destroy(a);redirect(old,next);return *old;
                }
            """),
            42,
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

    def test_virtual_owner_during_construction_and_replacement(self):
        types = """
          i32 trace;
          struct V{~V(){trace=trace*10+2;}};
          struct L:virtual V{Complete virtual_base<V>;
            ~L(){destroy_base<V>(this);trace=trace*10+9;}
            cleanup{trace=trace*10+3;}};
          struct R:virtual V{};
          void set(L& target){transfer_destruction<V>(target);}
          struct D:L,R{destruction_owner<V> = R; D(){set(*this);}};
          struct Outer{i32 pad;D d;};
        """
        self.assertEqual(
            self.program(
                types
                + """
              i32 main(){{Outer wrapper;auto s(storage_of(wrapper.d));destroy(wrapper.d);
                if(trace!=23){return 1;}construct_at<D>(s);}
                return trace==2323?42:0;}
            """
            ),
            42,
        )
        proved = self.compile(
            """
            struct V{V(i32 n){}};
            struct L:virtual V{L(){init virtual_base<V>(0);}};
            i32 early(L& target){transfer_destruction<V>(target);return 0;}
            struct D:L{D(){init virtual_base<V>(early(*this));}};
            i32 main(){D d;return 0;}
            """,
            "--check",
        )
        self.assertEqual(proved.returncode, 1)
        self.assertIn("LIFE002", proved.stderr)
        uncertain = """
            struct V{V(i32 n){}};
            struct L:virtual V{L(){init virtual_base<V>(0);}};
            struct Other:L{Other(){init virtual_base<V>(0);}};
            i32 early(L* target){transfer_destruction<V>(target);return 0;}
            struct D:L {
                D(L* alternate,bool safe){init virtual_base<V>(early(safe?alternate:this));}
            };
            i32 main(){Other other;D item(&other,DECISION);return 0;}
        """
        self.assertEqual(self.program(uncertain.replace("DECISION", "true")), 0)
        self.assertLess(self.program(uncertain.replace("DECISION", "false")), 0)

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
        frozen = self.compile(
            """
            struct V{};struct Layer:virtual V{~Layer(){transfer_destruction<V>(this);}};
            i32 main(){Layer d;return 0;}
            """,
            "--check",
        )
        self.assertNotEqual(frozen.returncode, 0)
        self.assertIn("LIFE005", frozen.stderr)
        invalid = self.compile(
            "struct V{};struct L:V{};void f(L& l){transfer_destruction<V>(l);}",
            "--check",
        )
        self.assertNotEqual(invalid.returncode, 0)
        self.assertIn("virtual base", invalid.stderr)

    def test_whole_rolls_back_completed_constructor_slots(self):
        source = """
            i32 trace;
            declare struct Outer;
            declare i32 request(Outer* owner);
            struct Parent{~Parent(){trace=trace*10+1;}};
            struct Stage{~Stage(){trace=trace*10+2;}};
            struct Future {
              Future(i32 mode){trace=trace*10+4;}
              ~Future(){trace=trace*10+5;}
            };
            struct Work {
              Stage finished;
              SLOTS
              CONSTRUCTOR
              ~Work(){trace=trace*10+9;}
            };
            struct Outer:Parent {
              Complete base<Parent>;
              ~Outer(){OBJECT trace=trace*10+7;}
              cleanup{trace=trace*10+3;}
            };
            i32 request(Outer* owner){destroy_base<Parent>(owner);return 0;}
            i32 main(){{Outer value;}return trace==123?42:1;}
        """
        ordinary = "Work(Outer* owner){request(owner);trace=trace*10+8;}"
        for slots, constructor, obj in (
            ("", ordinary, "Work partial(this);"),
            (
                "",
                "Work(Outer* owner){delegate(owner,42);trace=trace*10+8;}"
                "Work(Outer* owner,i32 n){request(owner);trace=trace*10+6;}",
                "Work partial(this);",
            ),
            (
                "i32 marker;",
                ordinary,
                "Work partial(this) -> {init marker(42);trace=trace*10+5;};",
            ),
            (
                "Future pending;",
                "Work(Outer* owner){init pending(request(owner));trace=trace*10+8;}",
                "Work partial(this);",
            ),
        ):
            with self.subTest(slots=slots, constructor=constructor, object=obj):
                self.assertEqual(
                    self.program(
                        source.replace("SLOTS", slots)
                        .replace("CONSTRUCTOR", constructor)
                        .replace("OBJECT", obj)
                    ),
                    42,
                )

    def test_whole_rolls_back_aggregate_array_and_tagged_payload_prefixes(self):
        source = """
            i32 trace;
            declare struct Outer;
            declare void request(Outer* owner);
            struct Parent{~Parent(){trace=trace*10+1;}};
            struct Stage{~Stage(){trace=trace*10+2;}};
            Outer* active;
            i32 count;
            WORK
            struct Outer:Parent {
              Complete base<Parent>;
              ~Outer(){active=this;OBJECT trace=trace*10+7;}
              cleanup{trace=trace*10+3;}
            };
            void request(Outer* owner){destroy_base<Parent>(owner);}
            i32 main(){{Outer value;}return trace==EXPECTED?42:1;}
        """
        explicit_array = """
            struct Work {
              Work(i32 step){if(step==2){request(active);}}
              ~Work(){trace=trace*10+2;}
            };
        """
        cases = {
            "explicit elements": (
                explicit_array,
                "Work[2] partial(Work(1),Work(2));",
                123,
            ),
            "empty prefix": (explicit_array, "Work[2] partial(Work(2),Work(1));", 13),
            "defaulted elements": (
                "struct Work{Work(){if(++count==2){request(active);}}"
                "~Work(){trace=trace*10+2;}};",
                "Work[3] partial;",
                123,
            ),
            "array copy": (
                "struct Work{Work(){}Work(const<Work>& other){if(++count==2){request(active);}}"
                "~Work(){trace=trace*10+2;}};",
                "Work[2] original;Work[2] partial(original);",
                12223,
            ),
            "aggregate": (
                "struct Work{Stage nested;Work(Outer* owner){request(owner);}"
                "~Work(){trace=trace*10+9;}};"
                "struct Aggregate{Stage first;Work pending;};",
                "Aggregate partial -> {init pending(active);};",
                1223,
            ),
            "memberwise copy": (
                "struct StageCopy{StageCopy(){}StageCopy(const<StageCopy>& other){}"
                "~StageCopy(){trace=trace*10+2;}};"
                "struct PendingCopy{PendingCopy(){}PendingCopy(const<PendingCopy>& other)"
                "{request(active);}~PendingCopy(){trace=trace*10+8;}};"
                "struct Work{StageCopy first;PendingCopy second;Work(const<Work>& other)=default;"
                "~Work(){trace=trace*10+9;}};",
                "Work original;Work partial(original);",
                129823,
            ),
            "tagged case": (
                "struct Pending{Pending(i32 code){request(active);}"
                "~Pending(){trace=trace*10+8;}};"
                "union Work{case Chosen(Stage first,Pending second);"
                "~Work(){trace=trace*10+9;}};",
                "Work partial(Work::Chosen(Stage(),Pending(1)));",
                123,
            ),
            "tagged copy": (
                "struct StageCopy{StageCopy(){}StageCopy(const<StageCopy>& other){}"
                "~StageCopy(){trace=trace*10+2;}};"
                "struct PendingCopy{PendingCopy(){}PendingCopy(const<PendingCopy>& other)"
                "{request(active);}~PendingCopy(){trace=trace*10+8;}};"
                "union Work{case Chosen(StageCopy first,PendingCopy second);"
                "Work(const<Work>& other)=default;~Work(){trace=trace*10+9;}};",
                "Work original(Work::Chosen(StageCopy(),PendingCopy()));Work partial(original);",
                129823,
            ),
            "authored tagged constructor": (
                "union Work{default case Chosen(Stage value);"
                "Work(i32 step){request(active);trace=trace*10+8;}"
                "~Work(){trace=trace*10+9;}};",
                "Work partial(1);",
                123,
            ),
        }
        for name, (work, obj, expected) in cases.items():
            with self.subTest(name=name):
                self.assertEqual(
                    self.program(
                        source.replace("WORK", work)
                        .replace("OBJECT", obj)
                        .replace("EXPECTED", str(expected))
                    ),
                    42,
                )

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

    def test_serial_core_configuration_and_logical_root_identity(self):
        source = "i32 main(){return 42;}"
        policy = r"""configuration {
            target="x86_64\u{2d}linux-gnu";
            source.unicode_version="17.0.\u{30}";
            exceptions.language=false;
            generic.higher_kinds=false;
            generic.associated_entities=false;
            static.schedule=serial;
            static.workers=1;
            static.identity_namespace="compiler\u{2d}test";
        };"""
        outputs = []
        for project in ("checkout-a", "checkout-b"):
            folder = self.dir / project
            subdir = folder / "src"
            subdir.mkdir(parents=True)
            config = folder / "cpn.config"
            config.write_text(policy, encoding="utf-8")
            code = subdir / "root.cpn"
            code.write_text(source, encoding="utf-8")
            result = subprocess.run(
                [*DRIVER, "--std=CPN26", "-S", "--config", config, code],
                capture_output=True,
                text=True,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            outputs.append(code.with_suffix(".ll").read_text(encoding="utf-8"))
        self.assertEqual(outputs[0], outputs[1])
        self.assertIn('source_filename = "src/root.cpn"', outputs[0])

        result = self.compile(
            source,
            "-S",
            "--root-id=test-root",
            "--logical-source=source/sub/../main.cpn",
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        ir = self.src.with_suffix(".ll").read_text(encoding="utf-8")
        self.assertIn("; ModuleID = 'test-root'", ir)
        self.assertIn('source_filename = "source/main.cpn"', ir)
        for path in ("/absolute.cpn", "../outside.cpn", "nested/../../outside.cpn", ""):
            with self.subTest(path=path):
                result = self.compile(source, "--check", "--logical-source=" + path)
                self.assertEqual(result.returncode, 1)
                self.assertIn("logical source path", result.stderr)

        config = self.dir / "cpn.config"
        for setting, code in (
            ("exceptions.language=true", "CFG002"),
            ("generic.higher_kinds=true", "CFG002"),
            ("static.schedule=custom_parallel", "CFG002"),
            ("static.schedule=unknown", "CFG001"),
            ("static.workers=2", "CFG001"),
            ('static.identity_namespace=""', "CFG001"),
            ("static.identity_namespace=unquoted", "CFG001"),
        ):
            with self.subTest(setting=setting):
                config.write_text("configuration {" + setting + ";};", encoding="utf-8")
                result = self.compile(source, "--check", "--config", config)
                self.assertEqual(result.returncode, 1)
                self.assertIn(code, result.stderr)

    def test_custom_preset_materialization_and_inherited_bindings(self):
        self.assertEqual(
            self.program(
                """
                i32 main() {
                    auto n(42);
                    auto value(1.0);
                    if (sizeof(n)==4 && sizeof(value)==8) { return n; }
                    return 0;
                }
                """,
                "--preset=Custom",
            ),
            42,
        )
        config = self.dir / "cpn.config"
        config.write_text(
            "configuration { numeric.integer.overflow=wrapping; };",
            encoding="utf-8",
        )
        self.assertEqual(
            self.program(
                """
                configuration {
                    preset=Custom;
                    numeric.literal.integer_default=i16;
                    numeric.float.formats=[f32];
                    numeric.literal.real_default=f32;
                };
                i32 main() {
                    i8 last(127);
                    ++last;
                    auto n(42);
                    auto value(1.0);
                    if(last==-128 && sizeof(n)==2 && sizeof(value)==4) {
                        return n;
                    }
                    return 0;
                }
                """,
                "--config",
                str(config),
            ),
            42,
        )
        restricted = """
            configuration {
                preset=Custom;
                numeric.integer.widths=[8];
                numeric.float.formats=[f32];
            };
        """
        result = self.compile(
            restricted
            + """
              generic<type T> i8 fixed(T n) { return 0; }
              i8 fixed(i8 n) { return n; }
              void f(){ i8 n(fixed(42)); f32 v(1.0); }
            """,
            "--check",
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        for excerpt, diagnostic in (
            (restricted + "void f(){auto n(42);}", "i32 is disabled"),
            (restricted + "void f(){auto v(1.0);}", "f64 is disabled"),
            (restricted + "void f(){auto n(~42);}", "i32 is disabled"),
            ("configured(preset=Custom) void f(){}", "CFG001"),
            ("configuration { preset=custom; };", "CFG001"),
            ("configuration { numeric.float.formats=[f32,f32]; };", "CFG001"),
            ("configuration { numeric.float.formats=[f128]; };", "CFG002"),
            ("configuration { numeric.fp.profile=unknown; };", "CFG001"),
            ("configuration { numeric.fp.profile=reproducible; };", "CFG002"),
        ):
            with self.subTest(source=excerpt):
                result = self.compile(excerpt, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

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
        views = """
            struct Pair{i32 n;};
            i32 read(bool replace){
                Pair p; auto inner(storage_of(p.n)); auto outer(storage_of(p));
                if(REPLACE){destroy(p);construct_at<Pair>(outer);}
                return inner.capacity_bytes()==usize(4) ? 42 : 1;
            }
            i32 main(){return read(INPUT);}
        """
        expired = views.replace("REPLACE", "true").replace("INPUT", "true")
        for use in (
            "return inner.capacity_bytes()==usize(4) ? 42 : 1;",
            "construct_at<i32>(inner,42);return 1;",
        ):
            checked = self.compile(
                expired.replace(
                    "return inner.capacity_bytes()==usize(4) ? 42 : 1;", use
                ),
                "--check",
            )
            self.assertEqual(checked.returncode, 1, checked.stderr)
            self.assertIn("ended containing generation", checked.stderr)
        dynamic = views.replace("REPLACE", "replace")
        self.assertEqual(self.program(dynamic.replace("INPUT", "false")), 42)
        self.assertEqual(self.program(dynamic.replace("INPUT", "true")), -signal.SIGILL)

    def test_const_static_objects_retain_independent_storage_authority(self):
        source = """
            const i32 first(18);
            constexpr i32 second(24);
            extern "C" define const i32 exposed(7);
            constexpr i32 original_sum(18+second);
            i32 read_second(){return second;}
            i32 main(){
                if(original_sum!=42){return 3;}
                auto a(storage_of(first));
                auto b(storage_of(second));
                auto c(storage_of(exposed));
                if (a.capacity_bytes()!=usize(4) || a.identity()==b.identity()) {return 1;}
                destroy(first);
                destroy(second);
                destroy(exposed);
                auto current(construct_at<i32>(a,33));
                auto another(construct_at<i32>(b,2));
                auto linked(construct_at<i32>(c,7));
                return *current+*another+*linked;
            }
        """
        for preset in ("Debug", "Release"):
            with self.subTest(preset=preset):
                self.assertEqual(self.program(source, "--preset", preset), 42)
        stale = self.compile(
            source.replace("return *current+*another+*linked;", "return second;"),
            "--check",
        )
        self.assertEqual(stale.returncode, 1, stale.stderr)
        self.assertIn("ended object generation", stale.stderr)
        dynamic = source.replace(
            "return *current+*another+*linked;", "return read_second();"
        )
        self.assertEqual(self.program(dynamic), -signal.SIGILL)
        branching = """
            const i32 stored(42);
            i32 read(bool retire){
                if (retire) {destroy(stored);}
                return stored;
            }
            i32 main(){return read(false);}
        """
        self.assertEqual(self.program(branching), 42)
        all_ended = self.compile(
            branching.replace(
                "{destroy(stored);}", "{destroy(stored);}else{destroy(stored);}"
            ),
            "--check",
        )
        self.assertEqual(all_ended.returncode, 1, all_ended.stderr)
        self.assertIn("ended object generation", all_ended.stderr)
        aggregate = """
            i32[2] stored(1,42);
            i32 main(){
                auto old(&stored[0]);
                auto extent(storage_of(stored[0]));
                destroy(stored[0]);construct_at<i32>(extent,3);
                return EXPR;
            }
        """
        for expr in ("stored[0]", "*old"):
            with self.subTest(expr=expr):
                checked = self.compile(aggregate.replace("EXPR", expr), "--check")
                self.assertEqual(checked.returncode, 1, checked.stderr)
                self.assertIn("ended object generation", checked.stderr)
        self.assertEqual(self.program(aggregate.replace("EXPR", "stored[1]")), 42)
        invalid = self.compile(
            "i32 main(){i32 local; auto view(storage_of(local));"
            "transfer_storage(view,view);return 0;}",
            "--check",
        )
        self.assertEqual(invalid.returncode, 1, invalid.stderr)
        self.assertIn("exclusive storage authority", invalid.stderr)

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

    def test_destructor_abandon_ends_aliased_member_generation(self):
        self.assertEqual(
            self.program("""
            i32 observed;
            void read(i32* p) { observed=*p; }
            struct Owner {
                i32 item(42);
                ~Owner() { auto saved(&item); abandon(item); read(saved); }
            };
            i32 main() { { Owner owner; } return observed; }
            """),
            -signal.SIGILL,
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
        replaced = """
            i32 main(){
                i32[2] values(10,42);
                auto old(&values[0]);
                auto next(&values[1]);
                destroy(values[0]);construct_at<i32>(storage_of(values[0]),1);
                return EXPR;
            }
        """
        for expr in ("*old", "values[0]"):
            with self.subTest(expr=expr):
                stale = self.compile(replaced.replace("EXPR", expr), "--check")
                self.assertEqual(stale.returncode, 1, stale.stderr)
                self.assertIn("ended object generation", stale.stderr)
        self.assertEqual(self.program(replaced.replace("EXPR", "*next")), 42)
        stale = self.compile(
            """
            struct Pair {i32 first(1);i32 next(42);};
            i32 read(bool change){
                Pair p;
                auto extent(storage_of(p.first));
                if(change){destroy(p.first);}else{abandon(p.first);}
                construct_at<i32>(extent,3);
                return p.first;
            }
            """,
            "--check",
        )
        self.assertEqual(stale.returncode, 1, stale.stderr)
        self.assertIn("ended object generation", stale.stderr)
        dynamic = """
            i32 read(bool change){
                i32[2] values(42,10);
                if(change){destroy(values[0]);}
                return values[0];
            }
            i32 main(){return read(DECISION);}
        """
        self.assertEqual(self.program(dynamic.replace("DECISION", "false")), 42)
        self.assertEqual(
            self.program(dynamic.replace("DECISION", "true")), -signal.SIGILL
        )
        self.assertEqual(
            self.program("""
                struct Pair {i32 first(42);};
                i32 main(){
                    Pair p;
                    destroy(p.first);
                    auto extent(storage_of(p));
                    destroy(p);
                    return construct_at<Pair>(extent)->first;
                }
            """),
            42,
        )
        nested = """
            struct Box {i32[2] items(1,42);};
            i32 main(){
                Box box;
                auto saved(&box.items[0]);
                auto extent(storage_of(box.items[0]));
                destroy(box.items[0]);construct_at<i32>(extent,3);
                return EXPR;
            }
        """
        for expr in ("*saved", "box.items[0]"):
            with self.subTest(expr=expr):
                checked = self.compile(nested.replace("EXPR", expr), "--check")
                self.assertEqual(checked.returncode, 1, checked.stderr)
                self.assertIn("ended object generation", checked.stderr)
        self.assertEqual(self.program(nested.replace("EXPR", "box.items[1]")), 42)
        helper = """
            void finish(i32& value,bool flag){
                if(flag){destroy(value);}else{abandon(value);}
            }
            void forward_finish(i32& value,bool flag){finish(value,flag);}
            i32 read(bool flag){
                i32[2] values(1,42);
                CALL(values[0],flag);
                return EXPR;
            }
            i32 main(){return read(false);}
        """
        for callee in ("finish", "forward_finish"):
            checked = self.compile(
                helper.replace("CALL", callee).replace("EXPR", "values[0]"),
                "--check",
            )
            self.assertEqual(checked.returncode, 1, checked.stderr)
            self.assertIn("ended object generation", checked.stderr)
        helper = helper.replace("CALL", "forward_finish")
        self.assertEqual(self.program(helper.replace("EXPR", "values[1]")), 42)
        conditional_helper = helper.replace("else{abandon(value);}", "")
        conditional_helper = conditional_helper.replace("values(1,42)", "values(42,1)")
        conditional_helper = conditional_helper.replace("EXPR", "values[0]")
        self.assertEqual(self.program(conditional_helper), 42)
        self.assertEqual(
            self.program(conditional_helper.replace("read(false)", "read(true)")),
            -signal.SIGILL,
        )
        pointer_helper = (
            helper.replace("i32& value", "i32* value")
            .replace("destroy(value)", "destroy(*value)")
            .replace("abandon(value)", "abandon(*value)")
            .replace("forward_finish(values[0]", "forward_finish(&values[0]")
        )
        stale = self.compile(pointer_helper.replace("EXPR", "values[0]"), "--check")
        self.assertEqual(stale.returncode, 1, stale.stderr)
        self.assertIn("ended object generation", stale.stderr)
        self.assertEqual(self.program(pointer_helper.replace("EXPR", "values[1]")), 42)
        indirect = pointer_helper.replace(
            "forward_finish(&values[0],flag);",
            "function<void(i32*,bool)>* selected(&forward_finish);"
            "selected(&values[0],flag);",
        )
        stale = self.compile(indirect.replace("EXPR", "values[0]"), "--check")
        self.assertEqual(stale.returncode, 1, stale.stderr)
        self.assertIn("ended object generation", stale.stderr)
        self.assertEqual(self.program(indirect.replace("EXPR", "values[1]")), 42)
        dispatch = """
            void finish(i32* value){destroy(*value);}
            void observe(i32* value){}
            i32 read(bool pick){
                i32[2] values(42,1);
                function<void(i32*)>* selected(&observe);
                if(pick){selected=&finish;}
                selected(&values[0]);
                return values[0];
            }
            i32 main(){return read(INPUT);}
        """
        self.assertEqual(self.program(dispatch.replace("INPUT", "false")), 42)
        self.assertEqual(
            self.program(dispatch.replace("INPUT", "true")), -signal.SIGILL
        )
        rebound = """
            void finish(i32* value,i32* other){
                value=other;
                destroy(*value);
            }
            i32 main(){
                i32[2] values(42,1);
                auto pointer(&values[0]);
                pointer=&values[1];
                finish(&values[0],pointer);
                return values[INDEX];
            }
        """
        self.assertEqual(self.program(rebound.replace("INDEX", "0")), 42)
        stale = self.compile(rebound.replace("INDEX", "1"), "--check")
        self.assertEqual(stale.returncode, 1, stale.stderr)
        self.assertIn("ended object generation", stale.stderr)
        ambiguous = """
            void finish(i32* value,i32* other,bool pick){
                if(pick){value=other;}
                destroy(*value);
            }
            i32 run(bool pick){
                i32[2] values(1,42);
                finish(&values[0],&values[1],pick);
                return values[1];
            }
            i32 main(){return run(INPUT);}
        """
        self.assertEqual(self.program(ambiguous.replace("INPUT", "false")), 42)
        self.assertEqual(
            self.program(ambiguous.replace("INPUT", "true")), -signal.SIGILL
        )

    def test_storage_view_after_ending_complete_object(self):
        self.assertEqual(
            self.program("""
            i32 main(){i32 n(5);destroy(n);
                       auto replacement(construct_at<i32>(storage_of(n),42));
                       return *replacement;}"""),
            42,
        )
        for setup, extent in (
            ("", "storage_of(values[0])"),
            ("auto view(storage_of(values[0]));", "view"),
            ("observe();", "storage_of(values[0])"),
            ("abandon(values[1]);", "storage_of(values[0])"),
            ("destroy(values[1]);", "storage_of(values[0])"),
        ):
            checked = self.compile(
                "void observe(){} i32 main(){i32[2] values(10,42);"
                + setup
                + "construct_at<i32>("
                + extent
                + ",1);return 42;}",
                "--check",
            )
            self.assertEqual(checked.returncode, 1, checked.stderr)
            self.assertIn("storage contains a live generation", checked.stderr)
        conditional = """
            i32 read(bool retire) {
                i32[2] values(1,2);
                auto view(storage_of(values[0]));
                if(retire){destroy(values[0]);}
                return *construct_at<i32>(view,42);
            }
            i32 main(){return read(INPUT);}
        """
        self.assertEqual(self.program(conditional.replace("INPUT", "true")), 42)
        self.assertEqual(
            self.program(conditional.replace("INPUT", "false")), -signal.SIGILL
        )
        self.assertEqual(
            self.program("""
                void retire(i32& value){destroy(value);}
                i32 main(){
                    i32[2] values(1,2);
                    auto view(storage_of(values[0]));
                    retire(values[0]);
                    return *construct_at<i32>(view,42);
                }
            """),
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

    def test_aggregate_frontier_identity_and_candidate_selection(self):
        self.assertEqual(
            self.program("""
            i32 trace; i32 drops;
            struct Base{Base(){trace=1;}};
            struct Self{Self* addr; i32 n; Self(i32 v){init addr(this);init n(v);trace=trace*10+v;}
              Self(const<Self>& s){init addr(this);init n(s.n);} ~Self(){++drops;}
            };
            Self make(i32 n){return Self(n);}
            struct Row:Base{Self a;Self b;};
            struct One{Self x;};
            struct Choice{i32 value;Choice(bool flag){init value(flag?7:9);}};
            i32 main(){
              i32 a(2);Row row(make(a),make(3));
              if(trace!=123 || row.a.addr!=&row.a || row.b.addr!=&row.b || drops!=0){return 1;}
              One o(make(4));if(o.x.addr!=&o.x){return 2;}
              Choice exact(20);Choice authored(true);return exact.value+authored.value+15;
            }"""),
            42,
        )

    def test_array_value_results_and_generated_default_loop(self):
        self.assertEqual(
            self.program("""
            struct Self{Self* addr;Self(){init addr(this);}Self(const<Self>& s){init addr(this);}};
            Self[2] make(){Self[2] original;return original;}
            i32 last(i32[70000]& values){return values[69999];}
            i32 main(){Self[2] values(make());
              if(values[0].addr!=&values[0] || values[1].addr!=&values[1]){return 1;}
              i32[70000] many(7);i32[0] e;i32[0] f(e);return 42+last(many);
            }"""),
            42,
        )

    def test_delegated_value_parameters_use_final_address(self):
        self.assertEqual(
            self.program("""
            i32 good; i32 drops;
            struct Self{Self* addr;Self(){init addr(this);}
              Self(const<Self>& s){init addr(this);} ~Self(){++drops;}};
            struct Holder{i32 n;
              Holder(){delegate(Self());}
              Holder(Self s){if(s.addr==&s){++good;}}
            };
            i32 main(){Holder a; Holder b(Self())-> {init n(40);};
              if(drops!=2){return 1;}return good+b.n;}
            """),
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

    def test_cleanup_validates_frontier_and_rejects_member_abandon(self):
        source = """
            i32 trace;
            struct Item {i32 id;~Item(){trace=trace*10+id;}};
            class Manual Pair {
            public:
                Item first(2); Item second(4);
                ~Pair() {} cleanup { ACTION }
            };
            i32 main(){{Pair value;}return trace;}
        """
        self.assertEqual(self.program(source.replace("ACTION", "destroy(first);")), -4)
        self.assertEqual(
            self.program(
                source.replace("ACTION", "Item& selected(first);destroy(selected);")
            ),
            -4,
        )
        self.assertEqual(
            self.program(source.replace("ACTION", "destroy(second);destroy(first);")),
            42,
        )
        after_end = source.replace("ACTION", "destroy(first);")
        self.assertEqual(
            self.program(
                after_end.replace("Pair value;", "Pair value;destroy(value.second);")
            ),
            42,
        )
        result = self.compile(source.replace("ACTION", "abandon(second);"), "--check")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("LIFE005", result.stderr)

    def test_native_manual_cleanup_retires_registered_replacement(self):
        self.assertEqual(
            self.program("""
                i32 trace;
                struct Seed { ~Seed(){trace=trace*10+4;} };
                struct New { ~New(){trace=trace*10+2;} };
                class Manual Pair {
                public:
                    Seed field;
                    ~Pair(){auto storage(storage_of(field));destroy(field);construct_at<New>(storage);}
                    cleanup{trace=trace*10+1;}
                };
                i32 main(){ {Pair value;} return trace==412?42:1; }
            """),
            42,
        )

    def test_consteval_cleanup_proves_reverse_frontier_violation(self):
        result = self.compile(
            """
            class Manual Pair {
            public:
                i32 first(2); i32 second(4);
                ~Pair() {} cleanup {destroy(first);}
            };
            consteval i32 evaluated(){Pair p;return 42;}
            constexpr i32 trigger(evaluated());
        """,
            "--check",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("LIFE005", result.stderr)

    def test_cleanup_can_observe_storage_of_ended_automatic_members(self):
        source = """
            i32 seen;
            struct Pair { i32 finished(42); ~Pair() {} cleanup { ACTION } };
            i32 main(){ {Pair value;}return seen; }
        """
        self.assertEqual(
            self.program(
                source.replace(
                    "ACTION",
                    "auto view(storage_of(finished));"
                    "if(view.capacity_bytes()==4){seen=42;}",
                )
            ),
            42,
        )
        result = self.compile(source.replace("ACTION", "seen=finished;"), "--check")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("LIFE002", result.stderr)

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
                "i32 f(){i32 a; i32& prior(a);auto view(storage_of(a));"
                "destroy(a);construct_at<i32>(view,42);return prior;}",
                "ended object generation",
            ),
            (
                "i32 f(){ i32 a; auto p(&a); destroy(a); return *p; }",
                "ended object generation",
            ),
            (
                "i32 f(){ i32 x; auto s(storage_of(x)); construct_at<i32>(s,4); return 0; }",
                "live generation",
            ),
            (
                "void f(bool side){i32 x; auto view(storage_of(x)); destroy(x);"
                "if(side){construct_at<i32>(view,1);}else{construct_at<i32>(view,2);}"
                "construct_at<i32>(view,3);}",
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

    def test_value_contracts_bind_at_declaration_and_check_at_completion(self):
        self.assertEqual(
            self.program("""
                i32 destroyed;
                struct Guard { ~Guard() { destroyed = 1; } };
                [[requires(value > 0), ensures(destroyed == 1),
                  ensures(return_value == value)]]
                declare i32 echo(i32 value);
                i32 echo(i32 renamed) { Guard local; return renamed; }
                i32 main() { return echo(42); }
            """),
            42,
        )
        self.assertEqual(
            self.program("""
                [[ensures(return_value > 0)]] i32 f() { return 0; }
                i32 main() { return f(); }
            """),
            -signal.SIGILL,
        )
        self.assertEqual(
            self.program(
                """
                [[requires(false), ensures(false)]] i32 f() { return 42; }
                i32 main() { return f(); }
                """,
                "--preset",
                "Release",
            ),
            42,
        )

    def test_contract_predicates_require_bool_and_admitted_operations(self):
        for source, message in [
            ("[[requires(n)]] declare i32 f(i32 n);", "requires bool"),
            ("[[requires((n = 1) == 1)]] declare i32 f(i32 n);", "mutate"),
            ("[[requires(return_value > 0)]] declare i32 f();", "return_value"),
            ("[[requires(n + 1 > 0)]] declare i32 f(i32 n);", "numeric"),
            (
                "[[ensures(false)]] consteval i32 f() { return 1; } "
                "constexpr i32 n(f());",
                "ensures #1",
            ),
        ]:
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_nonraising_float_contract_predicate(self):
        source = """
            [[requires(n == -0.0)]] f64 same(f64 n) { return n; }
            i32 main() { return same(0.0) == 0.0 ? 42 : 0; }
        """
        self.assertEqual(self.program(source), 42)
        result = self.compile(source, "-S")
        self.assertEqual(result.returncode, 0, result.stderr)
        module = self.src.with_suffix(".ll").read_text()
        family = f"@cpn.v1.fn.{self.src.name.encode().hex()}.{'same'.encode().hex()}."
        body = module.split(family, 1)[1].split("}", 1)[0]
        self.assertNotIn("fcmp", body)

    def test_prove_contracts_use_parameter_and_control_flow_facts(self):
        source = """
            configured(contracts.validation=prove)
            [[ensures(return_value==x)]]
            i32 identity(i32 x){return x;}
            configured(contracts.validation=prove)
            [[ensures(return_value>0)]]
            i32 positive(i32 x){
                if(x>0){return x;}
                if(false){return -1;}
                return 1;
            }
            i32 main(){return identity(positive(42));}
        """
        self.assertEqual(self.program(source), 42)
        module = self.src.with_suffix(".ll").read_text()
        self.assertNotIn("contract.prove", module)
        self.assertNotIn("call void @llvm.trap(", module)
        bad = self.compile(
            """
            configured(contracts.validation=prove)
            [[ensures(return_value==x)]]
            i32 mutate(i32 x){i32 original(x); x=0; return original;}
            """,
            "--check",
        )
        self.assertNotEqual(bad.returncode, 0)
        self.assertIn("cannot establish mutate ensures #1", bad.stderr)

    def test_prove_contracts_compose_ordered_scalar_relations(self):
        source = """
            configured(contracts.validation=prove)
            [[ensures(return_value<=upper)]]
            i32 bounded(i32 value,i32 middle,i32 next,i32 upper){
                i32 retries(2);
                while(retries>0){
                    if(value<=middle && middle<=next && next<=upper){return value;}
                    --retries;
                }
                return upper;
            }
            configured(contracts.validation=prove)
            [[ensures(return_value<=upper)]]
            u32 unsigned_bound(u32 value,u32 middle,u32 upper){
                if(value>middle || middle>upper){return upper;}
                return value;
            }
            i32 main(){
                if(unsigned_bound(u32(0x80000000),u32(0x80000001),u32(0xffffffff))
                   !=u32(0x80000000)){return 1;}
                return bounded(42,43,44,45);
            }
        """
        self.assertEqual(self.program(source), 42)
        for condition, returned in (
            ("value<=middle || middle<=upper", "return value;"),
            ("value<middle && middle<=upper", "upper=value; return middle;"),
        ):
            with self.subTest(condition=condition, returned=returned):
                r = self.compile(
                    "configured(contracts.validation=prove) "
                    "[[ensures(return_value<=upper)]] "
                    "i32 partial(i32 value,i32 middle,i32 upper){"
                    f"if({condition}){{{returned}}} return upper;}}",
                    "--check",
                )
                self.assertEqual(r.returncode, 1)
                self.assertIn("cannot establish partial ensures #1", r.stderr)

    def test_virtual_contract_override_composes_ordered_scalar_relations(self):
        source = """
            struct Base {
                virtual i32 f(i32 low,i32 middle,i32 high)
                    [[requires(low<middle && middle<=high),
                      ensures(return_value<=high)]] {return low;}
            };
            struct Derived:Base {
                i32 f(i32 low,i32 middle,i32 high)
                    [[requires(low<high), ensures(return_value<middle),
                      ensures(middle<=high)]] override {return low;}
            };
            i32 dispatch(Base& object){return object.f(42,43,44);}
            i32 main(){Derived object;return dispatch(object);}
        """
        self.assertEqual(self.program(source), 42)
        r = self.compile(source.replace("low<middle", "low<=middle"), "--check")
        self.assertEqual(r.returncode, 1)
        self.assertIn("precondition implication", r.stderr)

    def test_virtual_contract_override_proves_logical_implication(self):
        source = """
            struct Base {
                i32 limit;
                virtual i32 evaluate(i32 n)
                    [[requires(n>0), requires(limit>=2),
                      ensures(return_value>=0)]] {return n;}
            };
            struct Derived: Base {
                i32 evaluate(i32 input)
                    [[requires(input>=0 && this->limit>=1),
                      ensures(return_value>0)]] override {return 42;}
            };
            i32 via(Base& subject){return subject.evaluate(1);}
            i32 main(){Derived value;value.limit=2;return via(value);}
            """
        for inheritance in ("Base", "virtual Base"):
            with self.subTest(inheritance=inheritance):
                self.assertEqual(
                    self.program(
                        source.replace("Derived: Base", "Derived: " + inheritance)
                    ),
                    42,
                )

    def test_virtual_contract_override_rejects_unproved_implication(self):
        for source, diagnostic in (
            (
                """
                struct Base {
                    virtual i32 f(i32 n) [[requires(n>=0)]] {return n;}
                };
                struct Derived: Base {
                    i32 f(i32 n) [[requires(n>0)]] override {return n;}
                };
                """,
                "precondition implication",
            ),
            (
                """
                struct Base {
                    virtual i32 f() [[ensures(return_value>0)]] {return 1;}
                };
                struct Derived: Base {
                    i32 f() [[ensures(return_value>=0)]] override {return 0;}
                };
                """,
                "postcondition implication",
            ),
            (
                """
                struct Base {
                    i32 field;
                    virtual i32 f() [[requires(field>0)]] {return 1;}
                };
                struct Derived: Base {
                    i32 field;
                    i32 f() [[requires(field>0)]] override {return 1;}
                };
                """,
                "precondition implication",
            ),
            (
                """
                struct First {
                    virtual i32 f(i32 n) [[requires(n>0)]] {return n;}
                };
                struct Second {
                    virtual i32 f(i32 n) [[requires(n>=0)]] {return n;}
                };
                struct Both: First, Second {
                    i32 f(i32 n) [[requires(n>0)]] override {return n;}
                };
                """,
                "Second::f",
            ),
        ):
            with self.subTest(diagnostic=diagnostic):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_result_queries_and_receiver_qualified_references(self):
        self.assertEqual(
            self.program("""
                alias R = std::Result<i32,i16>;
                alias Empty = std::Result<void,i16>;
                alias ConstPayload = std::Result<const<i32>,i16>;
                constexpr i32 answer() {
                    R r(R::Ok(40));
                    i32& item(r.value());
                    item += 2;
                    return r.has_value() && !r.has_error() ? r.value() : 1;
                }
                constexpr i32 constant_answer(answer());
                [[effects(read(r))]]
                bool successful(const<R>& r) { return r.has_value(); }
                [[effects(read(r),trap(contract))]]
                i32 checked(const<R>& r) { return r.value(); }
                i32 main() {
                    R value(R::Ok(1));
                    const R readonly(R::Ok(2));
                    R error(R::Err(i16(3)));
                    const R error_readonly(R::Err(i16(4)));
                    ConstPayload immutable_payload(ConstPayload::Ok(5));
                    Empty done(Empty::Ok());
                    if (!SameType<decltype(value.value()),i32&> ||
                        !SameType<decltype(std::move(value).value()),i32&&> ||
                        !SameType<decltype(readonly.value()),const<i32>&> ||
                        !SameType<decltype(std::move(immutable_payload).value()),const<i32>&&> ||
                        !SameType<decltype(error.error()),i16&> ||
                        !SameType<decltype(error_readonly.error()),const<i16>&> ||
                        !SameType<decltype(done.value()),void>) { return 10; }
                    value.value() = 20;
                    error.error() = i16(22);
                    done.value();
                    if (!successful(value) || value.has_error() ||
                        !error.has_error() || error.has_value() ||
                        checked(value) + error.error() != 42 ||
                        constant_answer != 42 || readonly.value() != 2) {
                        return 11;
                    }
                    return 42;
                }
            """),
            42,
        )
        readonly = self.compile(
            """
            alias R=std::Result<i32,i32>;
            void f(const<R>& r) { r.value() = 1; }
            """,
            "--check",
        )
        self.assertEqual(readonly.returncode, 1)
        self.assertIn("writable lvalue", readonly.stderr)
        pointer = self.compile(
            "alias R=std::Result<i32,i32>; bool wrong(R* p){return p.has_value();}",
            "--check",
        )
        self.assertEqual(pointer.returncode, 1)

    def test_result_wrong_case_selects_contract_failure(self):
        alias = """
            alias R=std::Result<i32,i32>;
            alias Empty=std::Result<void,i32>;
        """
        for body in (
            "R item(R::Err(7));return item.value();",
            "R item(R::Ok(7));return item.error();",
            "Empty item(Empty::Err(7));item.value();return 42;",
        ):
            with self.subTest(body=body):
                self.assertEqual(
                    self.program(
                        alias + "i32 main(){" + body + "}", "--preset=Release"
                    ),
                    -signal.SIGILL,
                )
        wrong = self.compile(
            alias
            + """
                constexpr i32 invalid() { R r(R::Err(7)); return r.value(); }
                constexpr i32 required(invalid());
            """,
            "--check",
        )
        self.assertEqual(wrong.returncode, 1)
        self.assertIn("inactive case in constant evaluation", wrong.stderr)

    def test_result_payload_reference_keeps_the_selected_generation(self):
        source = """
            alias R=std::Result<i32,i32>;
            i32 read(bool replace) {
                R item(R::Ok(7));
                auto extent(storage_of(item));
                i32& previous(item.value());
                if (REPLACE) {
                    destroy(item);
                    auto current(construct_at<R>(extent,R::Ok(42)));
                    if (current->value() != 42) { return 1; }
                }
                return previous;
            }
            i32 main(){return read(INPUT);}
        """
        checked = self.compile(
            source.replace("REPLACE", "true").replace("INPUT", "true"),
            "--check",
            "--preset=Release",
        )
        self.assertEqual(checked.returncode, 1, checked.stderr)
        self.assertIn("ended object generation", checked.stderr)
        dynamic = source.replace("REPLACE", "replace")
        self.assertEqual(
            self.program(dynamic.replace("INPUT", "false"), "--preset=Release"),
            7,
        )
        self.assertEqual(
            self.program(dynamic.replace("INPUT", "true"), "--preset=Release"),
            -signal.SIGILL,
        )

    def test_result_fallible_accessors_and_qualified_ref_values(self):
        self.assertEqual(
            self.program("""
                alias Error=std::AccessError;
                alias R=std::Result<i32,i16>;
                alias Done=std::Result<void,i16>;
                alias Values=std::Result<std::Ref<i32>,Error>;
                alias Errors=std::Result<std::Ref<i16>,Error>;
                alias ConstValues=std::Result<std::Ref<const<i32>>,Error>;
                alias ConstErrors=std::Result<std::Ref<const<i16>>,Error>;
                alias CheckedDone=std::Result<void,Error>;
                constexpr bool wrong(const<Error>& error) {
                    match(error) {
                        case Error::WrongCase { return true; }
                        case Error::MissingValue { return false; }
                    }
                }
                [[effects(read(source))]]
                Values observe(R& source) { return source.try_value(); }
                constexpr i32 exercise(bool success) {
                    R result(success ? R::Ok(1) : R::Err(i16(40)));
                    Values item(result.try_value());
                    Errors error(result.try_error());
                    if (success) {
                        if (!item.has_value() || !error.has_error() ||
                            !wrong(error.error())) { return 3; }
                        const std::Ref<i32> copied(item.value());
                        i32& target(copied.get());
                        target += 41;
                        std::Ref<const<i32>> readonly(copied);
                        return readonly.get();
                    }
                    if (!item.has_error() || !error.has_value() ||
                        !wrong(item.error())) { return 4; }
                    i16& target(error.value().get());
                    target += i16(2);
                    return i32(result.error());
                }
                constexpr i32 folded(exercise(true)+exercise(false));
                i32 main() {
                    const R value(R::Ok(7));
                    const R error(R::Err(i16(9)));
                    Done finished(Done::Ok());
                    Done failed(Done::Err(i16(8)));
                    if (!SameType<decltype(value.try_value()),ConstValues> ||
                        !SameType<decltype(error.try_error()),ConstErrors> ||
                        !SameType<decltype(finished.try_value()),CheckedDone>) {
                        return 5;
                    }
                    ConstValues v(value.try_value());
                    ConstErrors e(error.try_error());
                    CheckedDone yes(finished.try_value());
                    CheckedDone no(failed.try_value());
                    yes.value();
                    if (v.value().get()!=7 || e.value().get()!=i16(9) ||
                        !yes.has_value() || !no.has_error() || !wrong(no.error())) {
                        return 6;
                    }
                    R input(R::Ok(42));
                    return exercise(true)==42 && exercise(false)==42 &&
                           folded==84 && observe(input).value().get()==42 ? 42 : 7;
                }
                """),
            42,
        )

    def test_result_ref_checks_generation_and_automatic_escape(self):
        alias = "alias R=std::Result<i32,i32>;"
        body = """
            R source(R::Ok(42));
            auto extent(storage_of(source));
            auto borrow(source.try_value());
            destroy(source);
            auto current(construct_at<R>(extent,R::Ok(19)));
            if (current->value()!=19) { return 3; }
            return borrow.value().get();
        """
        self.assertEqual(
            self.program(alias + "i32 main(){" + body + "}", "--preset=Release"),
            -signal.SIGILL,
        )
        for source, diagnosis in (
            (
                alias + "constexpr i32 dead(){" + body + "}constexpr i32 n(dead());",
                "ended object generation",
            ),
            (
                alias + "void set(const<R>& r){r.try_value().value().get()=1;}",
                "writable lvalue required",
            ),
            (
                alias + "std::Result<std::Ref<i32>,std::AccessError> leak(){"
                "R local(R::Ok(4));return local.try_value();}",
                "borrow of automatic storage escapes",
            ),
            (
                "std::Ref<i32> leak(){i32 local(4);return std::Ref<i32>(local);}",
                "borrow of automatic storage escapes",
            ),
        ):
            with self.subTest(diagnosis=diagnosis):
                rejected = self.compile(source, "--check")
                self.assertEqual(rejected.returncode, 1)
                self.assertIn(diagnosis, rejected.stderr)

    def test_ref_rejects_proven_use_after_full_expression(self):
        for declarations, target, field in (
            ("i32 make(){return 42;}", "i32", ""),
            (
                "struct Box {i32 answer; Box(i32 n){init answer(n);}};"
                "Box make(){return Box(42);}",
                "Box",
                ".answer",
            ),
        ):
            with self.subTest(referent=target):
                ref = f"std::Ref<const<{target}>>"
                self.assertEqual(
                    self.program(
                        declarations
                        + f"i32 main(){{return {ref}(make()).get(){field};}}"
                    ),
                    42,
                )
                ir = self.src.with_suffix(".ll").read_text()
                self.assertNotIn("@malloc", ir)
                self.assertNotIn("@llvm.lifetime.end", ir)
                expired = self.compile(
                    declarations
                    + f"i32 main(){{{ref} kept(make());return kept.get(){field};}}",
                    "--check",
                )
                self.assertEqual(expired.returncode, 1)
                self.assertIn("ended full-expression temporary", expired.stderr)
        for invalid in ("void", "i32&", "Forward", "const<Forward>"):
            with self.subTest(invalid_referent=invalid):
                invalid_type = self.compile(
                    f"declare struct Forward; alias R=std::Ref<{invalid}>;",
                    "--check",
                )
                self.assertEqual(invalid_type.returncode, 1)
                self.assertIn("constraint is not satisfied", invalid_type.stderr)

    def test_result_and_ref_check_expiry_through_control_flow(self):
        result = """
            alias R=std::Result<i32,i32>;
            alias Borrow=std::Result<std::Ref<i32>,std::AccessError>;
            R make(){return R::Ok(42);}
        """
        reference = "alias Ref=std::Ref<const<i32>>;i32 make(){return 42;}"
        cases = (
            (result, "auto held(make().try_value());return held.value().get();"),
            (
                result,
                "auto held((b?make():make()).try_value());return held.value().get();",
            ),
            (
                result,
                "auto held(b?make().try_value():make().try_value());return held.value().get();",
            ),
            (
                result,
                "Borrow held(make().try_value());Borrow copy(held);"
                "match(copy){case Borrow::Ok(ref item){return item.get();}"
                "case Borrow::Err(ref error){return 1;}}",
            ),
            (reference, "Ref held(b?Ref(make()):Ref(make()));return held.get();"),
            (
                reference,
                "i32 value(42);Ref held(b?Ref(make()):Ref(value));"
                "if(b){return held.get();}return 42;",
            ),
        )
        for declarations, body in cases:
            with self.subTest(body=body):
                rejected = self.compile(
                    declarations + "i32 inspect(bool b){" + body + "}",
                    "--check",
                )
                self.assertEqual(rejected.returncode, 1, rejected.stderr)
                self.assertIn("ended full-expression temporary", rejected.stderr)
        self.assertEqual(
            self.program(
                result
                + """
                i32 immediate(bool b){
                    return (b?make().try_value():make().try_value()).value().get();
                }
                i32 guarded(bool b){
                    R live(R::Ok(42));
                    auto held(b?make().try_value():live.try_value());
                    if(!b){return held.value().get();}
                    return 42;
                }
                i32 main(){
                    return immediate(true)==42 && immediate(false)==42 &&
                           guarded(true)==42 && guarded(false)==42 ? 42 : 1;
                }
                """
            ),
            42,
        )
        ir = self.src.with_suffix(".ll").read_text()
        self.assertNotIn("@malloc", ir)
        self.assertNotIn("@llvm.lifetime.end", ir)
        self.assertEqual(
            self.program("""
                alias R=std::Result<i32,i32>;
                R failed(){return R::Err(1);}
                i32 main(){auto held(failed().try_value());return held.value().get();}
            """),
            -signal.SIGILL,
        )

    def test_native_reference_initializer_ends_its_full_expression(self):
        result = "alias R=std::Result<i32,i32>; R make(){return R::Ok(21);}"
        expired = self.compile(
            result + "i32 main(){const<i32>& saved(make().value());return saved;}",
            "--check",
        )
        self.assertEqual(expired.returncode, 1, expired.stderr)
        self.assertIn("ended full-expression temporary", expired.stderr)
        self.assertEqual(
            self.program(
                result
                + """
                i32 main(){
                    R live(R::Ok(1));
                    const<i32>& saved(live.value());
                    live.value()=21;
                    return saved+make().value();
                }
                """
            ),
            42,
        )
        self.assertEqual(
            self.program("""
                i32 count;
                struct T{~T(){++count;}};
                T make(){return T();}
                i32 main(){const<T>& unused(make());return count==1?42:1;}
            """),
            42,
        )

    def test_borrow_publication_follows_reaching_branches(self):
        for source in (
            "i32 stable;i32* leak(bool b){i32 local;i32* view(&stable);"
            "if(b){view=&local;}return view;}",
            "i32 stable;struct Item{i32* view;};Item leak(bool b){"
            "i32 local;i32* view(&stable);if(b){view=&local;}return Item(view);}",
            "alias R=std::Result<i32,i32>;"
            "alias Borrow=std::Result<std::Ref<i32>,std::AccessError>;"
            "Borrow leak(bool b){R one(R::Ok(10));R two(R::Ok(20));"
            "Borrow held(b?one.try_value():two.try_value());return held;}",
        ):
            with self.subTest(source=source):
                rejected = self.compile(source, "--check")
                self.assertEqual(rejected.returncode, 1, rejected.stderr)
                self.assertIn("borrow of automatic storage escapes", rejected.stderr)
        self.assertEqual(
            self.program("""
                i32 stable(42);
                bool flipped(bool input){return !input;}
                i32* guarded(bool b){
                    i32 local(7);i32* view(&stable);
                    if(b){view=&local;}
                    if(!b){return view;}
                    return &stable;
                }
                i32* opaque_guard(bool b){
                    i32 local(7);i32* view(&stable);
                    if(b){view=&local;}
                    if(flipped(b)){return view;}
                    return &stable;
                }
                i32 main(){
                    return *guarded(true)==42 && *guarded(false)==42 &&
                           *opaque_guard(true)==42 && *opaque_guard(false)==42 ? 42 : 1;
                }
            """),
            42,
        )

    def test_scalar_domain_conversions_use_exact_integer_values(self):
        source = """
            enum Band:i8 {case Below(-2),case Above(2)};
            alias BoolResult=std::Result<bool,std::ScalarError>;
            alias BandResult=std::Result<Band,std::ScalarError>;
            alias EmptyResult=std::Result<void,std::ScalarError>;
            consteval i32 check(){
                BoolResult missing(std::try_from_underlying<bool>(18446744073709551617));
                match(missing){
                    case BoolResult::Ok(value x){return 0;}
                    case BoolResult::Err(value e){
                        match(e){
                            case std::ScalarError::InvalidBoolean{return 1;}
                            case _{return 0;}
                        }
                    }
                }
            }
            i32 inspect(i32 input){
                BandResult result(std::try_from_underlying<Band>(input));
                match(result){
                    case BandResult::Ok(value e){
                        return std::to_underlying(e)==i8(-2)?1:0;
                    }
                    case BandResult::Err(value e){return 0;}
                }
            }
            constexpr i32 valid(check());
            i32 main(){
                EmptyResult empty(EmptyResult::Ok());
                char largest(std::from_underlying<char>(u32(0x10ffff)));
                bool bit(std::from_underlying<bool>(1));
                if(valid==1 && std::to_underlying(bit)==u8(1) &&
                   std::to_underlying(largest)==u32(0x10ffff) && inspect(-2)==1 &&
                   inspect(254)==0){return 42;}
                return 0;
            }
        """
        self.assertEqual(self.program(source), 42)
        invalid = """
            i32 main(){char bad(std::from_underlying<char>(0xd800)); return 42;}
        """
        self.assertEqual(self.program(invalid), -signal.SIGILL)
        result = self.compile(
            "constexpr bool bad(std::from_underlying<bool>(-1));", "--check"
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("fails in constant evaluation", result.stderr)

    def test_named_integer_results_keep_policy_status_and_case(self):
        source = """
            alias Narrow=std::numeric::NumericResult<i8>;
            alias Code=std::numeric::NumericErrorCode;
            bool ordered(i32 try_add){return try_add<10;}
            constexpr bool overflow(i8 input){
                Narrow attempt(try_add(input,1));
                match(attempt) {
                    case Narrow::Ok(value result,value status){return false;}
                    case Narrow::Err(value code,value status){
                        return code==Code::OutOfRange && !status.wrapped &&
                               !status.clamped && status.fp_flags.empty();
                    }
                }
            }
            bool zero_divisor(i8 divisor){
                Narrow attempt(std::numeric::try_wrapping_div(i8(-128),divisor));
                match(attempt) {
                    case Narrow::Ok(value result,value status){
                        return result==-128 && status.wrapped &&
                               !status.clamped && status.value_inexact;
                    }
                    case Narrow::Err(value code,value status){
                        return code==Code::ZeroDivisor && !status.wrapped &&
                               !status.value_inexact;
                    }
                }
            }
            bool invalid_shift(i32 count){
                Narrow attempt(try_saturating_shl(i8(1),count));
                match(attempt) {
                    case Narrow::Ok(value result,value status){
                        return result==127 && status.clamped &&
                               !status.wrapped && status.value_inexact;
                    }
                    case Narrow::Err(value code,value status){
                        return code==Code::InvalidShift && !status.clamped;
                    }
                }
            }
            constexpr bool folded(overflow(i8(127)));
            i32 main(){
                if(!folded || !ordered(2) || !zero_divisor(0) || !zero_divisor(-1) ||
                   !invalid_shift(-1) || !invalid_shift(7) || !invalid_shift(8)){
                    return 1;
                }
                if(checked_rem(i8(-128),-1)!=0 || wrapping_div(i8(-128),-1)!=-128 ||
                   saturating_div(i8(-128),-1)!=127 ||
                   euclidean_mod(i8(-127),i8(-128))!=1 ||
                   logical_shr(i8(-1),7)!=u8(1) || magnitude(i8(-128))!=u8(128) ||
                   checked_add<i16>(i8(127),i8(1))!=i16(128) ||
                   wrapping_cast<u8>(-18446744073709551617)!=u8(255) ||
                   saturating_cast<i8>(18446744073709551617)!=i8(127)){
                    return 2;
                }
                return 42;
            }
        """
        for preset in ("Debug", "Release", "MinimalRelease"):
            with self.subTest(preset=preset):
                self.assertEqual(self.program(source, "--preset=" + preset), 42)
        self.assertEqual(
            self.program(
                "i32 main(){ i8 n(checked_add(i8(127),1)); return 42; }",
                "--preset=Release",
            ),
            -signal.SIGILL,
        )
        result = self.compile("constexpr i8 bad(checked_shl(i8(1),-1));", "--check")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("fails in required constant evaluation", result.stderr)

    def test_fixed_integer_bit_fields_and_reinterpretation(self):
        source = """
            alias ByteResult=std::numeric::NumericResult<u8>;
            alias Code=std::numeric::NumericErrorCode;
            generic<const usize Start, const usize Width>
            u8 extract(u16 source){return extract_bits<Start,Width>(source);}
            bool invalid_capacity(i32 count){
                ByteResult result(std::numeric::checked_extract_bits<u8>(u16(0),0,count));
                match(result){
                    case ByteResult::Ok(value extracted,ref status){return false;}
                    case ByteResult::Err(value code,ref status){
                        return code==Code::InvalidBitRange && status.fp_flags.empty();
                    }
                }
            }
            consteval u8 folded(){
                ByteResult result(checked_extract_bits<8,8>(u16(0x2a00)));
                match(result) {
                    case ByteResult::Ok(value extracted,ref status){return extracted;}
                    case ByteResult::Err(value code,ref status){return 0;}
                }
            }
            constexpr u8 constant(folded());
            i32 main(){
                if(constant != 42 || !invalid_capacity(9)){return 1;}
                if(reinterpret_bits<u16>(i8(-128))!=u16(65408) ||
                   reinterpret_bits<u16>(i8(-128),Zero)!=u16(128) ||
                   reinterpret_bits<i16>(u8(255),Sign)!=i16(-1) ||
                   extract<8,8>(u16(0x2a00)) != 42 ||
                   extract_bits<1<2?8:0,8>(u16(0x2a00)) != 42 ||
                   extract_bits<0,64>(u64(18446744073709551615)) != u64(18446744073709551615) ||
                   insert_bits(i8(0),7,1,1)!=i8(-128) ||
                   insert_bits_trunc(u16(0),8,8,-1)!=u16(0xff00)){
                    return 2;
                }
                return 42;
            }
        """
        for mode in ("Debug", "Release", "MinimalRelease"):
            with self.subTest(preset=mode):
                self.assertEqual(self.program(source, "--preset=" + mode), 42)
        for source, message in (
            ("i32 main(){return extract_bits<0,0>(i32(0));}", "NUM001"),
            ("i32 main(){return extract_bits<0,3>(i32(0));}", "u3 is unavailable"),
            (
                "i32 main(){auto v(checked_extract_bits<u8>(i32(0),-1,1));return 42;}",
                "statically invalid bit range",
            ),
            ("i32 main(){return extract_bits<i8>(i32(0),0,8);}", "unsigned fixed"),
            ("i32 main(){return try_insert_bits(u8(0),0,1,1);}", "unknown"),
        ):
            with self.subTest(source=source):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)
        self.assertEqual(
            self.program("""
                i32 extract(i32 count){return extract_bits<u8>(u16(0),0,count);}
                i32 main(){return extract(9);}
            """),
            -signal.SIGILL,
        )

    def test_checked_bit_insert_validates_range_before_value_and_commits_once(self):
        self.assertEqual(
            self.program("""
            alias Done=std::numeric::NumericResult<void>;
            alias Code=std::numeric::NumericErrorCode;
            i32 trace;
            i32 start(i8& target){target=32;trace=10*trace+1;return 0;}
            i32 extent(i32 n){trace=10*trace+2;return n;}
            i16 invalid(){trace=10*trace+3;return -1;}
            bool attempt(i8& target,i32 length,Code expected){
                Done result(checked_insert_bits_assign(target,start(target),
                                                       extent(length),invalid()));
                match(result) {
                    case Done::Ok(value status){return false;}
                    case Done::Err(value code,ref status){
                        return code==expected && target==32 && trace==123;
                    }
                }
            }
            i32 main(){
                i8 n;
                if(!attempt(n,9,Code::InvalidBitRange)){return 1;}
                trace=0;
                if(!attempt(n,3,Code::OutOfRange)){return 2;}
                insert_bits_trunc_assign(n,1,3,-1);
                if(n!=46){return 3;}
                Done result(checked_insert_bits_trunc_assign(n,0,2,-2));
                match(result) {
                    case Done::Ok(value status){return n==46 && status.wrapped ? 42 : 4;}
                    case Done::Err(value code,ref status){return 5;}
                }
            }
            """),
            42,
        )

    def test_named_numeric_assignment_reads_after_argument_evaluation(self):
        self.assertEqual(
            self.program("""
            alias Done=std::numeric::NumericResult<void>;
            alias Code=std::numeric::NumericErrorCode;
            i8 rhs(i8& target){target=40;return 2;}
            i32 main(){
                i8 n(1);
                checked_add_assign(n,rhs(n));
                if(n!=42){return 1;}
                Done outcome(try_add_assign(n,i16(1000)));
                match(outcome) {
                    case Done::Ok(value status){return 2;}
                    case Done::Err(value code,value status){
                        return code==Code::OutOfRange && !status.clamped ? n : 3;
                    }
                }
            }
            """),
            42,
        )

    def test_named_scalar_casts_use_exact_literal_and_typed_boundaries(self):
        self.assertEqual(
            self.program("""
                alias ByteResult=std::numeric::NumericResult<i8>;
                alias SingleResult=std::numeric::NumericResult<f32>;
                alias Code=std::numeric::NumericErrorCode;
                alias Mode=std::numeric::RoundingMode;
                consteval bool folded(){
                    ByteResult checked(try_checked_cast<i8>(127.9,TowardZero));
                    match(checked){
                        case ByteResult::Err(value code,ref status){return false;}
                        case ByteResult::Ok(value result,ref status){
                            if(result!=127 || !status.value_inexact ||
                               !status.fp_flags.empty()){return false;}
                        }
                    }
                    ByteResult exact(try_exact_cast<i8>(127.000000000000000001));
                    match(exact){
                        case ByteResult::Ok(value result,ref status){return false;}
                        case ByteResult::Err(value code,ref status){
                            if(code!=Code::OutOfRange || !status.value_inexact ||
                               !status.fp_flags.empty()){return false;}
                        }
                    }
                    SingleResult precision(try_exact_cast<f32>(0.1));
                    match(precision){
                        case SingleResult::Ok(value result,ref status){return false;}
                        case SingleResult::Err(value code,ref status){
                            return code==Code::NotExactlyRepresentable &&
                                   status.value_inexact && status.fp_flags.empty();
                        }
                    }
                }
                constexpr bool ok(folded());
                i32 trace;
                f64 take(){trace=1;return -2.5;}
                Mode policy(){trace=trace*10+2;return Mode::NearestTiesAway;}
                i32 main(){
                    if(!ok || checked_cast<i8>(take(),policy())!=-3 || trace!=12){return 1;}
                    if(checked_cast<i8>(f64(2.5),Mode::NearestTiesEven)!=2 ||
                       checked_cast<i8>(f64(-2.5),TowardPositiveInfinity)!=-2 ||
                       exact_cast<i8>(f64(127.000000000000000001))!=127 ||
                       exact_cast<i64>(f64(-0.0))!=0 ||
                       checked_cast<i64>(0x1p-1074,TowardPositiveInfinity)!=1 ||
                       truncating_cast<i8>(128.9)!=-128 ||
                       saturating_cast<i8>(-200.5)!=-128 ||
                       wrapping_cast<usize>(0x1.0000000000001p100)!=usize(281474976710656)){
                        return 2;
                    }
                    return 42;
                }
            """),
            42,
        )

    def test_integer_destination_casts_preserve_ambient_fp_state(self):
        self.assertEqual(
            self.program(
                """
                alias IntegerResult=std::numeric::NumericResult<i64>;
                alias ByteResult=std::numeric::NumericResult<i8>;
                alias Code=std::numeric::NumericErrorCode;
                extern "C" i64 wrap(f64 input){return wrapping_cast<i64>(input);}
                extern "C" i64 round_up(f64 input){
                    return checked_cast<i64>(input,TowardPositiveInfinity);
                }
                extern "C" i32 boundary(f64 input){
                    IntegerResult result(try_checked_cast<i64>(input));
                    match(result){
                        case IntegerResult::Ok(value item,ref status){return 0;}
                        case IntegerResult::Err(value code,ref status){
                            return code==Code::OutOfRange && !status.value_inexact &&
                                   status.fp_flags.empty() ? 42 : 1;
                        }
                    }
                }
                extern "C" i32 saturate(f64 input){
                    ByteResult result(try_saturating_cast<i8>(input));
                    match(result){
                        case ByteResult::Ok(value item,ref status){
                            return status.clamped && status.fp_flags.empty() ? i32(item) : 0;
                        }
                        case ByteResult::Err(value code,ref status){
                            return code==Code::NonFinite && status.fp_flags.empty() ? 42 : 1;
                        }
                    }
                }
                """,
                host="""
                #include <math.h>
                #include <stdint.h>
                #include <xmmintrin.h>
                extern int64_t wrap(double),round_up(double);
                extern int32_t boundary(double),saturate(double);
                int main(void) {
                    unsigned saved=_mm_getcsr(), state=(saved|0xff80u|5u);
                    _mm_setcsr(state);
                    int ok=wrap(-0x1.0000000000001p100)==-INT64_C(281474976710656) &&
                           round_up(0x1p-1074)==1 && boundary(0x1p63)==42 &&
                           saturate(INFINITY)==127 && saturate(-INFINITY)==-128 &&
                           saturate(NAN)==42 && _mm_getcsr()==state;
                    _mm_setcsr(saved);
                    return ok?42:1;
                }
                """,
            ),
            42,
        )

    def test_named_float_casts_observe_precision_rounded_range_and_tininess(self):
        self.assertEqual(
            self.program(
                """
                configuration { numeric.fp.trap_mask=[Overflow,Underflow,Inexact]; };
                alias R=std::numeric::NumericResult<f32>;
                alias Code=std::numeric::NumericErrorCode;
                alias Flag=std::numeric::FPFlag;
                extern "C" i32 narrow(f64 input,bool tiny){
                    R result(try_checked_cast<f32>(input,NearestTiesEven));
                    match(result){
                        case R::Ok(value item,ref status){
                            return item==f32(0x1p-126) && status.value_inexact &&
                                   status.fp_flags.contains(Flag::Inexact) &&
                                   status.fp_flags.contains(Flag::Underflow)==tiny ? 42 : 1;
                        }
                        case R::Err(value code,ref status){return 2;}
                    }
                }
                extern "C" i32 beyond(f64 input){
                    R result(try_checked_cast<f32>(input,TowardZero));
                    match(result){
                        case R::Ok(value item,ref status){return 1;}
                        case R::Err(value code,ref status){
                            return code==Code::OutOfRange && status.value_inexact &&
                                   status.fp_flags.contains(Flag::Overflow) &&
                                   status.fp_flags.contains(Flag::Inexact) ? 42 : 2;
                        }
                    }
                }
                extern "C" i32 probe(f64 input){
                    R result(try_exact_cast<f32>(input));
                    match(result){
                        case R::Ok(value item,ref status){return 1;}
                        case R::Err(value code,ref status){
                            return code==Code::NotExactlyRepresentable &&
                                   status.value_inexact && status.fp_flags.empty() ? 42 : 2;
                        }
                    }
                }
                extern "C" f32 from_u64(u64 input){
                    return checked_cast<f32>(input,NearestTiesAway);
                }
                """,
                host="""
                #include <stdbool.h>
                #include <stdint.h>
                #include <xmmintrin.h>
                extern int32_t narrow(double,bool),beyond(double),probe(double);
                extern float from_u64(uint64_t);
                int main(void) {
                    unsigned saved=_mm_getcsr(), control=(saved | 0x9fc0u) & ~0x3fu;
                    _mm_setcsr(control|1u);
                    int ok=narrow(0x1.fffffe1000000p-127,true)==42 &&
                           (_mm_getcsr()&0x31u)==0x31u &&
                           narrow(0x1.ffffff0000000p-127,false)==42 &&
                           beyond(0x1p128)==42 && (_mm_getcsr()&0x39u)==0x39u;
                    _mm_setcsr(control|1u);
                    ok=ok && probe(0.1)==42 && _mm_getcsr()==(control|1u) &&
                       from_u64(16777217)==16777218.0f && (_mm_getcsr()&0x21u)==0x21u;
                    _mm_setcsr(saved);
                    return ok?42:1;
                }
                """,
            ),
            42,
        )

        for source, diagnostic in (
            ("f32 f(){return wrapping_cast<f32>(1);}", "no such mapping"),
            ("i32 f(){return checked_cast<i32>(1,TowardZero);}", "no rounding stage"),
            ("i32 f(){return checked_cast<i32>(1.5,1);}", "requires RoundingMode"),
            ("constexpr i8 bad(exact_cast<i8>(127.9));", "fails in required constant"),
        ):
            with self.subTest(diagnostic=diagnostic):
                result = self.compile(source, "--check")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)

    def test_record_invariant_checks_stable_exposure(self):
        record = """
            [[invariant(amount >= 0)]]
            class Balance {
                i32 amount;
              public:
                Balance(i32 initial) { init amount(initial); }
                i32 read() const { return amount; }
                void set(i32 n) { amount = n; }
            };
        """
        for body, code in (
            ("Balance b(42); return b.read();", 42),
            ("Balance b(-1); return 43;", -signal.SIGILL),
            ("Balance b(42); b.set(-1); return 43;", -signal.SIGILL),
        ):
            with self.subTest(body=body):
                self.assertEqual(
                    self.program(record + "i32 main(){" + body + "}"), code
                )
        self.assertEqual(
            self.program(
                record + "i32 main(){Balance b(42); b.set(-1); return 42;}",
                "--preset=Release",
            ),
            42,
        )
        self.assertEqual(
            self.program("""
                [[invariant(n>0)]] struct Positive {
                    i32 n;
                    Positive(i32 value) { init n(value); }
                };
                i32 main(){Positive p(-1) -> {n=42;};return p.n;}
            """),
            42,
        )
        self.assertEqual(
            self.program("""
                [[invariant(n>0)]] struct Positive {
                    i32 n;
                    static Positive invalid(0);
                };
                i32 main(){return 42;}
            """),
            -signal.SIGILL,
        )

    def test_invariants_for_inherited_and_tagged_objects(self):
        self.assertEqual(
            self.program("""
                [[invariant(n>0)]] struct Base { i32 n(42); };
                struct Derived : Base { i32 read() const { return n; } };
                i32 main(){Derived d;d.n=0;return d.read();}
            """),
            -signal.SIGILL,
        )
        self.assertEqual(
            self.program("""
                bool valid(true);
                [[invariant(valid)]] union Payload {default case Empty;};
                i32 main(){valid=false;Payload v(Payload::Empty());return 42;}
            """),
            -signal.SIGILL,
        )

    def test_invariants_wait_for_the_receivers_stable_lifetime(self):
        record = """
            [[invariant(n>0)]] struct Positive {
                i32 n;
                constexpr i32 read() const { return n; }
                Positive(i32 value) {
                    init n(value);
                    if (read() < 0) { n=42; }
                }
                Positive(i32 value, const<Positive>& witness) {
                    init n(value);
                    i32 observed(witness.read());
                    n=42;
                }
                ~Positive() { n=-1; i32 during(read()); }
            };
            constexpr i32 compute(){Positive p(-1);return p.read();}
            constexpr i32 result(compute());
        """
        for body, expected in (
            ("Positive p(-1);return p.read()==result ? result : 1;", 42),
            ("Positive p(42);p.n=-1;Positive q(42,p);return q.n;", -signal.SIGILL),
        ):
            with self.subTest(body=body):
                self.assertEqual(
                    self.program(record + "i32 main(){" + body + "}"), expected
                )

    def test_invariants_bind_in_document_mode_and_validate_constant_values(self):
        for source, message in (
            ("[[invariant(1)]] struct Bad {};", "contract predicate requires bool"),
            ("[[invariant(unknown)]] class Bad {};", "unknown name 'unknown'"),
            ("[[invariant(true)]] declare struct Bad;", "inapplicable value contract"),
        ):
            with self.subTest(source=source):
                r = self.compile(source, "--preset=Release", "--check")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn(message, r.stderr)
        r = self.compile(
            "[[invariant(n>0)]] struct Positive{i32 n;};constexpr Positive p(0);",
            "--check",
        )
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("Positive invariant #1", r.stderr)

    def test_constexpr_shared_virtual_base_has_one_lifetime_and_native_layout(self):
        self.assertEqual(
            self.program("""
                [[requires(actual == expected)]]
                constexpr void expect(i32 actual, i32 expected) {}
                struct Root {
                    i32 n;
                    Root(i32 initial) {init n(initial);}
                    constexpr virtual i32 read() const {return n;}
                    ~Root(){expect(read(), 42);}
                };
                constexpr i32 through_root(const<Root>& root){return root.read();}
                struct Left : virtual Root {
                    Left(){
                        init virtual_base<Root>(1);
                        expect(through_root(*this), 40);
                        n=41;
                    }
                    constexpr i32 read() const override {return n+1;}
                    ~Left(){expect(through_root(*this), 43);}
                };
                struct Right : virtual Root {
                    Right(){
                        init virtual_base<Root>(2);
                        expect(through_root(*this), 41);
                        n=42;
                    }
                    ~Right(){expect(through_root(*this), 42);}
                };
                struct Both : Left, Right {
                    Both(){init virtual_base<Root>(39);}
                    constexpr i32 read() const override {return n+2;}
                    ~Both(){expect(through_root(*this), 44);}
                };
                constexpr i32 compute(){Both b;return through_root(b);}
                constexpr Both global;
                constexpr const<Left>* left(&global);
                constexpr const<Root>* shared(left);
                constexpr i32 folded(compute());
                constexpr i32 pointed(shared->read());
                i32 native(const<Root>& root){return root.read();}
                i32 main(){
                    return folded == 44 && pointed == 44 && native(global)==44
                        ? 42 : 0;
                }
            """),
            42,
        )

    def test_constexpr_shared_virtual_base_aliases_survive_generated_copy(self):
        self.assertEqual(
            self.program("""
                struct Shared {
                    i32 n(1);
                    Shared(const<Shared>& src)=default;
                    constexpr virtual void assign(i32 v){n=v;}
                };
                struct Left : virtual Shared {
                    Left(const<Left>& src)=default;
                };
                struct Right : virtual Shared {
                    Right(const<Right>& src)=default;
                };
                struct Both : Left, Right {
                    Both(const<Both>& src)=default;
                };
                constexpr i32 compute(){
                    Both value;
                    Left& left(value);
                    Right& right(value);
                    Shared* first(&left);
                    Shared* second(&right);
                    first->assign(42);
                    Both copied(value);
                    return first == second && right.n == 42 ? copied.n : 0;
                }
                constexpr i32 answer(compute());
                i32 main(){return answer;}
            """),
            42,
        )

    def test_constexpr_virtual_dispatch_preserves_active_layers(self):
        self.assertEqual(
            self.program("""
                [[requires(actual == expected)]]
                constexpr void expect(i32 actual, i32 expected) {}
                struct Base {
                    i32 seen;
                    Base() { seen=score(); }
                    constexpr virtual i32 score(i32 bias(0)) const {
                        return 7+bias;
                    }
                    ~Base() { expect(score(), 7); }
                };
                struct Pad { i32 field(1); };
                struct Derived : Pad, Base {
                    i32 n(42);
                    constexpr i32 score(i32 bias(1)) const override {
                        return n+bias;
                    }
                    ~Derived() { expect(score(0), 42); }
                };
                constexpr i32 through(const<Base>& value) {
                    return value.score();
                }
                constexpr i32 local() {
                    Derived d;
                    return d.seen == 7 ? through(d) : 0;
                }
                constexpr Derived global;
                constexpr i32 local_answer(local());
                constexpr i32 static_answer(through(global));
                constexpr const<Base>* address(&global);
                constexpr i32 pointer_answer(address->score());
                i32 native_read(const<Base>& value) { return value.score(); }
                i32 main() {
                    return local_answer == 42 && static_answer == 42 &&
                           pointer_answer == 42
                        ? native_read(global) : 0;
                }
            """),
            42,
        )

    def test_constexpr_virtual_call_updates_derived_storage_and_copy_slices(self):
        self.assertEqual(
            self.program("""
                struct Base {
                    i32 n;
                    Base(const<Base>& src)=default;
                    constexpr virtual void set(i32 v) { n=v; }
                    constexpr virtual i32 value() const { return n; }
                };
                struct Buffer { i32 field(3); };
                struct Record : Buffer, Base {
                    i32 result;
                    constexpr void set(i32 v) override { result=v; }
                    constexpr i32 value() const override { return result; }
                };
                constexpr i32 compute() {
                    Record r;
                    Base& view(r);
                    view.set(42);
                    Base copied(view);
                    return copied.value() == 0 ? r.value() : 1;
                }
                constexpr i32 answer(compute());
                i32 main() { return answer; }
            """),
            42,
        )

    def test_invariant_lifetime_is_restored_across_whole_and_return(self):
        self.assertEqual(
            self.program("""
                [[invariant(n>0)]] struct Positive {
                    i32 n;
                    i32 read() const { return n; }
                };
                struct Base {};
                declare struct Derived;
                declare void release(Derived& d);
                struct Derived:Base {
                    Complete base<Base>;
                    ~Derived(){release(*this);}
                };
                void release(Derived& d) {
                    Positive pending(42) -> {destroy_base<Base>(d);};
                }
                void early(){Positive pending(42) -> {return;};}
                void leave_tail() {
                    for(i32 i(0);i<2;++i) {Positive pending(42) -> {continue;};}
                    while(true) {Positive pending(42) -> {break;};}
                    Positive pending(42) -> {goto done;};
                    done: return;
                }
                i32 main(){
                    {Derived d;}early();leave_tail();
                    Positive p(42);return p.read();
                }
            """),
            42,
        )

    def test_consteval_array_element_replacement_retains_its_cleanup_rank(self):
        self.assertEqual(
            self.program("""
                struct Original {
                    i32* trace;
                    i32 digit;
                    Original(i32* counter,i32 value) {
                        init trace(counter);
                        init digit(value);
                    }
                    ~Original(){*trace=*trace*10+digit;}
                };
                struct Replacement {
                    i32* trace;
                    Replacement(i32* counter){init trace(counter);}
                    ~Replacement(){*trace=*trace*10+9;}
                };
                consteval i32 fold(){
                    i32 trace;
                    {
                        Original[3] values(
                            Original(&trace,1),Original(&trace,2),Original(&trace,3));
                        auto whole(storage_of(values));
                        auto middle(storage_of(values[1]));
                        auto first(storage_of(values[0]));
                        if(middle.identity()==first.identity()
                           || whole.identity()==middle.identity()){return 0;}
                        destroy(values[1]);
                        auto current(construct_at<Replacement>(middle,&trace));
                        auto current_extent(storage_of(*current));
                        if(current_extent.identity()!=middle.identity()
                           || values[0].digit!=1){return 0;}
                    }
                    return trace;
                }
                constexpr i32 retired(fold());
                i32 main(){return retired==2391 ? 42 : 0;}
            """),
            42,
        )

    def test_consteval_record_member_replacement_retains_its_cleanup_rank(self):
        self.assertEqual(
            self.program("""
                struct Original {
                    i32* trace;
                    i32 digit;
                    Original(i32* counter,i32 value) {
                        init trace(counter);
                        init digit(value);
                    }
                    ~Original(){*trace=*trace*10+digit;}
                };
                struct Replacement {
                    i32* trace;
                    Replacement(i32* counter){init trace(counter);}
                    ~Replacement(){*trace=*trace*10+9;}
                };
                struct Holder {
                    i32* trace;
                    Replacement* active;
                    Original first;
                    Original middle;
                    Original last;
                    Complete middle;
                    Holder(i32* counter) {
                        init trace(counter);
                        init active(nullptr);
                        init first(counter,1);
                        init middle(counter,2);
                        init last(counter,3);
                    }
                    ~Holder(){auto self(this);*self->trace=*trace*10+4;}
                    cleanup {
                        auto slot(storage_of(middle));
                        if(slot.capacity_bytes()==sizeof(Original)){
                            *trace=*trace*10+5;
                        }
                        if(active!=nullptr){destroy(*active);}
                    }
                };
                consteval i32 fold(){
                    i32 trace;
                    {
                        Holder holder(&trace);
                        auto middle(storage_of(holder.middle));
                        auto first(storage_of(holder.first));
                        if(middle.identity()==first.identity()){return 0;}
                        destroy(holder.middle);
                        auto current(construct_at<Replacement>(middle,&trace));
                        holder.active=current;
                        auto replacement_extent(storage_of(*current));
                        if(replacement_extent.identity()!=middle.identity()
                           || holder.first.digit!=1){return 0;}
                    }
                    return trace;
                }
                constexpr i32 retired(fold());
                i32 main(){return retired==243591 ? 42 : 0;}
            """),
            42,
        )

    def test_consteval_member_storage_tracks_nested_generations_and_bounds(self):
        self.assertEqual(
            self.program("""
                struct Fields { i32[2] values; };
                consteval i32 fold(){
                    Fields[2] records;
                    auto old(&records[0].values[1]);
                    auto slot(storage_of(*old));
                    destroy(records[0].values[1]);
                    auto current(construct_at<i32>(slot,42));
                    auto replacement_extent(storage_of(*current));
                    if(current!=old || replacement_extent.identity()!=slot.identity()){
                        return 1;
                    }
                    return *current;
                }
                constexpr i32 folded(fold());
                i32 main(){return folded;}
            """),
            42,
        )
        for body, message in (
            (
                "Box box; auto old(&box.item); destroy(box.item);"
                "construct_at<i32>(storage_of(box.item),42);return *old;",
                "ended object generation",
            ),
            (
                "Box box; destroy(box.item);"
                "construct_at<i32>(storage_of(box.item),42);return box.item;",
                "ended object generation",
            ),
            (
                "Box box; destroy(box.item);"
                "construct_at<i64>(storage_of(box.item),42);return 0;",
                "insufficient storage capacity",
            ),
            (
                "Box box; auto item(storage_of(box.item)); auto whole(storage_of(box));"
                "destroy(box); construct_at<Box>(whole);"
                "construct_at<i32>(item,42);return 0;",
                "ended object generation",
            ),
            (
                "Box box; destroy(box.item);"
                "auto current(construct_at<i32>(storage_of(box.item),42));"
                "abandon(box);return *current;",
                "ended object generation",
            ),
        ):
            with self.subTest(body=body):
                result = self.compile(
                    "struct Box{i32 item;};consteval i32 rejected(){" + body + "}"
                    "constexpr i32 value(rejected());",
                    "--check",
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_consteval_array_element_generation_and_extent_bounds(self):
        for body, message in (
            (
                "i32[2] a; i32* old(&a[0]); destroy(a[0]);"
                "construct_at<i32>(storage_of(a[0]),42); return *old;",
                "ended object generation",
            ),
            (
                "i32[2][2] a; auto row(storage_of(a[0]));"
                "auto child(storage_of(a[0][0])); destroy(a[0]);"
                "construct_at<i32[2]>(row); construct_at<i32>(child,42);return 0;",
                "ended object generation",
            ),
            (
                "i8[16] a; destroy(a[0]);"
                "construct_at<i64>(storage_of(a[0]),42);return 0;",
                "insufficient storage capacity",
            ),
            (
                "i32[2] a; destroy(a[0]);"
                "construct_at<i32>(storage_of(a[0]),42);"
                "i32[2] copy(a);return copy[0];",
                "ended element generation",
            ),
        ):
            with self.subTest(body=body):
                result = self.compile(
                    "consteval i32 rejected(){" + body + "}"
                    "constexpr i32 value(rejected());",
                    "--check",
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_consteval_reconstructs_automatic_storage_and_retires_current_type(self):
        self.assertEqual(
            self.program("""
                struct Original {
                    i32* counter;
                    i32 padding;
                    Original(i32* p){init counter(p);}
                    ~Original(){*counter+=1;}
                };
                struct Replacement {
                    i32* counter;
                    Replacement(i32* p){init counter(p);}
                    ~Replacement(){*counter+=10;}
                };
                consteval i32 repeated(){
                    i32 n(7);
                    i32* old(&n);
                    std::mem::StorageView extent(storage_of(n));
                    std::mem::StorageIdentity original(extent.identity());
                    destroy(n);
                    auto current(construct_at<i32>(extent,21));
                    if(old!=current){return 0;}
                    auto same_extent(storage_of(*current));
                    if(same_extent.identity()!=original
                       || same_extent.capacity_bytes()!=4
                       || same_extent.alignment()!=4){return 0;}
                    destroy(*current);
                    return *construct_at<i32>(same_extent,42);
                }
                consteval i32 cross_type(){
                    i32 count;
                    {
                        Original source(&count);
                        auto extent(storage_of(source));
                        destroy(source);
                        construct_at<Replacement>(extent,&count);
                    }
                    return count;
                }
                constexpr i32 result(repeated());
                constexpr i32 dropped(cross_type());
                i32 main(){
                    i32 native;
                    auto extent(storage_of(native));
                    auto identity(extent.identity());
                    destroy(native);
                    auto new_object(construct_at<i32>(extent,4));
                    auto new_view(storage_of(*new_object));
                    return dropped==11 && new_view.identity()==identity
                        && new_view.capacity_bytes()==4
                        && new_view.alignment()==4 ? result : 0;
                }
            """),
            42,
        )

    def test_consteval_replaces_active_union_case_and_rejects_stale_generations(self):
        self.assertEqual(
            self.program("""
                union Message {default case Empty;case Value(i32 number);};
                consteval i32 read(){
                    Message message;
                    abandon(message);
                    auto replacement(construct_at<Message>(
                        storage_of(message), Message::Value(42)));
                    match(*replacement){
                      case Message::Empty{return 0;}
                      case Message::Value(ref number){return number;}
                    }
                }
                constexpr i32 result(read());
                i32 main(){return result;}
            """),
            42,
        )
        for body, message in (
            (
                "i32 x; construct_at<i32>(storage_of(x),4); return 0;",
                "live generation",
            ),
            (
                "i8 x; destroy(x); construct_at<i64>(storage_of(x),4); return 0;",
                "insufficient storage capacity",
            ),
            (
                "i32 x; i32* old(&x); destroy(x); "
                "construct_at<i32>(storage_of(x),4); return *old;",
                "ended object generation",
            ),
        ):
            with self.subTest(body=body):
                result = self.compile(
                    "consteval i32 invalid(){" + body + "}"
                    "constexpr i32 value(invalid());",
                    "--check",
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)

    def test_constexpr_match_keeps_prvalue_payload_alive_through_arm_exit(self):
        source = """
            struct Payload {
                i32* trace;
                Payload(i32* p){init trace(p);}
                ~Payload(){*trace=*trace*10+2;}
            };
            union U {case One(Payload field);};
            constexpr i32 fold(){
                i32 trace;
                while(true){
                    match(U::One(Payload(&trace))){
                        case U::One(ref field){*field.trace=1;break;}
                    }
                }
                return trace;
            }
            constexpr i32 constant_trace(fold());
            i32 main(){return constant_trace==12 && fold()==12 ? 42 : 1;}
        """
        self.assertEqual(self.program(source), 42)

        expired = self.compile(
            """
            union U{case One(i32 field);};
            consteval i32 expired(){
                i32* pointer(nullptr);
                match(U::One(42)){case U::One(ref field){pointer=&field;}}
                return *pointer;
            }
            constexpr i32 result(expired());
            """,
            "--check",
        )
        self.assertEqual(expired.returncode, 1)
        self.assertIn("lifetime ended", expired.stderr)

    def test_constexpr_reconstructs_active_payload_at_its_cleanup_rank(self):
        self.assertEqual(
            self.program("""
                struct Original {
                    i32* trace; i32 digit;
                    Original(i32* p,i32 n){init trace(p);init digit(n);}
                    ~Original(){*trace=*trace*10+digit;}
                };
                struct Replacement {
                    i32* trace;
                    Replacement(i32* p){init trace(p);}
                    ~Replacement(){*trace=*trace*10+9;}
                };
                union U{case Pair(Original first,Original second);};
                constexpr i32 fold(){
                    i32 trace;
                    {
                        U object(U::Pair(Original(&trace,1),Original(&trace,2)));
                        match(object){case U::Pair(ref first,ref second){
                            auto slot(storage_of(first));
                            auto other(storage_of(second));
                            if(slot.identity()==other.identity()){return 0;}
                            destroy(first);
                            auto current(construct_at<Replacement>(slot,&trace));
                            auto current_slot(storage_of(*current));
                            if(current_slot.identity()!=slot.identity() ||
                               current_slot.capacity_bytes()!=sizeof(Original) ||
                               second.digit!=2){return 1;}
                        }}
                    }
                    return trace;
                }
                constexpr i32 constant_trace(fold());
                i32 main(){return constant_trace==129 && fold()==129 ? 42 : 1;}
            """),
            42,
        )
        source = """
            union U{case Field(i32 value);U(const<U>& other)=default;};
            MODE i32 fold(){
                U object(U::Field(42));
                match(object){case U::Field(ref field){BODY}}
            }
            RESULT
        """
        for body, message in (
            (
                "auto old(&field);auto view(storage_of(field));destroy(field);"
                "construct_at<i32>(view,42);return *old;",
                "ended object generation",
            ),
            (
                "auto view(storage_of(field));destroy(field);"
                "construct_at<i64>(view,42);return 0;",
                "insufficient storage capacity",
            ),
            (
                "auto view(storage_of(field));destroy(field);"
                "auto fresh(construct_at<i32>(view,42));abandon(object);return *fresh;",
                "ended object generation",
            ),
            (
                "destroy(field);U copy(object);return 0;",
                "ended object generation",
            ),
        ):
            with self.subTest(body=body):
                result = self.compile(
                    source.replace("MODE", "consteval")
                    .replace("BODY", body)
                    .replace("RESULT", "constexpr i32 result(fold());"),
                    "--check",
                )
                self.assertEqual(result.returncode, 1)
                self.assertIn(message, result.stderr)
        self.assertEqual(
            self.program(
                source.replace("MODE", "")
                .replace("BODY", "destroy(field);U copy(object);return 0;")
                .replace("RESULT", "i32 main(){return fold();}")
            ),
            -signal.SIGILL,
        )

    def test_constexpr_authored_union_copy_checks_contract_before_payload_copy(self):
        self.assertEqual(
            self.program("""
                struct Cell {
                    i32* count;
                    Cell(i32* p){init count(p);}
                    Cell(const<Cell>& other){init count(other.count);++*count;}
                };
                declare union U;
                declare constexpr bool first_copy(const<U>& value)
                    [[effects(read(value))]];
                union U {
                    case Data(Cell part);
                    [[requires(first_copy(other))]] U(const<U>& other){}
                };
                constexpr bool first_copy(const<U>& value) [[effects(read(value))]] {
                    match(value){case U::Data(ref part){return *part.count==0;}}
                }
                constexpr i32 fold(){
                    i32 count;U original(U::Data(Cell(&count)));U copy(original);
                    return count;
                }
                constexpr i32 copies(fold());
                i32 main(){return copies==1 && fold()==1 ? 42 : 1;}
            """),
            42,
        )

    def test_constexpr_tagged_assignment_invokes_the_authored_operation(self):
        self.assertEqual(
            self.program("""
                union U {
                    case Data(i32 value);
                    constexpr U& operator=(const<U>& other){
                        i32 incoming;
                        match(other){case U::Data(ref field){incoming=field;}}
                        match(*this){case U::Data(ref field){field=incoming+1;}}
                        return *this;
                    }
                };
                constexpr i32 fold(){
                    U a(U::Data(1));U b(U::Data(41));U& result(a=b);
                    match(result){case U::Data(ref field){return field;}}
                }
                constexpr i32 computed(fold());
                i32 main(){return computed==42 && fold()==42 ? 42 : 1;}
            """),
            42,
        )
        result = self.compile(
            """
            union U{case A;case B;};
            consteval i32 rejected(){U value(U::A());value=U::B();return 0;}
            constexpr i32 failure(rejected());
            """,
            "--check",
        )
        self.assertEqual(result.returncode, 1)
        self.assertRegex(result.stderr, "assignment|overload")

    def test_tagged_assignment_returns_the_fresh_case_generation(self):
        source = """
            union U {
                case Empty;
                case Data(i32 number);
                U(const<U>& other)=default;
                constexpr U& operator=(const<U>& other){
                    auto slot(storage_of(*this));
                    destroy(*this);
                    return *construct_at<U>(slot,other);
                }
            };
            constexpr i32 fold(){
                U target(U::Empty());U original(U::Data(42));
                auto slot(storage_of(target));
                U& fresh(target=original);
                auto new_view(storage_of(fresh));
                if(new_view.identity()!=slot.identity()){return 1;}
                match(fresh){case U::Empty{return 2;}
                             case U::Data(ref number){return number;}}
            }
            constexpr i32 computed(fold());
            i32 main(){return computed==42 && fold()==42 ? 42 : 3;}
        """
        self.assertEqual(self.program(source), 42)
        stale = self.compile(source.replace("match(fresh)", "match(target)"), "--check")
        self.assertEqual(stale.returncode, 1)
        self.assertIn("ended object generation", stale.stderr)

    def test_literal_rounding_classifies_overflow_before_destination_clamp(self):
        for mode, dest, token in (
            ("toward_zero", "f32", "0x1p128"),
            ("toward_negative_infinity", "f32", "0x1p128"),
            ("toward_positive_infinity", "f32", "-0x1p128"),
            ("toward_zero", "f64", "0x1p1024"),
            ("toward_zero", "f32", "340282366920938463463374607431768211456"),
        ):
            with self.subTest(mode=mode, dest=dest, token=token):
                result = self.compile(
                    f"configuration {{numeric.literal.real_rounding={mode};}};"
                    f"void invalid(){{{dest} n({token});}}",
                    "--check",
                )
                self.assertEqual(result.returncode, 1)
                self.assertIn(f"floating literal overflows {dest}", result.stderr)
        self.assertEqual(
            self.program(
                """
                configuration {numeric.literal.real_rounding=toward_zero;};
                constexpr f32 max_from_real(0x1.ffffffp127);
                constexpr f32 max_from_int(340282356779733661637539395458142568448);
                extern "C" f32 real_projection(){return max_from_real;}
                extern "C" f32 integer_projection(){return max_from_int;}
                extern "C" f32 negative_zero(){return -0.0;}
                """,
                host="""
                #include <stdint.h>
                #include <string.h>
                #include <xmmintrin.h>
                extern float real_projection(void), integer_projection(void), negative_zero(void);
                static uint32_t bits(float x){uint32_t out;memcpy(&out,&x,4);return out;}
                int main(void){
                    unsigned saved=_mm_getcsr();
                    _mm_setcsr((saved | 0x1f80u) & ~0x3fu);
                    int valid=bits(real_projection())==0x7f7fffffu &&
                              bits(integer_projection())==0x7f7fffffu &&
                              bits(negative_zero())==0x80000000u &&
                              !(_mm_getcsr() & 0x3du);
                    _mm_setcsr(saved);
                    return valid ? 42 : 1;
                }
                """,
            ),
            42,
        )


if __name__ == "__main__":
    unittest.main()
