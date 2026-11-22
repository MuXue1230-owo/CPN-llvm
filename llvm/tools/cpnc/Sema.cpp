#include "Sema.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

using namespace cpn;
using llvm::StringRef;
namespace {
std::vector<std::string> arguments(StringRef S) {
  std::vector<std::string> Out;
  unsigned Depth = 0;
  size_t Start = 0;
  for (size_t I = 0; I < S.size(); ++I) {
    char C = S[I];
    if (C == '<' || C == '(' || C == '[')
      ++Depth;
    else if (C == '>' || C == ')' || C == ']') {
      if (Depth)
        --Depth;
    } else if (C == ',' && !Depth) {
      Out.push_back(S.slice(Start, I).str());
      Start = I + 1;
    }
  }
  if (Start < S.size())
    Out.push_back(S.drop_front(Start).str());
  return Out;
}
std::string appliedName(std::string Name, const Family &Family,
                        const Substitution &S) {
  Name += "<";
  for (auto &G : Family.Decl.Generics) {
    if (G.K == Node::TypeParam)
      Name += S.Types.at(G.Text);
    else {
      llvm::SmallString<32> Buf;
      llvm::cast<llvm::ConstantInt>(S.Values.at(G.Text).IR)
          ->getValue()
          .toString(Buf, 10, signedType(G.Type));
      Name += Buf.str();
    }
    Name += ",";
  }
  return Name + ">";
}
} // namespace
std::string cpn::element(const std::string &T) {
  if (StringRef(T).ends_with("]"))
    return T.substr(0, T.rfind('['));
  return T.empty() ? T : T.substr(0, T.size() - 1);
}
llvm::Type *Context::ir(const std::string &T, const Token &At) {
  if (T == "f32")
    return llvm::Type::getFloatTy(C);
  if (T == "f64")
    return llvm::Type::getDoubleTy(C);
  if (T == "void")
    return llvm::Type::getVoidTy(C);
  if (T == "nullptr_t" || T == "storage" || StringRef(T).ends_with("*") ||
      StringRef(T).ends_with("&"))
    return llvm::PointerType::getUnqual(C);
  if (integer(T) || T == "bool" || T == "char") {
    unsigned Bits = width(T);
    if (Bits)
      return llvm::IntegerType::get(C, Bits);
  }
  if (StringRef(T).ends_with("]")) {
    auto I = T.rfind('[');
    uint64_t N = 0;
    if (I == std::string::npos ||
        StringRef(T).slice(I + 1, T.size() - 1).getAsInteger(10, N))
      fail(At, "invalid array extent");
    auto *Element = ir(T.substr(0, I), At);
    if (Element->isStructTy() && !Element->isSized())
      fail(At, "incomplete record element");
    if (!llvm::ArrayType::isValidElementType(Element) || !Element->isSized())
      fail(At, "array requires a complete object element type");
    return llvm::ArrayType::get(Element, N);
  }
  if (Signatures.count(T))
    fail(At, "function type requires a pointer");
  if (Enums.count(T))
    return ir(Enums.at(T), At);
  if (Records.count(T))
    return Records.at(T).IR;
  fail(At, "unsupported or unknown type '" + T + "'");
}
Frame::Frame(Context &U, Function *F, llvm::Function *IR, std::string P)
    : U(U), F(F), B(U.M), Opt(F ? F->Configuration : U.Opt),
      Prefix(F ? F->Prefix : std::move(P)), IR(IR),
      Env(F ? F->Env : Substitution()) {
  Scopes.emplace_back();
  TracksStorage = F && IR && usesStorage(F->Decl);
}
llvm::BasicBlock *Frame::block(llvm::StringRef Name) {
  return llvm::BasicBlock::Create(U.C, Name, IR);
}
void Frame::branch(llvm::BasicBlock *Dest) {
  if (!B.GetInsertBlock()->hasTerminator())
    B.CreateBr(Dest);
}
llvm::AllocaInst *Frame::allocate(const std::string &T, const Token &At) {
  auto *Ty = U.ir(T, At);
  if (!Ty->isSized())
    fail(At, "object requires a complete object type");
  llvm::IRBuilder<> Entry(IR->getEntryBlock().begin());
  return Entry.CreateAlloca(Ty);
}
cpn::Value Frame::load(cpn::Value V) {
  if (V.Type != "storage" && !StringRef(V.Type).ends_with("*"))
    ensureLive(V, {});
  if (V.Address && U.Ready.count(V.Address)) {
    if (!IR)
      fail({}, "dynamic static read is unavailable in a constant expression");
    guard(B.CreateNot(B.CreateLoad(B.getInt1Ty(), U.Ready.at(V.Address))));
  }
  if (!V.IR && V.Address) {
    if (!IR)
      fail({}, "constant expression required");
    V.IR = B.CreateLoad(U.ir(V.Type), V.Address);
  }
  return V;
}
std::string Frame::resolve(std::string S, const Token &At) {
  if (StringRef(S).starts_with("function<") && StringRef(S).ends_with(">")) {
    size_t Open = S.find('('), Close = S.rfind(')');
    if (Open == std::string::npos || Close == std::string::npos)
      fail(At, "invalid function type");
    std::vector<std::string> Sig = {resolve(S.substr(9, Open - 9), At)};
    for (auto &P : arguments(StringRef(S).slice(Open + 1, Close)))
      Sig.push_back(resolve(P, At));
    U.Signatures[S] = std::move(Sig);
    return S;
  }
  if (floating(S) && !Opt.FloatFormats.count(S))
    fail(At, "floating format is disabled");
  if (S == "byte")
    return "u8";
  if (builtin(S) || S == "auto")
    return S;
  if (auto I = Env.Types.find(S); I != Env.Types.end())
    return I->second;
  if (StringRef(S).ends_with("]")) {
    auto I = S.rfind('[');
    auto N = constantEval(
        parseExpression(StringRef(S).slice(I + 1, S.size() - 1), Opt));
    auto *C = llvm::dyn_cast_or_null<llvm::ConstantInt>(N.IR);
    if (!C || C->isZero() || (signedType(N.Type) && C->isNegative()) ||
        C->getValue().getActiveBits() > 31)
      fail(At, "array extent is outside the range of positive extents");
    return resolve(S.substr(0, I), At) + "[" +
           std::to_string(C->getZExtValue()) + "]";
  }
  if (StringRef(S).ends_with("&") || StringRef(S).ends_with("*"))
    return resolve(element(S), At) + S.back();
  if (StringRef(S).starts_with("const<") && StringRef(S).ends_with(">"))
    return "const<" + resolve(S.substr(6, S.size() - 7), At) + ">";
  if (StringRef(S).starts_with("forward ")) {
    auto T = resolve(S.substr(8), At);
    return StringRef(T).ends_with("&") ? T : T + "&&";
  }
  std::string Base = S.substr(0, S.find('<'));
  for (std::string P = Prefix;;) {
    auto Key = P + Base;
    if (U.Families.count(Key) && S.find('<') != std::string::npos) {
      auto &Fam = U.Families.at(Key);
      std::vector<Node> Explicit;
      auto Parts = arguments(StringRef(S).slice(S.find('<') + 1, S.size() - 1));
      for (size_t I = 0; I < Parts.size(); ++I) {
        if (I >= Fam.Decl.Generics.size())
          fail(At, "too many generic arguments");
        if (Fam.Decl.Generics[I].K == Node::TypeParam) {
          Node A(Node::TypeArg, At);
          A.Type = Parts[I];
          Explicit.push_back(A);
        } else
          Explicit.push_back(parseExpression(Parts[I], Opt));
      }
      auto E = bind(Fam, Explicit, {}, At);
      auto Full = appliedName(Key, Fam, E);
      if (!U.Records.count(Full)) {
        Frame Probe(U, nullptr, nullptr, Fam.Prefix);
        Probe.Env = E;
        if (!Fam.Decl.Params.empty() &&
            !llvm::cast<llvm::ConstantInt>(
                 Probe.constantEval(Fam.Decl.Params[0]).IR)
                 ->getZExtValue())
          fail(At, "constraint is not satisfied");
        U.record(Fam.Decl, Full, Fam.Prefix, E);
      }
      return Full;
    }
    if (U.Aliases.count(Key))
      return U.Aliases.at(Key);
    if (U.Records.count(Key) || U.Enums.count(Key))
      return Key;
    if (P.empty())
      break;
    P.resize(P.size() - 2);
    auto Sep = P.rfind("::");
    P = Sep == std::string::npos ? "" : P.substr(0, Sep + 2);
  }
  fail(At, "unsupported or unknown type '" + S + "'");
}
Substitution Frame::bind(const Family &Fam, const std::vector<Node> &Explicit,
                         const std::vector<cpn::Value> &Actual,
                         const Token &At) {
  Substitution S;
  auto &G = Fam.Decl.Generics;
  if (Explicit.size() > G.size())
    fail(At, "too many generic arguments");
  for (size_t I = 0; I < G.size(); ++I) {
    auto &P = G[I];
    const Node *A = I < Explicit.size() ? &Explicit[I] : nullptr;
    if (P.K == Node::TypeParam) {
      if (A) {
        if (A->K != Node::TypeArg)
          fail(At, "expected a type argument");
        S.Types[P.Text] = resolve(A->Type, At);
      } else {
        for (size_t J = 0; J < Actual.size() && J < Fam.Decl.Params.size();
             ++J) {
          auto Formal = Fam.Decl.Params[J].Type, Ty = Actual[J].Type;
          if (StringRef(Formal).starts_with("forward ")) {
            Formal = Formal.substr(8);
            if (Actual[J].Address && !Actual[J].Expiring)
              Ty += "&";
          }
          while (StringRef(Formal).ends_with("&"))
            Formal.pop_back();
          if (StringRef(Formal).starts_with("const<") &&
              StringRef(Formal).ends_with(">"))
            Formal = Formal.substr(6, Formal.size() - 7);
          while (StringRef(Formal).ends_with("*") &&
                 StringRef(Ty).ends_with("*")) {
            Formal.pop_back();
            Ty.pop_back();
          }
          if (Formal == P.Text) {
            if (Ty == "real")
              Ty = Opt.DefaultReal;
            if (Ty == "integer")
              Ty = Opt.DefaultInt;
            if (S.Types.count(P.Text) && S.Types[P.Text] != Ty)
              fail(At, "conflicting deduction");
            S.Types[P.Text] = Ty;
          }
        }
        if (!S.Types.count(P.Text) && !P.Children.empty()) {
          auto Ty = P.Children[0].Type;
          S.Types[P.Text] = S.Types.count(Ty) ? S.Types[Ty] : resolve(Ty, At);
        }
        if (!S.Types.count(P.Text))
          fail(At, "cannot deduce generic type");
      }
    } else {
      if (!A && !P.Children.empty())
        A = &P.Children[0];
      if (!A)
        fail(At, "missing generic constant");
      Frame Defaults(U, nullptr, nullptr, Fam.Prefix);
      Defaults.Env = S;
      auto V =
          I < Explicit.size() ? constantEval(*A) : Defaults.constantEval(*A);
      S.Values[P.Text] = convert(V, Defaults.resolve(P.Type, At), At);
    }
  }
  return S;
}
Function *Context::declare(const Node &N, const std::string &Name,
                           const std::string &P, const Substitution &E,
                           const std::string &Owner) {
  Frame Resolver(*this, nullptr, nullptr, P);
  Resolver.Env = E;
  validate(N, P, Owner);
  Function D;
  D.Decl = N;
  D.DefaultParams = N.Params;
  D.Name = Name;
  D.Owner = Owner;
  D.Prefix = P;
  D.Env = E;
  D.Configuration = Opt;
  D.Result = N.K == Node::Constructor || N.K == Node::Destructor
                 ? "void"
                 : Resolver.resolve(N.Type, N.At);
  std::vector<llvm::Type *> Types;
  if (!Owner.empty())
    Types.push_back(llvm::PointerType::getUnqual(C));
  bool HasDefault = false;
  std::set<std::string> Names;
  for (auto &Arg : N.Params) {
    if (!Arg.Text.empty() && !Names.insert(Arg.Text).second)
      fail(Arg.At, "duplicate parameter");
    if (!Arg.Children.empty() &&
        (Arg.Children[0].Text == "true" || Arg.Children[0].Text == "false") &&
        integer(Resolver.resolve(Arg.Type, Arg.At)))
      fail(Arg.At, "cannot convert bool to integer");
    if (!Arg.Children.empty())
      HasDefault = true;
    else if (HasDefault)
      fail(Arg.At, "default arguments must form a trailing suffix");
    D.Params.push_back(Resolver.resolve(Arg.Type, Arg.At));
    Types.push_back(ir(D.Params.back(), Arg.At));
  }
  auto &Group = Overloads[Name];
  for (auto *Prev : Group)
    if (!Owner.empty() && Prev->Params == D.Params &&
        Prev->Decl.Const == N.Const &&
        (Prev->Decl.Settings["category"].empty() !=
         (N.Settings.count("category") == 0 ||
          N.Settings.at("category").empty())))
      fail(N.At, "duplicate category-unqualified method");
  for (auto *Prev : Group)
    if (Prev->Params == D.Params && Prev->Decl.Const == N.Const &&
        Prev->Decl.Settings["category"] ==
            (N.Settings.count("category") ? N.Settings.at("category") : "")) {
      if (Prev->Result != D.Result || Prev->Decl.Foreign != N.Foreign ||
          Prev->Decl.Noexcept != N.Noexcept)
        fail(N.At, "incompatible redeclaration");
      if (N.Prototype)
        return Prev;
      if (!Prev->Decl.Prototype)
        fail(N.At, "function already defined");
      for (auto &Arg : N.Params)
        if (!Arg.Children.empty())
          fail(Arg.At, "defaults belong to the canonical declaration");
      auto Defaults = Prev->Decl.Params;
      Prev->Decl = N;
      for (size_t I = 0; I < Defaults.size(); ++I)
        if (!Defaults[I].Children.empty())
          Prev->Decl.Params[I].Children = Defaults[I].Children;
      return Prev;
    }
  bool Export = N.Foreign || Name == "main";
  if (Name == "main" && (D.Result != "i32" || !D.Params.empty()))
    fail(N.At, "the hosted entry point must be i32 main()");
  auto *FT = llvm::FunctionType::get(ir(D.Result, N.At), Types, false);
  std::string Symbol =
      Export ? Name : "cpn." + std::to_string(Serial++) + "." + Name;
  D.IR = llvm::Function::Create(FT,
                                Export ? llvm::GlobalValue::ExternalLinkage
                                       : llvm::GlobalValue::InternalLinkage,
                                Symbol, M);
  if (N.Foreign) {
    auto ext = [&](const std::string &Ty) {
      return signedType(Ty) ? llvm::Attribute::SExt : llvm::Attribute::ZExt;
    };
    if ((integer(D.Result) || D.Result == "bool") && width(D.Result) < 32)
      D.IR->addRetAttr(ext(D.Result));
    for (size_t I = 0; I < D.Params.size(); ++I)
      if ((integer(D.Params[I]) || D.Params[I] == "bool") &&
          width(D.Params[I]) < 32)
        D.IR->addParamAttr(I, ext(D.Params[I]));
  }
  Functions.push_back(std::move(D));
  Group.push_back(&Functions.back());
  return Group.back();
}
void Context::record(const Node &N, const std::string &Name,
                     const std::string &P, const Substitution &E) {
  auto &R = Records[Name];
  if (R.Complete)
    fail(N.At, "duplicate record definition");
  if (R.IR && R.Decl.K != Node::Record)
    fail(N.At, "conflicting nominal declaration");
  if (!R.IR)
    R.IR = llvm::StructType::create(C, "cpn." + Name);
  if (N.Prototype) {
    R.Decl = N;
    return;
  }
  R.Decl = N;
  R.Env = E;
  Frame Check(*this, nullptr, nullptr, P);
  Check.Env = E;
  std::vector<llvm::Type *> Layout;
  for (auto &Base : N.TemplateArgs) {
    auto T = Check.resolve(Base.Type, Base.At);
    if (!Records.count(T) || !Records.at(T).Complete)
      fail(Base.At, "base requires a complete record");
    if (Base.Definition)
      fail(Base.At, "virtual base layout is unavailable");
    if (std::find(R.Bases.begin(), R.Bases.end(), T) != R.Bases.end())
      fail(Base.At, "duplicate direct base");
    if (Records.at(T).Decl.Settings.count("final"))
      fail(Base.At, "base must be a complete non-final record");
    auto D = Base;
    D.Text = "$base:" + T;
    D.At.Text = D.Text;
    R.Fields.push_back({D, T});
    R.Bases.push_back(T);
    Layout.push_back(ir(T, Base.At));
  }
  for (auto &D : N.Children)
    if (D.K == Node::Field) {
      auto T = Check.resolve(D.Type, D.At);
      auto *Ty = ir(T, D.At);
      if (!Ty->isSized())
        fail(D.At, "field requires a complete object type");
      if (llvm::any_of(R.Fields,
                       [&](auto &F) { return F.Decl.Text == D.Text; }))
        fail(D.At, "duplicate member");
      R.Fields.push_back({D, T});
      Layout.push_back(Ty);
    }
  R.Polymorphic =
      llvm::any_of(R.Bases,
                   [&](auto &Base) { return Records.at(Base).Polymorphic; }) ||
      llvm::any_of(N.Children,
                   [](auto &C) { return C.Settings.count("virtual"); });
  if (R.Polymorphic)
    Layout.push_back(llvm::PointerType::getUnqual(C));
  if (Layout.empty())
    Layout.push_back(llvm::Type::getInt8Ty(C));
  R.IR->setBody(Layout);
  R.Complete = true;
  std::vector<Function *> Members;
  for (auto &D : N.Children)
    if (D.K == Node::Constructor || D.K == Node::Destructor ||
        D.K == Node::Function) {
      if (D.Settings.count("control"))
        continue;
      auto Key = Name + "::" +
                 (D.K == Node::Constructor  ? "$ctor"
                  : D.K == Node::Destructor ? "$drop"
                                            : D.Text);
      Members.push_back(declare(D, Key, P, E, Name));
    }
  buildTables(Name, Members);
  for (auto *F : Members)
    emit(*F);
}
void Context::unit(const std::vector<Node> &Decls, std::string P) {
  for (auto &D : Decls) {
    auto Name = P + D.Text;
    if (D.K == Node::Config) {
      configure(Opt, D);
      continue;
    }
    if (D.K == Node::Linkage || D.K == Node::Namespace) {
      unit(D.Children, D.K == Node::Linkage ? P : Name + "::");
      continue;
    }
    if (D.K == Node::Constraint) {
      Constraints[Name] = {D, P};
      continue;
    }
    if (!D.Generics.empty()) {
      validate(D, P);
      if (Families.count(Name))
        fail(D.At, "duplicate generic declaration");
      Families[Name] = {D, P};
      continue;
    }
    if (D.K == Node::Function) {
      auto *F = declare(D, Name, P, {});
      if (!D.Prototype)
        emit(*F);
      continue;
    }
    if (D.K == Node::Union) {
      tagged(D, Name, P);
      continue;
    }
    if (D.K == Node::Record) {
      record(D, Name, P, {});
      continue;
    }
    Frame F(*this, nullptr, nullptr, P);
    if (D.K == Node::Alias) {
      Aliases[Name] = F.resolve(D.Type, D.At);
      continue;
    }
    if (D.K == Node::Enumeration) {
      auto Ty = F.resolve(D.Type, D.At);
      if (!integer(Ty))
        fail(D.At, "integer enum underlying type required");
      if (Enums.count(Name) && Enums.at(Name) != Ty)
        fail(D.At, "incompatible enum declaration");
      Enums[Name] = Ty;
      std::set<uint64_t> Values;
      for (auto &Case : D.Children) {
        if (Case.Children.empty())
          fail(Case.At, "enum case requires an explicit value");
        auto V = F.convert(F.constantEval(Case.Children[0]), Ty, Case.At);
        auto K = llvm::cast<llvm::ConstantInt>(V.IR)->getZExtValue();
        if (!Values.insert(K).second)
          fail(Case.At, "duplicate enum value");
        V.Type = Name;
        Globals[Name + "::" + Case.Text] = V;
      }
      continue;
    }
    if (D.K == Node::Object) {
      Statics.emplace_back(Name, D);
      F.object(D, true);
      continue;
    }
    fail(D.At, "unsupported declaration");
  }
}
void Context::emit(Function &D) {
  if (D.Emitted || D.Emitting || D.Decl.Prototype)
    return;
  D.Emitting = true;
  Frame F(*this, &D, D.IR);
  F.B.SetInsertPoint(F.block("entry"));
  F.bindParams();
  if (D.Decl.Settings.count("closure"))
    F.bindCaptures();
  auto &Body = D.Decl.Children.front();
  if (D.Decl.K == Node::Constructor) {
    Construction Transaction(F, D, F.Self, nullptr, nullptr);
    Transaction.run(F);
  } else if (D.Decl.K == Node::Destructor)
    F.retirement();
  else
    F.stmt(Body);
  if (F.Live) {
    if (D.Result != "void")
      fail(D.Decl.At, "function can finish without returning a value");
    F.cleanup(0);
    F.B.CreateRetVoid();
  } else if (!F.B.GetInsertBlock()->hasTerminator())
    F.B.CreateUnreachable();
  for (auto &L : F.Labels)
    if (!F.DefinedLabels.count(L.first))
      fail(D.Decl.At, "unknown statement label");
  D.Emitting = false;
  D.Emitted = true;
}
void cpn::compile(llvm::Module &M, const std::vector<Node> &AST, Options O) {
  Context U(M, std::move(O));
  U.unit(AST);
  for (auto &F : U.Functions)
    if (F.IR->isDeclaration() && !F.Decl.Foreign) {
      if (!F.IR->use_empty())
        fail(F.Decl.At, "function needs a definition");
      F.IR->eraseFromParent();
    }
  std::set<std::string> Ids, Previous;
  for (auto &[Name, N] : U.Statics) {
    if (N.Settings.count("static_id") &&
        !Ids.insert(N.Settings.at("static_id")).second)
      fail(N.At, "STAT001: duplicate static identity");
    if (N.Settings.count("init_after")) {
      auto Dep = N.Settings.at("init_after");
      if (!U.Globals.count(Dep))
        fail(N.At, "unknown static dependency");
      if (!Previous.count(Dep))
        fail(N.At, "cyclic static initialization");
    }
    Previous.insert(Name);
  }
  auto Hook = [&](std::vector<llvm::Function *> &List, bool IsStartup) {
    if (List.empty())
      return;
    if (!IsStartup)
      std::reverse(List.begin(), List.end());
    auto *FT = llvm::FunctionType::get(llvm::Type::getVoidTy(U.C), false);
    auto *F =
        llvm::Function::Create(FT, llvm::GlobalValue::InternalLinkage,
                               IsStartup ? "cpn.startup" : "cpn.shutdown", M);
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(U.C, "entry", F));
    for (auto *Call : List)
      B.CreateCall(Call);
    B.CreateRetVoid();
    if (IsStartup)
      llvm::appendToGlobalCtors(M, F, 65535);
    else
      llvm::appendToGlobalDtors(M, F, 65535);
  };
  Hook(U.Startup, true);
  Hook(U.Shutdown, false);
}
