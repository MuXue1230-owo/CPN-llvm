#include "Sema.h"
#include "llvm/IR/ConstantFold.h"
using namespace cpn;
using llvm::StringRef;

bool Frame::containsPointerField(const std::string &Type) const {
  auto T = unconst(Type);
  if (StringRef(T).ends_with("]")) {
    auto E = element(T);
    return !StringRef(T).ends_with("[0]") &&
           (carriesPointerBounds(E) || containsPointerField(E));
  }
  auto It = U.Records.find(T);
  return It != U.Records.end() &&
         llvm::any_of(It->second.Fields, [&](const Field &F) {
           return carriesPointerBounds(F.Type) || containsPointerField(F.Type);
         });
}
Value Frame::constantAggregate(const std::string &T,
                               const std::vector<Node> &Args, const Token &At,
                               const Node *Tail) {
  if (Tail)
    fail(At, "constant evaluation of construction tails is unavailable");
  auto *Ty = U.ir(T, At);
  auto *Array = llvm::dyn_cast<llvm::ArrayType>(Ty);
  if (U.Variants.count(T))
    fail(At,
         "constant evaluation of a tagged payload requires its active case");
  auto *Record = Array ? nullptr : &U.Records.at(T);
  if (Record && (Record->VirtualCount || Record->Polymorphic))
    fail(At, "constant evaluation of virtual object layout is unavailable");
  size_t Count =
      Array ? (StringRef(T).ends_with("[0]") ? 0 : Array->getNumElements())
            : Record->Fields.size();
  size_t Bases = Array ? 0 : Record->Bases.size();
  std::string Elem = Array ? element(T) : "";
  std::vector<Value> Input;
  for (size_t I = 0; I < Args.size(); ++I) {
    auto Expected = Array               ? Elem
                    : I + Bases < Count ? Record->Fields[I + Bases].Type
                                        : "";
    Input.push_back(eval(Args[I], unconst(Expected)));
  }
  if (Input.size() == 1 && Input.front().Type == T) {
    auto V = Input.front();
    if (V.Address && !V.Prvalue &&
        !constructible(T,
                       V.Expiring ? SpecialOperation::MoveConstruct
                                  : SpecialOperation::CopyConstruct,
                       At))
      fail(At, "no available constant copy or move construction");
    if (Record && !V.Prvalue) {
      auto Op = V.Expiring ? SpecialOperation::MoveConstruct
                           : SpecialOperation::CopyConstruct;
      if (auto S = Record->Special.find(Op);
          S != Record->Special.end() && S->second.Body)
        fail(At, "authored constant copy or move construction is unavailable");
    }
    V.IR = load(V).IR;
    V.Address = nullptr;
    V.Expiring = V.Prvalue = true;
    return V;
  }
  if (Record && U.Overloads.count(T + "::$ctor")) {
    Function Aggregate;
    Aggregate.Owner = T;
    Aggregate.Decl = Node(Node::Constructor, At);
    bool Fits = Args.size() <= Count - Bases;
    if (Fits)
      for (size_t I = 0; I < Args.size(); ++I)
        Aggregate.Params.push_back(Record->Fields[Bases + I].Type);
    if (select("$ctor", Node(Node::Name, At), Input, {T}, false,
               Fits ? &Aggregate : nullptr) != &Aggregate)
      fail(At, "authored constructor requires constant-evaluation support");
  }
  if (Args.size() > Count - Bases)
    fail(At, "too many aggregate initializers");
  auto scalar = [&](const std::string &S) {
    auto E = unconst(S);
    return integer(E) || floating(E) || E == "bool" || E == "char" ||
           E == "nullptr_t" || StringRef(E).ends_with("*");
  };
  Value Result{T};
  Result.Prvalue = Result.Expiring = true;
  if ((Array && Input.empty() && scalar(Elem)) || Count == 0) {
    Result.IR = llvm::Constant::getNullValue(Ty);
    return Result;
  }
  if (Count > 100000 ||
      (U.ConstantDepth && (U.ConstantSteps += Count) > 100000))
    fail(At, "constant evaluation step budget exhausted");
  std::vector<llvm::Constant *> Fields;
  Frame Init(U, F, nullptr, Record ? T + "::" : Prefix);
  Init.Env = Record ? Record->Env : Env;
  Init.Opt = Opt;
  Init.LookupLimit = LookupLimit;
  if (Record)
    for (const auto &Field : Record->Fields)
      Init.Scopes[0].Names[Field.Decl.Text] = {};
  for (size_t I = 0; I < Count; ++I) {
    auto Type = Array ? Elem : Record->Fields[I].Type;
    Value V;
    if (I >= Bases && I - Bases < Input.size())
      V = convert(Input[I - Bases], unconst(Type), At);
    else if (Array)
      V = construct(Elem, {}, At);
    else {
      const auto &Field = Record->Fields[I];
      llvm::SaveAndRestore Policy(Init.Opt);
      llvm::SaveAndRestore Limit(Init.LookupLimit);
      if (Field.DefaultSite) {
        Init.Opt = Field.DefaultSite->Configuration;
        Init.LookupLimit = Field.DefaultSite->Through;
      }
      V = Init.construct(Type, Field.Decl.Children, Field.Decl.At);
    }
    auto *C = llvm::dyn_cast_or_null<llvm::Constant>(V.IR);
    if (!C || C->getType() != U.ir(Type, At))
      fail(At, "constant aggregate element required");
    Fields.push_back(C);
    if (Record)
      Init.Scopes[0].Names[Record->Fields[I].Decl.Text] = V;
  }
  Result.IR = Array ? llvm::ConstantArray::get(Array, Fields)
                    : llvm::ConstantStruct::get(Record->IR, Fields);
  return Result;
}

// Resolve the destination and its subscripts once, before evaluating the right
// side. Commit into the current aggregate so sibling updates made by that
// evaluation retain their values.
Value Frame::constantAssignment(const Node &N) {
  const Node *Root = &N.Children.front();
  std::vector<const Node *> Path;
  while (Root->K == Node::Index ||
         (Root->K == Node::Member && !Root->Definition)) {
    Path.push_back(Root);
    Root = &Root->Children.front();
  }
  if (Root->K != Node::Name)
    fail(N.At, "constant assignment requires a local variable");
  auto Scope = llvm::find_if(llvm::reverse(Scopes), [&](const Local &L) {
    return L.Names.count(Root->Text);
  });
  if (Scope == Scopes.rend())
    fail(N.At, "constant assignment requires a local variable");
  auto &LocalValue = Scope->Names.at(Root->Text);
  if (LocalValue.Address)
    fail(N.At, "constant evaluation cannot mutate runtime storage");
  auto Type = LocalValue.Type;
  bool Readonly = LocalValue.Readonly;
  std::vector<unsigned> Indices;
  for (auto *Part : llvm::reverse(Path)) {
    if (Part->K == Node::Index) {
      if (!StringRef(Type).ends_with("]"))
        fail(Part->At, "constant array position required");
      auto Index = eval(Part->Children[1]);
      auto *I = llvm::dyn_cast_or_null<llvm::ConstantInt>(Index.IR);
      auto Count = llvm::cast<llvm::ArrayType>(U.ir(Type))->getNumElements();
      if (!integer(Index.Type) || !I || StringRef(Type).ends_with("[0]") ||
          I->getValue().uge(Count) || !I->getValue().isIntN(32))
        fail(Part->At, "constant array index outside extent");
      Indices.push_back(I->getZExtValue());
      Type = element(Type);
    } else {
      if (!U.Records.count(Type))
        fail(Part->At, "member access requires a record");
      auto Bases = U.lookupPath(Type, Part->At, false);
      if (!Bases)
        fail(Part->At, "unknown constant field");
      for (auto I : *Bases) {
        Indices.push_back(I);
        Type = U.Records.at(Type).Bases[I];
      }
      auto &R = U.Records.at(Type);
      auto Field = llvm::find_if(
          R.Fields, [&](const auto &F) { return F.Decl.Text == Part->Text; });
      if (Field == R.Fields.end())
        fail(Part->At, "constant assignment requires a local field");
      checkAccess(Field->Decl, Type, Part->At);
      Indices.push_back(Field - R.Fields.begin());
      Type = Field->Type;
      Readonly |= Field->Decl.Const;
    }
    Readonly |= Type != unconst(Type);
    Type = unconst(Type);
  }
  if (Readonly)
    fail(N.At, "writable lvalue required");
  Value Old = LocalValue;
  if (!Indices.empty()) {
    auto *C = llvm::dyn_cast_or_null<llvm::Constant>(LocalValue.IR);
    if (!C)
      fail(N.At, "constant aggregate value required");
    Old = {Type, llvm::ConstantFoldExtractValueInstruction(C, Indices)};
  }
  Value V;
  if (N.Text == "=")
    V = eval(N.Children[1], Type);
  else {
    Node Op = N;
    Op.Text = N.Text == "++"   ? "+"
              : N.Text == "--" ? "-"
                               : N.Text.substr(0, N.Text.size() - 1);
    V = binary(Op, Old, N.K == Node::Unary ? literal(1) : eval(N.Children[1]));
  }
  V = convert(V, Type, N.At);
  if (Indices.empty())
    LocalValue = V;
  else
    LocalValue.IR = llvm::ConstantFoldInsertValueInstruction(
        llvm::cast<llvm::Constant>(LocalValue.IR),
        llvm::cast<llvm::Constant>(V.IR), Indices);
  return N.Definition ? Old : V;
}
