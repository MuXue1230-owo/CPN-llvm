#include "Sema.h"
#include "llvm/IR/ConstantFold.h"
using namespace cpn;
using llvm::StringRef;

void Context::chargeConstant(const Token &At, uint64_t Steps) {
  constexpr unsigned Limit = 100000;
  if (Steps > Limit - ConstantSteps)
    throw ResourceExhausted{{At, "constant evaluation step budget exhausted"}};
  ConstantSteps += Steps;
}
ConstantActivation::ConstantActivation(Context &U, const Token &At)
    : Depth(U.ConstantDepth, U.ConstantDepth + 1) {
  if (U.ConstantDepth == 1)
    U.ConstantSteps = 0;
  if (U.ConstantDepth > 256)
    throw ResourceExhausted{{At, "constant invocation depth exhausted"}};
  U.chargeConstant(At);
}
Value Frame::constantSelf(const Token &At) {
  auto Place = ConstantReceiver->Location
                   ? *ConstantReceiver->Location
                   : ConstantPlace{ConstantReceiver,
                                   {},
                                   ConstantReceiver->Type,
                                   ConstantReceiver->Readonly};
  Place.Readonly |= ConstantReceiver->Readonly;
  auto V = Place.read(*this, At);
  V.Location = std::make_shared<ConstantPlace>(std::move(Place));
  return V;
}

bool Frame::containsPointerField(const std::string &Type) const {
  auto T = unconst(Type);
  if (StringRef(T).ends_with("]")) {
    auto E = element(T);
    return !StringRef(T).ends_with("[0]") &&
           (carriesPointerBounds(E) || containsPointerField(E));
  }
  if (auto Cases = U.Variants.find(T); Cases != U.Variants.end())
    return llvm::any_of(Cases->second, [&](const auto &Key) {
      return llvm::any_of(U.Cases.at(Key).Types, [&](const auto &Field) {
        return carriesPointerBounds(Field) || containsPointerField(Field);
      });
    });
  auto It = U.Records.find(T);
  return It != U.Records.end() &&
         llvm::any_of(It->second.Fields, [&](const Field &F) {
           return carriesPointerBounds(F.Type) || containsPointerField(F.Type);
         });
}
Value Frame::constantConstructor(Function &D, const std::vector<Value> &Args,
                                 const Token &At, const Node *Tail) {
  if (D.Decl.Prototype || D.Decl.Children.empty())
    fail(At, "constant construction requires a constructor definition");
  Frame Root(U, &D, nullptr);
  Root.bindInlineParams(Args);
  Value Object{D.Owner, llvm::Constant::getNullValue(U.ir(D.Owner))};
  if (U.Variants.count(D.Owner)) {
    auto Default = U.DefaultCase.find(D.Owner);
    if (Default == U.DefaultCase.end())
      fail(At, "union construction requires a selected case");
    Object = Root.variant(U.Cases.at(Default->second), {}, At, nullptr, true);
    Root.ConstantReceiver = &Object;
    Root.constructorBody(D.Decl.Children.front());
    return Object;
  }
  Construction Plan(Root, D, Object, Tail, this);
  Plan.run(Root);
  return Plan.constantResult();
}

Value Frame::constantCopy(Value Source, const Token &At) {
  ConstantActivation Activation(U, At);
  const auto Type = unconst(Source.Type);
  if (Source.Expiring && Source.Readonly && U.Records.count(Type))
    fail(At, "moving requires a mutable source");
  auto Op = Source.Expiring ? SpecialOperation::MoveConstruct
                            : SpecialOperation::CopyConstruct;
  if (!constructible(Type, Op, At))
    fail(At, "no available constant copy or move construction");
  auto *C = llvm::dyn_cast_or_null<llvm::Constant>(Source.IR);
  if (!C)
    fail(At, "constant source object required");
  auto subobject = [&](const std::string &FieldType, unsigned I,
                       const Case *Alternative = nullptr) {
    auto *Fields = Alternative ? unpackVariant(*Alternative, C, At) : C;
    Value V{unconst(FieldType), Fields->getAggregateElement(I), nullptr,
            Source.Readonly || FieldType != unconst(FieldType)};
    V.Expiring = Source.Expiring;
    if (Source.Location) {
      auto Place = *Source.Location;
      Place.Type = V.Type;
      Place.Readonly |= V.Readonly;
      Place.Steps.push_back({I, Alternative});
      V.Location = std::make_shared<ConstantPlace>(std::move(Place));
    }
    return llvm::cast<llvm::Constant>(constantCopy(V, At).IR);
  };
  if (auto R = U.Records.find(Type); R != U.Records.end()) {
    if (R->second.Polymorphic || R->second.VirtualCount)
      fail(At, "constant evaluation of virtual object layout is unavailable");
    auto S = R->second.Special.find(Op);
    if (S != R->second.Special.end() && S->second.Body &&
        !U.Variants.count(Type))
      C = llvm::cast<llvm::Constant>(
          constantConstructor(*S->second.Body, {Source}, At, nullptr).IR);
    else if (U.Variants.count(Type)) {
      auto Tag = llvm::cast<llvm::ConstantInt>(C->getAggregateElement(0u))
                     ->getZExtValue();
      auto &Alternative = U.Cases.at(U.Variants.at(Type).at(Tag));
      std::vector<llvm::Constant *> Fields;
      for (unsigned I = 0; I < Alternative.Types.size(); ++I)
        Fields.push_back(subobject(Alternative.Types[I], I, &Alternative));
      C = packVariant(Alternative,
                      llvm::ConstantStruct::get(Alternative.Payload, Fields),
                      At);
      if (S != R->second.Special.end() && S->second.Body) {
        Frame Body(U, S->second.Body, nullptr);
        Body.bindInlineParams({Source});
        Value Dest{Type, C};
        Body.ConstantReceiver = &Dest;
        Body.constructorBody(S->second.Body->Decl.Children.front());
        C = llvm::cast<llvm::Constant>(Dest.IR);
      }
    } else {
      std::vector<llvm::Constant *> Fields;
      for (unsigned I = 0; I < R->second.Fields.size(); ++I)
        Fields.push_back(subobject(R->second.Fields[I].Type, I));
      C = llvm::ConstantStruct::get(R->second.IR, Fields);
    }
  } else if (auto *Array = llvm::dyn_cast<llvm::ArrayType>(C->getType());
             Array && U.aggregate(unconst(element(Type))) &&
             !StringRef(Type).ends_with("[0]")) {
    std::vector<llvm::Constant *> Fields;
    for (unsigned I = 0; I < Array->getNumElements(); ++I)
      Fields.push_back(subobject(element(Type), I));
    C = llvm::ConstantArray::get(Array, Fields);
  }
  Source.Type = Type;
  Source.IR = C;
  Source.Address = nullptr;
  Source.Location.reset();
  Source.Prvalue = Source.Expiring = true;
  Source.Readonly = false;
  return Source;
}
Value Frame::constantAggregate(const std::string &T,
                               const std::vector<Node> &Args, const Token &At,
                               const Node *Tail) {
  ConstantActivation Activation(U, At);
  auto *Ty = U.ir(T, At);
  auto *Array = llvm::dyn_cast<llvm::ArrayType>(Ty);

  auto *Record = Array ? nullptr : &U.Records.at(T);
  if (Record && (Record->VirtualCount || Record->Polymorphic))
    fail(At, "constant evaluation of virtual object layout is unavailable");
  auto finishTail = [&](Value V) {
    if (Tail) {
      llvm::SaveAndRestore<Construction *> Outer(Transaction, nullptr);
      llvm::SaveAndRestore Receiver(ConstantReceiver, &V);
      stmt(*Tail);
    }
    V.Expiring = V.Prvalue = true;
    return V;
  };
  std::map<std::string, const Node *> Producers;
  if (Tail)
    for (const auto &S : Tail->Children)
      if (S.K == Node::Init && !Producers.emplace(initSlot(S), &S).second)
        fail(S.At, "duplicate initialization producer");
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
    if (!V.Prvalue)
      V = constantCopy(V, At);
    if (!Producers.empty())
      fail(At, "unknown initialization target");
    return finishTail(V);
  }
  if (U.Variants.count(T)) {
    if (!Producers.empty())
      fail(At, "unknown initialization target");
    auto Group = visibleOverloads(T + "::$ctor");
    if (!Input.empty() || llvm::any_of(Group, [](auto *D) {
          return D->Params.empty() ||
                 !D->DefaultParams.front().Children.empty();
        })) {
      if (Group.empty())
        fail(At, "union construction requires a selected case");
      auto *D = select("$ctor", Node(Node::Name, At), Input, {T});
      return finishTail(constantConstructor(*D, Input, At, Tail));
    }
    if (!U.DefaultCase.count(T))
      fail(At, "union construction requires a selected case");
    return finishTail(
        variant(U.Cases.at(U.DefaultCase.at(T)), {}, At, nullptr, true));
  }
  if (Record && U.Overloads.count(T + "::$ctor")) {
    Function Aggregate;
    Aggregate.Owner = T;
    Aggregate.Decl = Node(Node::Constructor, At);
    bool Fits = Args.size() <= Count - Bases;
    if (Fits)
      for (size_t I = 0; I < Args.size(); ++I)
        Aggregate.Params.push_back(Record->Fields[Bases + I].Type);
    auto *D = select("$ctor", Node(Node::Name, At), Input, {T}, false,
                     Fits ? &Aggregate : nullptr);
    if (D != &Aggregate)
      return finishTail(constantConstructor(*D, Input, At, Tail));
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
    if (!Producers.empty())
      fail(At, "unknown initialization target");
    return finishTail(Result);
  }
  U.chargeConstant(At, Count);
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
    if (I >= Bases && I - Bases < Input.size()) {
      if (Record && Producers.count(Record->Fields[I].Decl.Text))
        fail(At, "duplicate aggregate initialization producer");
      V = materialize(convert(Input[I - Bases], unconst(Type), At), At);
    } else if (Array)
      V = construct(Elem, {}, At);
    else {
      const auto &Field = Record->Fields[I];
      llvm::SaveAndRestore Policy(Init.Opt);
      llvm::SaveAndRestore Limit(Init.LookupLimit);
      auto Producer = Producers.find(Field.Decl.Text);
      if (Producer != Producers.end()) {
        Scopes.push_back(Init.Scopes[0]);
        V = construct(Type, Producer->second->Children, Producer->second->At);
        Scopes.pop_back();
        Producers.erase(Producer);
      } else {
        if (Field.DefaultSite) {
          Init.Opt = Field.DefaultSite->Configuration;
          Init.LookupLimit = Field.DefaultSite->Through;
        }
        V = Init.construct(Type, Field.Decl.Children, Field.Decl.At);
      }
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
  if (!Producers.empty())
    fail(At, "unknown initialization target");
  return finishTail(Result);
}

// Resolve the destination and its subscripts once, before evaluating the right
// side. Commit into the current aggregate so sibling updates made by that
// evaluation retain their values.
std::optional<ConstantPlace> Frame::constantPlace(const Node &N) {
  const Node *Root = &N;
  std::vector<const Node *> Path;
  while (Root->K == Node::Index || Root->K == Node::Member) {
    if (Root->K == Node::Member && Root->Definition &&
        !(ConstantReceiver && Root->Children.front().K == Node::Name &&
          Root->Children.front().Text == "this"))
      return {};
    Path.push_back(Root);
    Root = &Root->Children.front();
  }
  if (Root->K != Node::Name)
    return {};
  auto Scope = llvm::find_if(llvm::reverse(Scopes), [&](const Local &L) {
    return L.Names.count(Root->Text);
  });
  Value *Target = nullptr;
  if (ConstantReceiver && Root->Text == "this" && !Path.empty())
    Target = ConstantReceiver;
  else if (Scope != Scopes.rend())
    Target = &Scope->Names.at(Root->Text);
  else if (ConstantReceiver &&
           U.lookupPath(ConstantReceiver->Type, Root->At, false)) {
    Path.push_back(Root);
    Target = ConstantReceiver;
  }
  if (!Target)
    return {};
  if (Target == ConstantReceiver && !Path.empty()) {
    if (auto It = ConstantMembersAlive.find(Path.back()->Text);
        It != ConstantMembersAlive.end() && !It->second)
      fail(N.At, "use after subobject destruction");
  }
  if (Transaction && Target == ConstantReceiver && !Path.empty())
    Transaction->checkAccess(*this, Path.back()->At);
  auto Place = Target->Location
                   ? *Target->Location
                   : ConstantPlace{Target, {}, Target->Type, Target->Readonly};
  Place.Readonly |= Target->Readonly;
  auto &Type = Place.Type;
  auto &Readonly = Place.Readonly;
  auto &Indices = Place.Steps;
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
      Indices.push_back({unsigned(I->getZExtValue())});
      Type = element(Type);
    } else {
      if (!U.Records.count(Type))
        fail(Part->At, "member access requires a record");
      auto Bases = U.lookupPath(Type, Part->At, false);
      if (!Bases)
        fail(Part->At, "unknown constant field");
      for (auto I : *Bases) {
        Indices.push_back({I});
        Type = U.Records.at(Type).Bases[I];
      }
      auto &R = U.Records.at(Type);
      auto Field = llvm::find_if(
          R.Fields, [&](const auto &F) { return F.Decl.Text == Part->Text; });
      if (U.StaticMembers.count(Type + "::" + Part->Text))
        return {};
      if (Field == R.Fields.end())
        fail(Part->At, "constant assignment requires a local field");
      checkAccess(Field->Decl, Type, Part->At);
      Indices.push_back({unsigned(Field - R.Fields.begin())});
      Type = Field->Type;
      Readonly |= Field->Decl.Const;
    }
    Readonly |= Type != unconst(Type);
    Type = unconst(Type);
  }
  return Place;
}

Value ConstantPlace::read(Frame &F, const Token &At) const {
  auto V = F.load(*Root);
  for (auto S : Steps) {
    auto *C = llvm::dyn_cast_or_null<llvm::Constant>(V.IR);
    if (!C)
      fail(At, "constant aggregate value required");
    if (S.Alternative)
      C = F.unpackVariant(*S.Alternative, C, At);
    V = {Type, C->getAggregateElement(S.Index)};
  }
  V.Type = Type;
  V.Readonly = Readonly;
  V.Prvalue = V.Expiring = false;
  return V;
}

void ConstantPlace::write(Frame &F, Value V, const Token &At) const {
  if (Readonly || Root->Address)
    fail(At, "constant assignment requires writable local storage");
  if (Steps.empty()) {
    V.Prvalue = V.Expiring = false;
    V.Location.reset();
    *Root = V;
    return;
  }
  auto *C = llvm::cast<llvm::Constant>(Root->IR);
  llvm::SmallVector<llvm::Constant *> Parents;
  for (auto S : Steps) {
    if (S.Alternative)
      C = F.unpackVariant(*S.Alternative, C, At);
    Parents.push_back(C);
    C = C->getAggregateElement(S.Index);
  }
  C = llvm::cast<llvm::Constant>(V.IR);
  for (auto S : llvm::reverse(Steps)) {
    C = llvm::ConstantFoldInsertValueInstruction(Parents.pop_back_val(), C,
                                                 {S.Index});
    if (S.Alternative)
      C = F.packVariant(*S.Alternative, C, At);
  }
  Root->IR = C;
}

Value Frame::constantAssignment(const Node &N) {
  auto Place = constantPlace(N.Children.front());
  if (!Place || Place->Root->Address || Place->Readonly)
    fail(N.At, "constant assignment requires a writable local variable");
  auto Old = Place->read(*this, N.At);
  const auto &Type = Place->Type;
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
  Place->write(*this, V, N.At);
  return N.Definition ? Old : V;
}
