#include "Sema.h"
#include "llvm/ADT/ScopeExit.h"
#include "llvm/Analysis/ValueTracking.h"
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
Value Frame::constantTemporary(Value V) {
  if (!V.Prvalue || !U.aggregate(V.Type) || V.ConstantTemporary)
    return V;
  V.Location.reset();
  V.ConstantTemporary = std::make_shared<Value>(V);
  V.Location = std::make_shared<ConstantPlace>(
      ConstantPlace{V.ConstantTemporary.get(), {}, V.Type, V.Readonly});
  V.Location->trackLifetime();
  Temps.push_back(V);
  return V;
}

Value Frame::constantSelf(const Token &At) {
  auto Place = ConstantReceiver->Location
                   ? *ConstantReceiver->Location
                   : ConstantPlace{ConstantReceiver,
                                   {},
                                   ConstantReceiver->Type,
                                   ConstantReceiver->Readonly};
  Place.Readonly |= ConstantReceiver->Readonly;
  Place.trackLifetime();
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

bool Frame::containsDispatchState(const std::string &Type) const {
  auto T = unconst(Type);
  if (StringRef(T).ends_with("]"))
    return !StringRef(T).ends_with("[0]") && containsDispatchState(element(T));
  if (auto Cases = U.Variants.find(T); Cases != U.Variants.end())
    return llvm::any_of(Cases->second, [&](const auto &Key) {
      return llvm::any_of(U.Cases.at(Key).Types, [&](const auto &Field) {
        return containsDispatchState(Field);
      });
    });
  auto It = U.Records.find(T);
  return It != U.Records.end() &&
         (It->second.Polymorphic || It->second.VirtualCount ||
          llvm::any_of(It->second.Fields, [&](const Field &F) {
            return containsDispatchState(F.Type);
          }));
}
Value Frame::constantConstructor(Function &D, const std::vector<Value> &Args,
                                 const Token &At, const Node *Tail,
                                 Value *BaseDestination) {
  requireObserver(D.Effects, At, &D);
  if (D.Decl.Prototype || D.Decl.Children.empty())
    fail(At, "constant construction requires a constructor definition");
  Frame Root(U, &D, nullptr);
  Root.BaseLayer = BaseDestination != nullptr;
  for (size_t I = 0; I < Args.size(); ++I)
    if (!StringRef(D.Params[I]).ends_with("&") && Args[I].Prvalue)
      consume(Args[I]);
  Root.bindInlineParams(Args);
  Root.checkContracts(true);
  Value Object =
      BaseDestination
          ? *BaseDestination
          : Value{D.Owner, llvm::Constant::getNullValue(U.ir(D.Owner))};
  if (U.Variants.count(D.Owner)) {
    auto Default = U.DefaultCase.find(D.Owner);
    if (Default == U.DefaultCase.end())
      fail(At, "union construction requires a selected case");
    Object =
        Root.variant(U.Cases.at(Default->second), {}, At, nullptr, true, false);
    Root.ConstantReceiver = &Object;
    U.ConstantInvariantLifetimes.push_back(&Object);
    auto End =
        llvm::scope_exit([&] { U.ConstantInvariantLifetimes.pop_back(); });
    Root.constructorBody(D.Decl.Children.front());
    return Object;
  }
  Construction Plan(Root, D, Object, Tail, this);
  Plan.run(Root);
  return load(Plan.constantResult());
}

Value Frame::constantCopy(Value Source, const Token &At, bool CheckInvariant,
                          Value *BaseDestination) {
  ConstantActivation Activation(U, At);
  const auto Type = unconst(Source.Type);
  if (Source.Location) {
    const auto &Place = *Source.Location;
    Place.checkLifetime(At);
    const auto &Storage = Place.Root->ConstantIdentity.Storage;
    if (Storage && !Storage->Subobjects.empty() &&
        StringRef(Type).ends_with("]")) {
      const auto Position = Place.indices();
      size_t LastElement = Position.size();
      for (auto Array = Type; StringRef(Array).ends_with("]");
           Array = unconst(element(Array)))
        ++LastElement;
      if (llvm::any_of(Storage->Subobjects, [&](const auto &Entry) {
            const auto &[Path, Element] = Entry;
            return Element.Ended && Path.size() > Position.size() &&
                   Path.size() <= LastElement &&
                   llvm::ArrayRef(Path).take_front(Position.size()) ==
                       llvm::ArrayRef(Position);
          }))
        fail(At, "array copy observes an ended element generation");
    }
  }
  if (Source.Expiring && Source.Readonly && U.Records.count(Type))
    fail(At, "moving requires a mutable source");
  auto Op = Source.Expiring ? SpecialOperation::MoveConstruct
                            : SpecialOperation::CopyConstruct;
  if (!constructible(Type, Op, At))
    fail(At, "no available constant copy or move construction");
  if (auto R = U.Records.find(Type);
      R != U.Records.end() && !U.Variants.count(Type)) {
    auto &Record = R->second;
    Value Dest = BaseDestination
                     ? *BaseDestination
                     : Value{Type, llvm::Constant::getNullValue(Record.IR)};
    auto Special = Record.Special.find(Op);
    if (Special != Record.Special.end() && Special->second.Body)
      Dest = constantConstructor(*Special->second.Body, {Source}, At, nullptr,
                                 BaseDestination);
    else
      for (unsigned I = BaseDestination ? Record.VirtualCount : 0;
           I < Record.Fields.size(); ++I) {
        auto Part = constantField(Source, I, At);
        Part.Expiring = Source.Expiring;
        if (I < Record.Bases.size()) {
          auto Base = constantField(Dest, I, At);
          constantCopy(Part, At, true, &Base);
        } else {
          auto Copy = constantCopy(Part, At);
          constantFieldPlace(Dest, I).write(*this, Copy, At);
        }
      }
    bindConstantVirtualLayout(Dest, At);
    installConstantTables(Dest, At);
    Dest = load(Dest);
    Dest.Prvalue = Dest.Expiring = true;
    if (CheckInvariant)
      checkInvariants(Dest);
    return Dest;
  }
  auto *C = llvm::dyn_cast_or_null<llvm::Constant>(Source.IR);
  if (!C)
    fail(At, "constant source object required");
  auto subobject = [&](const std::string &FieldType, unsigned I,
                       const Case *Alternative = nullptr) {
    auto *Fields = Alternative ? unpackVariant(*Alternative, C, At) : C;
    auto T = unconst(FieldType);
    bool Readonly = Source.Readonly || FieldType != T ||
                    (Alternative && Alternative->Decl.Params[I].Const);
    Value V{T, Fields->getAggregateElement(I), nullptr, Readonly};
    if (Source.Location) {
      auto Place = *Source.Location;
      Place.Type = T;
      Place.Readonly |= Readonly;
      Place.Steps.push_back({I, Alternative});
      V = Place.read(*this, At);
      V.Location = std::make_shared<ConstantPlace>(std::move(Place));
    }
    V.Expiring = Source.Expiring;
    return llvm::cast<llvm::Constant>(constantCopy(V, At).IR);
  };
  if (auto R = U.Records.find(Type); R != U.Records.end()) {
    auto S = R->second.Special.find(Op);
    auto CopyPayload = [&] {
      auto Tag = llvm::cast<llvm::ConstantInt>(C->getAggregateElement(0u))
                     ->getZExtValue();
      auto &Alternative = U.Cases.at(U.Variants.at(Type).at(Tag));
      std::vector<llvm::Constant *> Fields;
      for (unsigned I = 0; I < Alternative.Types.size(); ++I)
        Fields.push_back(subobject(Alternative.Types[I], I, &Alternative));
      return packVariant(Alternative,
                         llvm::ConstantStruct::get(Alternative.Payload, Fields),
                         At);
    };
    if (S == R->second.Special.end() || !S->second.Body)
      C = CopyPayload();
    else {
      auto *D = S->second.Body;
      requireObserver(D->Effects, At, D);
      Frame Body(U, D, nullptr);
      Body.bindInlineParams({Source});
      Body.checkContracts(true);
      Value Dest{Type, CopyPayload()};
      Body.ConstantReceiver = &Dest;
      U.ConstantInvariantLifetimes.push_back(&Dest);
      auto End =
          llvm::scope_exit([&] { U.ConstantInvariantLifetimes.pop_back(); });
      Body.constructorBody(D->Decl.Children.front());
      C = llvm::cast<llvm::Constant>(Dest.IR);
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
  Source.ConstantTemporary.reset();
  Source.Prvalue = Source.Expiring = true;
  Source.Readonly = false;
  if (U.Records.count(Type))
    installConstantTables(Source, At);
  if (CheckInvariant)
    checkInvariants(Source);
  return Source;
}
Value Frame::constantAggregate(const std::string &T,
                               const std::vector<Node> &Args, const Token &At,
                               const Node *Tail, Value *BaseDestination) {
  ConstantActivation Activation(U, At);
  auto *Ty = U.ir(T, At);
  auto *Array = llvm::dyn_cast<llvm::ArrayType>(Ty);

  auto *Record = Array ? nullptr : &U.Records.at(T);
  auto finishTail = [&](Value V) {
    if (Record) {
      bindConstantVirtualLayout(V, At);
      installConstantTables(V, At);
    }
    if (Tail) {
      llvm::SaveAndRestore<Construction *> Outer(Transaction, nullptr);
      llvm::SaveAndRestore Receiver(ConstantReceiver, &V);
      U.ConstantInvariantLifetimes.push_back(&V);
      auto End =
          llvm::scope_exit([&] { U.ConstantInvariantLifetimes.pop_back(); });
      try {
        stmt(*Tail);
      } catch (const ConstantTransfer &) {
        constantDrop(V, Tail->At, V.BaseView, false);
        throw;
      }
    }
    V = load(V);
    checkInvariants(V);
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
    if (!V.Prvalue || BaseDestination)
      V = constantCopy(V, At, false, BaseDestination);
    else {
      consume(V);
      V.Location.reset();
      V.ConstantTemporary.reset();
    }
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
      return finishTail(
          constantConstructor(*D, Input, At, Tail, BaseDestination));
    }
    if (!U.DefaultCase.count(T))
      fail(At, "union construction requires a selected case");
    return finishTail(
        variant(U.Cases.at(U.DefaultCase.at(T)), {}, At, nullptr, true, false));
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
      return finishTail(
          constantConstructor(*D, Input, At, Tail, BaseDestination));
  }
  if (Args.size() > Count - Bases)
    fail(At, "too many aggregate initializers");
  auto scalar = [&](const std::string &S) {
    auto E = unconst(S);
    return integer(E) || floating(E) || E == "bool" || E == "char" ||
           E == "nullptr_t" || StringRef(E).ends_with("*");
  };
  Value Result = BaseDestination ? *BaseDestination
                                 : Value{T, llvm::Constant::getNullValue(Ty)};
  Result.Prvalue = Result.Expiring = true;
  if ((Array && Input.empty() && scalar(Elem)) || Count == 0) {
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
  for (size_t I = BaseDestination ? Record->VirtualCount : 0; I < Count; ++I) {
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
      if (I < Bases) {
        auto Base = constantField(Result, I, At);
        if (Producer != Producers.end())
          Scopes.push_back(Init.Scopes[0]);
        auto &Source = Producer == Producers.end() ? Init : *this;
        V = Source.constantAggregate(Type,
                                     Producer == Producers.end()
                                         ? Field.Decl.Children
                                         : Producer->second->Children,
                                     At, nullptr, &Base);
        if (Producer != Producers.end()) {
          Scopes.pop_back();
          Producers.erase(Producer);
        }
      } else if (Producer != Producers.end()) {
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
    if (!C || (I >= Bases && C->getType() != U.ir(Type, At)))
      fail(At, "constant aggregate element required");
    if (Array)
      Fields.push_back(C);
    else if (I >= Bases)
      constantFieldPlace(Result, I).write(*this, V, At);
    Init.endExpression();
    if (Record)
      Init.Scopes[0].Names[Record->Fields[I].Decl.Text] = V;
  }
  if (Array)
    Result.IR = llvm::ConstantArray::get(Array, Fields);
  if (!Producers.empty())
    fail(At, "unknown initialization target");
  return finishTail(Result);
}

Value Frame::constantAddress(const ConstantPlace &Place, const Token &At,
                             bool ExtentOnly) {
  Place.checkLifetime(At, ExtentOnly);
  if (Place.Lifetime && Place.Lifetime->expired())
    fail(At, "constant reference designates an object whose lifetime ended");
  auto PointerType =
      (Place.Readonly ? qualifyConst(Place.Type) : Place.Type) + "*";
  if (Place.Root->Address) {
    auto Type = Place.Root->Type;
    auto *Address = symbolicAddress(*Place.Root, At);
    llvm::Value *Lower = Place.Root->ElementLower;
    llvm::Value *Upper = Place.Root->ElementUpper;
    for (auto Step : Place.Steps) {
      Lower = Upper = nullptr;
      if (Step.Alternative) {
        Address = llvm::cast<llvm::Constant>(
            payloadAddress(*Step.Alternative, Address, Step.Index));
        Type = Step.Alternative->Types[Step.Index];
      } else if (!Step.BaseOwner.empty()) {
        const auto &Owner = U.Records.at(Step.BaseOwner);
        Address = llvm::cast<llvm::Constant>(
            B.CreateStructGEP(Owner.IR, Address, Step.Index));
        unsigned I = Step.Index;
        if (Owner.VirtualCount && I >= Owner.tailSlot(0))
          I -= Owner.tailSlot(0);
        Type = Owner.Bases[I];
      } else if (auto *Array =
                     llvm::dyn_cast<llvm::ArrayType>(U.ir(Type, At))) {
        Lower = Address;
        Upper =
            B.CreateGEP(Array, Address,
                        {B.getInt32(0), B.getInt64(Array->getNumElements())});
        Address = llvm::cast<llvm::Constant>(B.CreateGEP(
            Array, Address, {B.getInt32(0), B.getInt64(Step.Index)}));
        Type = element(Type);
      } else {
        Address = llvm::cast<llvm::Constant>(
            fieldAddress({Type, nullptr, Address}, Step.Index));
        Type = U.Records.at(Type).Fields[Step.Index].Type;
      }
      Type = unconst(Type);
    }
    Value Pointer{PointerType, Address};
    Pointer.Lower = Lower ? Lower : Address;
    Pointer.Upper =
        Upper ? Upper
              : B.CreateGEP(U.ir(Place.Type, At), Address, B.getInt64(1));
    return Pointer;
  }
  auto &Lifetime = Place.Root->ConstantIdentity.Storage;
  if (!Lifetime)
    Lifetime = std::make_shared<ConstantStorage>();
  for (auto *Address : Lifetime->Designations)
    if (U.LocalConstantAddresses.at(Address).Place.Steps == Place.Steps)
      return {PointerType, Address};
  U.chargeConstant(At);
  auto *Ty = U.ir(Place.Type, At);
  auto *Address = new llvm::GlobalVariable(
      U.M, Ty, true, llvm::GlobalValue::PrivateLinkage,
      llvm::PoisonValue::get(Ty), "cpn.constant.address");
  auto Storage = Place;
  Storage.Readonly = false;
  auto *Physical = Lifetime->OriginalExtent && Place.Steps.empty()
                       ? llvm::cast<llvm::GlobalVariable>(
                             constantAddress(*Lifetime->OriginalExtent, At,
                                             /*ExtentOnly=*/true)
                                 .IR)
                       : Address;
  U.LocalConstantAddresses.emplace(
      Address, Context::LocalConstantAddress{Storage, Lifetime, At, Physical});
  Lifetime->Designations.push_back(Address);
  return {PointerType, Address};
}

ConstantPlace Frame::constantPointerPlace(const Value &Pointer,
                                          const Token &At) {
  if (!Pointer.IR || !StringRef(Pointer.Type).ends_with("*") ||
      Pointer.Type == "void*")
    fail(At, "typed object pointer required");
  if (llvm::isa<llvm::ConstantPointerNull>(Pointer.IR))
    fail(At, "null pointer access");
  auto Qualified = element(Pointer.Type);
  auto *Identity = llvm::dyn_cast<llvm::GlobalVariable>(
      llvm::getUnderlyingObject(Pointer.IR));
  auto It = U.LocalConstantAddresses.find(Identity);
  if (It == U.LocalConstantAddresses.end()) {
    if (Pointer.Upper) {
      int64_t Position, End;
      const auto &DL = U.M.getDataLayout();
      if (llvm::GetPointerBaseWithConstantOffset(Pointer.IR, Position, DL) ==
              llvm::GetPointerBaseWithConstantOffset(Pointer.Upper, End, DL) &&
          Position == End)
        fail(At, "cannot dereference a one-past pointer");
    }
    auto Storage =
        std::make_shared<Value>(unconst(Qualified), nullptr, Pointer.IR,
                                Qualified != unconst(Qualified));
    Storage->borrow(Pointer);
    Storage->ElementLower = Pointer.Lower;
    Storage->ElementUpper = Pointer.Upper;
    return ConstantPlace{Storage.get(),
                         {},
                         Storage->Type,
                         Storage->Readonly,
                         std::move(Storage)};
  }
  if (It->second.Lifetime.expired())
    fail(At, "constant pointer designates an object whose lifetime ended");
  if (Pointer.IR != Identity)
    fail(At, "constant local pointer offset requires an exact designation");
  auto Place = It->second.Place;
  Place.Readonly = Qualified != unconst(Qualified) || Place.Root->Readonly;
  return Place;
}

void Context::finishLocalConstantAddresses() {
  for (const auto &[Address, Binding] : LocalConstantAddresses) {
    Address->removeDeadConstantUsers();
    if (!Address->use_empty())
      fail(Binding.At, "constant result retains an evaluation-local address");
    Address->eraseFromParent();
  }
  LocalConstantAddresses.clear();
}

// Resolve the destination and its subscripts once, before evaluating the right
// side. Commit into the current aggregate so sibling updates made by that
// evaluation retain their values.
std::optional<ConstantPlace> Frame::constantPlace(const Node &N) {
  const Node *Root = &N;
  std::vector<const Node *> Path;
  std::optional<ConstantPlace> Designation;
  const bool ImplicitThis =
      ConstantReceiver && (!F || !F->Decl.Settings.count("closure"));
  while (Root->K == Node::Index || Root->K == Node::Member) {
    Path.push_back(Root);
    if (Root->K == Node::Member && Root->Definition &&
        !(ImplicitThis && Root->Children.front().K == Node::Name &&
          Root->Children.front().Text == "this")) {
      Designation =
          constantPointerPlace(eval(Root->Children.front()), Root->At);
      break;
    }
    Root = &Root->Children.front();
  }
  if (!Designation && Root->K == Node::Unary && Root->Text == "*")
    Designation = constantPointerPlace(eval(Root->Children.front()), Root->At);
  if (!Designation && Root->K != Node::Name)
    return {};
  auto Scope = llvm::find_if(llvm::reverse(Scopes), [&](const Local &L) {
    return L.Names.count(Root->Text);
  });
  Value *Target = nullptr;
  if (Designation)
    Target = Designation->Root;
  else if (ImplicitThis && Root->Text == "this" && !Path.empty())
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
  if (Target->Address && !Path.empty())
    if (auto R = U.Records.find(Target->Type);
        R != U.Records.end() && R->second.VirtualCount)
      return {};
  if (Target == ConstantReceiver && !Path.empty()) {
    if (auto It = ConstantMembersAlive.find(Path.back()->Text);
        It != ConstantMembersAlive.end() && !It->second)
      fail(N.At, "use after subobject destruction");
  }
  if (Transaction && Target == ConstantReceiver && !Path.empty())
    Transaction->checkAccess(*this, Path.back()->At);
  auto Place = Designation ? *Designation
               : Target->Location
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
      Place = constantBasePlace(std::move(Place), *Bases);
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
  Place.trackLifetime();
  return Place;
}

void ConstantPlace::trackLifetime() {
  if (Lifetime || Root->Address)
    return;
  auto &Identity = Root->ConstantIdentity.Storage;
  if (!Identity)
    Identity = std::make_shared<ConstantStorage>();
  Lifetime = Identity;
}

std::vector<unsigned> ConstantPlace::indices() const {
  std::vector<unsigned> Path;
  Path.reserve(Steps.size());
  for (const auto &Step : Steps)
    Path.push_back(Step.Index);
  return Path;
}

ConstantStorageSlot &ConstantPlace::registerExtent() const {
  auto &Storage = *Root->ConstantIdentity.Storage;
  if (Steps.empty())
    return Storage;
  return Storage.Subobjects[indices()];
}

const ConstantStorageSlot *ConstantPlace::registeredExtent() const {
  const auto &Storage = Root->ConstantIdentity.Storage;
  if (!Storage)
    return nullptr;
  if (Steps.empty())
    return Storage.get();
  auto I = Storage->Subobjects.find(indices());
  return I == Storage->Subobjects.end() ? nullptr : &I->second;
}

bool ConstantPlace::hasLiveExtent() const {
  auto *Extent = registeredExtent();
  return !Extent || !Extent->Ended ||
         (Extent->Replacement &&
          !Extent->Replacement->ConstantIdentity.Storage->Ended);
}

void ConstantPlace::checkLifetime(const Token &At, bool ExtentOnly) const {
  if (Lifetime && Lifetime->expired())
    fail(At, "constant reference designates an object whose lifetime ended");
  const auto &Identity = Root->ConstantIdentity.Storage;
  if (!Identity)
    return;
  if (Identity->Ended && (!ExtentOnly || !Steps.empty()))
    fail(At, "ended object generation");
  if (Identity->Subobjects.empty())
    return;
  std::vector<unsigned> Path;
  for (const auto &Step : Steps) {
    Path.push_back(Step.Index);
    auto I = Identity->Subobjects.find(Path);
    if (I == Identity->Subobjects.end())
      continue;
    bool Exact = Path.size() == Steps.size();
    if (I->second.Ended && (!ExtentOnly || !Exact))
      fail(At, "ended object generation");
  }
}

Value ConstantPlace::read(Frame &F, const Token &At) const {
  checkLifetime(At);
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
  if (!Steps.empty())
    V.BaseView = !Steps.back().BaseOwner.empty();
  V.Prvalue = V.Expiring = false;
  return V;
}

void ConstantPlace::write(Frame &F, Value V, const Token &At) const {
  checkLifetime(At);
  if (Readonly || Root->Address)
    fail(At, "constant assignment requires writable local storage");
  if (Steps.empty()) {
    V.Prvalue = V.Expiring = false;
    V.Location.reset();
    V.ConstantTemporary.reset();
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
  const auto &Type = Place->Type;
  if (N.Text == "=" && U.Variants.count(Type)) {
    auto Right = eval(N.Children[1], Type);
    auto Left = Place->read(*this, N.At);
    Left.Location = std::make_shared<ConstantPlace>(std::move(*Place));
    return applyOperator("operator=", N.At, {{Left, Right}, {}, {}});
  }
  auto Old = Place->read(*this, N.At);
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
