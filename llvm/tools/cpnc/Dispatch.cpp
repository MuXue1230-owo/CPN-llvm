#include "Sema.h"
#include "llvm/IR/ConstantFold.h"
using namespace cpn;
namespace {
bool same(Function *A, Function *B) {
  return A->Decl.Text == B->Decl.Text && A->Params == B->Params &&
         A->Decl.Const == B->Decl.Const &&
         A->Decl.Settings["category"] == B->Decl.Settings["category"];
}

ConstantPlace placeFor(Value &Object) {
  return Object.Location
             ? *Object.Location
             : ConstantPlace{&Object, {}, Object.Type, Object.Readonly};
}

ConstantPlace completePlace(ConstantPlace Place) {
  while (!Place.Steps.empty() && !Place.Steps.back().BaseOwner.empty()) {
    Place.Type = std::move(Place.Steps.back().BaseOwner);
    Place.Steps.pop_back();
  }
  return Place;
}

uint64_t layerOffset(const Context &U, const ConstantPlace &Place) {
  uint64_t Offset = 0;
  for (auto &Step : llvm::reverse(Place.Steps)) {
    if (Step.BaseOwner.empty())
      break;
    const auto &Owner = U.Records.at(Step.BaseOwner);
    Offset += U.M.getDataLayout().getStructLayout(Owner.IR)->getElementOffset(
        Step.Index);
  }
  return Offset;
}
void writeLayoutSlot(Frame &F, ConstantPlace Place, unsigned Index,
                     llvm::Constant *Value, const Token &At) {
  Place.Steps.push_back({Index});
  Place.write(F, {"", Value}, At);
}
} // namespace
bool Record::contains(const BasePath &From, const BasePath &To) const {
  if (From == To)
    return true;
  auto I = Edges.find(From);
  return I != Edges.end() && llvm::any_of(I->second, [&](const auto &Next) {
           return contains(Next, To);
         });
}
void Context::buildViews(const std::string &Name) {
  auto &Root = Records.at(Name);
  std::function<void(const std::string &, const BasePath &)> visit =
      [&](const std::string &T, const BasePath &Path) {
        if (!Root.Views.emplace(Path, T).second)
          return;
        auto &R = Records.at(T);
        for (auto I : R.Direct) {
          BasePath Next = Path;
          if (I < R.VirtualCount) {
            auto It = llvm::find(Root.Bases, R.Bases[I]);
            Next = {static_cast<unsigned>(It - Root.Bases.begin())};
          } else
            Next.push_back(I);
          Root.Edges[Path].push_back(Next);
          visit(R.Bases[I], Next);
        }
      };
  visit(Name, {});
}
std::optional<BasePath> Context::lookupPath(const std::string &Type,
                                            const Token &T, bool Method) const {
  auto RI = Records.find(Type);
  if (RI == Records.end())
    return {};
  auto &Root = RI->second;
  // Closures have no base graph.
  std::set<BasePath> Matches;
  auto collect = [&](auto &&Visit, const BasePath &Path, const Record &R,
                     const std::string &Name) -> void {
    if (Method ? Overloads.count(Name + "::" + T.Text) != 0 ||
                     FunctionFamilies.count(Name + "::" + T.Text) != 0
               : StaticMembers.count(Name + "::" + T.Text) ||
                     llvm::any_of(R.Fields, [&](auto &F) {
                       return F.Decl.Text == T.Text;
                     })) {
      Matches.insert(Path);
      return;
    }
    if (auto I = Root.Edges.find(Path); I != Root.Edges.end())
      for (auto &P : I->second)
        Visit(Visit, P, Records.at(Root.Views.at(P)), Root.Views.at(P));
  };
  collect(collect, {}, Root, Type);
  std::optional<BasePath> Found;
  for (auto &P : Matches) {
    if (llvm::any_of(Matches, [&](auto &Other) {
          return Other != P && Root.contains(Other, P);
        }))
      continue;
    if (Found)
      fail(T, Method ? "ambiguous inherited method"
                     : "ambiguous inherited member");
    Found = P;
  }
  return Found;
}
std::string Frame::methodOwner(const std::string &Type, const Token &T) {
  if (auto Path = U.lookupPath(Type, T, true))
    return Path->empty() ? Type : U.Records.at(Type).Views.at(*Path);
  return "";
}
void Context::buildTables(const std::string &Name,
                          const std::vector<Function *> &Methods) {
  auto &R = Records.at(Name);
  for (auto Index : R.Direct) {
    auto &BR = Records.at(R.Bases[Index]);
    R.VirtualDestructor |= BR.VirtualDestructor;
    for (auto *Parent : BR.Virtuals)
      if (llvm::none_of(R.Virtuals,
                        [&](auto *Item) { return same(Parent, Item); }))
        R.Virtuals.push_back(Parent);
  }
  for (auto *D : Methods) {
    if (D->Decl.K == Node::Destructor) {
      R.VirtualDestructor |= D->Decl.Settings.count("virtual");
      continue;
    }
    if (D->Decl.K != Node::Function)
      continue;
    auto It = std::find_if(R.Virtuals.begin(), R.Virtuals.end(),
                           [&](auto *Item) { return same(Item, D); });
    bool Override = D->Decl.Settings.count("override");
    if (It != R.Virtuals.end()) {
      if (!Override)
        fail(D->Decl.At, "invalid override of inherited virtual slot");
      D->Slot = It - R.Virtuals.begin();
      *It = D;
    } else if (Override)
      fail(D->Decl.At, "no matching inherited virtual slot");
    else if (D->Decl.Settings.count("virtual")) {
      D->Slot = R.Virtuals.size();
      R.Virtuals.push_back(D);
    } else if (D->Decl.Settings.count("final"))
      fail(D->Decl.At, "final requires a virtual slot");
  }
  if (!R.Polymorphic)
    return;
  for (auto &[View, ViewType] : R.Views) {
    auto &VR = Records.at(ViewType);
    if (!VR.Polymorphic)
      continue;
    std::vector<llvm::Constant *> Entries;
    DispatchTable Table{View, nullptr, {}};
    for (auto *Slot : VR.Virtuals) {
      // Select a final overrider among the layers which own this view. An
      // override in an unrelated branch cannot affect a nonshared base.
      std::map<BasePath, Function *> Candidates;
      for (auto &[Path, T] : R.Views) {
        if (!R.contains(Path, View))
          continue;
        auto &Virtuals = Records.at(T).Virtuals;
        auto It = llvm::find_if(
            Virtuals, [&](auto *F) { return F->Owner == T && same(F, Slot); });
        if (It != Virtuals.end())
          Candidates[Path] = *It;
      }
      // The static view may itself inherit this slot from a deeper base.
      if (Candidates.empty()) {
        for (auto &[Path, T] : R.Views)
          if (T == Slot->Owner && R.contains(View, Path))
            Candidates[Path] = Slot;
      }
      Function *Final = nullptr;
      BasePath Target;
      for (auto &[Path, F] : Candidates) {
        if (llvm::any_of(Candidates, [&](const auto &Other) {
              return Other.first != Path && R.contains(Other.first, Path);
            }))
          continue;
        if (Final)
          fail(R.Decl.At,
               "ambiguous final overrider of '" + Slot->Decl.Text + "'");
        Final = F;
        Target = Path;
      }
      if (!Final)
        fail(R.Decl.At, "missing final overrider");
      Entries.push_back(Final->IR);
      Table.Receivers.push_back(Target);
      Table.Targets.push_back(Final);
    }
    if (Entries.empty())
      Entries.push_back(
          llvm::ConstantPointerNull::get(llvm::PointerType::getUnqual(C)));
    auto *AT =
        llvm::ArrayType::get(llvm::PointerType::getUnqual(C), Entries.size());
    Table.Entries = new llvm::GlobalVariable(
        M, AT, true, llvm::GlobalValue::InternalLinkage,
        llvm::ConstantArray::get(AT, Entries),
        "cpn.vtable." + Name + "." + ViewType);
    DispatchTables.emplace(Table.Entries,
                           std::make_pair(Name, R.Tables.size()));
    R.Tables.push_back(std::move(Table));
  }
}
void Context::validateOverrides(const std::string &Name,
                                const std::vector<Function *> &Methods) {
  for (auto *D : Methods) {
    if (D->Decl.K != Node::Function || !D->Decl.Settings.count("override"))
      continue;
    for (const auto &[Path, Owner] : Records.at(Name).Views) {
      if (Path.empty())
        continue;
      for (auto *Base : Records.at(Owner).Virtuals) {
        if (Base->Owner != Owner || !same(Base, D))
          continue;
        // Construction-state indices belong to each declaring layer.
        if (Base->Decl.Settings.count("final") || !D->Initializes.empty() ||
            !D->RequiresAlive.empty() || D->Initializes != Base->Initializes ||
            D->RequiresAlive != Base->RequiresAlive ||
            !compatibleCallable(callableType(*D), callableType(*Base)))
          fail(D->Decl.At, "invalid override of inherited virtual slot");
        proveValueOverride(*D, *Base, Path);
      }
    }
  }
}
llvm::Value *Frame::fieldAddress(Value Obj, unsigned I) {
  auto &R = U.Records.at(Obj.Type);
  if (!IR) {
    auto *Address = symbolicAddress(Obj, {});
    if (I < R.VirtualCount) {
      llvm::Constant *Indices[] = {B.getInt32(0), B.getInt32(R.offsetSlot(I))};
      auto *OffsetCell = llvm::ConstantExpr::getGetElementPtr(
          U.M.getDataLayout(), R.Layer, Address, Indices);
      auto *Offset = llvm::dyn_cast_or_null<llvm::ConstantInt>(
          load({"i64", nullptr, OffsetCell}).IR);
      if (!Offset)
        fail({}, "constant virtual base requires a layout offset");
      return llvm::ConstantExpr::getGetElementPtr(
          U.M.getDataLayout(), B.getInt8Ty(), Address, {Offset});
    }
    llvm::Constant *Indices[] = {B.getInt32(0), B.getInt32(I)};
    return llvm::ConstantExpr::getGetElementPtr(U.M.getDataLayout(), R.IR,
                                                Address, Indices);
  }
  if (I >= R.VirtualCount)
    return B.CreateStructGEP(R.IR, Obj.Address, I);
  auto *Offset = B.CreateLoad(
      B.getInt64Ty(), B.CreateStructGEP(R.IR, Obj.Address, R.offsetSlot(I)));
  return B.CreateGEP(B.getInt8Ty(), Obj.Address, Offset);
}

ConstantPlace Frame::constantBasePlace(ConstantPlace Place,
                                       const BasePath &Path) const {
  for (unsigned Index : Path) {
    const auto &R = U.Records.at(Place.Type);
    const auto &Type = R.Bases[Index];
    if (Index < R.VirtualCount) {
      Place = completePlace(std::move(Place));
      const auto &Complete = U.Records.at(Place.Type);
      auto Virtual =
          llvm::ArrayRef(Complete.Bases).take_front(Complete.VirtualCount);
      Index = Complete.tailSlot(llvm::find(Virtual, Type) - Virtual.begin());
    }
    Place.Steps.push_back({Index, nullptr, Place.Type});
    Place.Type = Type;
  }
  return Place;
}

ConstantPlace Frame::constantFieldPlace(Value &Object, unsigned I) const {
  auto Place = placeFor(Object);
  const auto &R = U.Records.at(Object.Type);
  if (I < R.Bases.size())
    return constantBasePlace(std::move(Place), {I});
  Place.Steps.push_back({I});
  Place.Type = R.Fields[I].Type;
  return Place;
}

Value Frame::constantField(Value &Object, unsigned I, const Token &At) {
  const auto &R = U.Records.at(Object.Type);
  if (Object.Address) {
    auto V = Value{R.Fields[I].Type, nullptr, fieldAddress(Object, I),
                   Object.Readonly || R.Fields[I].Decl.Const};
    V.BaseView = I < R.Bases.size();
    return load(V);
  }
  auto Place = constantFieldPlace(Object, I);
  Place.Readonly |= Object.Readonly || R.Fields[I].Decl.Const;
  auto V = Place.read(*this, At);
  V.Location = std::make_shared<ConstantPlace>(std::move(Place));
  return V;
}

Value Frame::baseView(Value Obj, const BasePath &Path) {
  if (IR && Transaction && !Path.empty() && Obj.Address == Self.Address &&
      Obj.Type == Self.Type)
    Obj.ConstructionBase = {Obj.Address, Path.front()};
  if (!IR && !Path.empty() && !Obj.Address) {
    auto Place = constantBasePlace(placeFor(Obj), Path);
    auto Result = Place.read(*this, {});
    Result.ConstantTemporary = Obj.ConstantTemporary;
    if (Obj.Location)
      Result.Location = std::make_shared<ConstantPlace>(std::move(Place));
    return Result;
  }
  for (auto I : Path) {
    Obj.Address = fieldAddress(Obj, I);
    Obj.IR = nullptr;
    Obj.Type = U.Records.at(Obj.Type).Bases[I];
    Obj.BaseView = true;
    if (!IR)
      Obj.Location.reset();
  }
  return Obj;
}
// All eligible layers reach the same obligation through a relative offset.
// The binding is part of the complete object's lifetime, including its
// construction before an automatic or replaced storage slot is published.
llvm::StructType *Context::ownerRecordType() {
  auto *I = llvm::Type::getInt32Ty(C);
  auto *Flag = llvm::Type::getInt1Ty(C);
  return llvm::StructType::get(C, {I, I, Flag, Flag});
}
llvm::Value *Frame::ownerRecord(Value Layer, unsigned I) {
  auto &R = U.Records.at(Layer.Type);
  auto *Offset =
      B.CreateLoad(B.getInt64Ty(), B.CreateStructGEP(R.IR, Layer.Address,
                                                     R.ownerOffsetSlot(I)));
  return B.CreateGEP(B.getInt8Ty(), Layer.Address, Offset);
}
void Frame::enterOwnerLayer(Value Layer) {
  auto &R = U.Records.at(Layer.Type);
  if (!R.VirtualCount)
    return;
  B.CreateStore(B.getTrue(),
                B.CreateStructGEP(R.IR, Layer.Address, R.layerEnteredSlot()));
  auto *ID =
      B.CreateLoad(B.getInt32Ty(),
                   B.CreateStructGEP(R.IR, Layer.Address, R.layerIndexSlot()));
  auto *State = U.ownerRecordType();
  for (unsigned I = 0; I < R.VirtualCount; ++I) {
    auto *Row = ownerRecord(Layer, I);
    auto *Binding = B.CreateStructGEP(State, Row, 0);
    auto *Nominee = B.CreateStructGEP(State, Row, 1);
    auto *Pending = B.CreateLoad(B.getInt32Ty(), Nominee);
    auto *Ready = B.CreateLoad(B.getInt1Ty(), B.CreateStructGEP(State, Row, 2));
    auto *Establish = B.CreateAnd(Ready, B.CreateICmpEQ(ID, Pending));
    B.CreateStore(
        B.CreateSelect(Establish, ID, B.CreateLoad(B.getInt32Ty(), Binding)),
        Binding);
    B.CreateStore(B.CreateSelect(Establish, B.getInt32(-1), Pending), Nominee);
  }
}
void Frame::finishVirtualBase(Value Layer, unsigned I) {
  if (I < U.Records.at(Layer.Type).VirtualCount)
    B.CreateStore(B.getTrue(), B.CreateStructGEP(U.ownerRecordType(),
                                                 ownerRecord(Layer, I), 2));
}
void Frame::bindVirtualLayout(Value Obj) {
  auto &Root = U.Records.at(Obj.Type);
  if (!Root.VirtualCount)
    return;
  auto &DL = U.M.getDataLayout();
  auto *RootLayout = DL.getStructLayout(Root.IR);
  auto *State = U.ownerRecordType();
  auto *Rows = B.CreateStructGEP(Root.IR, Obj.Address, Root.obligationsSlot());
  std::map<BasePath, unsigned> Indices;
  for (const auto &[Path, Type] : Root.Views)
    Indices.emplace(Path, Indices.size());
  for (unsigned I = 0; I < Root.VirtualCount; ++I) {
    auto Found = Root.Owners.find(Root.Bases[I]);
    auto Pending =
        Found == Root.Owners.end() ? -1 : int(Indices.at(Found->second));
    B.CreateStore(llvm::ConstantStruct::get(
                      State, {B.getInt32(Indices.at({})), B.getInt32(Pending),
                              B.getFalse(), B.getFalse()}),
                  B.CreateGEP(State, Rows, B.getInt32(I)));
  }
  for (auto &[Path, T] : Root.Views) {
    auto *Ptr = Obj.Address;
    uint64_t Offset = 0;
    auto *R = &Root;
    // A canonical path begins at physical root storage, even for virtuals.
    for (auto I : Path) {
      unsigned Physical =
          (R == &Root && I < Root.VirtualCount) ? Root.tailSlot(I) : I;
      Offset += DL.getStructLayout(R->IR)->getElementOffset(Physical);
      Ptr = B.CreateStructGEP(R->IR, Ptr, Physical);
      R = &U.Records.at(R->Bases[I]);
    }
    if (R->VirtualCount) {
      B.CreateStore(B.getInt32(Indices.at(Path)),
                    B.CreateStructGEP(R->IR, Ptr, R->layerIndexSlot()));
      B.CreateStore(B.getFalse(),
                    B.CreateStructGEP(R->IR, Ptr, R->layerEnteredSlot()));
    }
    for (unsigned I = 0; I < R->VirtualCount; ++I) {
      auto J = llvm::find(Root.Bases, R->Bases[I]) - Root.Bases.begin();
      auto Delta = RootLayout->getElementOffset(Root.tailSlot(J)) - Offset;
      B.CreateStore(B.getInt64(Delta),
                    B.CreateStructGEP(R->IR, Ptr, R->offsetSlot(I)));
      auto StateOffset =
          RootLayout->getElementOffset(Root.obligationsSlot()) +
          uint64_t(J) * DL.getTypeAllocSize(State).getFixedValue() - Offset;
      B.CreateStore(B.getInt64(StateOffset),
                    B.CreateStructGEP(R->IR, Ptr, R->ownerOffsetSlot(I)));
    }
  }
}
// An incoming reference may designate only the nonvirtual layer of a larger
// object. Assemble its by-value representation without reading past that layer.
llvm::Value *Frame::snapshot(Value Obj) {
  auto &R = U.Records.at(Obj.Type);
  Value Copy{Obj.Type, nullptr, allocate(Obj.Type, {})};
  B.CreateStore(B.CreateLoad(R.Layer, Obj.Address), Copy.Address);
  for (unsigned I = 0; I < R.VirtualCount; ++I) {
    auto *V = U.Records.at(R.Bases[I]).Layer;
    auto *Dest = B.CreateStructGEP(R.IR, Copy.Address, R.tailSlot(I));
    B.CreateStore(B.CreateLoad(V, fieldAddress(Obj, I)), Dest);
  }
  bindVirtualLayout(Copy);
  installTables(Copy);
  return B.CreateLoad(R.IR, Copy.Address);
}
void Frame::installTables(Value Obj) {
  for (auto &Table : U.Records.at(Obj.Type).Tables) {
    auto View = baseView(Obj, Table.View);
    auto &R = U.Records.at(View.Type);
    B.CreateStore(Table.Entries,
                  B.CreateStructGEP(R.IR, View.Address, R.Fields.size()));
    auto *Deltas = B.CreateStructGEP(R.IR, View.Address, R.Fields.size() + 1);
    for (size_t I = 0; I < Table.Receivers.size(); ++I) {
      auto Receiver = baseView(Obj, Table.Receivers[I]);
      auto *Offset =
          B.CreateSub(B.CreatePtrToInt(Receiver.Address, B.getInt64Ty()),
                      B.CreatePtrToInt(View.Address, B.getInt64Ty()));
      B.CreateStore(Offset, B.CreateGEP(B.getInt64Ty(), Deltas, B.getInt64(I)));
    }
  }
}

void Frame::installConstantTables(Value &Obj, const Token &At) {
  const auto &Root = U.Records.at(Obj.Type);
  if (Root.Tables.empty())
    return;
  auto Layer = placeFor(Obj);
  for (const auto &Table : Root.Tables) {
    U.chargeConstant(At, 1 + Table.Targets.size());
    const auto &R = U.Records.at(Root.Views.at(Table.View));
    unsigned Vptr = R.Fields.size();
    auto *DeltaType =
        llvm::cast<llvm::ArrayType>(R.IR->getElementType(Vptr + 1));
    std::vector<llvm::Constant *> Deltas(DeltaType->getNumElements(),
                                         B.getInt64(0));
    auto View = constantBasePlace(Layer, Table.View);
    uint64_t Start = layerOffset(U, View);
    for (size_t I = 0; I < Table.Receivers.size(); ++I)
      Deltas[I] = B.getInt64(
          layerOffset(U, constantBasePlace(Layer, Table.Receivers[I])) - Start);
    writeLayoutSlot(*this, View, Vptr, Table.Entries, At);
    writeLayoutSlot(*this, View, Vptr + 1,
                    llvm::ConstantArray::get(DeltaType, Deltas), At);
  }
  Obj.IR = Layer.read(*this, At).IR;
}

void Frame::bindConstantVirtualLayout(Value &Obj, const Token &At) {
  const auto &Root = U.Records.at(Obj.Type);
  if (!Root.VirtualCount || Obj.BaseView)
    return;
  auto Complete = placeFor(Obj);
  auto *RootLayout = U.M.getDataLayout().getStructLayout(Root.IR);
  auto *State = U.ownerRecordType();
  std::map<BasePath, unsigned> Indices;
  for (const auto &[Path, Type] : Root.Views)
    Indices.emplace(Path, Indices.size());
  std::vector<llvm::Constant *> Rows;
  for (unsigned I = 0; I < Root.VirtualCount; ++I) {
    auto Owner = Root.Owners.find(Root.Bases[I]);
    unsigned Binding =
        Owner == Root.Owners.end() ? Indices.at({}) : Indices.at(Owner->second);
    Rows.push_back(
        llvm::ConstantStruct::get(State, {B.getInt32(Binding), B.getInt32(-1),
                                          B.getTrue(), B.getFalse()}));
  }
  auto *RowType = llvm::cast<llvm::ArrayType>(
      Root.IR->getElementType(Root.obligationsSlot()));
  writeLayoutSlot(*this, Complete, Root.obligationsSlot(),
                  llvm::ConstantArray::get(RowType, Rows), At);
  auto *RowsLayout = U.M.getDataLayout().getStructLayout(State);
  for (const auto &[Path, Type] : Root.Views) {
    const auto &Layer = U.Records.at(Type);
    if (!Layer.VirtualCount)
      continue;
    U.chargeConstant(At, 1 + Layer.VirtualCount);
    auto View = constantBasePlace(Complete, Path);
    uint64_t Offset = layerOffset(U, View);
    writeLayoutSlot(*this, View, Layer.layerIndexSlot(),
                    B.getInt32(Indices.at(Path)), At);
    writeLayoutSlot(*this, View, Layer.layerEnteredSlot(), B.getTrue(), At);
    for (unsigned I = 0; I < Layer.VirtualCount; ++I) {
      unsigned J = llvm::find(Root.Bases, Layer.Bases[I]) - Root.Bases.begin();
      uint64_t Target = RootLayout->getElementOffset(Root.tailSlot(J));
      writeLayoutSlot(*this, View, Layer.offsetSlot(I),
                      B.getInt64(Target - Offset), At);
      uint64_t Owner = RootLayout->getElementOffset(Root.obligationsSlot()) +
                       J * RowsLayout->getSizeInBytes().getFixedValue();
      writeLayoutSlot(*this, View, Layer.ownerOffsetSlot(I),
                      B.getInt64(Owner - Offset), At);
    }
  }
}

Function &Frame::constantVirtualTarget(Function &D, Value &Receiver,
                                       const Token &At) {
  Receiver = load(Receiver);
  if (D.Slot < 0)
    return D;
  const auto &Static = U.Records.at(Receiver.Type);
  auto *Image = llvm::dyn_cast_or_null<llvm::Constant>(Receiver.IR);
  auto *Entries = Image ? llvm::dyn_cast_or_null<llvm::GlobalVariable>(
                              Image->getAggregateElement(Static.Fields.size()))
                        : nullptr;
  auto It = U.DispatchTables.find(Entries);
  if (It == U.DispatchTables.end())
    fail(At, "constant virtual call requires an active object layer");
  const auto &[Type, Index] = It->second;
  const auto &Table = U.Records.at(Type).Tables[Index];
  auto Slot = unsigned(D.Slot);
  if (Slot >= Table.Targets.size())
    fail(At, "constant virtual slot is unavailable");
  const auto &Path = Table.Receivers[Slot];
  auto &Target = *Table.Targets[Slot];
  if (Path == Table.View)
    return Target;
  auto *Deltas = Image->getAggregateElement(Static.Fields.size() + 1);
  auto *Offset =
      llvm::cast<llvm::ConstantInt>(Deltas->getAggregateElement(Slot));
  if (auto *Address =
          llvm::dyn_cast_or_null<llvm::Constant>(Receiver.Address)) {
    auto *Adjusted = llvm::ConstantExpr::getGetElementPtr(
        U.M.getDataLayout(), B.getInt8Ty(), Address, {Offset});
    Receiver = load({Target.Owner, nullptr, Adjusted, Receiver.Readonly});
  } else if (Receiver.Location) {
    auto Complete = completePlace(*Receiver.Location);
    const auto &Root = U.Records.at(Complete.Type);
    uint64_t Expected =
        layerOffset(U, *Receiver.Location) + Offset->getZExtValue();
    for (const auto &[Candidate, Type] : Root.Views) {
      if (Type != Target.Owner)
        continue;
      auto Place = constantBasePlace(Complete, Candidate);
      if (layerOffset(U, Place) != Expected)
        continue;
      Place.Readonly |= Receiver.Readonly;
      Receiver = Place.read(*this, At);
      Receiver.Location = std::make_shared<ConstantPlace>(std::move(Place));
      return Target;
    }
    fail(At, "constant virtual receiver has no complete-object designation");
  } else
    fail(At, "constant virtual receiver has no complete-object designation");
  return Target;
}
Value Frame::indirect(Value Ptr, const std::vector<Node> &Args,
                      const Token &At) {
  auto T = element(Ptr.Type);
  if (!U.Signatures.count(T))
    fail(At, "function-pointer contract required");
  auto Effects = callableEffects(T);
  auto Predicate = callablePredicateEffects(T);
  if (InPredicate) {
    auto All = Effects;
    if (All)
      All->insert(Predicate.begin(), Predicate.end());
    requireObserver(All, At);
  }
  if (F && callableFlag(T, " whole"))
    F->MayWhole = true;
  if (RequireNoexcept && !callableFlag(T, " noexcept"))
    fail(At, "expression requires a nonthrowing call");
  auto &Sig = U.Signatures.at(T);
  if (Sig.size() != Args.size() + 1)
    fail(At, "wrong argument count");
  if (!IR) {
    auto *Target = llvm::dyn_cast_or_null<llvm::Function>(Ptr.IR);
    if (!Target)
      fail(At, "constant call requires a designated function");
    auto Decl = llvm::find_if(
        U.Functions, [&](const Function &D) { return D.IR == Target; });
    if (Decl != U.Functions.end())
      return constantCall(*Decl, Args, At);
    for (const auto &[Type, R] : U.Records)
      if (R.ClosureEntry == Target) {
        auto *Call = U.Overloads.at(Type + "::$call").front();
        return constantCall(*Call, Args, At,
                            {Type, llvm::Constant::getNullValue(R.IR)});
      }
    fail(At, "constant call requires a CPN function definition");
  }
  std::vector<llvm::Type *> Types;
  std::vector<llvm::Value *> Vals;
  auto *Storage = resultAddress(Sig.front(), At);
  auto Flags = callableFlags(T);
  std::set<unsigned> NoEscape, Borrowed;
  bool MayWriteCallStorage = Storage || callableFlag(T, " whole");
  std::set<unsigned> Origins;
  std::string StorageOrigin;
  std::vector<Value> Actual;
  unsigned Sources = 0;
  if (Storage) {
    Types.push_back(B.getPtrTy());
    Vals.push_back(Storage);
  }
  for (size_t I = 0; I < Args.size(); ++I) {
    auto Position = std::to_string(I);
    Types.push_back(U.aggregate(Sig[I + 1]) ? B.getPtrTy() : U.ir(Sig[I + 1]));
    auto &Param = Sig[I + 1];
    auto V = eval(Args[I], Param);
    if (Flags.count("noescape#" + Position))
      NoEscape.insert(I);
    MayWriteCallStorage |= Flags.count("consumes#" + Position) != 0;
    if (Flags.count("borrow#" + Position)) {
      Borrowed.insert(I);
      Origins.insert(V.Origins.begin(), V.Origins.end());
      StorageOrigin = V.Storage;
      ++Sources;
    }
    if (llvm::StringRef(Param).ends_with("&")) {
      V = bindReference(V, Param, At);
      Vals.push_back(V.Address);
    } else {
      V = materialize(convert(V, Param, At), At);
      Vals.push_back(U.aggregate(Param) ? V.Address : V.IR);
    }
    Actual.push_back(V);
  }
  auto *FT = llvm::FunctionType::get(
      Storage ? B.getVoidTy() : U.ir(Sig.front()), Types, false);
  auto *Before = wholeEpoch();
  auto Metadata = openPointerCall(Ptr.IR, Sig.front(),
                                  llvm::ArrayRef(Sig).drop_front(), Actual);
  auto *Call = B.CreateCall(FT, Ptr.IR, Vals);
  Call->setAttributes(U.scalarCallABI(
      Sig.front(), llvm::ArrayRef(Sig).drop_front(), !!Storage));
  llvm::SmallVector<unsigned> ValueAggregates;
  for (unsigned I = 0; I < Args.size(); ++I)
    if (U.aggregate(Sig[I + 1]))
      ValueAggregates.push_back(I);
  describeBorrowCall(*Call, At, Opt, llvm::ArrayRef(Sig).drop_front(),
                     Storage ? 1 : 0, NoEscape, Borrowed, Effects,
                     MayWriteCallStorage || !ValueAggregates.empty());
  describeEffectCall(*Call, Effects, Storage ? 1 : 0, false, nullptr,
                     ValueAggregates, Predicate);
  if (Sig[0] == "never") {
    Call->setDoesNotReturn();
    return endDivergentCall();
  }
  closePointerCall(Metadata);
  propagateWhole(Before);
  for (size_t I = 0; I < Actual.size(); ++I)
    if (carriesBorrow(Sig[I + 1]) && Active.count(Actual[I].Storage))
      Active[Actual[I].Storage] = -1;
  auto Result = callResult(Sig[0], Call, At, Storage);
  Result.Origins = std::move(Origins);
  if (Sources == 1)
    Result.Storage = std::move(StorageOrigin);
  return pointerCallResult(Result, Metadata, Sig.front());
}

Value Frame::endDivergentCall() {
  B.CreateUnreachable();
  // Keep binding later source in a disconnected block.
  B.SetInsertPoint(block("after.never"));
  Live = false;
  return {"never"};
}
