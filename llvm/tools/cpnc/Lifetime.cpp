#include "Sema.h"
#include "llvm/ADT/ScopeExit.h"
#include <iterator>
using namespace cpn;
std::string Frame::directField(const Node &N) const {
  if (N.K == Node::Name) {
    for (auto &Scope : Scopes)
      if (Scope.Names.count(N.Text))
        return "";
    return FieldFlags.count(N.Text) || ConstantMembersAlive.count(N.Text)
               ? N.Text
               : "";
  }
  if (N.K == Node::Member && N.Definition && N.Children[0].K == Node::Name &&
      N.Children[0].Text == "this" &&
      (FieldFlags.count(N.Text) || ConstantMembersAlive.count(N.Text)))
    return N.Text;
  return "";
}
void Frame::endField(const std::string &Slot, const Token &At,
                     bool RunDestructor, bool Explicit) {
  auto It = FieldFlags.find(Slot);
  if (It == FieldFlags.end())
    fail(At, "request must select a direct subobject");
  const auto &R = U.Records.at(Self.Type);
  auto FieldIndex = unsigned(
      llvm::find_if(R.Fields,
                    [&](const Field &F) { return F.Decl.Text == Slot; }) -
      R.Fields.begin());
  assert(FieldIndex < R.Fields.size());
  if (Explicit && InDestructorCleanup) {
    if (!RunDestructor)
      fail(At, "LIFE005: member Abandon is forbidden in Cleanup");
    checkCleanupFrontier(Slot, At);
  }
  auto *Alive = destructionSlotAlive(FieldIndex);
  if (Explicit)
    guard(B.CreateNot(Alive), "lifecycle");
  auto *Do = block("retire.slot"), *Done = block("retire.next");
  B.CreateCondBr(Alive, Do, Done);
  B.SetInsertPoint(Do);
  Token Name = At;
  Name.Text = Slot;
  auto Field = member(Self, Name, /*NeedLive=*/false);
  if (Explicit) {
    if (!RunDestructor)
      checkAbandon(Field.Type, At);
    ensureLive(Field, At);
    markStorageWrite(Field.Address);
  }
  B.CreateStore(B.getFalse(), It->second);
  if (RunDestructor)
    dropChild(Self, Field, FieldIndex < R.Bases.size());
  else if (Field.Slot)
    retireStorage(Field, false);
  branch(Done);
  B.SetInsertPoint(Done);
}
llvm::Value *Frame::destructionMemberRegistration(unsigned Index) {
  const auto &Field = U.Records.at(Self.Type).Fields[Index];
  return B.CreateCall(U.M.getFunction("cpn.slot.find"),
                      {fieldAddress(Self, Index), U.typeID(Field.Type),
                       slotFor(Self), B.getTrue()});
}

llvm::Value *Frame::destructionSlotAlive(unsigned Index) {
  const auto &R = U.Records.at(Self.Type);
  const auto &Field = R.Fields[Index];
  auto *Flag = B.CreateLoad(B.getInt1Ty(), FieldFlags.at(Field.Decl.Text));
  if (Index < R.Bases.size()) {
    if (!U.Whole)
      return Flag;
    auto *Available = B.CreateCall(
        U.M.getFunction("cpn.view.available"),
        {fieldAddress(Self, Index), U.typeID(Field.Type), B.getFalse()});
    return B.CreateAnd(Flag, Available);
  }
  if (!TracksStorage)
    return Flag;
  // Retirement through a borrowed view or an active replacement changes
  // the registration without modifying this activation's flags.
  auto *Registered = destructionMemberRegistration(Index);
  auto *Stamp = B.CreateCall(U.M.getFunction("cpn.generation"),
                             {Registered, B.getFalse()});
  return B.CreateSelect(B.CreateIsNull(Registered), Flag,
                        B.CreateTrunc(Stamp, B.getInt1Ty()));
}

void Frame::checkCleanupFrontier(const std::string &Slot, const Token &At) {
  const auto &R = U.Records.at(IR ? Self.Type : ConstantReceiver->Type);
  auto Selected = llvm::find_if(
      R.Fields, [&](const Field &F) { return F.Decl.Text == Slot; });
  assert(Selected != R.Fields.end());
  if (!IR) {
    for (auto I = Selected + 1; I != R.Fields.end(); ++I)
      if (ConstantMembersAlive.at(I->Decl.Text) &&
          constantFieldPlace(*ConstantReceiver, I - R.Fields.begin())
              .hasLiveExtent())
        fail(At, "LIFE005: Cleanup must destroy the reverse-frontier slot");
    return;
  }
  llvm::Value *HasLater = B.getFalse();
  for (auto I = Selected + 1; I != R.Fields.end(); ++I)
    HasLater = B.CreateOr(HasLater, destructionSlotAlive(I - R.Fields.begin()));
  guard(HasLater, "lifecycle");
}

void Frame::checkCleanupStorageRequest(Value Object, bool Destroy) {
  const auto &R = U.Records.at(Self.Type);
  llvm::Value *HasLater = B.getFalse(), *Invalid = B.getFalse();
  // A replacement can be reached through a typed borrow of its new type.
  // Its registration still identifies the original member's cleanup rank.
  for (size_t I = R.Fields.size(); I > R.Bases.size(); --I) {
    auto *Matches =
        B.CreateICmpEQ(Object.Slot, destructionMemberRegistration(I - 1));
    auto *Bad = Destroy ? B.CreateAnd(Matches, HasLater) : Matches;
    Invalid = B.CreateOr(Invalid, Bad);
    HasLater = B.CreateOr(HasLater, destructionSlotAlive(I - 1));
  }
  guard(Invalid, "lifecycle");
}
void Frame::checkAbandon(const std::string &Type, const Token &At) {
  auto Nontrivial = [&](auto &&Visit, const std::string &T) -> bool {
    if (llvm::StringRef(T).ends_with("]"))
      return !llvm::StringRef(T).ends_with("[0]") && Visit(Visit, element(T));
    if (!U.Records.count(T))
      return false;
    if (U.Overloads.count(T + "::$drop"))
      return true;
    if (auto It = U.Variants.find(T); It != U.Variants.end())
      for (const auto &Case : It->second)
        for (const auto &Field : U.Cases.at(Case).Types)
          if (Visit(Visit, Field))
            return true;
    return llvm::any_of(U.Records.at(T).Fields,
                        [&](const Field &F) { return Visit(Visit, F.Type); });
  };
  if (!Nontrivial(Nontrivial, Type))
    return;
  Opt.diagnose(At, Severity::Anomaly, "LIFE004",
               "abandon bypasses nontrivial cleanup of " + Type);
}
void Frame::endConstantScope() {
  auto Names = std::move(Scopes.back().ConstantDrops);
  Scopes.back().ConstantDrops.clear();
  for (const auto &Name : llvm::reverse(Names))
    retireConstantCell(Scopes.back().Names.at(Name), F ? F->Decl.At : Token{});
}

void Frame::retireConstantCell(Value &Cell, const Token &At, bool Explicit,
                               bool Destroy) {
  if (!Cell.ConstantIdentity.Storage && !Explicit) {
    if (Destroy)
      constantDrop(Cell, At);
    else
      checkAbandon(Cell.Type, At);
    return;
  }
  retireConstantExtent({&Cell, {}, Cell.Type, Cell.Readonly}, At, Explicit,
                       Destroy);
}

void Frame::retireConstantExtent(ConstantPlace Place, const Token &At,
                                 bool Explicit, bool Destroy, bool AsBase) {
  Place.trackLifetime();
  Place.checkLifetime(At, /*ExtentOnly=*/true);
  auto &Slot = Place.registerExtent();
  if (Slot.Retiring || Slot.Constructing)
    fail(At, "object lifetime transition is already in progress");
  if (Slot.Ended) {
    if (Explicit)
      fail(At, "ended object generation");
    if (Slot.Replacement)
      retireConstantCell(*Slot.Replacement, At, false, Destroy);
    return;
  }
  auto Object = Place.read(*this, At);
  llvm::SaveAndRestore Retiring(Slot.Retiring, true);
  auto End = llvm::scope_exit([&] { Slot.Ended = true; });
  const auto &Storage = *Place.Root->ConstantIdentity.Storage;
  if (llvm::StringRef(Place.Type).ends_with("]")) {
    const auto Element = unconst(element(Place.Type));
    bool AggregateElements = U.aggregate(Element);
    if (!AggregateElements && Storage.Subobjects.empty())
      return;
    auto *Array = llvm::cast<llvm::ArrayType>(U.ir(Place.Type, At));
    auto Count = llvm::StringRef(Place.Type).ends_with("[0]")
                     ? 0
                     : Array->getNumElements();
    auto Retire = [&](uint64_t Index) {
      U.chargeConstant(At);
      auto Child = Place;
      Child.Type = Element;
      Child.Steps.push_back({Index});
      retireConstantExtent(std::move(Child), At, false, Destroy);
    };
    if (AggregateElements) {
      for (uint64_t I = Count; I; --I)
        Retire(I - 1);
      return;
    }
    // Scalar elements have no ordinary cleanup. Visit only registered slots,
    // including replacements, in descending order of their original indices.
    const auto Prefix = Place.indices();
    auto Before = Prefix;
    Before.push_back(Count);
    while (Before.back()) {
      auto Next = Storage.Subobjects.lower_bound(Before);
      if (Next == Storage.Subobjects.begin())
        break;
      const auto &Path = std::prev(Next)->first;
      if (Path.size() <= Prefix.size() ||
          llvm::ArrayRef(Path).take_front(Prefix.size()) !=
              llvm::ArrayRef(Prefix))
        break;
      Before.back() = Path[Prefix.size()];
      Retire(Before.back());
    }
    return;
  }
  if (Destroy) {
    Object.Location = std::make_shared<ConstantPlace>(std::move(Place));
    constantDrop(Object, At, AsBase);
    return;
  }

  checkAbandon(Object.Type, At);
  // Each replacement has its own typed generation, even though its storage
  // still belongs to the containing extent. Abandon also ends these
  // generations.
  const auto Position = Place.indices();
  for (const auto &[Path, Child] : Storage.Subobjects)
    if (Child.Replacement && Path.size() > Position.size() &&
        llvm::ArrayRef(Path).take_front(Position.size()) ==
            llvm::ArrayRef(Position)) {
      U.chargeConstant(At);
      retireConstantCell(*Child.Replacement, At, false, false);
    }
}

void Frame::endConstantField(const std::string &Slot, bool Run, const Token &At,
                             bool Explicit) {
  if (!ConstantMembersAlive.at(Slot))
    fail(At, "subobject destruction obligation already consumed");
  const auto &R = U.Records.at(ConstantReceiver->Type);
  unsigned Index =
      llvm::find_if(R.Fields,
                    [&](const cpn::Field &F) { return F.Decl.Text == Slot; }) -
      R.Fields.begin();
  if (Explicit && InDestructorCleanup) {
    if (!Run)
      fail(At, "LIFE005: abandon is unavailable in Cleanup");
    checkCleanupFrontier(Slot, At);
  }
  auto Place = constantFieldPlace(*ConstantReceiver, Index);
  retireConstantExtent(std::move(Place), At, Explicit, Run,
                       Index < R.Bases.size());
}

void Frame::constantDrop(Value Object, const Token &At, bool AsBase,
                         bool RunOwnDestructor) {
  requirePredicateCleanup(Object.Type, At);
  auto Type = unconst(Object.Type);
  if (!U.aggregate(Type))
    return;
  ConstantActivation Activation(U, At);
  Object = load(Object);
  Object.Type = Type;
  const auto *Extent =
      Object.Location ? Object.Location->registeredExtent() : nullptr;
  if (!AsBase && (!Extent || !Extent->Retiring))
    Object.Location.reset();
  else if (Object.Location) {
    auto Place = *Object.Location;
    Place.Readonly = false;
    Object.Location = std::make_shared<ConstantPlace>(std::move(Place));
  }
  Object.ConstantTemporary.reset();
  Object.Address = nullptr;
  auto *C = llvm::dyn_cast_or_null<llvm::Constant>(Object.IR);
  if (!C)
    fail(At, "constant object required for destruction");
  if (auto *Array = llvm::dyn_cast<llvm::ArrayType>(C->getType())) {
    auto E = element(Type);
    if (U.aggregate(unconst(E)) && !llvm::StringRef(Type).ends_with("[0]"))
      for (uint64_t I = Array->getNumElements(); I; --I)
        constantDrop({E, constantElement(C, I - 1)}, At);
    return;
  }
  auto &R = U.Records.at(Type);
  installConstantTables(Object, At);
  auto D = U.Overloads.find(Type + "::$drop");
  Function *Destructor =
      RunOwnDestructor && D != U.Overloads.end() ? D->second.front() : nullptr;
  Frame Body(U, Destructor, nullptr, Type + "::");
  Object.Readonly = false;
  Body.ConstantReceiver = &Object;
  U.ConstantInvariantLifetimes.push_back(&Object);
  auto End = llvm::scope_exit([&] { U.ConstantInvariantLifetimes.pop_back(); });
  std::set<std::string> Manual;
  for (size_t I = 0; I < R.Fields.size(); ++I) {
    auto &Name = R.Fields[I].Decl.Text;
    Body.ConstantMembersAlive[Name] = !AsBase || I >= R.VirtualCount;
    if (R.Decl.Settings.count("manual") && I >= R.Bases.size())
      Manual.insert(Name);
  }
  for (const auto &Decl : R.Decl.Children)
    if (Decl.K == Node::Init && Decl.Type == "Complete") {
      if (Decl.Text == "*")
        for (const auto &Field : R.Fields)
          Manual.insert(Field.Decl.Text);
      else
        Manual.insert(Decl.Text);
    }
  if (Destructor) {
    if (Destructor->Decl.Prototype || Destructor->Decl.Children.empty())
      fail(At, "constant destruction requires a destructor definition");
    Body.checkContracts(true);
    Body.constructorBody(Destructor->Decl.Children.front());
  }
  if (U.Variants.count(Type)) {
    auto *Image = llvm::cast<llvm::Constant>(Object.IR);
    auto Tag = llvm::cast<llvm::ConstantInt>(Image->getAggregateElement(0u))
                   ->getZExtValue();
    auto &Active = U.Cases.at(U.Variants.at(Type).at(Tag));
    auto Subject = Object.Location ? *Object.Location
                                   : ConstantPlace{&Object, {}, Type, false};
    for (unsigned I = Active.Types.size(); I; --I) {
      auto Payload = Subject;
      Payload.Type = Active.Types[I - 1];
      Payload.Steps.push_back({I - 1, &Active});
      Body.retireConstantExtent(std::move(Payload), At, false, true);
    }
  }
  auto HasObligation = [&](const cpn::Field &Field) {
    return Body.ConstantMembersAlive.at(Field.Decl.Text) &&
           Body.constantFieldPlace(Object, &Field - R.Fields.data())
               .hasLiveExtent();
  };
  for (auto &Field : llvm::reverse(R.Fields)) {
    const auto &Name = Field.Decl.Text;
    if (!HasObligation(Field))
      continue;
    if (llvm::StringRef(Name).starts_with("$virtual:"))
      break;
    if (Manual.count(Name) && Destructor)
      break;
    Body.endConstantField(Name, true, At);
  }
  if (Destructor && Destructor->Decl.Children.size() > 1) {
    llvm::SaveAndRestore Cleanup(Body.InDestructorCleanup, true);
    Body.constructorBody(Destructor->Decl.Children[1]);
  }
  for (auto &Field : llvm::reverse(R.Fields))
    if (HasObligation(Field))
      Body.endConstantField(Field.Decl.Text, true, At);
  if (Destructor)
    Body.checkContracts(false);
}
void Frame::retirement() {
  auto &R = U.Records.at(Self.Type);
  auto *Previous =
      pushInvariantLifetime(Self, nullptr, /*IsConstruction=*/false);
  installTables(Self);
  auto &Manual = ManualDropSlots;
  for (unsigned I = 0; I < R.Fields.size(); ++I) {
    auto &Field = R.Fields[I];
    auto *Flag = allocate("bool", Field.Decl.At);
    B.CreateStore(B.getInt1(!BaseLayer || I >= R.VirtualCount), Flag);
    FieldFlags[Field.Decl.Text] = Flag;
    if (R.Decl.Settings.count("manual") && I >= R.Bases.size())
      Manual.insert(Field.Decl.Text);
  }
  for (auto &D : R.Decl.Children)
    if (D.K == Node::Init && D.Type == "Complete") {
      if (D.Text == "*") {
        for (size_t I = R.VirtualCount; I < R.Fields.size(); ++I)
          Manual.insert(R.Fields[I].Decl.Text);
      } else if (FieldFlags.count(D.Text))
        Manual.insert(D.Text);
      else
        fail(D.At, "Complete must select a direct subobject");
    }
  InlineReturn = block("dtor.sweep");
  if (U.Whole) {
    auto *Body = block("dtor.body");
    B.CreateCondBr(B.CreateCall(U.M.getFunction("cpn.view.skip"),
                                {Self.Address, U.typeID(Self.Type)}),
                   InlineReturn, Body);
    B.SetInsertPoint(Body);
  }
  stmt(F->Decl.Children[0]);
  branch(InlineReturn);
  B.SetInsertPoint(InlineReturn);
  Live = true;
  if (R.Decl.K == Node::Union)
    dropPayload(Self);
  auto *Cleanup = block("dtor.cleanup");
  for (auto I = R.Fields.rbegin(); I != R.Fields.rend(); ++I) {
    auto &Slot = I->Decl.Text;
    if (llvm::StringRef(Slot).starts_with("$virtual:"))
      break;
    if (Manual.count(Slot)) {
      auto *Next = block("dtor.pass");
      auto *Barrier = destructionSlotAlive(I.base() - R.Fields.begin() - 1);
      B.CreateCondBr(Barrier, Cleanup, Next);
      B.SetInsertPoint(Next);
    } else
      endField(Slot, I->Decl.At, true, false);
  }
  branch(Cleanup);
  B.SetInsertPoint(Cleanup);
  InlineReturn = block("dtor.remainder");
  if (F->Decl.Children.size() > 1) {
    llvm::SaveAndRestore Phase(InDestructorCleanup, true);
    stmt(F->Decl.Children[1]);
  }
  branch(InlineReturn);
  B.SetInsertPoint(InlineReturn);
  InlineReturn = nullptr;
  Live = true;
  for (auto I = R.Fields.rbegin(); I != R.Fields.rend(); ++I)
    endField(I->Decl.Text, I->Decl.At, true, false);
  popInvariantLifetime(Previous, /*IsConstruction=*/false);
}
