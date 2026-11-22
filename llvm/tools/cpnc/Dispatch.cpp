#include "Sema.h"
using namespace cpn;
namespace {
bool same(Function *A, Function *B) {
  return A->Decl.Text == B->Decl.Text && A->Params == B->Params &&
         A->Decl.Const == B->Decl.Const &&
         A->Decl.Settings["category"] == B->Decl.Settings["category"];
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
      if (!Override || (*It)->Decl.Settings.count("final") ||
          // These indices designate fields declared by the owning layer.
          // Equal offsets in two different layers denote different slots.
          (D->Owner != (*It)->Owner &&
           (!D->Initializes.empty() || !D->RequiresAlive.empty())) ||
          D->Initializes != (*It)->Initializes ||
          D->RequiresAlive != (*It)->RequiresAlive ||
          ((*It)->Decl.Noexcept && !D->Decl.Noexcept) ||
          !compatibleCallable(callableType(*D), callableType(**It)))
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
    R.Tables.push_back(std::move(Table));
  }
}
llvm::Value *Frame::fieldAddress(Value Obj, unsigned I) {
  auto &R = U.Records.at(Obj.Type);
  if (!IR) {
    auto *Address = symbolicAddress(Obj, {});
    if (I < R.VirtualCount)
      fail({}, "virtual base offset requires runtime storage");
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
Value Frame::baseView(Value Obj, const BasePath &Path) {
  for (auto I : Path) {
    if (!IR && !Obj.Address && llvm::isa_and_nonnull<llvm::Constant>(Obj.IR)) {
      Obj.IR = llvm::cast<llvm::Constant>(Obj.IR)->getAggregateElement(I);
    } else {
      Obj.Address = fieldAddress(Obj, I);
      Obj.IR = nullptr;
    }
    Obj.Type = U.Records.at(Obj.Type).Bases[I];
    Obj.BaseView = true;
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
Value Frame::indirect(Value Ptr, const std::vector<Node> &Args,
                      const Token &At) {
  auto T = element(Ptr.Type);
  if (!U.Signatures.count(T))
    fail(At, "function-pointer contract required");
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
    if (Decl == U.Functions.end())
      fail(At, "constant call requires a CPN function definition");
    return constantCall(*Decl, Args, At);
  }
  std::vector<llvm::Type *> Types;
  std::vector<llvm::Value *> Vals;
  auto *Storage = resultAddress(Sig.front(), At);
  auto Flags = callableFlags(T);
  std::set<unsigned> Origins;
  std::string StorageOrigin;
  std::vector<Value> Actual;
  unsigned Sources = 0;
  if (Storage) {
    Types.push_back(B.getPtrTy());
    Vals.push_back(Storage);
  }
  for (size_t I = 0; I < Args.size(); ++I) {
    Types.push_back(U.aggregate(Sig[I + 1]) ? B.getPtrTy() : U.ir(Sig[I + 1]));
    auto &Param = Sig[I + 1];
    auto V = eval(Args[I], Param);
    if (Flags.count("borrow#" + std::to_string(I))) {
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
