#include "Sema.h"
#include "llvm/Analysis/ConstantFolding.h"
using namespace cpn;

void Context::tagged(const Node &D, const std::string &Name,
                     const std::string &P, const Substitution &Env) {
  auto &R = Records[Name];
  if (R.IR && R.Decl.K != Node::Union)
    fail(D.At, "conflicting nominal declaration");
  if (R.Complete)
    fail(D.At, "duplicate union definition");
  R.Decl = D;
  R.EnclosingScope = llvm::StringRef(P).rtrim(':').str();
  if (!R.IR)
    R.IR = llvm::StructType::create(C, "cpn." + Name);
  if (D.Prototype)
    return;
  R.Env = Env;
  R.Env.Types[D.Text] = Name;
  Frame F(*this, nullptr, nullptr, Name + "::");
  F.Env = R.Env;
  const auto &DL = M.getDataLayout();
  uint64_t Size = 0;
  llvm::Type *AlignType = llvm::Type::getInt8Ty(C);
  auto &Alternatives = Variants[Name];
  for (const auto &Decl : D.Children) {
    if (nestedType(Decl, Name, F))
      continue;
    if (Decl.K != Node::Variant) {
      if (Decl.K == Node::Field && Decl.Settings.count("storage") &&
          Decl.Settings.at("storage") == "static") {
        if (!StaticMembers
                 .emplace(Name + "::" + Decl.Text, std::make_pair(Name, Decl))
                 .second)
          fail(Decl.At, "duplicate static member");
        continue;
      }
      if (Decl.K == Node::Field || Decl.K == Node::Init ||
          Decl.Settings.count("virtual"))
        fail(Decl.At,
             "union members cannot add common fields or virtual bases");
      if (Decl.Text == "operator=" && Decl.Settings.count("control") &&
          Decl.Settings.at("control") == "default")
        fail(Decl.At,
             "union assignment requires an active-case replacement contract");
      continue;
    }
    auto Key = Name + "::" + Decl.Text;
    if (Cases.count(Key))
      fail(Decl.At, "duplicate union case");
    Case V{Name, unsigned(Alternatives.size()), nullptr, Decl, {}};
    std::vector<llvm::Type *> Fields;
    for (auto &A : Decl.Params) {
      auto T = F.resolve(A.Type, A.At);
      auto *Ty = ir(T, A.At);
      if (!Ty->isSized() || llvm::StringRef(T).ends_with("&"))
        fail(A.At, "union payload requires a complete object type");
      V.Decl.Params[V.Types.size()].Const |= unconst(T) != T;
      V.Types.push_back(unconst(T));
      Fields.push_back(Ty);
    }
    V.Payload = llvm::StructType::get(C, Fields);
    Size = std::max(Size, DL.getTypeAllocSize(V.Payload).getFixedValue());
    if (DL.getABITypeAlign(V.Payload) > DL.getABITypeAlign(AlignType))
      AlignType = V.Payload;
    if (Decl.Definition && !DefaultCase.emplace(Name, Key).second)
      fail(Decl.At, "duplicate default case");
    Cases.emplace(Key, std::move(V));
    Alternatives.push_back(Key);
  }
  // Aligned integer slots preserve native payload offsets and can carry a
  // link-time pointer relocation as one constant initializer.
  unsigned Unit = DL.getABITypeAlign(AlignType).value();
  auto *Word = llvm::IntegerType::get(C, Unit * 8);
  R.IR->setBody({llvm::Type::getInt32Ty(C), llvm::ArrayType::get(AlignType, 0),
                 llvm::ArrayType::get(Word, llvm::divideCeil(Size, Unit))});
  R.Layer = R.IR;
  R.Complete = true;
  declareMembers(Name, Name + "::");
  // Default case viability is a declaration requirement, even if the root
  // unit never default-constructs this union.
  if (auto I = DefaultCase.find(Name); I != DefaultCase.end()) {
    auto &Case = Cases.at(I->second);
    if (!Case.Types.empty()) {
      auto *Probe = llvm::Function::Create(
          llvm::FunctionType::get(F.B.getVoidTy(), false),
          llvm::GlobalValue::InternalLinkage, "cpn.union.default.check", M);
      Frame Check(*this, nullptr, Probe, Name + "::");
      Check.B.SetInsertPoint(Check.block("entry"));
      Check.variant(Case, {}, Case.Decl.At, Check.allocate(Name, Case.Decl.At),
                    true, false);
      Probe->eraseFromParent();
    }
  }
}

const Case *Frame::findCase(const std::string &Name, const Token &At) {
  std::string Tail;
  auto Owner = memberQualifier(Name, At, Tail);
  if (!Owner)
    return nullptr;
  auto It = U.Cases.find(*Owner + "::" + Tail);
  return It == U.Cases.end() ? nullptr : &It->second;
}
llvm::Value *Frame::payloadAddress(const Case &C, llvm::Value *Object,
                                   unsigned Index) {
  auto *Storage = B.CreateStructGEP(U.ir(C.Owner), Object, 2);
  return B.CreateStructGEP(C.Payload, Storage, Index);
}

Value Frame::variant(const Case &C, const std::vector<Node> &Args,
                     const Token &At, llvm::Value *Dest, bool Default,
                     bool CheckInvariant) {
  if (!Default && Args.size() != C.Types.size())
    fail(At, "wrong union payload arity");
  if (!IR) {
    std::vector<llvm::Constant *> Fields;
    for (size_t I = 0; I < C.Types.size(); ++I) {
      auto V = Default ? construct(C.Types[I], {}, At)
                       : materialize(convert(eval(Args[I], C.Types[I]),
                                             C.Types[I], Args[I].At),
                                     Args[I].At);
      Fields.push_back(llvm::cast<llvm::Constant>(V.IR));
    }
    Value V{C.Owner,
            packVariant(C, llvm::ConstantStruct::get(C.Payload, Fields), At)};
    if (CheckInvariant)
      checkInvariants(V);
    V.Prvalue = V.Expiring = true;
    return V;
  }
  auto *Ptr = Dest ? Dest : allocate(C.Owner, At);
  for (size_t I = 0; I < C.Types.size(); ++I) {
    auto *Slot = payloadAddress(C, Ptr, I);
    if (Default)
      construct(C.Types[I], {}, At, Slot);
    else if (!directConstruction(Args[I], C.Types[I], Slot)) {
      auto V = convert(eval(Args[I], C.Types[I], Slot), C.Types[I], Args[I].At);
      materialize(V, Args[I].At, Slot);
    }
  }
  B.CreateStore(B.getInt32(C.Tag), B.CreateStructGEP(U.ir(C.Owner), Ptr, 0));
  Value V{C.Owner, B.CreateLoad(U.ir(C.Owner), Ptr), Ptr};
  if (CheckInvariant)
    checkInvariants(V);
  if (!Dest) {
    V.Prvalue = V.Expiring = true;
    Temps.push_back(V);
  }
  return V;
}

llvm::Constant *Frame::packVariant(const Case &C, llvm::Constant *Payload,
                                   const Token &At) {
  auto *Ty = U.Records.at(C.Owner).IR;
  auto *Storage = llvm::cast<llvm::ArrayType>(Ty->getElementType(2));
  auto *Word = Storage->getElementType();
  const auto &DL = U.M.getDataLayout();
  uint64_t Size = DL.getTypeAllocSize(C.Payload);
  uint64_t Stride = DL.getTypeAllocSize(Word);
  llvm::Constant *Data = llvm::Constant::getNullValue(Storage);
  if (!Payload->isNullValue()) {
    U.chargeConstant(At, Storage->getNumElements());
    std::vector<llvm::Constant *> Words;
    for (uint64_t I = 0; I < Storage->getNumElements(); ++I) {
      auto *W = I * Stride < Size
                    ? llvm::ConstantFoldLoadFromConst(
                          Payload, Word, llvm::APInt(64, I * Stride), DL)
                    : llvm::Constant::getNullValue(Word);
      if (!W || llvm::isa<llvm::UndefValue>(W))
        fail(At, "union payload cannot be represented as a target constant");
      Words.push_back(W);
    }
    Data = llvm::ConstantArray::get(Storage, Words);
  }
  auto *Image = llvm::ConstantStruct::get(
      Ty, {B.getInt32(C.Tag),
           llvm::Constant::getNullValue(Ty->getElementType(1)), Data});
  U.ConstantPayloads[Image] = Payload;
  return Image;
}

llvm::Constant *Frame::unpackVariant(const Case &C, llvm::Constant *Image,
                                     const Token &At) {
  auto *Tag =
      llvm::dyn_cast_or_null<llvm::ConstantInt>(Image->getAggregateElement(0u));
  auto P = U.ConstantPayloads.find(Image);
  if (!Tag || Tag->getZExtValue() != C.Tag || P == U.ConstantPayloads.end())
    fail(At, "inactive constant union payload");
  return P->second;
}

void Frame::constantMatch(const Node &N) {
  const auto &SubjectExpr = N.Children.front();
  auto Place = constantPlace(SubjectExpr);
  auto Subject = Place ? Place->read(*this, N.At) : eval(SubjectExpr);
  if (!Place && Subject.Location)
    Place = *Subject.Location;
  if (Subject.Prvalue)
    consume(Subject);
  auto Alternatives = U.Variants.find(Subject.Type);
  if (Alternatives == U.Variants.end())
    fail(N.At, "match requires a union value");
  auto *Image = llvm::cast<llvm::Constant>(Subject.IR);
  auto Tag = llvm::cast<llvm::ConstantInt>(Image->getAggregateElement(0u))
                 ->getZExtValue();
  const Node *Body = nullptr;
  Local Bindings;
  std::set<unsigned> Seen;
  bool Wild = false;
  for (const auto &Arm : llvm::drop_begin(N.Children)) {
    if (Wild)
      fail(Arm.At, "wildcard must be the final match arm");
    if (Arm.Text == "_") {
      Wild = true;
      if (!Body)
        Body = &Arm.Children.front();
      continue;
    }
    auto *C = findCase(Arm.Text, Arm.At);
    if (!C || C->Owner != Subject.Type)
      fail(Arm.At, "unknown union case");
    if (!Seen.insert(C->Tag).second || C->Types.size() != Arm.Params.size())
      fail(Arm.At, "duplicate case or incomplete payload pattern");
    std::set<std::string> Names;
    for (unsigned I = 0; I < Arm.Params.size(); ++I) {
      auto &P = Arm.Params[I];
      if (P.Type == "_")
        continue;
      if (!Names.insert(P.Text).second)
        fail(P.At, "duplicate match binding");
      if (P.Type == "move" && !Subject.Expiring)
        fail(P.At, "move binding requires an expiring subject");
      if (Tag != C->Tag)
        continue;
      auto Field = Place.value_or(
          ConstantPlace{&Subject, {}, Subject.Type, Subject.Readonly});
      Field.Type = C->Types[I];
      Field.Readonly |= C->Decl.Params[I].Const;
      Field.Steps.push_back({I, C});
      auto V = Field.read(*this, P.At);
      if (P.Type == "ref")
        V.Location = std::make_shared<ConstantPlace>(std::move(Field));
      else {
        V.Location = std::make_shared<ConstantPlace>(std::move(Field));
        V.Expiring = P.Type == "move";
        V = constantCopy(V, P.At);
        V.Prvalue = V.Expiring = false;
        V.Readonly = false;
        if (U.aggregate(V.Type))
          Bindings.ConstantDrops.push_back(P.Text);
      }
      Bindings.Names.emplace(P.Text, V);
    }
    if (Tag == C->Tag)
      Body = &Arm.Children.front();
  }
  if (!Wild && Seen.size() != Alternatives->second.size())
    fail(N.At, "non-exhaustive match");
  if (!Body)
    fail(N.At, "invalid constant union discriminant");
  Scopes.push_back(std::move(Bindings));
  // A return or loop transfer still leaves the binding and subject scopes.
  auto finish = [&] {
    endConstantScope();
    Scopes.pop_back();
    if (Subject.Prvalue)
      constantDrop(load(Subject), N.At);
    endExpression();
  };
  try {
    stmt(*Body);
  } catch (const ConstantTransfer &) {
    finish();
    throw;
  }
  finish();
}

// Only the active alternative has live payload objects.
void Frame::visitPayload(Value Object,
                         llvm::function_ref<void(const Case &)> Visit) {
  auto *Invalid = block("union.invalid"), *End = block("union.end");
  auto *Tag = B.CreateStructGEP(U.ir(Object.Type), Object.Address, 0);
  auto *Switch = B.CreateSwitch(B.CreateLoad(B.getInt32Ty(), Tag), Invalid);
  for (const auto &Key : U.Variants.at(Object.Type)) {
    const auto &C = U.Cases.at(Key);
    auto *BB = block("union.case");
    Switch->addCase(B.getInt32(C.Tag), BB);
    B.SetInsertPoint(BB);
    Visit(C);
    branch(End);
  }
  B.SetInsertPoint(Invalid);
  B.CreateUnreachable();
  B.SetInsertPoint(End);
}

void Frame::transferPayload(Value Source, llvm::Value *Dest,
                            SpecialOperation Op, const Token &At) {
  auto *Ty = U.ir(Source.Type);
  visitPayload(Source, [&](const Case &C) {
    for (size_t I = 0; I < C.Types.size(); ++I)
      transfer({C.Types[I], nullptr, payloadAddress(C, Source.Address, I),
                Source.Readonly || C.Decl.Params[I].Const},
               payloadAddress(C, Dest, I), Op, At);
    B.CreateStore(B.getInt32(C.Tag), B.CreateStructGEP(Ty, Dest, 0));
  });
}

void Frame::beginUnionConstructor() {
  const auto &R = U.Records.at(F->Owner);
  for (auto Op :
       {SpecialOperation::CopyConstruct, SpecialOperation::MoveConstruct}) {
    auto I = R.Special.find(Op);
    if (I != R.Special.end() && I->second.Body == F) {
      Value Source{F->Owner, nullptr, IR->getArg(1),
                   Op == SpecialOperation::CopyConstruct};
      transferPayload(Source, Self.Address, Op, F->Decl.At);
      return;
    }
  }
  auto Default = U.DefaultCase.find(F->Owner);
  if (Default == U.DefaultCase.end())
    fail(F->Decl.At, "union construction requires a selected case");
  variant(U.Cases.at(Default->second), {}, F->Decl.At, Self.Address, true,
          false);
}
void Frame::dropPayload(Value Object) {
  visitPayload(Object, [&](const Case &C) {
    for (size_t I = C.Types.size(); I; --I)
      dropChild(Object, {C.Types[I - 1], nullptr,
                         payloadAddress(C, Object.Address, I - 1)});
  });
}
void Frame::match(const Node &N) {
  auto Subject = eval(N.Children[0]);
  if (!U.Variants.count(Subject.Type))
    fail(N.At, "match requires a union value");
  Scopes.emplace_back();
  if (Subject.Prvalue) {
    consume(Subject);
    Subject.DeclaredAt = {N.At.Line, N.At.Column};
    Scopes.back().Drops.push_back(Subject);
  }
  endExpression();
  auto *Address = Subject.Address;
  if (!Address) {
    Address = allocate(Subject.Type, N.At);
    B.CreateStore(Subject.IR, Address);
  }
  auto *End = block("match.end"), *Invalid = block("match.invalid");
  auto *SW = B.CreateSwitch(B.CreateExtractValue(Subject.IR, 0), Invalid);
  std::set<std::string> Seen;
  bool Any = false, Wild = false;
  for (size_t I = 1; I < N.Children.size(); ++I) {
    auto &Arm = N.Children[I];
    auto *BB = block("match.case");
    B.SetInsertPoint(BB);
    Scopes.emplace_back();
    if (Wild)
      fail(Arm.At, "wildcard must be the final match arm");
    if (Arm.Text == "_") {
      Wild = true;
      SW->setDefaultDest(BB);
    } else {
      const auto *Selected = findCase(Arm.Text, Arm.At);
      if (!Selected || Selected->Owner != Subject.Type)
        fail(Arm.At, "unknown union case");
      const auto &C = *Selected;
      if (!Seen.insert(C.Decl.Text).second ||
          C.Types.size() != Arm.Params.size())
        fail(Arm.At, "duplicate case or incomplete payload pattern");
      SW->addCase(B.getInt32(C.Tag), BB);
      for (size_t J = 0; J < Arm.Params.size(); ++J) {
        auto &P = Arm.Params[J];
        if (P.Type == "_")
          continue;
        auto *Ptr = payloadAddress(C, Address, J);
        Value Binding{C.Types[J], nullptr, Ptr,
                      Subject.Readonly || C.Decl.Params[J].Const};
        Binding = subobject(Subject, Binding);
        ensureLive(Binding, P.At);
        if (P.Type != "ref") {
          bool Move = P.Type == "move";
          if (Move && !Subject.Expiring)
            fail(P.At, "move binding requires an expiring subject");
          auto *Copy = allocate(Binding.Type, P.At);
          transfer(Binding, Copy,
                   Move ? SpecialOperation::MoveConstruct
                        : SpecialOperation::CopyConstruct,
                   P.At);
          Binding = {C.Types[J], nullptr, Copy};
          Binding.DeclaredAt = {Arm.At.Line, Arm.At.Column};
          Scopes.back().Drops.push_back(Binding);
        }
        if (!Scopes.back().Names.emplace(P.Text, Binding).second)
          fail(P.At, "duplicate match binding");
      }
    }
    Live = true;
    if (Transaction)
      Transaction->restoreFlow(Arm.Children[0]);
    stmt(Arm.Children[0]);
    Any |= Live;
    if (Live)
      cleanup(Scopes.size() - 1);
    branch(End);
    Scopes.pop_back();
  }
  if (!Wild && Seen.size() != U.Variants.at(Subject.Type).size())
    fail(N.At, "non-exhaustive match");
  B.SetInsertPoint(Invalid);
  B.CreateUnreachable();
  B.SetInsertPoint(End);
  if (Transaction)
    Transaction->restoreFlow(N, true);
  Live = Any;
  if (Live)
    cleanup(Scopes.size() - 1);
  Scopes.pop_back();
}
