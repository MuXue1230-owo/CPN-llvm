#include "Sema.h"
using namespace cpn;

void Context::tagged(const Node &D, const std::string &Name,
                     const std::string &P, const Substitution &Env) {
  auto &R = Records[Name];
  if (R.IR && R.Decl.K != Node::Union)
    fail(D.At, "conflicting nominal declaration");
  if (R.Complete)
    fail(D.At, "duplicate union definition");
  R.Decl = D;
  if (!R.IR)
    R.IR = llvm::StructType::create(C, "cpn." + Name);
  if (D.Prototype)
    return;
  R.Env = Env;
  R.Env.Types[D.Text] = Name;
  Frame F(*this, nullptr, nullptr, P);
  F.Env = R.Env;
  const auto &DL = M.getDataLayout();
  uint64_t Size = 0;
  llvm::Type *AlignType = llvm::Type::getInt8Ty(C);
  auto &Alternatives = Variants[Name];
  for (const auto &Decl : D.Children) {
    if (Decl.K != Node::Variant) {
      if (Decl.K == Node::Field || Decl.K == Node::Init ||
          Decl.Settings.count("virtual"))
        fail(Decl.At,
             "union members cannot add common fields or virtual bases");
      if (Decl.K == Node::Constructor && !Decl.Settings.count("control"))
        fail(Decl.At, "authored union constructors are unavailable");
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
  R.IR->setBody({llvm::Type::getInt32Ty(C), llvm::ArrayType::get(AlignType, 0),
                 llvm::ArrayType::get(llvm::Type::getInt8Ty(C), Size)});
  R.Layer = R.IR;
  R.Complete = true;
  declareMembers(Name, P);
}

const Case *Frame::findCase(const std::string &Name, const Token &At) {
  auto Pos = Name.rfind("::");
  if (Pos == std::string::npos || Pos == 0)
    return nullptr;
  auto Owner = Name.substr(0, Pos);
  auto Base = Owner.substr(0, Owner.find('<'));
  if (!Env.Types.count(Owner) &&
      scopeKey(Prefix, Base, [&](const std::string &Key) {
        return U.Records.count(Key) || U.Aliases.count(Key) ||
               U.Families.count(Key);
      }).empty())
    return nullptr;
  auto It = U.Cases.find(resolve(Owner, At) + Name.substr(Pos));
  return It == U.Cases.end() ? nullptr : &It->second;
}
llvm::Value *Frame::payloadAddress(const Case &C, llvm::Value *Object,
                                   unsigned Index) {
  auto *Storage = B.CreateStructGEP(U.ir(C.Owner), Object, 2);
  return B.CreateStructGEP(C.Payload, Storage, Index);
}

Value Frame::variant(const Case &C, const std::vector<Node> &Args,
                     const Token &At, llvm::Value *Dest, bool Default) {
  if (!Default && Args.size() != C.Types.size())
    fail(At, "wrong union payload arity");
  if (!IR)
    fail(At, "union construction requires object storage");
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
  if (!Dest) {
    V.Prvalue = V.Expiring = true;
    Temps.push_back(V);
  }
  return V;
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
  Live = Any;
  if (Live)
    cleanup(Scopes.size() - 1);
  Scopes.pop_back();
}
