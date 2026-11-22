#include "Sema.h"
using namespace cpn;
namespace {
bool same(Function *A, Function *B) {
  return A->Decl.Text == B->Decl.Text && A->Params == B->Params &&
         A->Decl.Const == B->Decl.Const &&
         A->Decl.Settings["category"] == B->Decl.Settings["category"];
}
} // namespace
std::string Frame::methodOwner(const std::string &Type, const Token &T) {
  if (U.Overloads.count(Type + "::" + T.Text))
    return Type;
  if (!U.Records.count(Type))
    return "";
  std::string Found;
  for (auto &Base : U.Records.at(Type).Bases) {
    auto M = methodOwner(Base, T);
    if (M.empty())
      continue;
    if (!Found.empty())
      fail(T, "ambiguous inherited method");
    Found = std::move(M);
  }
  return Found;
}
void Context::buildTables(const std::string &Name,
                          const std::vector<Function *> &Methods) {
  auto &R = Records.at(Name);
  for (auto &Base : R.Bases) {
    auto &BR = Records.at(Base);
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
          ((*It)->Decl.Noexcept && !D->Decl.Noexcept) ||
          (*It)->Result != D->Result)
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
  using Layer = std::pair<std::string, uint64_t>;
  std::function<void(std::vector<Layer>)> table = [&](std::vector<Layer> Path) {
    auto [View, Offset] = Path.back();
    auto &VR = Records.at(View);
    auto *Layout = M.getDataLayout().getStructLayout(VR.IR);
    if (VR.Polymorphic) {
      std::vector<llvm::Constant *> Entries;
      for (auto *Slot : VR.Virtuals) {
        auto *Target = Slot;
        uint64_t TargetOffset = Offset;
        for (auto &[Name, Start] : Path) {
          auto &Part = Records.at(Name);
          auto It = std::find_if(
              Part.Virtuals.begin(), Part.Virtuals.end(),
              [&](auto *F) { return F->Owner == Name && same(F, Slot); });
          if (It != Part.Virtuals.end()) {
            Target = *It;
            TargetOffset = Start;
            break;
          }
        }
        llvm::Function *Entry = Target->IR;
        if (TargetOffset != Offset) {
          Entry = llvm::Function::Create(Target->IR->getFunctionType(),
                                         llvm::GlobalValue::InternalLinkage,
                                         "cpn.virtual.adjust", M);
          llvm::IRBuilder<> B(llvm::BasicBlock::Create(C, "entry", Entry));
          std::vector<llvm::Value *> Args;
          Args.push_back(B.CreateGEP(B.getInt8Ty(), Entry->getArg(0),
                                     B.getInt64(TargetOffset - Offset)));
          for (unsigned I = 1; I < Entry->arg_size(); ++I)
            Args.push_back(Entry->getArg(I));
          auto *Call = B.CreateCall(Target->IR, Args);
          if (Entry->getReturnType()->isVoidTy())
            B.CreateRetVoid();
          else
            B.CreateRet(Call);
        }
        Entries.push_back(Entry);
      }
      if (Entries.empty())
        Entries.push_back(
            llvm::ConstantPointerNull::get(llvm::PointerType::getUnqual(C)));
      auto *AT =
          llvm::ArrayType::get(llvm::PointerType::getUnqual(C), Entries.size());
      auto *GV = new llvm::GlobalVariable(M, AT, true,
                                          llvm::GlobalValue::InternalLinkage,
                                          llvm::ConstantArray::get(AT, Entries),
                                          "cpn.vtable." + Name + "." + View);
      R.Tables.emplace_back(Offset + Layout->getElementOffset(VR.Fields.size()),
                            GV);
    }
    for (size_t I = 0; I < VR.Bases.size(); ++I) {
      auto Child = Path;
      Child.emplace_back(VR.Bases[I], Offset + Layout->getElementOffset(I));
      table(std::move(Child));
    }
  };
  table({{Name, 0}});
}
void Frame::installTables(Value Obj) {
  for (auto &[Offset, GV] : U.Records.at(Obj.Type).Tables)
    B.CreateStore(GV,
                  B.CreateGEP(B.getInt8Ty(), Obj.Address, B.getInt64(Offset)));
}
Value Frame::indirect(Value Ptr, const std::vector<Node> &Args,
                      const Token &At) {
  auto T = element(Ptr.Type);
  if (!U.Signatures.count(T))
    fail(At, "function-pointer contract required");
  auto &Sig = U.Signatures.at(T);
  if (Sig.size() != Args.size() + 1)
    fail(At, "wrong argument count");
  std::vector<llvm::Type *> Types;
  std::vector<llvm::Value *> Vals;
  for (size_t I = 0; I < Args.size(); ++I) {
    Types.push_back(U.ir(Sig[I + 1]));
    Vals.push_back(convert(eval(Args[I], Sig[I + 1]), Sig[I + 1], At).IR);
  }
  auto *FT = llvm::FunctionType::get(U.ir(Sig.front()), Types, false);
  return {Sig[0], B.CreateCall(FT, Ptr.IR, Vals)};
}
