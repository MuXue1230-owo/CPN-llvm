#include "Sema.h"
using namespace cpn;
std::string Frame::directField(const Node &N) const {
  if (N.K == Node::Name) {
    for (auto &Scope : Scopes)
      if (Scope.Names.count(N.Text))
        return "";
    return FieldFlags.count(N.Text) ? N.Text : "";
  }
  if (N.K == Node::Member && N.Definition && N.Children[0].K == Node::Name &&
      N.Children[0].Text == "this" && FieldFlags.count(N.Text))
    return N.Text;
  return "";
}
void Frame::endField(const std::string &Slot, const Token &At,
                     bool RunDestructor, bool Explicit) {
  auto It = FieldFlags.find(Slot);
  if (It == FieldFlags.end())
    fail(At, "request must select a direct subobject");
  auto *Alive = B.CreateLoad(B.getInt1Ty(), It->second);
  if (Explicit)
    guard(B.CreateNot(Alive));
  auto *Do = block("retire.slot"), *Done = block("retire.next");
  B.CreateCondBr(Alive, Do, Done);
  B.SetInsertPoint(Do);
  B.CreateStore(B.getFalse(), It->second);
  Token Name = At;
  Name.Text = Slot;
  if (RunDestructor)
    dropChild(Self, member(Self, Name),
              llvm::StringRef(Slot).starts_with("$base:") ||
                  llvm::StringRef(Slot).starts_with("$virtual:"));
  branch(Done);
  B.SetInsertPoint(Done);
}
void Frame::retirement() {
  auto &R = U.Records.at(Self.Type);
  installTables(Self);
  std::set<std::string> Manual;
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
        for (auto &Field : R.Fields)
          Manual.insert(Field.Decl.Text);
      } else if (FieldFlags.count(D.Text))
        Manual.insert(D.Text);
      else
        fail(D.At, "Complete must select a direct subobject");
    }
  InlineReturn = block("dtor.sweep");
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
      B.CreateCondBr(B.CreateLoad(B.getInt1Ty(), FieldFlags.at(Slot)), Cleanup,
                     Next);
      B.SetInsertPoint(Next);
    } else
      endField(Slot, I->Decl.At, true, false);
  }
  branch(Cleanup);
  B.SetInsertPoint(Cleanup);
  InlineReturn = block("dtor.remainder");
  if (F->Decl.Children.size() > 1)
    stmt(F->Decl.Children[1]);
  branch(InlineReturn);
  B.SetInsertPoint(InlineReturn);
  InlineReturn = nullptr;
  Live = true;
  for (auto I = R.Fields.rbegin(); I != R.Fields.rend(); ++I)
    endField(I->Decl.Text, I->Decl.At, true, false);
}
