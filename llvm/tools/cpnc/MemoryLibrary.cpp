#include "Sema.h"

using namespace cpn;
using llvm::StringRef;

void Context::bindMemoryLibrary(bool) {
  Aliases.emplace("std::mem::StorageView", StorageViewType);
  Aliases.emplace("std::mem::StorageIdentity", StorageIdentityType);
}

std::optional<Value> Frame::memoryCall(const Node &Call,
                                       const std::vector<Node> &Args,
                                       Value Receiver) {
  StringRef Name(Call.Text);
  Name.consume_front("::");
  if (Call.K == Node::Name && Name == "transfer_storage")
    fail(Call.At, "transfer_storage requires exclusive storage authority");
  if (Call.K != Node::Member || Receiver.Type != StorageViewType)
    return {};
  if (!Args.empty() || !Call.TemplateArgs.empty())
    fail(Call.At, "StorageView observers take no arguments");
  return storageViewObserver(load(Receiver), Name, Call.At);
}

bool cpn::usesMemoryLibrary(const Node &N) {
  if (StringRef(N.Text).starts_with("std::mem::") ||
      StringRef(N.Type).contains("std::mem::") || N.Text == "transfer_storage")
    return true;
  return llvm::any_of(N.Children, usesMemoryLibrary) ||
         llvm::any_of(N.Params, usesMemoryLibrary) ||
         llvm::any_of(N.TemplateArgs, usesMemoryLibrary) ||
         llvm::any_of(N.Contracts, usesMemoryLibrary);
}
