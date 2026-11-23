#include "Sema.h"

using namespace cpn;
using llvm::StringRef;

void Context::bindScalarLibrary() {
  // These nonallocating types use the same nominal identity and active-case
  // layout as ordinary unions, including in required constant evaluation.
  auto Library = parse(R"cpn(
    namespace std {
      union ScalarError {
        case InvalidBoolean;
        case InvalidScalar;
        case UndeclaredEnumerator;
        ScalarError(const<ScalarError>& other)=default;
        ScalarError(ScalarError&& other)=default;
      };
      generic<type T, type E> union Result {
        case Ok(T value);
        case Err(E error);
        Result(const<Result>& other)=default;
        Result(Result&& other)=default;
      };
      generic<type E> specialize union Result<void, E> {
        case Ok;
        case Err(E error);
        Result(const<Result>& other)=default;
        Result(Result&& other)=default;
      };
    }
  )cpn",
                       Opt);
  // Family owner sites share the source unit's position table.
  for (auto [Index, Decl] : llvm::enumerate(Library.front().Children)) {
    Decl.At.Line = 0;
    Decl.At.Column = Index + 1;
  }
  unit(Library);
}

std::optional<Value> Frame::scalarConversion(const Node &Call, StringRef Name,
                                             const std::vector<Node> &Args) {
  if (Call.K != Node::Name)
    return {};
  Name.consume_front("::");
  bool Forward = Name == "std::to_underlying";
  bool Fallible = Name == "std::try_from_underlying";
  if (!Forward && !Fallible && Name != "std::from_underlying")
    return {};
  if (Args.size() != 1 || Call.TemplateArgs.size() != (Forward ? 0 : 1))
    fail(Call.At, "invalid scalar-domain conversion arguments");

  auto Input = load(eval(Args.front()));
  auto Target =
      Forward ? Input.Type : resolve(Call.TemplateArgs.front().Type, Call.At);
  const bool Boolean = Target == "bool", Character = Target == "char";
  if (!Boolean && !Character && !U.DefinedEnums.count(Target))
    fail(Call.At, "scalar-domain conversion requires bool, char, or a complete "
                  "enumeration");

  auto Underlying = Boolean     ? std::string("u8")
                    : Character ? std::string("u32")
                                : U.Enums.at(Target);
  if (Forward) {
    Underlying = resolve(Underlying, Call.At);
    return Value{Underlying, B.CreateZExtOrTrunc(Input.IR, U.ir(Underlying))};
  }
  if (!integer(Input.Type))
    fail(Call.At, "scalar-domain reconstruction requires an integer");

  unsigned Bits =
      std::max(Input.IR->getType()->getIntegerBitWidth(), width(Underlying)) +
      1;
  auto *Wide = B.getIntNTy(Bits);
  auto *Integer = B.CreateIntCast(Input.IR, Wide, signedType(Input.Type));
  auto Number = [&](uint64_t N) { return llvm::ConstantInt::get(Wide, N); };
  llvm::Value *Valid = B.getFalse();
  if (Boolean)
    Valid = B.CreateICmpULE(Integer, Number(1));
  else if (Character) {
    auto *InRange = B.CreateICmpULE(Integer, Number(0x10ffff));
    auto *NotSurrogate = B.CreateOr(B.CreateICmpULT(Integer, Number(0xd800)),
                                    B.CreateICmpUGT(Integer, Number(0xdfff)));
    Valid = B.CreateAnd(InRange, NotSurrogate);
  } else if (auto It = U.EnumValues.find(Target); It != U.EnumValues.end())
    for (auto *Enumerator : It->second) {
      auto *Exact = B.CreateIntCast(Enumerator, Wide, signedType(Underlying));
      Valid = B.CreateOr(Valid, B.CreateICmpEQ(Integer, Exact));
    }
  auto Convert = [&]() {
    return B.CreateIntCast(Integer, U.ir(Target), false);
  };

  auto *Known = llvm::dyn_cast<llvm::ConstantInt>(Valid);
  if (!Fallible) {
    if (!IR && (!Known || Known->isZero()))
      fail(Call.At,
           "scalar-domain reconstruction fails in constant evaluation");
    if (Known && Known->isZero())
      Opt.diagnose(Call.At, Severity::Anomaly, {},
                   "scalar-domain reconstruction selects ContractTrap");
    guard(B.CreateNot(Valid), "contract");
    return Value{Target, Convert()};
  }

  const auto Type =
      resolve("::std::Result<" + Target + ",::std::ScalarError>", Call.At);
  const auto &Ok = U.Cases.at(Type + "::Ok");
  const auto &Err = U.Cases.at(Type + "::Err");
  const auto &Error =
      U.Cases.at(Boolean     ? "std::ScalarError::InvalidBoolean"
                 : Character ? "std::ScalarError::InvalidScalar"
                             : "std::ScalarError::UndeclaredEnumerator");
  if (!IR) {
    bool Success = !llvm::cast<llvm::ConstantInt>(Valid)->isZero();
    const auto &Alternative = Success ? Ok : Err;
    auto *Payload = llvm::cast<llvm::Constant>(
        Success ? Convert() : variant(Error, {}, Call.At).IR);
    Value V{Type, packVariant(
                      Alternative,
                      llvm::ConstantStruct::get(Alternative.Payload, {Payload}),
                      Call.At)};
    V.Prvalue = V.Expiring = true;
    return V;
  }

  auto *Storage = resultAddress(Type, Call.At);
  auto Finish = [&](const Case &Alternative) {
    auto *Slot = payloadAddress(Alternative, Storage, 0);
    if (&Alternative == &Ok)
      B.CreateStore(Convert(), Slot);
    else
      variant(Error, {}, Call.At, Slot);
    B.CreateStore(B.getInt32(Alternative.Tag),
                  B.CreateStructGEP(U.ir(Type), Storage, 0));
  };
  if (Known)
    Finish(Known->isZero() ? Err : Ok);
  else {
    auto *Success = block("scalar.valid"), *Failure = block("scalar.invalid"),
         *Done = block("scalar.result");
    B.CreateCondBr(Valid, Success, Failure);
    B.SetInsertPoint(Success);
    Finish(Ok);
    B.CreateBr(Done);
    B.SetInsertPoint(Failure);
    Finish(Err);
    B.CreateBr(Done);
    B.SetInsertPoint(Done);
  }
  return callResult(Type, nullptr, Call.At, Storage);
}
