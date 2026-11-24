#ifndef LLVM_TOOLS_CPNC_CONSTRAINTLOGIC_H
#define LLVM_TOOLS_CPNC_CONSTRAINTLOGIC_H

#include <algorithm>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace cpn {
// An ordered Boolean decision graph provides the canonical proposition shared
// by syntax binding and semantic constraint ordering.
class ConstraintLogic {
public:
  using Formula = unsigned;

  explicit ConstraintLogic(std::function<void(unsigned)> Charge)
      : Charge(std::move(Charge)) {}

  size_t nodeCount() const { return Nodes.size() - 2; }
  void chargeVisit(unsigned Depth) const { Charge(Depth); }

  Formula variable(const std::string &Key) {
    auto I = Atoms.try_emplace(Key, Atoms.size()).first;
    return node(I->second, 0, 1);
  }

  std::optional<Formula> findVariable(const std::string &Key) const {
    auto I = Atoms.find(Key);
    if (I == Atoms.end())
      return std::nullopt;
    return Unique.at({I->second, 0, 1});
  }

  Formula negate(Formula F, unsigned Depth = 0) {
    if (F < 2)
      return 1 - F;
    if (auto I = Negations.find(F); I != Negations.end())
      return I->second;
    Charge(Depth);
    auto [Atom, False, True] = Nodes[F];
    auto Result = node(Atom, negate(False, Depth + 1), negate(True, Depth + 1));
    Negations.emplace(F, Result);
    return Result;
  }

  Formula conjunction(Formula L, Formula R, unsigned Depth = 0) {
    if (L > R)
      std::swap(L, R);
    if (L == 0 || L == R)
      return L;
    if (L == 1)
      return R;
    if (auto I = Conjunctions.find({L, R}); I != Conjunctions.end())
      return I->second;
    Charge(Depth);
    auto [LA, LF, LT] = Nodes[L];
    auto [RA, RF, RT] = Nodes[R];
    unsigned Top = std::min(LA, RA);
    auto False = conjunction(LA == Top ? LF : L, RA == Top ? RF : R, Depth + 1);
    auto True = conjunction(LA == Top ? LT : L, RA == Top ? RT : R, Depth + 1);
    auto Result = node(Top, False, True);
    Conjunctions.emplace(std::pair(L, R), Result);
    return Result;
  }

  Formula disjunction(Formula L, Formula R) {
    return negate(conjunction(negate(L), negate(R)));
  }

  bool stronger(Formula L, Formula R) {
    return L != R && conjunction(L, negate(R)) == 0;
  }

private:
  using Decision = std::tuple<unsigned, Formula, Formula>;
  std::function<void(unsigned)> Charge;
  std::map<std::string, unsigned> Atoms;
  std::vector<Decision> Nodes{{}, {}};
  std::map<Decision, Formula> Unique;
  std::map<std::pair<Formula, Formula>, Formula> Conjunctions;
  std::map<Formula, Formula> Negations;

  Formula node(unsigned Atom, Formula False, Formula True) {
    if (False == True)
      return False;
    Decision Key{Atom, False, True};
    auto [I, New] = Unique.try_emplace(Key, Nodes.size());
    if (New)
      Nodes.push_back(Key);
    return I->second;
  }
};
} // namespace cpn

#endif
