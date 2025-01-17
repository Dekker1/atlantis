#pragma once

#include "atlantis/propagation/invariants/invariant.hpp"
#include "atlantis/propagation/solverBase.hpp"
#include "atlantis/propagation/types.hpp"
#include "atlantis/types.hpp"

namespace atlantis::propagation {

/**
 * Invariant for y <- a ^ b
 *
 */
class Pow : public Invariant {
 private:
  VarId _output;
  VarViewId _base, _exponent;
  Int _zeroReplacement{1};

 public:
  explicit Pow(SolverBase&, VarId output, VarViewId base, VarViewId exponent);

  explicit Pow(SolverBase&, VarViewId output, VarViewId base,
               VarViewId exponent);

  void registerVars() override;
  void updateBounds(bool widenOnly) override;
  void recompute(Timestamp) override;
  VarViewId nextInput(Timestamp) override;
  void notifyCurrentInputChanged(Timestamp) override;
  void notifyInputChanged(Timestamp, LocalId) override;
};

}  // namespace atlantis::propagation
