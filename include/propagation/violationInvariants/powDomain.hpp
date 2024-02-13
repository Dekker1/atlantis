#pragma once

#include "propagation/solver.hpp"
#include "propagation/variables/intVar.hpp"
#include "propagation/violationInvariants/violationInvariant.hpp"
#include "types.hpp"

namespace atlantis::propagation {

class PowDomain : public ViolationInvariant {
 private:
  VarId _x, _y;

 public:
  explicit PowDomain(SolverBase&, VarId violationId, VarId x, VarId y);

  void registerVars() override;
  void updateBounds(bool widenOnly) override;
  void recompute(Timestamp) override;
  void notifyInputChanged(Timestamp, LocalId) override;
  VarId nextInput(Timestamp) override;
  void notifyCurrentInputChanged(Timestamp) override;

  static bool shouldPost(SolverBase&, VarId x, VarId y);
};

}  // namespace atlantis::propagation