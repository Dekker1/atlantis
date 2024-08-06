#pragma once

#include <memory>
#include <vector>

#include "atlantis/misc/blackboxFunction.hpp"
#include "atlantis/propagation/invariants/invariant.hpp"
#include "atlantis/propagation/solverBase.hpp"
#include "atlantis/propagation/types.hpp"

namespace atlantis::propagation {

class Blackbox : public Invariant {
 private:
  std::unique_ptr<blackbox::BlackBoxFn> _blackBoxFn;
  std::vector<VarId> _outputs;
  std::vector<VarId> _inputs;

 public:
  Blackbox(SolverBase&, std::unique_ptr<blackbox::BlackBoxFn>&& blackBoxFn,
           std::vector<VarId>&& outputs, std::vector<VarId>&& inputs);

  void registerVars() override;
  void updateBounds(bool) override {}
  void recompute(Timestamp) override;
  void notifyInputChanged(Timestamp, LocalId) override;
  VarId nextInput(Timestamp) override;
  void notifyCurrentInputChanged(Timestamp) override;
};

}  // namespace atlantis::propagation
