#pragma once

#include <memory>
#include <vector>

#include "propagation/solver.hpp"
#include "propagation/views/intView.hpp"

namespace atlantis::propagation {

class LessEqualConst : public IntView {
 private:
  Int _val;

 public:
  explicit LessEqualConst(SolverBase& solver, VarId parentId, Int val)
      : IntView(solver, parentId), _val(val) {}

  [[nodiscard]] Int value(Timestamp) override;
  [[nodiscard]] Int committedValue() override;
  [[nodiscard]] Int lowerBound() const override;
  [[nodiscard]] Int upperBound() const override;
};

}  // namespace atlantis::propagation