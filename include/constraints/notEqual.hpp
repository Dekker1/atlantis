#pragma once

#include <algorithm>
#include <functional>

#include "constraint.hpp"
#include "core/types.hpp"
#include "variables/intVar.hpp"

class Engine;
class NotEqual : public Constraint {
 private:
  const VarId _x, _y;

 public:
  explicit NotEqual(Engine&, VarId violationId, VarId x, VarId y);

  void registerVars() override;
  void updateBounds(bool widenOnly = false) override;
  void recompute(Timestamp) override;
  void notifyInputChanged(Timestamp, LocalId) override;
  void commit(Timestamp) override;
  VarId nextInput(Timestamp) override;
  void notifyCurrentInputChanged(Timestamp) override;
};
