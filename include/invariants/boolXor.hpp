#pragma once

#include <algorithm>
#include <functional>

#include "core/types.hpp"
#include "invariants/invariant.hpp"
#include "variables/intVar.hpp"

/**
 * Invariant for output <- xor(x, y) [bool(x) != bool(y)]
 *
 */

class Engine;
class BoolXor : public Invariant {
 private:
  const VarId _output, _x, _y;

 public:
  explicit BoolXor(Engine&, VarId output, VarId x, VarId y);
  void registerVars() override;
  void updateBounds(bool widenOnly = false) override;
  void recompute(Timestamp) override;
  void notifyInputChanged(Timestamp, LocalId) override;
  void commit(Timestamp) override;
  VarId nextInput(Timestamp) override;
  void notifyCurrentInputChanged(Timestamp) override;
};
