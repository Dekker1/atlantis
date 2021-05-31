#pragma once

#include <vector>

#include "core/engine.hpp"
#include "core/types.hpp"
#include "invariants/invariant.hpp"

/**
 * Invariant for y <- varArray[index] where varArray is a vector of VarId.
 *
 */

class ElementVar : public Invariant {
 private:
  VarId _index;
  std::vector<VarId> _varArray;
  VarId _y;

 public:
  ElementVar(VarId index, std::vector<VarId> varArray, VarId y);
  void init(Timestamp, Engine&) override;
  void recompute(Timestamp, Engine&) override;
  void notifyIntChanged(Timestamp, Engine&, LocalId) override;
  VarId getNextParameter(Timestamp, Engine&) override;
  void notifyCurrentParameterChanged(Timestamp, Engine&) override;
  void commit(Timestamp, Engine&) override;
};
