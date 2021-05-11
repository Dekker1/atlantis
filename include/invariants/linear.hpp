#pragma once

#include <vector>


#include "core/types.hpp"
#include "invariants/invariant.hpp"

class Engine;

/**
 * Invariant for b <- sum(A_i*X_i)
 *
 */

class Linear : public Invariant {
 private:
  std::vector<Int> m_A;
  std::vector<VarId> m_X;
  std::vector<SavedInt> m_localX;
  VarId m_b;

 public:
  Linear(std::vector<VarId> X, VarId b)
      : Linear(std::vector<Int>(X.size(), 1), X, b) {}
  Linear(std::vector<Int> A, std::vector<VarId> X, VarId b);

  void init(Timestamp, Engine&) override;
  void recompute(Timestamp, Engine&) override;
  VarId getNextDependency(Timestamp, Engine&) override;
  void notifyCurrentDependencyChanged(Timestamp, Engine& e) override;
  void notifyIntChanged(Timestamp t, Engine& e, LocalId id) override;
  void commit(Timestamp, Engine&) override;
};
