#pragma once

#include <limits>
#include <memory>
#include <vector>

#include "../core/constraint.hpp"
#include "../core/engine.hpp"
#include "../core/intVar.hpp"
#include "../core/savedInt.hpp"
#include "../core/tracer.hpp"
#include "../core/types.hpp"

class AllDifferent : public Constraint {
 private:
  std::vector<VarId> m_variables;
  std::vector<SavedInt> m_localValues;
  std::vector<SavedInt> m_counts;
  Int m_offset;
  void increaseCount(Timestamp ts, Engine& e, Int value);
  void decreaseCount(Timestamp ts, Engine& e, Int value);

 public:
  AllDifferent(VarId violationId, std::vector<VarId> t_variables);

  virtual ~AllDifferent() = default;
  virtual void init(Timestamp, Engine&) override;
  virtual void recompute(Timestamp, Engine&) override;
  virtual void notifyIntChanged(Timestamp t, Engine& e, LocalId id) override;
  virtual void commit(Timestamp, Engine&) override;
  virtual VarId getNextDependency(Timestamp, Engine& e) override;
  virtual void notifyCurrentDependencyChanged(Timestamp, Engine& e) override;
};

inline void AllDifferent::increaseCount(Timestamp ts, Engine& e, Int value) {
  Int newCount = m_counts.at(value - m_offset).incValue(ts, 1);
  assert(newCount >= 0);
  assert(newCount <= static_cast<Int>(m_variables.size()));
  if (newCount >= 2) {
    e.incValue(ts, m_violationId, 1);
  }
}

inline void AllDifferent::decreaseCount(Timestamp ts, Engine& e, Int value) {
  Int newCount = m_counts.at(value - m_offset).incValue(ts, -1);
  assert(newCount >= 0);
  assert(newCount <= static_cast<Int>(m_variables.size()));
  if (newCount >= 1) {
    e.incValue(ts, m_violationId, -1);
  }
}
