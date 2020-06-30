#pragma once

#include <memory>
#include <vector>
#include <limits>

#include "../core/constraint.hpp"
#include "../core/engine.hpp"
#include "../core/intVar.hpp"
#include "../core/tracer.hpp"
#include "../core/types.hpp"
#include "../core/savedInt.hpp"

class AllDifferent : public Constraint {
 private:
  std::vector<VarId> m_variables;
  std::vector<SavedInt> m_counts;
  Int m_offset;
  void increaseCount(Timestamp ts, Engine& e, Int value);
  void decreaseCount(Timestamp ts, Engine& e, Int value);
 public:
  AllDifferent(VarId violationId, std::vector<VarId> t_variables);
  
  virtual ~AllDifferent() = default;
  virtual void init(Timestamp, Engine&) override;
  virtual void recompute(Timestamp, Engine&) override;
  virtual void notifyIntChanged(Timestamp t, Engine& e, LocalId id,
                                Int oldValue, Int newValue, Int data) override;
  virtual void commit(Timestamp, Engine&) override;
  virtual VarId getNextDependency(Timestamp, Engine& e) override;
  virtual void notifyCurrentDependencyChanged(Timestamp, Engine& e) override;
};
