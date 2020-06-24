#pragma once

#include <memory>
#include <vector>

#include "../core/constraint.hpp"
#include "../core/engine.hpp"
#include "../core/intVar.hpp"
#include "../core/tracer.hpp"
#include "../core/types.hpp"

class LessEqual : public Constraint {
 private:
  VarId m_x;
  VarId m_y;

 public:
  LessEqual(VarId violationId, VarId x, VarId y);
  
  ~LessEqual() = default;
  virtual void init(Timestamp, Engine&) override;
  virtual void recompute(Timestamp, Engine&) override;
  virtual void notifyIntChanged(Timestamp t, Engine& e, LocalId id,
                                Int oldValue, Int newValue, Int data) override;
  virtual void commit(Timestamp, Engine&) override;
  virtual VarId getNextDependency(Timestamp) override;
  virtual void notifyCurrentDependencyChanged(Timestamp, Engine& e) override;
};