#pragma once

#include "core/types.hpp"
#include "invariants/invariant.hpp"

class Engine;  // Forward declaration

class Constraint : public Invariant {
 private:
 protected:
  const VarId _violationId;
  explicit Constraint(VarId violationId)
      : Invariant(), _violationId(violationId) {}

 public:
  [[nodiscard]] inline VarId violationId() const;
  [[nodiscard]] inline Int violationCount(Engine&, Timestamp&) const;
};