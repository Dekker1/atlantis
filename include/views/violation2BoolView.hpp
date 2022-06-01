#pragma once

#include <memory>
#include <vector>

#include "views/intView.hpp"

class Violation2BoolView : public IntView {
 public:
  explicit Violation2BoolView(const VarId parentId) : IntView(parentId) {}

  [[nodiscard]] Int value(Timestamp) override;
  [[nodiscard]] Int committedValue() override;
  [[nodiscard]] Int lowerBound() const override { return 0; }
  [[nodiscard]] Int upperBound() const override { return 1; }
};