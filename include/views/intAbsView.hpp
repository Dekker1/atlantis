#pragma once

#include <memory>
#include <vector>

#include "views/intView.hpp"

class IntAbsView : public IntView {
 public:
  IntAbsView(const VarId parentId) : IntView(parentId) {}

  [[nodiscard]] Int value(Timestamp) override;
  [[nodiscard]] Int committedValue() override;
  [[nodiscard]] Int lowerBound() const override;
  [[nodiscard]] Int upperBound() const override;
};