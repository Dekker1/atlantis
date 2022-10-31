#pragma once

#include <memory>
#include <vector>

#include "core/engine.hpp"
#include "views/intView.hpp"

class NotEqualConst : public IntView {
 private:
  const Int _val;

 public:
  explicit NotEqualConst(Engine& engine, VarId parentId, Int val)
      : IntView(engine, parentId), _val(val) {}

  [[nodiscard]] Int value(Timestamp) override;
  [[nodiscard]] Int committedValue() override;
  [[nodiscard]] Int lowerBound() const override;
  [[nodiscard]] Int upperBound() const override;
};