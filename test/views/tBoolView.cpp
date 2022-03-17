#include <gtest/gtest.h>

#include <memory>
#include <vector>

#include "core/propagationEngine.hpp"
#include "core/types.hpp"
#include "views/boolView.hpp"

namespace {

class BoolViewTest : public ::testing::Test {
 protected:
  std::unique_ptr<PropagationEngine> engine;

  void SetUp() override { engine = std::make_unique<PropagationEngine>(); }
};

TEST_F(BoolViewTest, CreateBoolView) {
  engine->open();

  const VarId var = engine->makeIntVar(10, 0, 10);
  auto viewOfVar = engine->makeIntView<BoolView>(var);
  auto viewOfView = engine->makeIntView<BoolView>(viewOfVar);

  EXPECT_EQ(engine->committedValue(viewOfVar), Int(1));
  EXPECT_EQ(engine->committedValue(viewOfView), Int(1));

  engine->close();
}

TEST_F(BoolViewTest, ComputeBounds) {
  engine->open();
  auto a = engine->makeIntVar(20, -100, 100);

  auto va = engine->makeIntView<BoolView>(a);

  EXPECT_EQ(engine->lowerBound(va), Int(0));
  EXPECT_EQ(engine->upperBound(va), Int(1));

  engine->close();

  EXPECT_EQ(engine->lowerBound(va), Int(0));
  EXPECT_EQ(engine->upperBound(va), Int(1));
}

TEST_F(BoolViewTest, RecomputeBoolView) {
  engine->open();
  auto a = engine->makeIntVar(20, -100, 100);

  auto viewOfVarId = engine->makeIntView<BoolView>(a);

  EXPECT_EQ(engine->currentValue(viewOfVarId), Int(1));

  engine->close();

  EXPECT_EQ(engine->currentValue(viewOfVarId), Int(1));

  engine->beginMove();
  engine->setValue(a, 0);
  engine->endMove();

  engine->beginProbe();
  engine->query(a);
  engine->endProbe();

  EXPECT_EQ(engine->currentValue(viewOfVarId), Int(0));
}

}
