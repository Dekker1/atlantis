#include <iostream>
#include <limits>
#include <random>
#include <vector>

#include "core/propagationEngine.hpp"
#include "core/savedInt.hpp"
#include "core/types.hpp"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "invariants/elementVar.hpp"
#include "propagation/topDownPropagationGraph.hpp"

using ::testing::AtLeast;
using ::testing::Return;

namespace {

class MockElementVar : public ElementVar {
 public:
  MockElementVar(VarId i, std::vector<VarId>&& X, VarId b)
      : ElementVar(i, std::vector<VarId>{X}, b),
        real_(i, std::vector<VarId>{X}, b) {
    ON_CALL(*this, recompute)
        .WillByDefault([this](Timestamp timestamp, Engine& engine) {
          return real_.recompute(timestamp, engine);
        });
    ON_CALL(*this, getNextDependency)
        .WillByDefault([this](Timestamp t, Engine& e) {
          return real_.getNextDependency(t, e);
        });

    ON_CALL(*this, notifyCurrentDependencyChanged)
        .WillByDefault([this](Timestamp t, Engine& e) {
          real_.notifyCurrentDependencyChanged(t, e);
        });

    ON_CALL(*this, notifyIntChanged)
        .WillByDefault(
            [this](Timestamp t, Engine& e, LocalId id, Int newValue) {
              real_.notifyIntChanged(t, e, id, newValue);
            });

    ON_CALL(*this, commit).WillByDefault([this](Timestamp t, Engine& e) {
      real_.commit(t, e);
    });
  }

  MOCK_METHOD(void, recompute, (Timestamp timestamp, Engine& engine),
              (override));

  MOCK_METHOD(VarId, getNextDependency, (Timestamp, Engine&), (override));
  MOCK_METHOD(void, notifyCurrentDependencyChanged, (Timestamp, Engine& e),
              (override));

  MOCK_METHOD(void, notifyIntChanged,
              (Timestamp t, Engine& e, LocalId id, Int newValue), (override));
  MOCK_METHOD(void, commit, (Timestamp timestamp, Engine& engine), (override));

 private:
  ElementVar real_;
};

class ElementVarTest : public ::testing::Test {
 protected:
  std::mt19937 gen;

  std::unique_ptr<PropagationEngine> engine;

  virtual void SetUp() {
    std::random_device rd;
    gen = std::mt19937(rd());
    engine = std::make_unique<PropagationEngine>();
  }
};

TEST_F(ElementVarTest, CreateElement) {
  engine->open();

  std::vector<VarId> args{};
  int numArgs = 10;
  for (int value = 0; value < numArgs; ++value) {
    args.push_back(engine->makeIntVar(value, -100, 100));
  }

  VarId idx = engine->makeIntVar(3, 0, numArgs - 1);

  VarId output = engine->makeIntVar(-10, -100, 100);

  auto invariant = engine->makeInvariant<MockElementVar>(
      idx, std::vector<VarId>{args}, output);

  EXPECT_CALL(*invariant, recompute(testing::_, testing::_)).Times(AtLeast(1));

  EXPECT_CALL(*invariant, commit(testing::_, testing::_)).Times(AtLeast(1));

  engine->close();

  EXPECT_EQ(engine->getValue(output), 3);
}

TEST_F(ElementVarTest, NotificationsChangeIndex) {
  engine->open();

  std::vector<VarId> args{};
  int numArgs = 10;
  for (int value = 0; value < numArgs; ++value) {
    args.push_back(engine->makeIntVar(value, -100, 100));
  }

  VarId idx = engine->makeIntVar(0, 0, numArgs - 1);

  VarId output = engine->makeIntVar(-10, -100, 100);

  auto invariant = engine->makeInvariant<MockElementVar>(
      idx, std::vector<VarId>{args}, output);

  EXPECT_CALL(*invariant, recompute(testing::_, testing::_)).Times(AtLeast(1));

  EXPECT_CALL(*invariant, commit(testing::_, testing::_)).Times(AtLeast(1));

  engine->close();

  EXPECT_CALL(*invariant, getNextDependency(testing::_, testing::_)).Times(3);

  EXPECT_CALL(*invariant,
              notifyCurrentDependencyChanged(testing::_, testing::_))
      .Times(1);

  engine->beginMove();
  engine->updateValue(idx, 5);
  engine->endMove();

  engine->beginQuery();
  engine->query(output);
  engine->endQuery();
}

}  // namespace
