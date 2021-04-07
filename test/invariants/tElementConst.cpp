#include <iostream>
#include <limits>
#include <random>
#include <vector>

#include "core/propagationEngine.hpp"
#include "core/savedInt.hpp"
#include "core/types.hpp"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "invariants/elementConst.hpp"

using ::testing::AtLeast;
using ::testing::Return;

namespace {

class MockElementConst : public ElementConst {
 public:
  bool m_initialized = false;

  void init(Timestamp timestamp, Engine& e) override {
    m_initialized = true;
    ElementConst::init(timestamp, e);
  }

  MockElementConst(VarId i, std::vector<Int>&& X, VarId b)
      : ElementConst(i, std::vector<Int>{X}, b) {
    ON_CALL(*this, recompute)
        .WillByDefault([this](Timestamp timestamp, Engine& engine) {
          return ElementConst::recompute(timestamp, engine);
        });
    ON_CALL(*this, getNextDependency)
        .WillByDefault([this](Timestamp t, Engine& e) {
          return ElementConst::getNextDependency(t, e);
        });

    ON_CALL(*this, notifyCurrentDependencyChanged)
        .WillByDefault([this](Timestamp t, Engine& e) {
          ElementConst::notifyCurrentDependencyChanged(t, e);
        });

    ON_CALL(*this, notifyIntChanged)
        .WillByDefault([this](Timestamp t, Engine& e, LocalId id) {
          ElementConst::notifyIntChanged(t, e, id);
        });

    ON_CALL(*this, commit).WillByDefault([this](Timestamp t, Engine& e) {
      ElementConst::commit(t, e);
    });
  }

MOCK_METHOD(void, recompute, (Timestamp timestamp, Engine& engine), (override));

MOCK_METHOD(VarId, getNextDependency, (Timestamp, Engine&), (override));
MOCK_METHOD(void, notifyCurrentDependencyChanged, (Timestamp, Engine& e),
            (override));

MOCK_METHOD(void, notifyIntChanged, (Timestamp t, Engine& e, LocalId id),
            (override));
MOCK_METHOD(void, commit, (Timestamp timestamp, Engine& engine), (override));

private:
};

class ElementConstTest : public ::testing::Test {
 protected:
  std::mt19937 gen;

  std::unique_ptr<PropagationEngine> engine;

  virtual void SetUp() {
    std::random_device rd;
    gen = std::mt19937(rd());
    engine = std::make_unique<PropagationEngine>();
  }

  void testNotifications(PropagationEngine::PropagationMode propMode) {
    engine->open();

    std::vector<Int> args{};
    int numArgs = 10;
    for (Int value = 0; value < numArgs; ++value) {
      args.push_back(value);
    }

    VarId idx = engine->makeIntVar(0, 0, numArgs - 1);

    VarId output = engine->makeIntVar(-10, -100, 100);

    auto invariant = engine->makeInvariant<MockElementConst>(
        idx, std::vector<Int>{args}, output);
    
    EXPECT_TRUE(invariant->m_initialized);

    EXPECT_CALL(*invariant, recompute(testing::_, testing::_)).Times(AtLeast(1));

    EXPECT_CALL(*invariant, commit(testing::_, testing::_)).Times(AtLeast(1));

    engine->mode = propMode;

    engine->close();

    if (engine->mode == PropagationEngine::PropagationMode::TOP_DOWN) {
      EXPECT_CALL(*invariant, getNextDependency(testing::_, testing::_)).Times(0);
      EXPECT_CALL(*invariant,
                  notifyCurrentDependencyChanged(testing::_, testing::_))
          .Times(0);
      EXPECT_CALL(*invariant,
                  notifyIntChanged(testing::_, testing::_, testing::_))
          .Times(1);
    } else if (engine->mode == PropagationEngine::PropagationMode::BOTTOM_UP) {
      EXPECT_CALL(*invariant, getNextDependency(testing::_, testing::_)).Times(2);
      EXPECT_CALL(*invariant,
                  notifyCurrentDependencyChanged(testing::_, testing::_))
          .Times(1);

      EXPECT_CALL(*invariant,
                  notifyIntChanged(testing::_, testing::_, testing::_))
          .Times(0);
    } else if (engine->mode == PropagationEngine::PropagationMode::MIXED) {
      EXPECT_EQ(0, 1);  // TODO: define the test case for mixed mode.
    }

    engine->beginMove();
    engine->setValue(idx, 5);
    engine->endMove();

    engine->beginQuery();
    engine->query(output);
    engine->endQuery();
  }
};

TEST_F(ElementConstTest, CreateElement) {
  engine->open();

  std::vector<Int> args{};
  int numArgs = 10;
  for (Int value = 0; value < numArgs; ++value) {
    args.push_back(value);
  }

  VarId idx = engine->makeIntVar(3, 0, numArgs - 1);

  VarId output = engine->makeIntVar(-10, -100, 100);

  auto invariant = engine->makeInvariant<MockElementConst>(
      idx, std::vector<Int>{args}, output);

  EXPECT_TRUE(invariant->m_initialized);

  EXPECT_CALL(*invariant, recompute(testing::_, testing::_)).Times(AtLeast(1));

  EXPECT_CALL(*invariant, commit(testing::_, testing::_)).Times(AtLeast(1));

  engine->close();

  EXPECT_EQ(engine->getNewValue(output), 3);
}

TEST_F(ElementConstTest, NotificationsTopDown) {
  testNotifications(PropagationEngine::PropagationMode::TOP_DOWN);
}

TEST_F(ElementConstTest, NotificationsBottomUp) {
  testNotifications(PropagationEngine::PropagationMode::BOTTOM_UP);
}

}  // namespace