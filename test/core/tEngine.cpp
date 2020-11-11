#include <iostream>
#include <limits>
#include <random>
#include <vector>

#include "core/propagationEngine.hpp"
#include "core/savedInt.hpp"
#include "core/types.hpp"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "invariants/linear.hpp"

using ::testing::AtLeast;
using ::testing::Return;

namespace {

class MockInvariantSimple : public Invariant {
 public:
  bool m_initialized = false;

  MockInvariantSimple() : Invariant(NULL_ID) {}

  void init(Timestamp, Engine&) override { m_initialized = true; }

  MOCK_METHOD(void, recompute, (Timestamp timestamp, Engine& engine),
              (override));

  MOCK_METHOD(VarId, getNextDependency, (Timestamp, Engine&), (override));
  MOCK_METHOD(void, notifyCurrentDependencyChanged, (Timestamp, Engine& e),
              (override));

  MOCK_METHOD(void, notifyIntChanged, (Timestamp t, Engine& e, LocalId id),
              (override));
  MOCK_METHOD(void, commit, (Timestamp timestamp, Engine& engine), (override));
};

class MockInvariantAdvanced : public Invariant {
 public:
  bool m_initialized = false;
  std::vector<VarId> m_inputs;
  VarId m_output;

  MockInvariantAdvanced(std::vector<VarId>&& t_inputs, VarId t_output)
      : Invariant(NULL_ID), m_inputs(std::move(t_inputs)), m_output(t_output) {
    m_modifiedVars.resize(m_inputs.size(), false);
  }

  void init(Timestamp, Engine& e) override {
    assert(m_id != NULL_ID);

    registerDefinedVariable(e, m_output);
    for (size_t i = 0; i < m_inputs.size(); ++i) {
      e.registerInvariantDependsOnVar(m_id, m_inputs[i], LocalId(i));
    }
    m_initialized = true;
  }

  MOCK_METHOD(void, recompute, (Timestamp timestamp, Engine& engine),
              (override));
  MOCK_METHOD(VarId, getNextDependency, (Timestamp, Engine&), (override));
  MOCK_METHOD(void, notifyCurrentDependencyChanged, (Timestamp, Engine& e),
              (override));
  MOCK_METHOD(void, notifyIntChanged, (Timestamp t, Engine& e, LocalId id),
              (override));
  MOCK_METHOD(void, commit, (Timestamp timestamp, Engine& engine), (override));
};

class EngineTest : public ::testing::Test {
 protected:
  std::mt19937 gen;

  std::unique_ptr<PropagationEngine> engine;

  virtual void SetUp() {
    std::random_device rd;
    gen = std::mt19937(rd());
    engine = std::make_unique<PropagationEngine>();
  }
};

TEST_F(EngineTest, CreateVariablesAndInvariant) {
  engine->open();

  size_t intVarCount = 10;
  for (size_t value = 0; value < intVarCount; ++value) {
    engine->makeIntVar(value, Int(-100), Int(100));
  }

  // TODO: use some other invariants...
  auto invariant = engine->makeInvariant<MockInvariantSimple>();

  EXPECT_CALL(*invariant, recompute(testing::_, testing::_)).Times(AtLeast(1));

  EXPECT_CALL(*invariant, commit(testing::_, testing::_)).Times(AtLeast(1));

  ASSERT_TRUE(invariant->m_initialized);

  engine->close();
  EXPECT_EQ(engine->getStore().getNumVariables(), intVarCount);
  EXPECT_EQ(engine->getStore().getNumInvariants(), size_t(1));
}

TEST_F(EngineTest, RecomputeAndCommit) {
  engine->open();

  size_t intVarCount = 10;
  for (size_t value = 0; value < intVarCount; ++value) {
    engine->makeIntVar(value, -100, 100);
  }

  // TODO: use some other invariants...
  auto invariant = engine->makeInvariant<MockInvariantSimple>();

  EXPECT_CALL(*invariant, recompute(testing::_, testing::_)).Times(1);

  EXPECT_CALL(*invariant, commit(testing::_, testing::_)).Times(1);

  ASSERT_TRUE(invariant->m_initialized);

  engine->close();

  ASSERT_EQ(engine->getStore().getNumVariables(), intVarCount);
  ASSERT_EQ(engine->getStore().getNumInvariants(), size_t(1));
}

TEST_F(EngineTest, SimplePropagation) {
  engine->open();

  VarId output = engine->makeIntVar(0, -10, 10);
  VarId a = engine->makeIntVar(1, -10, 10);
  VarId b = engine->makeIntVar(2, -10, 10);
  VarId c = engine->makeIntVar(3, -10, 10);

  auto invariant = engine->makeInvariant<MockInvariantAdvanced>(
      std::vector<VarId>({a, b, c}), output);

  EXPECT_CALL(*invariant, recompute(testing::_, testing::_)).Times(1);

  EXPECT_CALL(*invariant, commit(testing::_, testing::_)).Times(1);

  engine->close();

  engine->beginMove();
  Timestamp moveTimestamp = engine->getCurrentTime();

  engine->setValue(a, -1);
  engine->setValue(b, -2);
  engine->setValue(c, -3);
  engine->endMove();

  if (engine->mode == PropagationEngine::PropagationMode::TOP_DOWN) {
    EXPECT_CALL(*invariant, getNextDependency(moveTimestamp, testing::_))
        .Times(0);

    EXPECT_CALL(*invariant,
                notifyCurrentDependencyChanged(moveTimestamp, testing::_))
        .Times(0);
  } else if (engine->mode == PropagationEngine::PropagationMode::BOTTOM_UP) {
    EXPECT_CALL(*invariant, getNextDependency(moveTimestamp, testing::_))
        .WillOnce(Return(a))
        .WillOnce(Return(b))
        .WillOnce(Return(c))
        .WillRepeatedly(Return(NULL_ID));

    EXPECT_CALL(*invariant,
                notifyCurrentDependencyChanged(moveTimestamp, testing::_))
        .Times(3);
  } else if (engine->mode == PropagationEngine::PropagationMode::MIXED) {
    EXPECT_EQ(0, 1);  // TODO: define the test case for mixed mode.
  }

  engine->beginQuery();
  engine->query(output);
  engine->endQuery();
}

TEST_F(EngineTest, SimpleCommit) {
  engine->open();

  VarId output = engine->makeIntVar(0, -10, 10);
  VarId a = engine->makeIntVar(1, -10, 10);
  VarId b = engine->makeIntVar(2, -10, 10);
  VarId c = engine->makeIntVar(3, -10, 10);

  auto invariant = engine->makeInvariant<MockInvariantAdvanced>(
      std::vector<VarId>({a, b, c}), output);

  engine->close();

  if (engine->mode == PropagationEngine::PropagationMode::TOP_DOWN) {
    EXPECT_CALL(*invariant, getNextDependency(testing::_, testing::_)).Times(0);

    EXPECT_CALL(*invariant,
                notifyCurrentDependencyChanged(testing::_, testing::_))
        .Times(0);
  } else if (engine->mode == PropagationEngine::PropagationMode::BOTTOM_UP) {
    EXPECT_CALL(*invariant, getNextDependency(testing::_, testing::_))
        .WillOnce(Return(a))
        .WillOnce(Return(b))
        .WillOnce(Return(c))
        .WillRepeatedly(Return(NULL_ID));

    EXPECT_CALL(*invariant,
                notifyCurrentDependencyChanged(testing::_, testing::_))
        .Times(3);
  } else if (engine->mode == PropagationEngine::PropagationMode::MIXED) {
    EXPECT_EQ(0, 1);  // TODO: define the test case for mixed mode.
  }

  engine->beginMove();
  engine->setValue(a, -1);
  engine->setValue(b, -2);
  engine->setValue(c, -3);
  engine->endMove();
  engine->beginQuery();
  engine->query(output);
  engine->endQuery();

  if (engine->mode == PropagationEngine::PropagationMode::TOP_DOWN) {
    EXPECT_CALL(*invariant, getNextDependency(testing::_, testing::_)).Times(0);

    EXPECT_CALL(*invariant,
                notifyCurrentDependencyChanged(testing::_, testing::_))
        .Times(0);
  } else if (engine->mode == PropagationEngine::PropagationMode::BOTTOM_UP) {
    EXPECT_CALL(*invariant, getNextDependency(testing::_, testing::_))
        .WillOnce(Return(a))
        .WillOnce(Return(b))
        .WillOnce(Return(c))
        .WillRepeatedly(Return(NULL_ID));

    EXPECT_CALL(*invariant,
                notifyCurrentDependencyChanged(testing::_, testing::_))
        .Times(1);
  } else if (engine->mode == PropagationEngine::PropagationMode::MIXED) {
    EXPECT_EQ(0, 1);  // TODO: define the test case for mixed mode.
  }

  engine->beginMove();
  engine->setValue(a, 0);
  engine->endMove();
  engine->beginCommit();
  engine->query(output);
  engine->endCommit();

  EXPECT_EQ(engine->getCommittedValue(a), 0);
  EXPECT_EQ(engine->getCommittedValue(b), 2);
  EXPECT_EQ(engine->getCommittedValue(c), 3);
}

TEST_F(EngineTest, DelayedCommit) {
  engine->open();

  VarId a = engine->makeIntVar(1, -10, 10);
  VarId b = engine->makeIntVar(1, -10, 10);
  VarId c = engine->makeIntVar(1, -10, 10);
  VarId d = engine->makeIntVar(1, -10, 10);
  VarId e = engine->makeIntVar(1, -10, 10);
  VarId f = engine->makeIntVar(1, -10, 10);
  VarId g = engine->makeIntVar(1, -10, 10);

  engine->makeInvariant<Linear>(std::vector<Int>({1, 1}),
                                std::vector<VarId>({a, b}), c);

  engine->makeInvariant<Linear>(std::vector<Int>({1, 1}),
                                std::vector<VarId>({c, d}), e);

  engine->makeInvariant<Linear>(std::vector<Int>({1, 1}),
                                std::vector<VarId>({c, f}), g);

  engine->close();
  // 1+1 = c = 2
  // c+1 = e = 3
  // c+1 = g = 3
  EXPECT_EQ(engine->getCommittedValue(c), 2);
  EXPECT_EQ(engine->getCommittedValue(e), 3);
  EXPECT_EQ(engine->getCommittedValue(g), 3);

  engine->beginMove();
  engine->setValue(a, 2);
  engine->endMove();

  engine->beginCommit();
  engine->query(e);
  engine->endCommit();

  EXPECT_EQ(engine->getCommittedValue(e), 4);

  engine->beginMove();
  engine->setValue(d, 0);
  engine->endMove();

  engine->beginCommit();
  engine->query(g);
  engine->endCommit();

  EXPECT_EQ(engine->getCommittedValue(g), 4);
}

}  // namespace
