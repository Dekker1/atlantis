#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <random>
#include <vector>

#include "../testHelper.hpp"
#include "constraints/notEqual.hpp"
#include "core/propagationEngine.hpp"
#include "core/types.hpp"

using ::testing::AtLeast;
using ::testing::Return;

namespace {

class NotEqualTest : public InvariantTest {
 public:
  Int computeViolation(Timestamp ts, std::array<VarId, 2> inputs) {
    return computeViolation(engine->value(ts, inputs.at(0)),
                            engine->value(ts, inputs.at(1)));
  }

  Int computeViolation(std::array<Int, 2> inputs) {
    return computeViolation(inputs.at(0), inputs.at(1));
  }

  Int computeViolation(Timestamp ts, const VarId x, const VarId y) {
    return computeViolation(engine->value(ts, x), engine->value(ts, y));
  }

  Int computeViolation(const Int xVal, const Int yVal) {
    return xVal == yVal ? 1 : 0;
  }
};

TEST_F(NotEqualTest, UpdateBounds) {
  std::vector<std::pair<Int, Int>> boundVec{
      {-20, -15}, {-10, -10}, {-5, 0}, {-2, 2}, {0, 5}, {10, 10}, {15, 20}};
  engine->open();
  const VarId x = engine->makeIntVar(
      boundVec.front().first, boundVec.front().first, boundVec.front().second);
  const VarId y = engine->makeIntVar(
      boundVec.front().first, boundVec.front().first, boundVec.front().second);
  const VarId violationId = engine->makeIntVar(0, 0, 2);
  NotEqual& invariant =
      engine->makeConstraint<NotEqual>(*engine, violationId, x, y);
  engine->close();

  for (const auto& [xLb, xUb] : boundVec) {
    EXPECT_TRUE(xLb <= xUb);
    engine->updateBounds(x, xLb, xUb, false);
    for (const auto& [yLb, yUb] : boundVec) {
      EXPECT_TRUE(yLb <= yUb);
      engine->updateBounds(y, yLb, yUb, false);
      invariant.updateBounds();
      std::vector<Int> violations;
      for (Int xVal = xLb; xVal <= xUb; ++xVal) {
        engine->setValue(engine->currentTimestamp(), x, xVal);
        for (Int yVal = yLb; yVal <= yUb; ++yVal) {
          engine->setValue(engine->currentTimestamp(), y, yVal);
          invariant.updateBounds();
          invariant.recompute(engine->currentTimestamp());
          violations.emplace_back(
              engine->value(engine->currentTimestamp(), violationId));
        }
      }
      const auto& [minViol, maxViol] =
          std::minmax_element(violations.begin(), violations.end());
      ASSERT_EQ(*minViol, engine->lowerBound(violationId));
      if (*maxViol != engine->upperBound(violationId)) {
        ASSERT_EQ(*maxViol, engine->upperBound(violationId));
      }
    }
  }
}

TEST_F(NotEqualTest, Recompute) {
  const Int xLb = -1;
  const Int xUb = 0;
  const Int yLb = 0;
  const Int yUb = 1;
  EXPECT_TRUE(xLb <= xUb);
  EXPECT_TRUE(yLb <= yUb);

  engine->open();
  const VarId x = engine->makeIntVar(xUb, xLb, xUb);
  const VarId y = engine->makeIntVar(yUb, yLb, yUb);
  const VarId violationId =
      engine->makeIntVar(0, 0, std::max(xUb - yLb, yUb - xLb));
  NotEqual& invariant =
      engine->makeConstraint<NotEqual>(*engine, violationId, x, y);
  engine->close();

  for (Int xVal = xLb; xVal <= xUb; ++xVal) {
    for (Int yVal = yLb; yVal <= yUb; ++yVal) {
      engine->setValue(engine->currentTimestamp(), x, xVal);
      engine->setValue(engine->currentTimestamp(), y, yVal);

      const Int expectedViolation = computeViolation(xVal, yVal);
      invariant.recompute(engine->currentTimestamp());
      EXPECT_EQ(expectedViolation,
                engine->value(engine->currentTimestamp(), violationId));
    }
  }
}

TEST_F(NotEqualTest, NotifyInputChanged) {
  const Int lb = -50;
  const Int ub = -49;
  EXPECT_TRUE(lb <= ub);

  engine->open();
  std::array<VarId, 2> inputs{engine->makeIntVar(ub, lb, ub),
                              engine->makeIntVar(ub, lb, ub)};
  const VarId violationId = engine->makeIntVar(0, 0, ub - lb);
  NotEqual& invariant = engine->makeConstraint<NotEqual>(
      *engine, violationId, inputs.at(0), inputs.at(1));
  engine->close();

  for (Int val = lb; val <= ub; ++val) {
    for (size_t i = 0; i < inputs.size(); ++i) {
      engine->setValue(engine->currentTimestamp(), inputs.at(i), val);
      const Int expectedViolation =
          computeViolation(engine->currentTimestamp(), inputs);

      invariant.notifyInputChanged(engine->currentTimestamp(), LocalId(i));
      EXPECT_EQ(expectedViolation,
                engine->value(engine->currentTimestamp(), violationId));
    }
  }
}

TEST_F(NotEqualTest, NextInput) {
  const Int lb = 5;
  const Int ub = 10;
  EXPECT_TRUE(lb <= ub);

  engine->open();
  const std::array<VarId, 2> inputs = {engine->makeIntVar(lb, lb, ub),
                                       engine->makeIntVar(ub, lb, ub)};
  const VarId violationId = engine->makeIntVar(0, 0, 2);
  const VarId minVarId = *std::min_element(inputs.begin(), inputs.end());
  const VarId maxVarId = *std::max_element(inputs.begin(), inputs.end());
  NotEqual& invariant = engine->makeConstraint<NotEqual>(
      *engine, violationId, inputs.at(0), inputs.at(1));
  engine->close();

  for (Timestamp ts = engine->currentTimestamp() + 1;
       ts < engine->currentTimestamp() + 4; ++ts) {
    std::vector<bool> notified(maxVarId + 1, false);
    for (size_t i = 0; i < inputs.size(); ++i) {
      const VarId varId = invariant.nextInput(ts);
      EXPECT_NE(varId, NULL_ID);
      EXPECT_TRUE(minVarId <= varId);
      EXPECT_TRUE(varId <= maxVarId);
      EXPECT_FALSE(notified.at(varId));
      notified[varId] = true;
    }
    EXPECT_EQ(invariant.nextInput(ts), NULL_ID);
    for (size_t varId = minVarId; varId <= maxVarId; ++varId) {
      EXPECT_TRUE(notified.at(varId));
    }
  }
}

TEST_F(NotEqualTest, NotifyCurrentInputChanged) {
  const Int lb = -10002;
  const Int ub = -10000;
  EXPECT_TRUE(lb <= ub);

  engine->open();
  std::uniform_int_distribution<Int> valueDist(lb, ub);
  const std::array<VarId, 2> inputs = {
      engine->makeIntVar(valueDist(gen), lb, ub),
      engine->makeIntVar(valueDist(gen), lb, ub)};
  const VarId violationId = engine->makeIntVar(0, 0, ub - lb);
  NotEqual& invariant = engine->makeConstraint<NotEqual>(
      *engine, violationId, inputs.at(0), inputs.at(1));
  engine->close();

  for (Timestamp ts = engine->currentTimestamp() + 1;
       ts < engine->currentTimestamp() + 4; ++ts) {
    for (const VarId varId : inputs) {
      EXPECT_EQ(invariant.nextInput(ts), varId);
      const Int oldVal = engine->value(ts, varId);
      do {
        engine->setValue(ts, varId, valueDist(gen));
      } while (engine->value(ts, varId) == oldVal);
      invariant.notifyCurrentInputChanged(ts);
      EXPECT_EQ(engine->value(ts, violationId), computeViolation(ts, inputs));
    }
  }
}

TEST_F(NotEqualTest, Commit) {
  const Int lb = -10;
  const Int ub = 10;
  EXPECT_TRUE(lb <= ub);

  engine->open();
  std::uniform_int_distribution<Int> valueDist(lb, ub);
  std::array<size_t, 2> indices{0, 1};
  std::array<Int, 2> committedValues{valueDist(gen), valueDist(gen)};
  std::array<VarId, 2> inputs{
      engine->makeIntVar(committedValues.at(0), lb, ub),
      engine->makeIntVar(committedValues.at(1), lb, ub)};
  std::shuffle(indices.begin(), indices.end(), rng);

  const VarId violationId = engine->makeIntVar(0, 0, 2);
  NotEqual& invariant = engine->makeConstraint<NotEqual>(
      *engine, violationId, inputs.at(0), inputs.at(1));
  engine->close();

  EXPECT_EQ(engine->value(engine->currentTimestamp(), violationId),
            computeViolation(engine->currentTimestamp(), inputs));

  for (const size_t i : indices) {
    Timestamp ts = engine->currentTimestamp() + Timestamp(1 + i);
    for (size_t j = 0; j < inputs.size(); ++j) {
      // Check that we do not accidentally commit:
      ASSERT_EQ(engine->committedValue(inputs.at(j)), committedValues.at(j));
    }

    const Int oldVal = committedValues.at(i);
    do {
      engine->setValue(ts, inputs.at(i), valueDist(gen));
    } while (oldVal == engine->value(ts, inputs.at(i)));

    // notify changes
    invariant.notifyInputChanged(ts, LocalId(i));

    // incremental value
    const Int notifiedViolation = engine->value(ts, violationId);
    invariant.recompute(ts);

    ASSERT_EQ(notifiedViolation, engine->value(ts, violationId));

    engine->commitIf(ts, inputs.at(i));
    committedValues.at(i) = engine->value(ts, inputs.at(i));
    engine->commitIf(ts, violationId);

    invariant.commit(ts);
    invariant.recompute(ts + 1);
    ASSERT_EQ(notifiedViolation, engine->value(ts + 1, violationId));
  }
}

class MockNotEqual : public NotEqual {
 public:
  bool registered = false;
  void registerVars() override {
    registered = true;
    NotEqual::registerVars();
  }
  explicit MockNotEqual(Engine& engine, VarId violationId, VarId x, VarId y)
      : NotEqual(engine, violationId, x, y) {
    ON_CALL(*this, recompute).WillByDefault([this](Timestamp timestamp) {
      return NotEqual::recompute(timestamp);
    });
    ON_CALL(*this, nextInput).WillByDefault([this](Timestamp timestamp) {
      return NotEqual::nextInput(timestamp);
    });
    ON_CALL(*this, notifyCurrentInputChanged)
        .WillByDefault([this](Timestamp timestamp) {
          NotEqual::notifyCurrentInputChanged(timestamp);
        });
    ON_CALL(*this, notifyInputChanged)
        .WillByDefault([this](Timestamp timestamp, LocalId id) {
          NotEqual::notifyInputChanged(timestamp, id);
        });
    ON_CALL(*this, commit).WillByDefault([this](Timestamp timestamp) {
      NotEqual::commit(timestamp);
    });
  }
  MOCK_METHOD(void, recompute, (Timestamp), (override));
  MOCK_METHOD(VarId, nextInput, (Timestamp), (override));
  MOCK_METHOD(void, notifyCurrentInputChanged, (Timestamp), (override));
  MOCK_METHOD(void, notifyInputChanged, (Timestamp, LocalId), (override));
  MOCK_METHOD(void, commit, (Timestamp), (override));
};
TEST_F(NotEqualTest, EngineIntegration) {
  for (const auto& [propMode, markingMode] : propMarkModes) {
    if (!engine->isOpen()) {
      engine->open();
    }
    const VarId x = engine->makeIntVar(5, -100, 100);
    const VarId y = engine->makeIntVar(0, -100, 100);
    const VarId viol = engine->makeIntVar(0, 0, 1);
    testNotifications<MockNotEqual>(
        &engine->makeConstraint<MockNotEqual>(*engine, viol, x, y), propMode,
        markingMode, 3, x, 0, viol);
  }
}

}  // namespace
