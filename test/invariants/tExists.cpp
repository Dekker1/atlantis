#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <rapidcheck/gtest.h>

#include <limits>
#include <random>
#include <vector>

#include "../testHelper.hpp"
#include "core/propagationEngine.hpp"
#include "core/types.hpp"
#include "invariants/exists.hpp"

using ::testing::AtLeast;
using ::testing::AtMost;
using ::testing::Return;

namespace {

class ExistsTest : public InvariantTest {
 protected:
  const size_t numInputs = 1000;
  Int inputLb = 0;
  Int inputUb = std::numeric_limits<Int>::max();
  std::vector<VarId> inputs;
  std::uniform_int_distribution<Int> inputValueDist;

 public:
  void SetUp() override {
    InvariantTest::SetUp();
    inputs.resize(numInputs, NULL_ID);
    inputValueDist = std::uniform_int_distribution<Int>(inputLb, inputUb);
  }

  void TearDown() override {
    InvariantTest::TearDown();
    inputs.clear();
  }

  Int computeOutput(const Timestamp ts, const std::vector<VarId>& variables) {
    Int min_val = std::numeric_limits<Int>::max();
    for (size_t i = 0; i < variables.size(); ++i) {
      min_val = std::min(min_val, engine->value(ts, variables.at(i)));
    }
    return min_val;
  }

  Int computeOutput(const std::vector<Int>& values) const {
    return *std::min(values.begin(), values.end());
  }
};

TEST_F(ExistsTest, UpdateBounds) {
  std::vector<std::pair<Int, Int>> boundVec{{0, 100}, {150, 250}};
  engine->open();

  std::vector<VarId> vars{engine->makeIntVar(0, 0, 10),
                          engine->makeIntVar(0, 0, 10),
                          engine->makeIntVar(0, 0, 10)};
  const VarId outputId = engine->makeIntVar(0, 0, 2);
  Exists& invariant = engine->makeInvariant<Exists>(*engine, outputId,
                                                    std::vector<VarId>(vars));
  for (const auto& [aLb, aUb] : boundVec) {
    EXPECT_TRUE(aLb <= aUb);
    engine->updateBounds(vars.at(0), aLb, aUb, false);
    for (const auto& [bLb, bUb] : boundVec) {
      EXPECT_TRUE(bLb <= bUb);
      engine->updateBounds(vars.at(1), bLb, bUb, false);
      for (const auto& [cLb, cUb] : boundVec) {
        EXPECT_TRUE(cLb <= cUb);
        engine->updateBounds(vars.at(2), cLb, cUb, false);
        invariant.updateBounds();

        ASSERT_EQ(std::min(aLb, std::min(bLb, cLb)),
                  engine->lowerBound(outputId));
        ASSERT_EQ(std::min(aUb, std::min(bUb, cUb)),
                  engine->upperBound(outputId));
      }
    }
  }
}

TEST_F(ExistsTest, Recompute) {
  const Int iLb = 0;
  const Int iUb = 20;

  ASSERT_TRUE(iLb <= iUb);

  std::uniform_int_distribution<Int> iDist(iLb, iUb);

  engine->open();

  const VarId a = engine->makeIntVar(iDist(gen), iLb, iUb);
  const VarId b = engine->makeIntVar(iDist(gen), iLb, iUb);
  const VarId c = engine->makeIntVar(iDist(gen), iLb, iUb);

  inputs = std::vector<VarId>{a, b, c};

  const VarId outputId = engine->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());

  Exists& invariant = engine->makeInvariant<Exists>(*engine, outputId, inputs);
  engine->close();

  for (Int aVal = iLb; aVal <= iUb; ++aVal) {
    for (Int bVal = iLb; bVal <= iUb; ++bVal) {
      for (Int cVal = iLb; cVal <= iUb; ++cVal) {
        engine->setValue(engine->currentTimestamp(), a, aVal);
        engine->setValue(engine->currentTimestamp(), b, bVal);
        engine->setValue(engine->currentTimestamp(), c, cVal);
        const Int expectedOutput =
            computeOutput(engine->currentTimestamp(), inputs);
        invariant.recompute(engine->currentTimestamp());
        EXPECT_EQ(expectedOutput,
                  engine->value(engine->currentTimestamp(), outputId));
      }
    }
  }
}

TEST_F(ExistsTest, NotifyInputChanged) {
  engine->open();
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.at(i) = engine->makeIntVar(inputValueDist(gen), inputLb, inputUb);
  }
  const VarId outputId = engine->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());
  Exists& invariant = engine->makeInvariant<Exists>(*engine, outputId, inputs);
  engine->close();

  for (size_t i = 0; i < inputs.size(); ++i) {
    const Int oldVal = engine->value(engine->currentTimestamp(), inputs.at(i));
    do {
      engine->setValue(engine->currentTimestamp(), inputs.at(i),
                       inputValueDist(gen));
    } while (oldVal == engine->value(engine->currentTimestamp(), inputs.at(i)));

    const Int expectedOutput =
        computeOutput(engine->currentTimestamp(), inputs);

    invariant.notifyInputChanged(engine->currentTimestamp(), LocalId(i));
    EXPECT_EQ(expectedOutput,
              engine->value(engine->currentTimestamp(), outputId));
  }
}

TEST_F(ExistsTest, NextInput) {
  engine->open();
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.at(i) = engine->makeIntVar(inputValueDist(gen), inputLb, inputUb);
  }

  const VarId minVarId = *std::min_element(inputs.begin(), inputs.end());
  const VarId maxVarId = *std::max_element(inputs.begin(), inputs.end());

  std::shuffle(inputs.begin(), inputs.end(), rng);

  const VarId outputId = engine->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());
  Exists& invariant = engine->makeInvariant<Exists>(*engine, outputId, inputs);

  for (Timestamp ts = engine->currentTimestamp() + 1;
       ts < engine->currentTimestamp() + 4; ++ts) {
    std::vector<bool> notified(maxVarId + 1, false);
    for (size_t i = 0; i < numInputs; ++i) {
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

TEST_F(ExistsTest, NotifyCurrentInputChanged) {
  engine->open();
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.at(i) = engine->makeIntVar(inputValueDist(gen), inputLb, inputUb);
  }
  const VarId outputId = engine->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());
  Exists& invariant = engine->makeInvariant<Exists>(*engine, outputId, inputs);
  engine->close();

  for (Timestamp ts = engine->currentTimestamp() + 1;
       ts < engine->currentTimestamp() + 4; ++ts) {
    for (const VarId varId : inputs) {
      EXPECT_EQ(invariant.nextInput(ts), varId);
      const Int oldVal = engine->value(ts, varId);
      do {
        engine->setValue(ts, varId, inputValueDist(gen));
      } while (engine->value(ts, varId) == oldVal);
      invariant.notifyCurrentInputChanged(ts);
      EXPECT_EQ(engine->value(ts, outputId), computeOutput(ts, inputs));
    }
  }
}

TEST_F(ExistsTest, Commit) {
  std::vector<size_t> indices(numInputs, 0);
  std::vector<Int> committedValues(numInputs, 0);

  engine->open();
  for (size_t i = 0; i < numInputs; ++i) {
    indices.at(i) = i;
    const Int inputVal = inputValueDist(gen);
    committedValues.at(i) = inputVal;
    inputs.at(i) = engine->makeIntVar(inputVal, inputLb, inputUb);
  }
  std::shuffle(indices.begin(), indices.end(), rng);

  const VarId outputId = engine->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());
  Exists& invariant = engine->makeInvariant<Exists>(*engine, outputId, inputs);
  engine->close();

  EXPECT_EQ(engine->value(engine->currentTimestamp(), outputId),
            computeOutput(engine->currentTimestamp(), inputs));

  for (const size_t i : indices) {
    Timestamp ts = engine->currentTimestamp() + Timestamp(i);
    for (size_t j = 0; j < numInputs; ++j) {
      // Check that we do not accidentally commit:
      ASSERT_EQ(engine->committedValue(inputs.at(j)), committedValues.at(j));
    }

    const Int oldVal = committedValues.at(i);
    do {
      engine->setValue(ts, inputs.at(i), inputValueDist(gen));
    } while (oldVal == engine->value(ts, inputs.at(i)));

    // notify changes
    invariant.notifyInputChanged(ts, LocalId(i));

    // incremental value
    const Int notifiedOutput = engine->value(ts, outputId);
    invariant.recompute(ts);

    ASSERT_EQ(notifiedOutput, engine->value(ts, outputId));

    engine->commitIf(ts, inputs.at(i));
    committedValues.at(i) = engine->value(ts, inputs.at(i));
    engine->commitIf(ts, outputId);

    invariant.commit(ts);
    invariant.recompute(ts + 1);
    ASSERT_EQ(notifiedOutput, engine->value(ts + 1, outputId));
  }
}

RC_GTEST_FIXTURE_PROP(ExistsTest, ShouldAlwaysBeMin,
                      (uint aVal, uint bVal, uint cVal)) {
  engine->open();

  const VarId a = engine->makeIntVar(0, 0, std::numeric_limits<Int>::max());
  const VarId b = engine->makeIntVar(0, 0, std::numeric_limits<Int>::max());
  const VarId c = engine->makeIntVar(0, 0, std::numeric_limits<Int>::max());
  const VarId output =
      engine->makeIntVar(0, 0, std::numeric_limits<Int>::max());
  engine->makeInvariant<Exists>(*engine, output, std::vector<VarId>{a, b, c});
  engine->close();

  engine->beginMove();
  engine->setValue(a, static_cast<Int>(aVal));
  engine->setValue(b, static_cast<Int>(bVal));
  engine->setValue(c, static_cast<Int>(cVal));
  engine->endMove();

  engine->beginCommit();
  engine->query(output);
  engine->endCommit();

  RC_ASSERT(engine->committedValue(output) ==
            std::min<Int>(aVal, std::min<Int>(bVal, cVal)));
}

class MockExists : public Exists {
 public:
  bool registered = false;
  void registerVars() override {
    registered = true;
    Exists::registerVars();
  }
  explicit MockExists(Engine& engine, VarId output, std::vector<VarId> varArray)
      : Exists(engine, output, varArray) {
    ON_CALL(*this, recompute).WillByDefault([this](Timestamp timestamp) {
      return Exists::recompute(timestamp);
    });
    ON_CALL(*this, nextInput).WillByDefault([this](Timestamp timestamp) {
      return Exists::nextInput(timestamp);
    });
    ON_CALL(*this, notifyCurrentInputChanged)
        .WillByDefault([this](Timestamp timestamp) {
          Exists::notifyCurrentInputChanged(timestamp);
        });
    ON_CALL(*this, notifyInputChanged)
        .WillByDefault([this](Timestamp timestamp, LocalId id) {
          Exists::notifyInputChanged(timestamp, id);
        });
    ON_CALL(*this, commit).WillByDefault([this](Timestamp timestamp) {
      Exists::commit(timestamp);
    });
  }
  MOCK_METHOD(void, recompute, (Timestamp), (override));
  MOCK_METHOD(VarId, nextInput, (Timestamp), (override));
  MOCK_METHOD(void, notifyCurrentInputChanged, (Timestamp), (override));
  MOCK_METHOD(void, notifyInputChanged, (Timestamp, LocalId), (override));
  MOCK_METHOD(void, commit, (Timestamp), (override));
};
TEST_F(ExistsTest, EngineIntegration) {
  for (const auto& [propMode, markingMode] : propMarkModes) {
    if (!engine->isOpen()) {
      engine->open();
    }
    std::vector<VarId> args;
    const Int numArgs = 10;
    for (Int value = 1; value <= numArgs; ++value) {
      args.push_back(engine->makeIntVar(value, 1, numArgs));
    }
    const VarId modifiedVarId = args.front();
    const VarId output = engine->makeIntVar(-10, -100, numArgs * numArgs);
    testNotifications<MockExists>(
        &engine->makeInvariant<MockExists>(*engine, output, args), propMode,
        markingMode, numArgs + 1, modifiedVarId, 5, output);
  }
}

}  // namespace
