#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include <rapidcheck/gtest.h>

#include <limits>
#include <vector>

#include "../invariantTestHelper.hpp"
#include "propagation/invariants/exists.hpp"
#include "propagation/solver.hpp"

namespace atlantis::testing {

using namespace atlantis::propagation;

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

  Int computeOutput(const Timestamp ts, const std::vector<VarId>& vars) {
    Int min_val = std::numeric_limits<Int>::max();
    for (auto var : vars) {
      min_val = std::min(min_val, solver->value(ts, var));
    }
    return min_val;
  }

  static Int computeOutput(const std::vector<Int>& values) {
    return *std::min(values.begin(), values.end());
  }
};

TEST_F(ExistsTest, UpdateBounds) {
  std::vector<std::pair<Int, Int>> boundVec{{0, 100}, {150, 250}};
  solver->open();

  std::vector<VarId> vars{solver->makeIntVar(0, 0, 10),
                          solver->makeIntVar(0, 0, 10),
                          solver->makeIntVar(0, 0, 10)};
  const VarId outputId = solver->makeIntVar(0, 0, 2);
  Exists& invariant = solver->makeInvariant<Exists>(*solver, outputId,
                                                    std::vector<VarId>(vars));
  for (const auto& [aLb, aUb] : boundVec) {
    EXPECT_TRUE(aLb <= aUb);
    solver->updateBounds(vars.at(0), aLb, aUb, false);
    for (const auto& [bLb, bUb] : boundVec) {
      EXPECT_TRUE(bLb <= bUb);
      solver->updateBounds(vars.at(1), bLb, bUb, false);
      for (const auto& [cLb, cUb] : boundVec) {
        EXPECT_TRUE(cLb <= cUb);
        solver->updateBounds(vars.at(2), cLb, cUb, false);
        invariant.updateBounds(false);

        ASSERT_EQ(std::min(aLb, std::min(bLb, cLb)),
                  solver->lowerBound(outputId));
        ASSERT_EQ(std::min(aUb, std::min(bUb, cUb)),
                  solver->upperBound(outputId));
      }
    }
  }
}

TEST_F(ExistsTest, Recompute) {
  const Int iLb = 0;
  const Int iUb = 20;

  ASSERT_TRUE(iLb <= iUb);

  std::uniform_int_distribution<Int> iDist(iLb, iUb);

  solver->open();

  const VarId a = solver->makeIntVar(iDist(gen), iLb, iUb);
  const VarId b = solver->makeIntVar(iDist(gen), iLb, iUb);
  const VarId c = solver->makeIntVar(iDist(gen), iLb, iUb);

  inputs = std::vector<VarId>{a, b, c};

  const VarId outputId = solver->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());

  Exists& invariant = solver->makeInvariant<Exists>(*solver, outputId,
                                                    std::vector<VarId>(inputs));
  solver->close();

  for (Int aVal = iLb; aVal <= iUb; ++aVal) {
    for (Int bVal = iLb; bVal <= iUb; ++bVal) {
      for (Int cVal = iLb; cVal <= iUb; ++cVal) {
        solver->setValue(solver->currentTimestamp(), a, aVal);
        solver->setValue(solver->currentTimestamp(), b, bVal);
        solver->setValue(solver->currentTimestamp(), c, cVal);
        const Int expectedOutput =
            computeOutput(solver->currentTimestamp(), inputs);
        invariant.recompute(solver->currentTimestamp());
        EXPECT_EQ(expectedOutput,
                  solver->value(solver->currentTimestamp(), outputId));
      }
    }
  }
}

TEST_F(ExistsTest, NotifyInputChanged) {
  solver->open();
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.at(i) = solver->makeIntVar(inputValueDist(gen), inputLb, inputUb);
  }
  const VarId outputId = solver->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());
  Exists& invariant = solver->makeInvariant<Exists>(*solver, outputId,
                                                    std::vector<VarId>(inputs));
  solver->close();

  for (size_t i = 0; i < inputs.size(); ++i) {
    const Int oldVal = solver->value(solver->currentTimestamp(), inputs.at(i));
    do {
      solver->setValue(solver->currentTimestamp(), inputs.at(i),
                       inputValueDist(gen));
    } while (oldVal == solver->value(solver->currentTimestamp(), inputs.at(i)));

    const Int expectedOutput =
        computeOutput(solver->currentTimestamp(), inputs);

    invariant.notifyInputChanged(solver->currentTimestamp(), LocalId(i));
    EXPECT_EQ(expectedOutput,
              solver->value(solver->currentTimestamp(), outputId));
  }
}

TEST_F(ExistsTest, NextInput) {
  solver->open();
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.at(i) = solver->makeIntVar(inputValueDist(gen), inputLb, inputUb);
  }

  const VarId minVarId = *std::min_element(inputs.begin(), inputs.end());
  const VarId maxVarId = *std::max_element(inputs.begin(), inputs.end());

  std::shuffle(inputs.begin(), inputs.end(), rng);

  const VarId outputId = solver->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());
  Exists& invariant = solver->makeInvariant<Exists>(*solver, outputId,
                                                    std::vector<VarId>(inputs));

  for (Timestamp ts = solver->currentTimestamp() + 1;
       ts < solver->currentTimestamp() + 4; ++ts) {
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
  solver->open();
  for (size_t i = 0; i < numInputs; ++i) {
    inputs.at(i) = solver->makeIntVar(inputValueDist(gen), inputLb, inputUb);
  }
  const VarId outputId = solver->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());
  Exists& invariant = solver->makeInvariant<Exists>(*solver, outputId,
                                                    std::vector<VarId>(inputs));
  solver->close();

  for (Timestamp ts = solver->currentTimestamp() + 1;
       ts < solver->currentTimestamp() + 4; ++ts) {
    for (const VarId& varId : inputs) {
      EXPECT_EQ(invariant.nextInput(ts), varId);
      const Int oldVal = solver->value(ts, varId);
      do {
        solver->setValue(ts, varId, inputValueDist(gen));
      } while (solver->value(ts, varId) == oldVal);
      invariant.notifyCurrentInputChanged(ts);
      EXPECT_EQ(solver->value(ts, outputId), computeOutput(ts, inputs));
    }
  }
}

TEST_F(ExistsTest, Commit) {
  std::vector<size_t> indices(numInputs, 0);
  std::vector<Int> committedValues(numInputs, 0);

  solver->open();
  for (size_t i = 0; i < numInputs; ++i) {
    indices.at(i) = i;
    const Int inputVal = inputValueDist(gen);
    committedValues.at(i) = inputVal;
    inputs.at(i) = solver->makeIntVar(inputVal, inputLb, inputUb);
  }
  std::shuffle(indices.begin(), indices.end(), rng);

  const VarId outputId = solver->makeIntVar(0, std::numeric_limits<Int>::min(),
                                            std::numeric_limits<Int>::max());
  Exists& invariant = solver->makeInvariant<Exists>(*solver, outputId,
                                                    std::vector<VarId>(inputs));
  solver->close();

  EXPECT_EQ(solver->value(solver->currentTimestamp(), outputId),
            computeOutput(solver->currentTimestamp(), inputs));

  for (const size_t i : indices) {
    Timestamp ts = solver->currentTimestamp() + Timestamp(i);
    for (size_t j = 0; j < numInputs; ++j) {
      // Check that we do not accidentally commit:
      ASSERT_EQ(solver->committedValue(inputs.at(j)), committedValues.at(j));
    }

    const Int oldVal = committedValues.at(i);
    do {
      solver->setValue(ts, inputs.at(i), inputValueDist(gen));
    } while (oldVal == solver->value(ts, inputs.at(i)));

    // notify changes
    invariant.notifyInputChanged(ts, LocalId(i));

    // incremental value
    const Int notifiedOutput = solver->value(ts, outputId);
    invariant.recompute(ts);

    ASSERT_EQ(notifiedOutput, solver->value(ts, outputId));

    solver->commitIf(ts, inputs.at(i));
    committedValues.at(i) = solver->value(ts, inputs.at(i));
    solver->commitIf(ts, outputId);

    invariant.commit(ts);
    invariant.recompute(ts + 1);
    ASSERT_EQ(notifiedOutput, solver->value(ts + 1, outputId));
  }
}

RC_GTEST_FIXTURE_PROP(ExistsTest, ShouldAlwaysBeMin,
                      (uint aVal, uint bVal, uint cVal)) {
  solver->open();

  const VarId a = solver->makeIntVar(0, 0, std::numeric_limits<Int>::max());
  const VarId b = solver->makeIntVar(0, 0, std::numeric_limits<Int>::max());
  const VarId c = solver->makeIntVar(0, 0, std::numeric_limits<Int>::max());
  const VarId output =
      solver->makeIntVar(0, 0, std::numeric_limits<Int>::max());
  solver->makeInvariant<Exists>(*solver, output, std::vector<VarId>{a, b, c});
  solver->close();

  solver->beginMove();
  solver->setValue(a, static_cast<Int>(aVal));
  solver->setValue(b, static_cast<Int>(bVal));
  solver->setValue(c, static_cast<Int>(cVal));
  solver->endMove();

  solver->beginCommit();
  solver->query(output);
  solver->endCommit();

  RC_ASSERT(solver->committedValue(output) ==
            std::min<Int>(aVal, std::min<Int>(bVal, cVal)));
}

class MockExists : public Exists {
 public:
  bool registered = false;
  void registerVars() override {
    registered = true;
    Exists::registerVars();
  }
  explicit MockExists(SolverBase& solver, VarId output,
                      std::vector<VarId>&& varArray)
      : Exists(solver, output, std::move(varArray)) {
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
TEST_F(ExistsTest, SolverIntegration) {
  for (const auto& [propMode, markingMode] : propMarkModes) {
    if (!solver->isOpen()) {
      solver->open();
    }
    std::vector<VarId> args;
    const Int numArgs = 10;
    for (Int value = 1; value <= numArgs; ++value) {
      args.push_back(solver->makeIntVar(value, 1, numArgs));
    }
    const VarId modifiedVarId = args.front();
    const VarId output = solver->makeIntVar(-10, -100, numArgs * numArgs);
    testNotifications<MockExists>(
        &solver->makeInvariant<MockExists>(*solver, output, std::move(args)),
        {propMode, markingMode, numArgs + 1, modifiedVarId, 5, output});
  }
}

}  // namespace atlantis::testing