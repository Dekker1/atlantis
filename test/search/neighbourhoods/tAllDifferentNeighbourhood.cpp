#include <gtest/gtest.h>

#include "search/neighbourhoods/allDifferentNeighbourhood.hpp"

class AllDifferentNeighbourhoodTest : public ::testing::Test {
 public:
  PropagationEngine engine;
  search::Assignment assignment{engine, NULL_ID, NULL_ID};
  search::RandomProvider random{123456789};

  std::vector<VarId> variables;
  std::vector<Int> domain{1, 2, 3, 4};

  void SetUp() override {
    engine.open();
    for (auto i = 0u; i < 4; ++i) {
      variables.push_back(engine.makeIntVar(0, 1, 4));
    }
    engine.close();
  }
};

TEST_F(AllDifferentNeighbourhoodTest, all_values_are_initialised) {
  search::neighbourhoods::AllDifferentNeighbourhood neighbourhood(
      variables, domain, engine);

  assignment.assign(
      [&](auto& modifier) { neighbourhood.initialise(random, modifier); });

  for (const auto& var : variables) {
    EXPECT_TRUE(engine.committedValue(var) >= 1);
    EXPECT_TRUE(engine.committedValue(var) <= 4);
  }
}
