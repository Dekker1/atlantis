#include <gtest/gtest.h>

#include "constraints/equal.hpp"
#include "core/propagationEngine.hpp"
#include "invariants/linear.hpp"
#include "search/assignment.hpp"

class AssignmentTest : public testing::Test {
 public:
  VarId a;
  VarId b;
  VarId c;
  VarId d;

  VarId violation;

  PropagationEngine engine;

  // Models the following simple COP:
  // c <- a + b (a and b have domain 0..10)
  // violation = v(c == 3)
  // obj: minimise(a)
  void SetUp() override {
    engine.open();
    a = engine.makeIntVar(0, 0, 10);
    b = engine.makeIntVar(0, 0, 10);
    c = engine.makeIntVar(0, 0, 10);
    d = engine.makeIntVar(3, 3, 3);
    violation = engine.makeIntVar(0, 0, 10);

    engine.makeInvariant<Linear>(std::vector<VarId>{a, b}, c);
    engine.makeConstraint<Equal>(violation, c, d);
    engine.close();
  }
};

TEST_F(AssignmentTest, search_variables_are_identified) {
  search::Assignment assignment{engine, violation, a};

  std::vector<VarId> expectedSearchVariables{a, b};
  EXPECT_EQ(assignment.searchVariables(), expectedSearchVariables);
}

TEST_F(AssignmentTest, cost) {
  search::Assignment assignment{engine, violation, a};

  EXPECT_FALSE(assignment.cost().satisfiesConstraints());

  // c has value 0, which is 3 away from 3.
  EXPECT_EQ(assignment.cost().evaluate(1, 1), 3);

  assignment.assign([&](auto& modifications) {
    modifications.set(a, 2);
    modifications.set(b, 1);
  });

  EXPECT_TRUE(assignment.cost().satisfiesConstraints());

  // no violation and a (the objective) has value 2.
  EXPECT_EQ(assignment.cost().evaluate(1, 1), 2);
}

TEST_F(AssignmentTest, assign_sets_values) {
  search::Assignment assignment{engine, violation, a};

  assignment.assign([&](auto& modifications) {
    modifications.set(a, 1);
    modifications.set(b, 2);
  });

  EXPECT_EQ(assignment.value(a), 1);
  EXPECT_EQ(assignment.value(b), 2);
}

TEST_F(AssignmentTest, probe) {
  search::Assignment assignment{engine, violation, a};

  auto cost = assignment.probe([&](auto& modifications) {
    modifications.set(a, 1);
    modifications.set(b, 2);
  });

  EXPECT_FALSE(assignment.cost().satisfiesConstraints());
  EXPECT_EQ(assignment.cost().evaluate(1, 1), 3);

  EXPECT_TRUE(cost.satisfiesConstraints());
  EXPECT_EQ(cost.evaluate(1, 1), 1);
}

TEST_F(AssignmentTest, satisfies_constraints) {
  search::Assignment assignment{engine, violation, a};

  EXPECT_FALSE(assignment.satisfiesConstraints());

  assignment.assign([&](auto& modifications) {
    modifications.set(a, 1);
    modifications.set(b, 2);
  });

  EXPECT_TRUE(assignment.satisfiesConstraints());
}