#include "../nodeTestBase.hpp"
#include "core/propagationEngine.hpp"
#include "invariantgraph/invariants/intDivNode.hpp"

class IntDivNodeTest : public NodeTestBase {
 public:
  std::shared_ptr<fznparser::SearchVariable> a;
  std::shared_ptr<fznparser::SearchVariable> b;
  std::shared_ptr<fznparser::SearchVariable> c;

  std::vector<std::unique_ptr<invariantgraph::VariableNode>> _variables;
  std::unique_ptr<invariantgraph::IntDivNode> node;

  void SetUp() override {
    a = FZN_SEARCH_VARIABLE("a", 0, 10);
    b = FZN_SEARCH_VARIABLE("b", 1, 10);
    c = FZN_SEARCH_VARIABLE("c", 3, 5);

    FZN_DEFINES_VAR_ANNOTATION(annotations, c);
    auto constraint = makeConstraint("int_div", annotations, a, b, c);

    node = invariantgraph::BinaryOpNode::fromModelConstraint<
        invariantgraph::IntDivNode>(constraint, nodeFactory);
  }
};

TEST_F(IntDivNodeTest, construction) {
  EXPECT_EQ(node->a()->variable(), a);
  EXPECT_EQ(node->b()->variable(), b);
  EXPECT_EQ(node->definedVariables().size(), 1);
  EXPECT_EQ(node->definedVariables()[0]->variable(), c);
  expectMarkedAsInput(node.get(), {node->a(), node->b()});
}

TEST_F(IntDivNodeTest, application) {
  PropagationEngine engine;
  engine.open();
  registerVariables(engine, {a, b});
  node->registerWithEngine(engine, _variableMap);
  engine.close();

  EXPECT_EQ(engine.lowerBound(engineVariable(c)), 0);
  EXPECT_EQ(engine.upperBound(engineVariable(c)), 10);

  // a and b
  EXPECT_EQ(engine.searchVariables().size(), 2);

  // a, b and c
  EXPECT_EQ(engine.numVariables(), 3);

  // intDiv
  EXPECT_EQ(engine.numInvariants(), 1);
}