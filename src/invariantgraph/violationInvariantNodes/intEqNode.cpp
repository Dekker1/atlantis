#include "invariantgraph/violationInvariantNodes/intEqNode.hpp"

#include "../parseHelper.hpp"

namespace invariantgraph {

IntEqNode::IntEqNode(VarNodeId a, VarNodeId b, VarNodeId r)
    : ViolationInvariantNode({a, b}, r) {}

IntEqNode::IntEqNode(VarNodeId a, VarNodeId b, bool shouldHold)
    : ViolationInvariantNode({a, b}, shouldHold) {}

std::unique_ptr<IntEqNode> IntEqNode::fromModelConstraint(
    const fznparser::Constraint& constraint, InvariantGraph& invariantGraph) {
  assert(hasCorrectSignature(acceptedNameNumArgPairs(), constraint));

  if (constraint.arguments().size() != 2 &&
      constraint.arguments().size() != 3) {
    throw std::runtime_error("IntEq constraint takes two var bool arguments");
  }

  VarNodeId a = invariantGraph.createVarNode(
      std::get<fznparser::IntArg>(constraint.arguments().at(0)));

  VarNodeId b = invariantGraph.createVarNode(
      std::get<fznparser::IntArg>(constraint.arguments().at(1)));

  if (constraint.arguments().size() == 2) {
    return std::make_unique<IntEqNode>(a, b, true);
  }

  const auto& reified = get<fznparser::BoolArg>(constraint.arguments().at(2));
  if (reified.isFixed()) {
    return std::make_unique<IntEqNode>(a, b, reified.toParameter());
  }
  return std::make_unique<IntEqNode>(
      a, b, invariantGraph.createVarNode(reified.var()));
}

void IntEqNode::registerOutputVariables(InvariantGraph& invariantGraph,
                                        Engine& engine) {
  registerViolation(invariantGraph, engine);
}

void IntEqNode::registerNode(InvariantGraph& invariantGraph, Engine& engine) {
  assert(violationVarId(invariantGraph) != NULL_ID);
  assert(invariantGraph.varId(a()) != NULL_ID);
  assert(invariantGraph.varId(b()) != NULL_ID);

  if (shouldHold()) {
    engine.makeConstraint<Equal>(engine, violationVarId(invariantGraph),
                                 invariantGraph.varId(a()),
                                 invariantGraph.varId(b()));
  } else {
    assert(!isReified());
    engine.makeConstraint<NotEqual>(engine, violationVarId(invariantGraph),
                                    invariantGraph.varId(a()),
                                    invariantGraph.varId(b()));
  }
}

}  // namespace invariantgraph