#include "invariantgraph/violationInvariantNodes/arrayBoolAndNode.hpp"

#include "../parseHelper.hpp"

namespace atlantis::invariantgraph {

ArrayBoolAndNode::ArrayBoolAndNode(std::vector<VarNodeId>&& as,
                                   VarNodeId output)
    : ViolationInvariantNode(std::move(as), output) {}

ArrayBoolAndNode::ArrayBoolAndNode(std::vector<VarNodeId>&& as, bool shouldHold)
    : ViolationInvariantNode(std::move(as), shouldHold) {}

std::unique_ptr<ArrayBoolAndNode> ArrayBoolAndNode::fromModelConstraint(
    const fznparser::Constraint& constraint, InvariantGraph& invariantGraph) {
  assert(hasCorrectSignature(acceptedNameNumArgPairs(), constraint));
  if (constraint.arguments().size() != 2) {
    throw std::runtime_error("ArrayBoolAnd constraint takes two arguments");
  }
  if (!std::holds_alternative<fznparser::BoolVarArray>(
          constraint.arguments().front())) {
    throw std::runtime_error(
        "ArrayBoolAnd constraint first argument must be an bool var array");
  }
  if (!std::holds_alternative<fznparser::BoolArg>(
          constraint.arguments().back())) {
    throw std::runtime_error(
        "ArrayBoolAnd constraint optional second argument must be a bool "
        "var");
  }
  const auto& boolVarArray =
      get<fznparser::BoolVarArray>(constraint.arguments().front());

  if (boolVarArray.size() == 0 || boolVarArray.isParArray()) {
    return nullptr;
  }

  std::vector<VarNodeId> varNodeIds =
      invariantGraph.createVarNodes(boolVarArray);

  const fznparser::BoolArg& reified =
      get<fznparser::BoolArg>(constraint.arguments().back());
  if (reified.isFixed()) {
    return std::make_unique<invariantgraph::ArrayBoolAndNode>(
        std::move(varNodeIds), reified.toParameter());
  }
  return std::make_unique<invariantgraph::ArrayBoolAndNode>(
      std::move(varNodeIds), invariantGraph.createVarNode(reified.var()));
}

void ArrayBoolAndNode::registerOutputVars(InvariantGraph& invariantGraph,
                                          propagation::SolverBase& solver) {
  if (violationVarId(invariantGraph) == propagation::NULL_ID) {
    if (shouldHold()) {
      registerViolation(invariantGraph, solver);
    } else {
      assert(!isReified());
      _intermediate = solver.makeIntVar(0, 0, 0);
      setViolationVarId(invariantGraph,
                        solver.makeIntView<propagation::NotEqualConst>(
                            solver, _intermediate, 0));
    }
  }
}

void ArrayBoolAndNode::registerNode(InvariantGraph& invariantGraph,
                                    propagation::SolverBase& solver) {
  assert(violationVarId(invariantGraph) != propagation::NULL_ID);
  std::vector<propagation::VarId> inputs;
  std::transform(staticInputVarNodeIds().begin(), staticInputVarNodeIds().end(),
                 std::back_inserter(inputs),
                 [&](const auto& node) { return invariantGraph.varId(node); });

  solver.makeInvariant<propagation::ForAll>(
      solver, !shouldHold() ? _intermediate : violationVarId(invariantGraph),
      inputs);
}

}  // namespace atlantis::invariantgraph