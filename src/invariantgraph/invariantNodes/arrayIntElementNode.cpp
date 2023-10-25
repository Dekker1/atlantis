#include "invariantgraph/invariantNodes/arrayIntElementNode.hpp"

#include "../parseHelper.hpp"

namespace atlantis::invariantgraph {

ArrayIntElementNode::ArrayIntElementNode(std::vector<Int>&& as, VarNodeId b,
                                         VarNodeId output, Int offset)
    : InvariantNode({output}, {b}), _as(std::move(as)), _offset(offset) {}

std::unique_ptr<ArrayIntElementNode> ArrayIntElementNode::fromModelConstraint(
    const fznparser::Constraint& constraint, InvariantGraph& invariantGraph) {
  assert(hasCorrectSignature(acceptedNameNumArgPairs(), constraint));

  const fznparser::IntArg& idx =
      std::get<fznparser::IntArg>(constraint.arguments().at(0));

  std::vector<Int> as =
      std::get<fznparser::IntVarArray>(constraint.arguments().at(1))
          .toParVector();

  const fznparser::IntArg& c =
      std::get<fznparser::IntArg>(constraint.arguments().at(2));

  const Int offset =
      constraint.identifier() != "array_int_element_offset"
          ? 1
          : (idx.isParameter() ? idx.parameter() : idx.var().lowerBound());

  return std::make_unique<ArrayIntElementNode>(
      std::move(as), invariantGraph.createVarNode(idx),
      invariantGraph.createVarNode(c), offset);
}

void ArrayIntElementNode::registerOutputVars(
    InvariantGraph& invariantGraph, propagation::SolverBase& solver) {
  if (invariantGraph.varId(outputVarNodeIds().front()) == propagation::NULL_ID) {
    assert(invariantGraph.varId(b()) != propagation::NULL_ID);
    invariantGraph.varNode(outputVarNodeIds().front())
        .setVarId(solver.makeIntView<propagation::ElementConst>(
            solver, invariantGraph.varId(b()), _as, _offset));
  }
}

void ArrayIntElementNode::registerNode(InvariantGraph&, propagation::SolverBase&) {}

}  // namespace invariantgraph