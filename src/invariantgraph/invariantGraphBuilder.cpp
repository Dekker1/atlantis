#include "invariantgraph/invariantGraphBuilder.hpp"

#include "invariantgraph/constraints/allDifferentNode.hpp"
#include "invariantgraph/constraints/intEqNode.hpp"
#include "invariantgraph/constraints/intLinEqNode.hpp"
#include "invariantgraph/constraints/intLinLeNode.hpp"
#include "invariantgraph/constraints/intLinNeNode.hpp"
#include "invariantgraph/constraints/intNeNode.hpp"
#include "invariantgraph/invariants/arrayIntElementNode.hpp"
#include "invariantgraph/invariants/arrayVarIntElementNode.hpp"
#include "invariantgraph/invariants/binaryOpNode.hpp"
#include "invariantgraph/invariants/intDivNode.hpp"
#include "invariantgraph/invariants/intModNode.hpp"
#include "invariantgraph/invariants/intPowNode.hpp"
#include "invariantgraph/invariants/intTimesNode.hpp"
#include "invariantgraph/invariants/linearNode.hpp"
#include "invariantgraph/invariants/maxNode.hpp"
#include "invariantgraph/invariants/minNode.hpp"
#include "invariantgraph/views/intAbsNode.hpp"
#include "invariantgraph/views/intEqReifNode.hpp"
#include "invariantgraph/views/intLeReifNode.hpp"
#include "invariantgraph/views/intLinEqReifNode.hpp"
#include "invariantgraph/views/intLinLeReifNode.hpp"
#include "invariantgraph/views/intLinNeReifNode.hpp"
#include "invariantgraph/views/intLtReifNode.hpp"
#include "invariantgraph/views/intNeReifNode.hpp"
#include "invariantgraph/invariantGraphRoot.hpp"

std::unique_ptr<invariantgraph::InvariantGraph>
invariantgraph::InvariantGraphBuilder::build(
    const std::unique_ptr<fznparser::Model>& model) {
  _variableMap.clear();
  _variables.clear();
  _definingNodes.clear();

  createNodes(model);

  auto graph = std::make_unique<invariantgraph::InvariantGraph>(
      std::move(_variables), std::move(_definingNodes));
  return graph;
}

void invariantgraph::InvariantGraphBuilder::createNodes(
    const std::unique_ptr<fznparser::Model>& model) {
  for (const auto& variable : model->variables()) {
    if (variable->type() == fznparser::LiteralType::VARIABLE_ARRAY) {
      continue;
    }

    auto variableNode = std::make_unique<VariableNode>(
        std::dynamic_pointer_cast<fznparser::SearchVariable>(variable));

    _variableMap.emplace(variable, variableNode.get());
    _variables.push_back(std::move(variableNode));
  }

  std::unordered_set<VarRef> definedVars;
  std::unordered_set<ConstraintRef> processedConstraints;

  // First, define based on annotations.
  for (const auto& constraint : model->constraints()) {
    if (!constraint->annotations().has<fznparser::DefinesVarAnnotation>()) {
      continue;
    }

    auto ann = constraint->annotations().get<fznparser::DefinesVarAnnotation>();
    if (definedVars.count(ann->defines().lock())) {
      continue;
    }

    if (auto node = makeVariableDefiningNode(constraint)) {
      for (const auto& variableNode : node->definedVariables()) {
        assert(variableNode->variable());
        definedVars.emplace(variableNode->variable());
      }

      _definingNodes.push_back(std::move(node));
      processedConstraints.emplace(constraint);
    }
  }

  // Second, define an implicit constraint (neighborhood) on remaining
  // constraints.
  //  for (const auto& constraint : model->constraints()) {
  //    if (processedConstraints.count(constraint) ||
  //    !canBeImplicit(constraint) ||
  //        !allVariablesFree(constraint, definedVars)) {
  //      continue;
  //    }
  //
  //    auto implicitConstraint = makeImplicitConstraint(constraint);
  //    for (auto variableNode : implicitConstraint->definingVariables()) {
  //      definedVars.emplace(variableNode->variable());
  //    }
  //    _implicitConstraints.push_back(std::move(implicitConstraint));
  //    processedConstraints.emplace(constraint);
  //  }

  // Third, define soft constraints.
  for (const auto& constraint : model->constraints()) {
    if (processedConstraints.count(constraint)) {
      continue;
    }

    _definingNodes.push_back(makeSoftConstraint(constraint));
  }

  // Finally, define all free variables by the InvariantGraphRoot
  std::vector<VariableNode*> freeVariables;
  for (const auto& variableNode : _variables) {
    if (definedVars.count(variableNode->variable()) == 0) {
      freeVariables.push_back(variableNode.get());
    }
  }
  _definingNodes.push_back(std::make_unique<invariantgraph::InvariantGraphRoot>(freeVariables));
}

// bool invariantgraph::InvariantGraphBuilder::canBeImplicit(
//     const ConstraintRef&) {
//   // TODO: Implicit constraints
//   return false;
// }
//
//// ==========================================================================
//// See the example at https://en.cppreference.com/w/cpp/utility/variant/visit
// template <class... Ts>
// struct overloaded : Ts... {
//   using Ts::operator()...;
// };
//// explicit deduction guide (not needed as of C++20)
// template <class... Ts>
// overloaded(Ts...) -> overloaded<Ts...>;
//// ==========================================================================
//
// bool invariantgraph::InvariantGraphBuilder::allVariablesFree(
//    const ConstraintRef& constraint,
//    const std::unordered_set<VarRef>& definedVars) {
//  auto isFree =
//      [&definedVars](const std::shared_ptr<fznparser::Literal>& literal) {
//        if (literal->type() != fznparser::LiteralType::SEARCH_VARIABLE)
//          return false;
//
//        return definedVars.count(
//                   std::dynamic_pointer_cast<fznparser::Variable>(literal)) >
//                   0;
//      };
//
//  for (const auto& arg : constraint->arguments()) {
//    bool free = true;
//    std::visit(
//        overloaded{[&free, &isFree](
//                       const std::shared_ptr<fznparser::Literal>& literal) {
//                     if (!isFree(literal)) free = false;
//                   },
//                   [&free, &isFree](
//                       const std::vector<std::shared_ptr<fznparser::Literal>>&
//                           literals) {
//                     if (!std::all_of(literals.begin(), literals.end(),
//                     isFree))
//                       free = false;
//                   }},
//        arg);
//
//    if (!free) return false;
//  }
//
//  return true;
//}
//
std::unique_ptr<invariantgraph::VariableDefiningNode>
invariantgraph::InvariantGraphBuilder::makeVariableDefiningNode(
    const ConstraintRef& constraint) {
  std::string_view name = constraint->name();

#define NODE_REGISTRATION(nameStr, nodeType)            \
  if (name == nameStr)                                  \
  return invariantgraph::nodeType::fromModelConstraint( \
      constraint, [this](auto var) { return _variableMap.at(var); })

#define BINARY_OP_REGISTRATION(nodeType)                    \
  if (name == invariantgraph::nodeType::constraint_name())  \
  return invariantgraph::BinaryOpNode::fromModelConstraint< \
      invariantgraph::nodeType>(                            \
      constraint, [this](auto var) { return _variableMap.at(var); })

  NODE_REGISTRATION("int_lin_eq", LinearNode);
  NODE_REGISTRATION("int_abs", IntAbsNode);
  NODE_REGISTRATION("array_int_maximum", MaxNode);
  NODE_REGISTRATION("array_int_minimum", MinNode);
  NODE_REGISTRATION("array_int_element", ArrayIntElementNode);
  NODE_REGISTRATION("array_var_int_element", ArrayVarIntElementNode);
  BINARY_OP_REGISTRATION(IntDivNode);
  BINARY_OP_REGISTRATION(IntModNode);
  BINARY_OP_REGISTRATION(IntTimesNode);
  BINARY_OP_REGISTRATION(IntPowNode);
  NODE_REGISTRATION("int_abs", IntAbsNode);
  NODE_REGISTRATION("int_eq_reif", IntEqReifNode);
  NODE_REGISTRATION("int_le_reif", IntLeReifNode);
  NODE_REGISTRATION("int_lin_eq_reif", IntLinEqReifNode);
  NODE_REGISTRATION("int_lin_le_reif", IntLinLeReifNode);
  NODE_REGISTRATION("int_lin_ne_reif", IntLinNeReifNode);
  NODE_REGISTRATION("int_lt_reif", IntLtReifNode);
  NODE_REGISTRATION("int_ne_reif", IntNeReifNode);

  throw std::runtime_error("Unsupported constraint: " + std::string(name));
#undef BINARY_OP_REGISTRATION
#undef NODE_REGISTRATION
}

// std::unique_ptr<invariantgraph::ImplicitConstraintNode>
// invariantgraph::InvariantGraphBuilder::makeImplicitConstraint(
//    const ConstraintRef&) {
//  return std::make_unique<invariantgraph::ImplicitConstraintNode>();
//}
//
std::unique_ptr<invariantgraph::SoftConstraintNode>
invariantgraph::InvariantGraphBuilder::makeSoftConstraint(
    const ConstraintRef& constraint) {
  std::string_view name = constraint->name();

#define NODE_REGISTRATION(nameStr, nodeType)            \
  if (name == nameStr)                                  \
  return invariantgraph::nodeType::fromModelConstraint( \
      constraint, [this](auto var) { return _variableMap.at(var); })

  NODE_REGISTRATION("alldifferent", AllDifferentNode);
  NODE_REGISTRATION("int_lin_le", IntLinLeNode);
  NODE_REGISTRATION("int_lin_eq", IntLinEqNode);
  NODE_REGISTRATION("int_lin_ne", IntLinNeNode);
  NODE_REGISTRATION("int_eq", IntEqNode);
  NODE_REGISTRATION("int_ne", IntNeNode);

  throw std::runtime_error(std::string("Failed to create soft constraint: ")
                               .append(constraint->name()));
#undef NODE_REGISTRATION
}
