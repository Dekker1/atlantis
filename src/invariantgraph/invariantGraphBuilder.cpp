#include "invariantgraph/invariantGraphBuilder.hpp"

#include <algorithm>

#include "invariantgraph/constraints/allDifferentNode.hpp"
#include "invariantgraph/constraints/leqNode.hpp"
#include "invariantgraph/invariants/linearNode.hpp"
#include "invariantgraph/invariants/maxNode.hpp"

std::unique_ptr<invariantgraph::InvariantGraph>
invariantgraph::InvariantGraphBuilder::build(
    const std::unique_ptr<fznparser::Model>& model) {
  _variableMap.clear();

  createNodes(model);

  auto graph = std::make_unique<invariantgraph::InvariantGraph>(
      std::move(_variables), std::move(_invariants),
      std::move(_softConstraints));
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

    auto invariant = makeInvariant(constraint);
    definedVars.emplace(invariant->output()->variable());
    _invariants.push_back(std::move(invariant));

    processedConstraints.emplace(constraint);
  }

  // Second, define an implicit constraint (neighborhood) on remaining
  // constraints.
  for (const auto& constraint : model->constraints()) {
    if (processedConstraints.count(constraint) || !canBeImplicit(constraint) ||
        !allVariablesFree(constraint, definedVars)) {
      continue;
    }

    auto implicitConstraint = makeImplicitConstraint(constraint);
    for (auto variableNode : implicitConstraint->definingVariables()) {
      definedVars.emplace(variableNode->variable());
    }
    _implicitConstraints.push_back(std::move(implicitConstraint));
    processedConstraints.emplace(constraint);
  }

  // Third, define soft constraints.
  for (const auto& constraint : model->constraints()) {
    if (processedConstraints.count(constraint)) {
      continue;
    }

    _softConstraints.push_back(makeSoftConstraint(constraint));
  }
}

bool invariantgraph::InvariantGraphBuilder::canBeImplicit(
    const ConstraintRef&) {
  // TODO: Implicit constraints
  return false;
}

// ==========================================================================
// See the example at https://en.cppreference.com/w/cpp/utility/variant/visit
template <class... Ts>
struct overloaded : Ts... {
  using Ts::operator()...;
};
// explicit deduction guide (not needed as of C++20)
template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;
// ==========================================================================

bool invariantgraph::InvariantGraphBuilder::allVariablesFree(
    const ConstraintRef& constraint,
    const std::unordered_set<VarRef>& definedVars) {
  auto isFree =
      [&definedVars](const std::shared_ptr<fznparser::Literal>& literal) {
        if (literal->type() != fznparser::LiteralType::SEARCH_VARIABLE)
          return false;

        return definedVars.count(
                   std::dynamic_pointer_cast<fznparser::Variable>(literal)) > 0;
      };

  for (const auto& arg : constraint->arguments()) {
    bool free = true;
    std::visit(
        overloaded{[&free, &isFree](
                       const std::shared_ptr<fznparser::Literal>& literal) {
                     if (!isFree(literal)) free = false;
                   },
                   [&free, &isFree](
                       const std::vector<std::shared_ptr<fznparser::Literal>>&
                           literals) {
                     if (!std::all_of(literals.begin(), literals.end(), isFree))
                       free = false;
                   }},
        arg);

    if (!free) return false;
  }

  return true;
}

std::unique_ptr<invariantgraph::InvariantNode>
invariantgraph::InvariantGraphBuilder::makeInvariant(
    const ConstraintRef& constraint) {
  std::string_view name = constraint->name();
  if (name == "int_lin_eq") {
    return invariantgraph::LinearNode::fromModelConstraint(
        constraint, [this](auto var) { return _variableMap.at(var); });
  } else if (name == "int_max" || name == "array_int_maximum") {
    return invariantgraph::MaxNode::fromModelConstraint(
        constraint, [this](auto var) { return _variableMap.at(var); });
  }

  throw std::runtime_error("Unsupported constraint: " + std::string(name));
}

std::unique_ptr<invariantgraph::ImplicitConstraintNode>
invariantgraph::InvariantGraphBuilder::makeImplicitConstraint(
    const ConstraintRef&) {
  return std::make_unique<invariantgraph::ImplicitConstraintNode>();
}

std::unique_ptr<invariantgraph::SoftConstraintNode>
invariantgraph::InvariantGraphBuilder::makeSoftConstraint(
    const ConstraintRef& constraint) {
  std::string_view name = constraint->name();

  if (name == "alldifferent") {
    return invariantgraph::AllDifferentNode::fromModelConstraint(
        constraint, [this](auto var) { return _variableMap.at(var); });
  }

  if (name == "int_lin_le") {
    return invariantgraph::LeqNode::fromModelConstraint(
        constraint, [this](auto var) { return _variableMap.at(var); });
  }

  throw std::runtime_error(std::string("Failed to create soft constraint: ")
                               .append(constraint->name()));
}