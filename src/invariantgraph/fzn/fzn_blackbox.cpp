#include <memory>

#include "./fznHelper.hpp"
#include "atlantis/invariantgraph/invariantNodes/blackboxNode.hpp"
#include "atlantis/misc/blackboxFunction.hpp"
#include "fznparser/annotation.hpp"
#include "fznparser/variables.hpp"

namespace atlantis::invariantgraph::fzn {

bool fzn_blackbox(FznInvariantGraph& graph,
                  std::unique_ptr<blackbox::BlackBoxFn>&& blackboxFn,
                  const std::shared_ptr<fznparser::IntVarArray>& int_in,
                  const std::shared_ptr<fznparser::FloatVarArray>& float_in,
                  const std::shared_ptr<fznparser::IntVarArray>& int_out,
                  const std::shared_ptr<fznparser::FloatVarArray>& float_out) {
  if (float_in->size() > 0 || float_out->size()) {
    throw FznArgumentException(
        "Blackbox constraint uses floating point variables, but this is "
        "not yet supported");
  }

  graph.addInvariantNode(std::make_unique<BlackBoxNode>(
      graph,
      std::move(blackboxFn),
      graph.retrieveVarNodes(int_in),
      graph.retrieveVarNodes(int_out)
  ));
  return true;
}

bool fzn_blackbox(FznInvariantGraph& graph,
                  const fznparser::Constraint& constraint) {
  if (constraint.identifier() != "fzn_blackbox") {
    return false;
  }

  FZN_CONSTRAINT_ARRAY_TYPE_CHECK(constraint, 0, fznparser::IntVarArray, true)
  FZN_CONSTRAINT_ARRAY_TYPE_CHECK(constraint, 1, fznparser::FloatVarArray, true)
  FZN_CONSTRAINT_ARRAY_TYPE_CHECK(constraint, 2, fznparser::IntVarArray, true)
  FZN_CONSTRAINT_ARRAY_TYPE_CHECK(constraint, 3, fznparser::FloatVarArray, true)

  const fznparser::Annotation* methodAnn = nullptr;
  for (auto& ann : constraint.annotations()) {
    if (ann.identifier() == "blackbox_dll") {
      FZN_ANN_TYPE_CHECK(ann, 0, std::string, false);
      methodAnn = &ann;
      break;
    } else if (ann.identifier() == "blackbox_exec") {
      FZN_ANN_TYPE_CHECK(ann, 0, std::string, false);
      methodAnn = &ann;
    }
  }
  if (methodAnn == nullptr) {
    throw FznArgumentException(
        "Constraint " + constraint.identifier() +
        " does not contain a execution method annotation.");
  }
  std::unique_ptr<blackbox::BlackBoxFn> blackboxFn =
      blackbox::BlackBoxFn::from_annotation(*methodAnn);

  return fzn_blackbox(
      graph, std::move(blackboxFn),
      getArgArray<fznparser::IntVarArray>(constraint.arguments().at(0)),
      getArgArray<fznparser::FloatVarArray>(constraint.arguments().at(1)),
      getArgArray<fznparser::IntVarArray>(constraint.arguments().at(2)),
      getArgArray<fznparser::FloatVarArray>(constraint.arguments().at(3)));
}

}  // namespace atlantis::invariantgraph::fzn
