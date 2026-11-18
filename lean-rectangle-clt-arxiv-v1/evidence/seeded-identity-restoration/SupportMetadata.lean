import RectangleCLTArxivV1.GaussianSeedInterpolationIdentity
import RectangleCLTArxivV1.PairedRestorationIntrinsic
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[
    ``RectangleCLT.Companion.SplitV4.variableSeededInterpolationLaw,
    ``RectangleCLT.Companion.SplitV4.canonicalSignedCubicContraction,
    ``RectangleCLT.Companion.SplitV4.genericManuscriptFourthPathIntegrand,
    ``RectangleCLT.Companion.SplitV4.genericManuscriptFourthCombination,
    ``RectangleCLT.Companion.SplitV4.C4Test.hasDerivAt_genericVariableHeatExpectation,
    ``RectangleCLT.Companion.SplitV4.genericVariableSelectorDerivative_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.genericSelectorOperator_fourth_identity,
    ``RectangleCLT.Companion.SplitV4.genericRow_commonPoint_identity,
    ``RectangleCLT.Companion.SplitV4.genericRowTranslation_identity,
    ``RectangleCLT.Companion.SplitV4.canonicalFourthTensor_pair_slot_equivalence,
    ``RectangleCLT.Companion.SplitV4.canonicalFourthTensor_triple_slot_equivalence,
    ``RectangleCLT.Companion.SplitV4.genericSelectorFourthRemainder_outer_interval,
    ``RectangleCLT.Companion.SplitV4.genericCubicContraction_eq_signedTensor,
    ``RectangleCLT.Companion.SplitV4.restoration_data_gaussian_identDistrib,
    ``RectangleCLT.Companion.SplitV4.restorationThirdExpectation_conditional_transport,
    ``RectangleCLT.Companion.SplitV4.restorationFourthExpectation_conditional_transport,
    ``RectangleCLT.Companion.SplitV4.array_restorationThirdDerivative_stein,
    ``RectangleCLT.Companion.SplitV4.array_restorationFourthDerivative_stein,
    ``RectangleCLT.Companion.SplitV4.translated_score_array_series_interchange,
    ``RectangleCLT.Companion.SplitV4.translated_score_hasSum_expected_orders,
    ``RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_baseline,
    ``RectangleCLT.Companion.SplitV4.conditional_translated_restoration_coefficient_relative_pair,
    ``RectangleCLT.Companion.SplitV4.conditional_translated_order_bound_of_budget,
    ``RectangleCLT.Companion.SplitV4.conditional_translated_score_restoration_of_budget,
    ``RectangleCLT.Companion.SplitV4.restoration_third_relative_signed_of_matrixEstimate,
    ``RectangleCLT.Companion.SplitV4.restoration_fourth_relative_pair_of_matrixEstimate,
    ``RectangleCLT.Companion.SplitV4.selector_nuclear_bound_of_rectangle_concentration,
    ``RectangleCLT.Companion.SplitV4.restoration_paired_baseline_product,
    ``RectangleCLT.Companion.SplitV4.restoration_third_relative_product,
    ``RectangleCLT.Companion.SplitV4.restoration_fourth_relative_product,
    ``RectangleCLT.Companion.F_mul_prod_pi_translation,
    ``RectangleCLT.Companion.hasSum_translationZ_binomial,
    ``RectangleCLT.Companion.translationZ_pow_eq_sum_tuples]
  let mut queue := targets.toList
  let mut seen : Std.HashSet Name := {}
  let mut graph : Array Json := #[]
  let mut endpoints : Array Json := #[]
  while !queue.isEmpty do
    let target := queue.head!
    queue := queue.tail!
    if seen.contains target then
      continue
    seen := seen.insert target
    let ci ← getConstInfo target
    let deps := ci.type.getUsedConstants ++
      (ci.value? true |>.map Expr.getUsedConstants |>.getD #[])
    let deps := deps.toList.eraseDups.toArray
    let projectDeps := deps.filter fun n =>
      let s := n.toString
      s.startsWith "RectangleCLT" || s.startsWith "GenericChaining" ||
        s.startsWith "_private.RectangleCLT" || s.startsWith "_private.GenericChaining"
    graph := graph.push <| Json.mkObj [
      ("name", toJson target.toString),
      ("direct_project_dependencies", toJson (projectDeps.map Name.toString))]
    queue := projectDeps.toList ++ queue
    if targets.contains target then
      let ty ← liftTermElabM do
        let fmt ← Meta.ppExpr ci.type
        pure fmt.pretty
      endpoints := endpoints.push <| Json.mkObj [
        ("name", toJson target.toString), ("expanded_type", toJson ty),
        ("direct_dependencies", toJson (deps.map Name.toString))]
  IO.println <| (Json.mkObj [
    ("scope", toJson "Actual seeded interpolation identity and full intrinsic conditional paired restoration"),
    ("endpoints", Json.arr endpoints), ("project_dependency_graph", Json.arr graph)]).compress
