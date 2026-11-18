import RectangleCLTArxivV1.DerivativesIntrinsic
import RectangleCLTArxivV1.IntrinsicDerivativeProposition
import RectangleCLTArxivV1.NormalizedObservationsIntrinsic
import RectangleCLTArxivV1.RademacherBoundary
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.hasDerivAt_thresholdLogistic,
    ``RectangleCLTArxivV1.hasDerivAt_log_thresholdEnvelope,
    ``RectangleCLTArxivV1.thresholdEnvelope_lower_on_interval,
    ``RectangleCLTArxivV1.thresholdEnvelope_le_common_threshold_difference,
    ``RectangleCLTArxivV1.smallerEnvelope_le_threshold_integral,
    ``RectangleCLTArxivV1.integral_smallerEnvelope_le_of_matching_boundary_printed,
    ``RectangleCLTArxivV1.integral_logisticEnvelope_le_of_layer_bound_printed,
    ``RectangleCLTArxivV1.integral_logisticEnvelope_intrinsic,
    ``RectangleCLTArxivV1.integral_smallerEnvelope_directSlepian_intrinsic]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let ci ← getConstInfo target
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    let ty ← liftTermElabM do
      let fmt ← Meta.ppExpr ci.type
      pure fmt.pretty
    let val ← liftTermElabM do
      if ci.isThm then pure "theorem proof omitted; transitive axioms checked" else
      match ci.value? true with
      | some expr => pure (← Meta.ppExpr expr).pretty
      | none => pure "inductive declaration; fields reviewed in source"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("expanded_type", toJson ty), ("definition", toJson val),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
