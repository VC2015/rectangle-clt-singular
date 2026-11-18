import RectangleCLTArxivV1.IntrinsicDerivativeProposition
import RectangleCLTArxivV1.NormalizedObservationsIntrinsic
import RectangleCLTArxivV1.RademacherBoundary
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option pp.all true in
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.theorem_1_intrinsic_clt,
    ``RectangleCLTArxivV1.intrinsicFourthMomentCLT_factor_exists,
    ``RectangleCLTArxivV1.proposition_1_intrinsic_derivatives,
    ``RectangleCLTArxivV1.IntrinsicDerivativePropositionContract,
    ``RectangleCLTArxivV1.initializationDiscrepancy_intrinsic_le,
    ``RectangleCLTArxivV1.corollary_1_normalized_observations,
    ``RectangleCLTArxivV1.normalized_intrinsic_envelope_rate,
    ``RectangleCLTArxivV1.lemma_C1_rademacher_boundary,
    ``RectangleCLTArxivV1.lemma_C1_rademacher_maximum,
    ``RectangleCLT.BoundedIndependentHypotheses,
    ``RectangleCLT.Companion.SplitV4.RelativeMomentBounds,
    ``RectangleCLTArxivV1.IntrinsicFourthBounds]
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
