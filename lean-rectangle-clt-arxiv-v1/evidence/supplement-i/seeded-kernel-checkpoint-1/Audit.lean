import RectangleCLTArxivV1.SupplementalISeededKernel
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let targets := #[``RectangleCLTArxivV1.cap_parameter_copy_sum_measurable,
    ``RectangleCLTArxivV1.capSeededPairContribution_measurable_theta,
    ``RectangleCLTArxivV1.capSeededSingleContribution_measurable_theta,
    ``RectangleCLTArxivV1.capSeededExceptionalPattern_measurable_theta,
    ``RectangleCLTArxivV1.capSeededSeparatedPattern_measurable_theta,
    ``RectangleCLTArxivV1.cap_intervalIntegrable_measurable_of_Icc_bound,
    ``RectangleCLTArxivV1.capSeededExceptionalPattern_intervalIntegrable_theta,
    ``RectangleCLTArxivV1.capSeededFourthPattern_measurable_theta,
    ``RectangleCLTArxivV1.capSeededFourthPattern_intervalIntegrable_theta,
    ``RectangleCLTArxivV1.capSeededSeparatedPattern_intervalIntegrable_theta,
    ``RectangleCLTArxivV1.capSeededKernelCombination,
    ``RectangleCLTArxivV1.capSeededKernelCombination_add,
    ``RectangleCLTArxivV1.capSeededExceptionalRemainder,
    ``RectangleCLTArxivV1.capSeededSeparatedRemainder,
    ``RectangleCLTArxivV1.cap_seededFourthRemainder_exceptional_split,
    ``RectangleCLTArxivV1.capSeededKernelCombination_abs_le,
    ``RectangleCLTArxivV1.cap_seeded_exceptional_remainder_bound]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array Json := #[]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do throwError "Unexpected axiom {ax} in {target}"
    rows := rows.push (Json.mkObj [("name", toJson target.toString),
      ("transitive_axioms", toJson (axs.toList.map Name.toString))])
  IO.println (Json.mkObj [("targets", Json.arr rows), ("all_axioms_allowed", toJson true)]).compress
