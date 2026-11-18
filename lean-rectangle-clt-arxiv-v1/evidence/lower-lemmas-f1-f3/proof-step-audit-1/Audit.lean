import RectangleCLTArxivV1.LowerLemmaF1Support
import RectangleCLTArxivV1.LowerLemmaF2
import RectangleCLTArxivV1.LowerLemmaF3
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let targets := #[``RectangleCLT.Companion.SplitV4.moderate_inverse_expansion,
    ``RectangleCLT.Companion.SplitV4.Printed.moderateArrayMean_strictMono_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.existsUnique_moderateArrayMean_eq_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.existsUnique_moderateArrayMean_printed_interval,
    ``RectangleCLT.Companion.SplitV4.Printed.integrable_strict_laplace_weight,
    ``RectangleCLTArxivV1.lowerFamilyNormalizedObservations_unit_covariance,
    ``RectangleCLTArxivV1.lowerFamilyNormalizedObservations_rank,
    ``RectangleCLTArxivV1.lowerFamilyNormalizedObservations_pairGap,
    ``RectangleCLTArxivV1.lowerFamilyGaussianFactor_matches_covariance]
  for target in targets do
    let axs ← Lean.collectAxioms target
    for ax in axs do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {target}"
    logInfo m!"{target} uses {axs.toList}"
