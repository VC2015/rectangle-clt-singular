import RectangleCLTArxivV1.GaussianSeedInterpolationIdentity
import RectangleCLTArxivV1.PairedRestorationIntrinsic
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[
    ``RectangleCLTArxivV1.seededInterpolationThirdMultiplier_hasDerivAt,
    ``RectangleCLTArxivV1.seededInterpolation_covariance_calibration,
    ``RectangleCLTArxivV1.seededInterpolation_third_calibration,
    ``RectangleCLTArxivV1.seededInterpolationFourthCombination_eq,
    ``RectangleCLTArxivV1.seededInterpolationFourthPath_eq,
    ``RectangleCLTArxivV1.lemma_B1_gaussian_seed_interpolation,
    ``RectangleCLTArxivV1.IntrinsicPairedRestorationConclusion,
    ``RectangleCLTArxivV1.IntrinsicPairedRestorationContract,
    ``RectangleCLTArxivV1.paired_restoration_contract_intrinsic,
    ``RectangleCLTArxivV1.lemma_B2_intrinsic_paired_restoration]
  for target in targets do
    let axioms ← Lean.collectAxioms target
    for a in axioms do
      unless allowed.contains a do
        throwError "Unexpected axiom {a} in {target}"
    logInfo m!"{target}: {axioms.toList}"
