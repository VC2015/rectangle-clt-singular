import RectangleCLTCompanion.SplitV4.SeedCalibration
import Lean.Util.CollectAxioms

/-! Run this file to inspect the exact scalar identities and reject every
transitive axiom outside the handoff's allowlist. This is an audit of scalar
helpers, not a certificate of the full seeded interpolation lemma. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.calibrated_cubic_coefficient

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.seededFourthKernel_eq_integral

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.calibrated_retention_mem_Icc,
    ``RectangleCLT.Companion.SplitV4.calibrated_covariance,
    ``RectangleCLT.Companion.SplitV4.calibrated_third_moment,
    ``RectangleCLT.Companion.SplitV4.calibrated_cubic_coefficient,
    ``RectangleCLT.Companion.SplitV4.signedDensity_mass,
    ``RectangleCLT.Companion.SplitV4.signedDensity_first_moment,
    ``RectangleCLT.Companion.SplitV4.seededFourthKernel_eq_integral,
    ``RectangleCLT.Companion.SplitV4.calibrated_fourth_kernel,
    ``RectangleCLT.Companion.SplitV4.calibrated_cubic_kernel,
    ``RectangleCLT.Companion.SplitV4.calibrated_independent_copy_kernel,
    ``RectangleCLT.Companion.SplitV4.calibrated_signed_hessian_coefficient,
    ``RectangleCLT.Companion.SplitV4.calibrated_cubic_restoration_coefficient,
    ``RectangleCLT.Companion.SplitV4.slepian_fourth_kernel,
    ``RectangleCLT.Companion.SplitV4.calibrated_fourth_kernel_abs_le_one,
    ``RectangleCLT.Companion.SplitV4.calibrated_fourth_kernel_abs_integral_le_one,
    ``RectangleCLT.Companion.SplitV4.signedDensity_can_be_negative]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in seeded scalar helper {name}"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited 16 Appendix B scalar helpers; full seeded path remains separate."
