import RectangleCLTCompanion.SplitV4.OrliczFaceTransfer
import Lean.Util.CollectAxioms

/-! Fresh strict audit for the genuine-Orlicz polyhedral branch. -/

#print RectangleCLT.Companion.Psi1IndependentHypotheses
#print RectangleCLT.Companion.psi1Norm
#print RectangleCLT.Companion.psi1Scales
#print RectangleCLT.Companion.SubexponentialIndependentHypotheses

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.exp_projection_le_weighted_exp

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.covariance_mulVec_of_centered_memLp

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.orliczPolyhedralCLT

#print axioms RectangleCLT.Companion.SplitV4.exp_projection_le_weighted_exp
#print axioms RectangleCLT.Companion.SplitV4.projected_exponential_moments
#print axioms RectangleCLT.Companion.SplitV4.covariance_mulVec_of_centered_memLp
#print axioms RectangleCLT.Companion.SplitV4.orliczPolyhedralCLT

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.exp_projection_le_weighted_exp,
    ``RectangleCLT.Companion.SplitV4.projected_exponential_moments,
    ``RectangleCLT.Companion.SplitV4.subexponentialIndependent_projected,
    ``RectangleCLT.Companion.SplitV4.covariance_mulVec_of_centered_memLp,
    ``RectangleCLT.Companion.SplitV4.normalizedObservationSum_mulVec,
    ``RectangleCLT.Companion.SplitV4.subexponential_projected_covariance,
    ``RectangleCLT.Companion.SplitV4.orliczPolyhedralCLT]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in genuine-Orlicz face-transfer closure"
  logInfo "Audited 7 genuine-Orlicz face-transfer declarations, including the actual polyhedral supremum endpoint."
  logInfo "No coordinate independence or covariance nondegeneracy is assumed. The relative and polynomial branches remain separate."
