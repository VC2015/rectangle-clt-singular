import RectangleCLTCompanion.SplitV4.GenericC4CubicTensor
import Lean.Util.CollectAxioms

/-! Strict audit of the literal signed K3 tensor and whole generic B.1 endpoint. -/

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.hasDerivAt_integral_genericVariableSeededInterpolationLaw_tensor

#print axioms RectangleCLT.Companion.SplitV4.hasDerivAt_integral_genericVariableSeededInterpolationLaw_tensor

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.canonicalDiagonal_eq_coordinate_sum,
    ``RectangleCLT.Companion.SplitV4.signedCubicTensor,
    ``RectangleCLT.Companion.SplitV4.canonicalSignedCubicContraction,
    ``RectangleCLT.Companion.SplitV4.signedCubicTensor_triple,
    ``RectangleCLT.Companion.SplitV4.genericCubicContraction_eq_signedTensor,
    ``RectangleCLT.Companion.SplitV4.integrable_canonicalSignedCubicContraction_comp,
    ``RectangleCLT.Companion.SplitV4.integrable_canonicalSignedCubicContraction_seededLaw,
    ``RectangleCLT.Companion.SplitV4.hasDerivAt_integral_genericVariableSeededInterpolationLaw_tensor]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in generic B1 signed tensor closure"
  logInfo "Audited 8 GenericC4CubicTensor declarations; only the three standard axioms are permitted."
