import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenLeading
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets := #[``RectangleCLTArxivV1.nonsimpleNativePairFrame,
    ``RectangleCLTArxivV1.nonsimpleNativePairLevels,
    ``RectangleCLTArxivV1.nonsimpleNativePairPoint,
    ``RectangleCLTArxivV1.nonsimpleNativePairFrame_orthonormal,
    ``RectangleCLTArxivV1.gaussianFrameSectionPoint_nonsimpleNativePair,
    ``RectangleCLTArxivV1.nonsimpleNativePairFrame_span_actualFace,
    ``RectangleCLTArxivV1.nonsimpleNativePairPoint_native,
    ``RectangleCLTArxivV1.nonsimpleNativePairPoint_supporting_levels,
    ``RectangleCLTArxivV1.nonsimpleNativePairPoint_eq_actualFaceNormalPoint,
    ``RectangleCLTArxivV1.nonsimpleNativePair_normalLength_eq_actualFaceNormalPoint_normSq,
    ``RectangleCLTArxivV1.nonsimpleNativePair_mass_eq_actualFaceMass,
    ``RectangleCLTArxivV1.hardGaussianRidgeLeadingTerm_eq_actualFace]
  let env ← getEnv
  let (_, state) := ((targets.forM Lean.CollectAxioms.collect).run env).run {}
  for n in state.axioms do
    unless allowed.contains n do
      throwError "Forbidden axiom {n}"
  logInfo m!"PASS: {targets.size} actual leading-ridge declarations; axioms {state.axioms}"

set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePairFrame
set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePairLevels
set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePairPoint
set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePairFrame_orthonormal
set_option pp.all true in
#print RectangleCLTArxivV1.gaussianFrameSectionPoint_nonsimpleNativePair
set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePairFrame_span_actualFace
set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePairPoint_native
set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePairPoint_supporting_levels
set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePairPoint_eq_actualFaceNormalPoint
set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePair_normalLength_eq_actualFaceNormalPoint_normSq
set_option pp.all true in
#print RectangleCLTArxivV1.nonsimpleNativePair_mass_eq_actualFaceMass
set_option pp.all true in
#print RectangleCLTArxivV1.hardGaussianRidgeLeadingTerm_eq_actualFace
