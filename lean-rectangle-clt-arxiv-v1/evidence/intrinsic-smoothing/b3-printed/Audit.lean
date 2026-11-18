import RectangleCLTArxivV1.SmoothingGaussianMean

#print axioms RectangleCLTArxivV1.gaussian_mean_relative_to_single_face
#check RectangleCLTArxivV1.gaussian_mean_relative_to_single_face

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some ci := env.find? ``RectangleCLTArxivV1.gaussian_mean_relative_to_single_face
    | throwError "B.3 endpoint missing"
  let some body := ci.value? true | throwError "B.3 endpoint has no proof"
  let used := body.getUsedConstants
  for required in #[``RectangleCLT.Companion.weighted_exp_mean_le,
      ``RectangleCLT.Companion.SplitV4.Printed.gaussian_one_face_exponential_via_independence,
      ``RectangleCLT.Companion.tangentMean_orthogonal,
      ``RectangleCLT.Companion.tangentMean_dot_mean,
      ``RectangleCLT.Companion.tangentMean_normSq,
      ``RectangleCLT.Companion.weighted_mean_sq_le_second] do
    unless used.contains required do
      throwError "Missing printed B.3 proof dependency {required}"
  if used.contains ``RectangleCLT.Companion.gaussian_mean_relative_to_one_face then
    throwError "B.3 proof bypassed its explicit printed assembly"
  logInfo "PASS: B.3 Jensen, orthogonal independence factorization, tangent decomposition and Cauchy--Schwarz are actual direct proof dependencies."
