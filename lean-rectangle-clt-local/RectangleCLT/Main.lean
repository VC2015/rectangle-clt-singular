import RectangleCLT.GaussianFourthFinal

/-! The bounded local-covariance rectangle CLT, with a concrete universal
constant. The analytic derivative caps and the master estimate are discharged
by proved theorems; none is a premise of the public CLT below. -/

universe u

namespace RectangleCLT

noncomputable section

/-- An explicit universal constant for the sharp bandwidth estimate. -/
def mainCLTMasterConstant : ℝ :=
  sharpMasterAssemblyConstant (3 * gaussianFourthConstant)

theorem mainCLTMasterConstant_ge_one : 1 ≤ mainCLTMasterConstant :=
  sharpMasterAssemblyConstant_ge_one
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) gaussianFourthConstant_pos.le)

/-- The sharp master estimate for actual rectangle probabilities, proved
without an assumed analytic cap. -/
theorem mainCLTMasterEstimate : LocalMasterEstimate.{u} mainCLTMasterConstant := by
  apply localMasterEstimate_of_gaussianFourthIntegralCap
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) gaussianFourthConstant_pos.le)
  exact gaussianFourthIntegralCap_of_pointwise gaussianFourthConstant_ge_short
    gaussianFourthPointwiseCap

/-- A fixed universal constant, chosen before all data and dimensions. -/
def mainCLTConstant : ℝ := max 1 (13 * mainCLTMasterConstant)

theorem mainCLTConstant_ge_one : 1 ≤ mainCLTConstant := le_max_left _ _

/-- The main bounded rectangle CLT from the updated manuscript. Only the
bounded independent data and intrinsic local covariance hypotheses in
`LocalRectangleCLT` are required; the full covariance may be singular. -/
theorem localRectangleCLT : LocalRectangleCLT.{u} mainCLTConstant :=
  localRectangleCLT_of_master (zero_le_one.trans mainCLTMasterConstant_ge_one)
    mainCLTMasterEstimate

/-- The main CLT with one universal constant for every admissible model. -/
theorem localRectangleCLTExists : LocalRectangleCLTExists.{u} :=
  ⟨mainCLTConstant, mainCLTConstant_ge_one, localRectangleCLT⟩

end
end RectangleCLT
