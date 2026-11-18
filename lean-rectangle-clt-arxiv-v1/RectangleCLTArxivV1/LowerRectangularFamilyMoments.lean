import RectangleCLTArxivV1.LowerRectangularFamilyFinite

/-! Exact centered moments of the actual two-count observations. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

theorem integral_lowerFamilyObservation (P : SymmetricFamilyParameters) {r m : ℕ} (k : Fin (r * m)) :
    (∫ z, lowerFamilyObservation P z k ∂lowerFamilySeedLaw P r m) = 0 := by
  rw [lowerFamilySeedLaw, integral_prod_symm _ (integrable_family_finite _ _)]
  change (∫ y, (∫ z : FamilySigns r,
      P.scale * familySign (z (finProdFinEquiv.symm k).1) +
        familyActivated P y (finProdFinEquiv.symm k).2 ∂familySignLaw r) ∂familyRestLaw P m) = 0
  simp_rw [integral_familySignLaw_affine]
  exact integral_familyActivated P _

theorem integral_lowerFamilyObservation_product (P : SymmetricFamilyParameters) {r m : ℕ}
    (k l : Fin (r * m)) :
    (∫ z, lowerFamilyObservation P z k * lowerFamilyObservation P z l ∂lowerFamilySeedLaw P r m) =
      lowerFamilyCovariance r m P.variance k l := by
  classical
  rw [lowerFamilySeedLaw, integral_prod_symm _ (integrable_family_finite _ _)]
  change (∫ y, (∫ z : FamilySigns r,
      (P.scale * familySign (z (finProdFinEquiv.symm k).1) +
        familyActivated P y (finProdFinEquiv.symm k).2) *
      (P.scale * familySign (z (finProdFinEquiv.symm l).1) +
        familyActivated P y (finProdFinEquiv.symm l).2) ∂familySignLaw r) ∂familyRestLaw P m) = _
  simp_rw [integral_familySignLaw_affine_product]
  rw [integral_family_finite_add, integral_const, measureReal_univ_eq_one, one_smul,
    integral_familyActivated_product, P.scale_sq]
  rfl

theorem integral_lowerFamilyObservation_fourth (P : SymmetricFamilyParameters) {r m : ℕ}
    (k : Fin (r * m)) :
    (∫ z, lowerFamilyObservation P z k ^ 4 ∂lowerFamilySeedLaw P r m) =
      1 + 4 * P.variance - 5 * P.variance ^ 2 + P.theta * P.pi * P.amplitude ^ 4 := by
  rw [lowerFamilySeedLaw, integral_prod_symm _ (integrable_family_finite _ _)]
  change (∫ y, (∫ z : FamilySigns r,
      (P.scale * familySign (z (finProdFinEquiv.symm k).1) +
        familyActivated P y (finProdFinEquiv.symm k).2) ^ 4 ∂familySignLaw r) ∂familyRestLaw P m) = _
  simp_rw [integral_familySignLaw_affine_fourth]
  simp only [integral_family_finite_add, integral_const_mul, integral_familyActivated_sq,
    integral_familyActivated_fourth, integral_const, measureReal_univ_eq_one, one_smul]
  have hs := P.scale_sq
  nlinarith [sq_nonneg (P.scale ^ 2 - (1 - P.variance))]

end
end RectangleCLTArxivV1
