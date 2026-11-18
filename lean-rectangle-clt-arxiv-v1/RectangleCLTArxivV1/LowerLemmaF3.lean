import RectangleCLTArxivV1.LowerRectangularFamily

/-! The complete actual two-count common construction of Lemma F.3. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem lemma_F_3_raw_covariance (P : SymmetricFamilyParameters) {n r m : ℕ} (i : Fin n) :
    covariance (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P i) =
      lowerFamilyCovariance r m P.variance := by
  ext j k
  rw [covariance,lowerFamilyRawObservations_centered P i j,lowerFamilyRawObservations_centered P i k,
    mul_zero,sub_zero,lowerFamilyRawObservations_second]

theorem lemma_F_3_gaussian_covariance (P : SymmetricFamilyParameters) (r m : ℕ) :
    covariance (lowerGridGaussianLaw r m P.scale (Real.sqrt P.variance)) id =
      lowerFamilyCovariance r m P.variance := by
  rw [covariance_lowerGridGaussianLaw]
  simp only [P.scale_sq,Real.sq_sqrt P.variance_pos.le]
  rfl

theorem lemma_F_3_properties_of_parameters (P : SymmetricFamilyParameters) {n r m : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hm : 2 ≤ m) :
    LowerRectangularFamilyProperties P n r m ∧
    (∀ i : Fin n, covariance (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P i) =
      lowerFamilyCovariance r m P.variance) ∧
    covariance (lowerGridGaussianLaw r m P.scale (Real.sqrt P.variance)) id =
      lowerFamilyCovariance r m P.variance :=
  ⟨lemma_lower_family_properties P hn hr hm,lemma_F_3_raw_covariance P,lemma_F_3_gaussian_covariance P r m⟩

/-- The probability law and all its properties are constructed from the
literal primitive probabilities and amplitude. The only variance premise
is their printed parameter-range requirement. -/
theorem lemma_F_3_common_symmetric_construction {n r m : ℕ} (θ π a : ℝ)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (_hrm : r ≤ m) (hm : 2 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hπ : 0 < π) (hπ1 : π ≤ 1) (ha : 0 < a)
    (hv : θ*π*a^2 < 1/2) :
    ∃ P : SymmetricFamilyParameters,
      P.theta = θ ∧ P.pi = π ∧ P.amplitude = a ∧
      LowerRectangularFamilyProperties P n r m ∧
      (∀ i : Fin n, covariance (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P i) =
        lowerFamilyCovariance r m P.variance) ∧
      covariance (lowerGridGaussianLaw r m P.scale (Real.sqrt P.variance)) id =
        lowerFamilyCovariance r m P.variance := by
  let P : SymmetricFamilyParameters :=
    { theta := θ, pi := π, amplitude := a, theta_pos := hθ, theta_le_one := hθ1,
      pi_pos := hπ, pi_le_one := hπ1, amplitude_pos := ha, variance_lt_half := hv }
  exact ⟨P,rfl,rfl,rfl,lemma_F_3_properties_of_parameters P hn hr hm⟩

end
end RectangleCLTArxivV1
