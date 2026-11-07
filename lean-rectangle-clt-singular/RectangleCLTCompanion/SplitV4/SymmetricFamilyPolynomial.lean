import RectangleCLTCompanion.SplitV4.SymmetricFamilyCertification
import RectangleCLTCompanion.SplitV4.PolynomialUniform

/-! Literal polynomial class membership for the genuine masked common family.
Only numerical inequalities on its explicit parameters enter the moment bounds. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem familyRawObservations_envelope_moment_le (P : SymmetricFamilyParameters)
    {n m : ℕ} (i : Fin n) {q B : ℝ} (hq : 1 ≤ q)
    (hB : P.scale + P.amplitude * P.theta^(1/q) ≤ B) :
    (∫ z, ‖familyRawObservations P i z‖^q ∂familyArrayLaw P n m) ≤ B^q := by
  have hroot := (familyRawObservations_Lq_envelope P (m := m) i hq).trans hB
  have hI : 0 ≤ ∫ z, ‖familyRawObservations P i z‖^q ∂familyArrayLaw P n m :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hI (1/q)) hroot (by linarith : 0 ≤ q)
  rw [← Real.rpow_mul hI, one_div_mul_cancel (by linarith : q ≠ 0), Real.rpow_one] at hh
  exact hh

theorem symmetricFamily_polynomialIndependent (P : SymmetricFamilyParameters)
    {n m : ℕ} (hn : 1 ≤ n) {q B : ℝ} (hq : 1 ≤ q)
    (hEnvelope : P.scale + P.amplitude * P.theta^(1/q) ≤ B)
    (hFourth : 1+4*P.variance-5*P.variance^2+P.theta*P.pi*P.amplitude^4 ≤ B^2) :
    PolynomialIndependentHypotheses (familyArrayLaw P n m) (familyRawObservations P) q B := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  refine ⟨fun _ => measurable_of_finite _, familyRawObservations_independent P n m,
    familyRawObservations_centered P, fun _ => integrable_family_finite _ _,
    fun _ _ => integrable_family_finite _ _, ?_, fun i => familyRawObservations_envelope_moment_le P i hq hEnvelope, ?_⟩
  · intro j
    simp_rw [pow_two, familyRawObservations_second, familyCovariance_unit_diagonal]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    simpa only [one_div] using inv_mul_cancel₀ hN
  · intro j
    simp_rw [familyRawObservations_fourth]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, one_div, inv_mul_cancel₀ hN, one_mul]
    exact hFourth

end
end RectangleCLT.Companion.SplitV4
