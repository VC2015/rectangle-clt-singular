import RectangleCLTArxivV1.SupplementalHOuterEntropy

/-! Quantitative outer entropy with a common dimensional scale. The
comparison scale is the tuple count, so the common concentration factor
never occurs inside a logarithm. -/
namespace RectangleCLTArxivV1
open MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem supplementalH_entropy_cardinality_budget
    {M B A L R m : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hL : 1 ≤ L) (hR : 1 ≤ R) (hm : 1 ≤ m) (hlog : Real.log m ≤ L)
    (K : ℕ) (hMass : M ≤ A*R) (hReference : B ≤ A*m^K) :
    M*Real.log (m^K)+B/(m^K)-M ≤ A*((K:ℝ)+1)*L*R := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hpow : 0 < m^K := pow_pos hmpos K
  have hk : 0 ≤ (K:ℝ) := Nat.cast_nonneg K
  have hlog0 : 0 ≤ Real.log m := Real.log_nonneg hm
  have hlogK : 0 ≤ (K:ℝ)*Real.log m := mul_nonneg hk hlog0
  have hprod := mul_le_mul hMass (mul_le_mul_of_nonneg_left hlog hk) hlogK (mul_nonneg hA (zero_le_one.trans hR))
  have hdiv : B/(m^K) ≤ A := (div_le_iff₀ hpow).mpr hReference
  have hLR : 1 ≤ L*R := one_le_mul_of_one_le_of_one_le hL hR
  have hpad : A ≤ A*L*R := by nlinarith [mul_le_mul_of_nonneg_left hLR hA]
  rw [Real.log_pow]
  nlinarith only [hprod,hdiv,hM,hpad]

/-- The actual finite-family entropy estimate used for both the cubic
signed weights and angle-weighted pair weights. `A` may be `C*h*κ` or
`C*h^2*κ/σ`, and `R` may be `sqrt L`. -/
theorem supplementalH_integral_entropy_cardinality_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (p b : ι → Ω → ℝ)
    (hpm : ∀ a, Measurable (p a)) (hbm : ∀ a, Measurable (b a))
    (hp : ∀ a x, 0 ≤ p a x) (hpb : ∀ a x, p a x ≤ b a x)
    (hpi : ∀ a, Integrable (p a) μ) (hbi : ∀ a, Integrable (b a) μ)
    {A L R m : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hm : 1 ≤ m) (hlog : Real.log m ≤ L) (K : ℕ)
    (hMass : (∫ x, ∑ a, p a x ∂μ) ≤ A*R)
    (hReference : (∫ x, ∑ a, b a x ∂μ) ≤ A*m^K) :
    (∫ x, ∑ a, p a x*Real.log (b a x/p a x) ∂μ) ≤ A*((K:ℝ)+1)*L*R := by
  have ht := integral_sum_entropy_le_fixed_scale μ p b hpm hbm hp hpb hpi hbi
    (pow_pos (zero_lt_one.trans_le hm) K)
  exact ht.trans (supplementalH_entropy_cardinality_budget
    (integral_nonneg (fun x => Finset.sum_nonneg (fun a _ => hp a x)))
    hA hL hR hm hlog K hMass hReference)

end
end RectangleCLTArxivV1
