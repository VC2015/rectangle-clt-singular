import RectangleCLTArxivV1.SupplementalHLinearGrowth

/-!
# The log-sum inequality with the outer base average

The reference and actual masses are integrated together, before their ratio is
put inside a logarithm. This is the step that preserves a common factor such
as `h * κ` or `h ^ 2 * κ / σ` without introducing its logarithm.
-/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- A scalar supporting-line form of the log-sum inequality, including
zero actual mass. The comparison parameter is fixed before integration. -/
theorem entropy_term_le_reference {p b τ : ℝ} (hp : 0 ≤ p)
    (hpb : p ≤ b) (hτ : 0 < τ) :
    p * Real.log (b / p) ≤ p * Real.log τ + b / τ - p := by
  rcases hp.eq_or_lt with hp | hp
  · subst p
    simpa using div_nonneg hpb hτ.le
  · have hb : 0 < b := hp.trans_le hpb
    have hratio : 0 < b / (p * τ) := div_pos hb (mul_pos hp hτ)
    have hlog := Real.log_le_sub_one_of_pos hratio
    have heq : Real.log (b / (p * τ)) = Real.log (b / p) - Real.log τ := by
      rw [Real.log_div hb.ne' (mul_pos hp hτ).ne',
        Real.log_div hb.ne' hp.ne', Real.log_mul hp.ne' hτ.ne']
      ring
    rw [heq] at hlog
    have hh := mul_le_mul_of_nonneg_left hlog hp.le
    have hcancel : p * (b / (p * τ) - 1) = b / τ - p := by
      field_simp
      <;> ring
    rw [hcancel] at hh
    nlinarith only [hh]

theorem entropy_term_nonneg {p b : ℝ} (hp : 0 ≤ p) (hpb : p ≤ b) :
    0 ≤ p * Real.log (b / p) := by
  rcases hp.eq_or_lt with hp | hp
  · simp [← hp]
  · exact mul_nonneg hp.le (Real.log_nonneg ((le_div_iff₀ hp).mpr (by simpa using hpb)))

/-- Genuine integrability of the entropy term follows from integrability
of the two masses. No entropy-integrability premise is needed later. -/
theorem integrable_entropy_term {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p b : Ω → ℝ) (hpm : Measurable p) (hbm : Measurable b)
    (hp : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ b x)
    (hpi : Integrable p μ) (hbi : Integrable b μ) :
    Integrable (fun x => p x * Real.log (b x / p x)) μ := by
  have hi : Integrable (fun x => p x * Real.log (1 : ℝ) + b x / 1 - p x) μ :=
    ((hpi.mul_const _).add (hbi.div_const _)).sub hpi
  apply hi.mono' ((hpm.mul (hbm.div hpm).log).aestronglyMeasurable)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (entropy_term_nonneg (hp x) (hpb x))]
    exact entropy_term_le_reference (hp x) (hpb x) zero_lt_one)

/-- Multiplying both masses by the same nonnegative angle weight leaves
that weight outside the logarithm, including the zero-angle case. -/
theorem entropy_term_common_factor {c p b : ℝ} (hc : 0 ≤ c) :
    (c*p)*Real.log ((c*b)/(c*p)) = c*(p*Real.log (b/p)) := by
  rcases hc.eq_or_lt with hc | hc
  · simp [← hc]
  · rw [mul_div_mul_left b p hc.ne']
    ring

/-- Fixed-scale outer-averaged log-sum bound. Choosing the comparison
scale before integration also preserves the common concentration factor. -/
theorem integral_sum_entropy_le_fixed_scale
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (p b : ι → Ω → ℝ)
    (hpm : ∀ a, Measurable (p a)) (hbm : ∀ a, Measurable (b a))
    (hp : ∀ a x, 0 ≤ p a x) (hpb : ∀ a x, p a x ≤ b a x)
    (hpi : ∀ a, Integrable (p a) μ) (hbi : ∀ a, Integrable (b a) μ)
    {τ : ℝ} (hτ : 0 < τ) :
    (∫ x, ∑ a, p a x * Real.log (b a x / p a x) ∂μ) ≤
      (∫ x, ∑ a, p a x ∂μ) * Real.log τ +
        (∫ x, ∑ a, b a x ∂μ) / τ - (∫ x, ∑ a, p a x ∂μ) := by
  classical
  have hpSum : Integrable (fun x => ∑ a, p a x) μ :=
    integrable_finset_sum _ (fun a _ => hpi a)
  have hbSum : Integrable (fun x => ∑ a, b a x) μ :=
    integrable_finset_sum _ (fun a _ => hbi a)
  have hiEntropy := integrable_finset_sum Finset.univ
    (fun a _ => integrable_entropy_term μ (p a) (b a) (hpm a) (hbm a) (hp a) (hpb a) (hpi a) (hbi a))
  have hiBound : Integrable (fun x => ∑ a, (p a x * Real.log τ + b a x / τ - p a x)) μ :=
    integrable_finset_sum _ (fun a _ => (((hpi a).mul_const _).add ((hbi a).div_const _)).sub (hpi a))
  have hh := integral_mono hiEntropy hiBound
    (fun x => Finset.sum_le_sum (fun a _ => entropy_term_le_reference (hp a x) (hpb a x) hτ))
  apply hh.trans_eq
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
  calc
    _ = (∫ x, (∑ a, p a x) * Real.log τ + (∑ a, b a x) / τ ∂μ) -
        (∫ x, ∑ a, p a x ∂μ) :=
      integral_sub ((hpSum.mul_const (Real.log τ)).add (hbSum.div_const τ)) hpSum
    _ = _ := by
      rw [integral_add (hpSum.mul_const (Real.log τ)) (hbSum.div_const τ),
        integral_mul_const, integral_div]

/-- The actual outer-averaged log-sum inequality for any finite family.
Both total masses are genuine integrals under the same base law. -/
theorem integral_sum_entropy_le_log_ratio
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (p b : ι → Ω → ℝ)
    (hpm : ∀ a, Measurable (p a)) (hbm : ∀ a, Measurable (b a))
    (hp : ∀ a x, 0 ≤ p a x) (hpb : ∀ a x, p a x ≤ b a x)
    (hpi : ∀ a, Integrable (p a) μ) (hbi : ∀ a, Integrable (b a) μ) :
    (∫ x, ∑ a, p a x * Real.log (b a x / p a x) ∂μ) ≤
      (∫ x, ∑ a, p a x ∂μ) *
        Real.log ((∫ x, ∑ a, b a x ∂μ) / (∫ x, ∑ a, p a x ∂μ)) := by
  classical
  let M := ∫ x, ∑ a, p a x ∂μ
  let B := ∫ x, ∑ a, b a x ∂μ
  have hpSum : Integrable (fun x => ∑ a, p a x) μ := integrable_finset_sum _ (fun a _ => hpi a)
  have hbSum : Integrable (fun x => ∑ a, b a x) μ := integrable_finset_sum _ (fun a _ => hbi a)
  have hMSum (x) : 0 ≤ ∑ a, p a x := Finset.sum_nonneg (fun a _ => hp a x)
  have hM : 0 ≤ M := integral_nonneg hMSum
  have hMB : M ≤ B := integral_mono hpSum hbSum (fun x => Finset.sum_le_sum (fun a _ => hpb a x))
  rcases hM.eq_or_lt with hMz | hM
  · have hzero : ∀ᵐ x ∂μ, ∑ a, p a x = 0 :=
      (integral_eq_zero_iff_of_nonneg hMSum hpSum).mp hMz.symm
    have he : (∫ x, ∑ a, p a x * Real.log (b a x / p a x) ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with x hx
      have hpa (a : ι) : p a x = 0 := by
        have hh : p a x ≤ ∑ a, p a x := Finset.single_le_sum (fun a _ => hp a x) (Finset.mem_univ a)
        exact le_antisymm (by simpa only [hx] using hh) (hp a x)
      change (∑ a, p a x * Real.log (b a x / p a x)) = 0
      simp only [hpa, zero_mul, Finset.sum_const_zero]
    change _ ≤ M * Real.log (B / M)
    rw [← hMz, zero_mul, he]
  · have hB : 0 < B := hM.trans_le hMB
    let τ := B / M
    have hτ : 0 < τ := div_pos hB hM
    have hiEntropy := integrable_finset_sum Finset.univ
      (fun a _ => integrable_entropy_term μ (p a) (b a) (hpm a) (hbm a) (hp a) (hpb a) (hpi a) (hbi a))
    have hiBound : Integrable (fun x => ∑ a, (p a x * Real.log τ + b a x / τ - p a x)) μ :=
      integrable_finset_sum _ (fun a _ => (((hpi a).mul_const _).add ((hbi a).div_const _)).sub (hpi a))
    have hh := integral_mono hiEntropy hiBound
      (fun x => Finset.sum_le_sum (fun a _ => entropy_term_le_reference (hp a x) (hpb a x) hτ))
    have he : (∫ x, ∑ a, (p a x * Real.log τ + b a x / τ - p a x) ∂μ) = M * Real.log τ + B / τ - M := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
      calc
        _ = (∫ x, (∑ a, p a x) * Real.log τ + (∑ a, b a x) / τ ∂μ) -
            (∫ x, ∑ a, p a x ∂μ) :=
          integral_sub ((hpSum.mul_const (Real.log τ)).add (hbSum.div_const τ)) hpSum
        _ = _ := by
          rw [integral_add (hpSum.mul_const (Real.log τ)) (hbSum.div_const τ),
            integral_mul_const, integral_div]

    rw [he] at hh
    have hcancel : B / τ = M := by
      dsimp only [τ]
      field_simp
    change _ ≤ M * Real.log (B / M)
    simpa only [hcancel, add_sub_cancel_right] using hh

end
end RectangleCLTArxivV1
