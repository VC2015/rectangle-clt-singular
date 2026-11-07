import RectangleCLTCompanion.SplitV4.BennettMaximum
import RectangleCLTCompanion.SplitV4.EnvelopeTruncation

/-!
The expected maximum in Appendix E (Lemma E.1).  The bounded part uses the
actual Bennett exponential moments at a small positive Laplace parameter;
the envelope moment controls the centered omitted sum.  Genuine moment
integrability is part of the public probability contract.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def envelopeMaximumConstant : ℝ := 4 + 2 * Real.exp 1

theorem one_le_envelopeMaximumConstant : 1 ≤ envelopeMaximumConstant := by
  unfold envelopeMaximumConstant
  linarith [Real.exp_pos 1]

theorem bennettKernel_le_exp_one {a : ℝ} (ha : a ≤ 1) :
    bennettKernel a ≤ Real.exp 1 := by
  have hc : IntervalIntegrable (fun _ : ℝ => Real.exp 1) volume (0 : ℝ) 1 :=
    intervalIntegrable_const
  have hb := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (bennettKernel_integrable a) hc (fun r hr => ?_)
  · simpa [bennettKernel] using hb
  · have hra : r * a ≤ 1 := by
      exact (mul_le_mul_of_nonneg_left ha hr.1).trans (by simpa using hr.2)
    calc
      (1 - r) * Real.exp (r * a) ≤ 1 * Real.exp 1 :=
        mul_le_mul (by linarith [hr.1]) (Real.exp_le_exp.mpr hra)
          (Real.exp_nonneg _) (by norm_num)
      _ = _ := one_mul _

theorem bennettCorrection_le_exp_one_mul_sq {a : ℝ} (ha : a ≤ 1) :
    bennettCorrection a ≤ Real.exp 1 * a ^ 2 := by
  rw [bennettCorrection_eq_sq_mul_kernel]
  exact (mul_le_mul_of_nonneg_left (bennettKernel_le_exp_one ha) (sq_nonneg a)).trans_eq
    (mul_comm _ _)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A true Bernstein maximum consequence of the checked Bennett MGF.
The right side uses the full covariance variance budget, without rank or
coordinate independence assumptions. -/
theorem bounded_vector_bernstein_maximum {p n : ℕ}
    {T : Fin n → Ω → Vector p} {U v : ℝ}
    (h : BoundedIndependentHypotheses μ T U) (hp : 1 ≤ p)
    (hU : 0 < U) (hv : 0 ≤ v)
    (hvariance : ∀ j, (∑ i, ∫ ω, T i ω j ^ 2 ∂μ) ≤ v) :
    (∫ ω, ‖sumVector T ω‖ ∂μ) ≤
      (1 + Real.exp 1) * (Real.sqrt (v * dimensionLog p) + U * dimensionLog p) := by
  let L := dimensionLog p
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  let r := Real.sqrt (v / L)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  let D := U + r
  have hD : 0 < D := by dsimp [D]; linarith
  let t := 1 / D
  have ht : 0 < t := one_div_pos.mpr hD
  have htU : t * U ≤ 1 := by
    dsimp [t]
    rw [one_div_mul_eq_div, div_le_one hD]
    dsimp [D]
    linarith
  have hcorr := bennettCorrection_le_exp_one_mul_sq htU
  have hmgf : (v / U ^ 2) * bennettCorrection (t * U) ≤ Real.exp 1 * v * t ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hcorr (div_nonneg hv (sq_nonneg U))
    have heq : (v / U ^ 2) * (Real.exp 1 * (t * U) ^ 2) =
        Real.exp 1 * v * t ^ 2 := by field_simp; ring
    exact hm.trans_eq heq
  have hvrel : v = L * r ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt (div_nonneg hv hL.le)]
    field_simp
  have hvdiv : v / D ≤ L * r := by
    apply (div_le_iff₀ hD).mpr
    dsimp [D]
    nlinarith [mul_nonneg hU.le (mul_nonneg hL.le hr)]
  have hsqrt : Real.sqrt (v * L) = L * r := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hv hL.le) (mul_nonneg hL.le hr)).mpr
    rw [mul_pow]
    rw [hvrel]
    ring
  have hlog : Real.log (2 * (p : ℝ)) ≤ L := by
    apply Real.log_le_log
    · have hp' : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
      positivity
    · have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg p)
  have hb := bounded_vector_bennett_maximum h hp hU ht hvariance
  calc
    _ ≤ (Real.log (2 * (p : ℝ)) + (v / U ^ 2) * bennettCorrection (t * U)) / t := hb
    _ ≤ (L + Real.exp 1 * v * t ^ 2) / t :=
      div_le_div_of_nonneg_right (add_le_add hlog hmgf) ht.le
    _ = L * D + Real.exp 1 * (v / D) := by dsimp [t]; field_simp; ring
    _ ≤ L * D + Real.exp 1 * (L * r) := add_le_add_left
      (mul_le_mul_of_nonneg_left hvdiv (Real.exp_nonneg _)) _
    _ ≤ _ := by
      rw [hsqrt]
      dsimp [D]
      nlinarith [mul_nonneg (Real.exp_nonneg 1) (mul_nonneg hU.le hL.le)]

/-- The cutoff algebra preserves the genuine real exponent in E.1. -/
theorem envelope_cutoff_rate_identities {A L q : ℝ}
    (hA : 0 < A) (hL : 0 < L) (hq : 1 < q) :
    (A / L ^ (1 / q)) * L = A * L ^ (1 - 1 / q) ∧
    A ^ q / (A / L ^ (1 / q)) ^ (q - 1) = A * L ^ (1 - 1 / q) := by
  constructor
  · rw [Real.rpow_sub hL, Real.rpow_one]
    ring
  · rw [Real.div_rpow hA.le (Real.rpow_nonneg hL.le _) _,
      ← Real.rpow_mul hL.le]
    have hexp : (1 / q) * (q - 1) = 1 - 1 / q := by
      field_simp
    rw [hexp]
    have hApow : A ^ q = A * A ^ (q - 1) := by
      calc
        _ = A ^ (1 + (q - 1)) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hA, Real.rpow_one]
    rw [hApow]
    field_simp
    ring

/-- A zero genuine envelope-moment budget forces the actual sum to vanish. -/
theorem sumVector_ae_zero_of_envelope_budget_zero {p n : ℕ}
    (Y : Fin n → Ω → Vector p) {q : ℝ} (hq : 0 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖Y i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖Y i ω‖ ^ q ∂μ) ≤ 0) :
    sumVector Y =ᵐ[μ] 0 := by
  have hn (i : Fin n) : 0 ≤ ∫ ω, ‖Y i ω‖ ^ q ∂μ :=
    integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _)
  have hi (i : Fin n) : Y i =ᵐ[μ] 0 := by
    have hzero : (∫ ω, ‖Y i ω‖ ^ q ∂μ) = 0 := le_antisymm
      ((Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ i)).trans hbudget) (hn i)
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun ω => Real.rpow_nonneg (norm_nonneg (Y i ω)) q) (hmoment i)).mp hzero
    filter_upwards [hae] with ω hω
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg _) hq.ne').mp hω)
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  simp only [sumVector, hω, Finset.sum_const_zero, Pi.zero_apply]

/-- Lemma E.1 for the actual independent centered vectors and genuine
moments. The explicit universal constant is chosen before dimensions and
probability models, hence satisfies the allowed dependence on fixed `q`.
The nonnegative `A` is the envelope-moment scale; nonnegativity of `v` is
derived from its variance budget. Both zero-budget cases are included. -/
theorem expected_maximum_under_envelope_moment {p n : ℕ}
    (Y : Fin n → Ω → Vector p) (hp : 1 ≤ p)
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hcenter : ∀ i j, (∫ ω, Y i ω j ∂μ) = 0)
    {q A v : ℝ} (hq : 2 < q) (hA : 0 ≤ A)
    (hsecond : ∀ i j, Integrable (fun ω => Y i ω j ^ 2) μ)
    (hvariance : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 2 ∂μ) ≤ v)
    (hmoment : ∀ i, Integrable (fun ω => ‖Y i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖Y i ω‖ ^ q ∂μ) ≤ A ^ q) :
    (∫ ω, ‖sumVector Y ω‖ ∂μ) ≤
      envelopeMaximumConstant * (Real.sqrt (v * dimensionLog p) +
        A * dimensionLog p ^ (1 - 1 / q)) := by
  have hqpos : 0 < q := by linarith
  have hqone : 1 < q := by linarith
  have hC : 0 ≤ envelopeMaximumConstant := zero_le_one.trans one_le_envelopeMaximumConstant
  by_cases hAzero : A = 0
  · subst A
    have hzbudget : (∑ i, ∫ ω, ‖Y i ω‖ ^ q ∂μ) ≤ 0 := by
      simpa only [Real.zero_rpow hqpos.ne'] using hbudget
    have hz := sumVector_ae_zero_of_envelope_budget_zero Y hqpos hmoment hzbudget
    have hnormzero : (fun ω => ‖sumVector Y ω‖) =ᵐ[μ] 0 := by
      filter_upwards [hz] with ω hω
      simp only [hω, Pi.zero_apply, norm_zero]
    rw [integral_congr_ae hnormzero]
    simp only [Pi.zero_apply, integral_zero, zero_mul, add_zero]
    exact mul_nonneg hC (Real.sqrt_nonneg _)
  have hApos : 0 < A := hA.lt_of_ne' hAzero
  let L := dimensionLog p
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  let u := A / L ^ (1 / q)
  have hu : 0 < u := div_pos hApos (Real.rpow_pos_of_pos hL _)
  have hv : 0 ≤ v := by
    let j : Fin p := ⟨0, by omega⟩
    exact (Finset.sum_nonneg (fun i _ => integral_nonneg
      (fun ω => sq_nonneg (Y i ω j)))).trans (hvariance j)
  let Z := envelopeCenteredTruncation μ Y u
  have hZ : BoundedIndependentHypotheses μ Z (2 * u) :=
    envelopeCenteredTruncation_boundedHypotheses hY hind hu.le
  have hZvar (j : Fin p) : (∑ i, ∫ ω, Z i ω j ^ 2 ∂μ) ≤ v :=
    (envelopeCenteredTruncation_second_moment_sum_le hY hu.le hsecond j).trans (hvariance j)
  have hb := bounded_vector_bernstein_maximum hZ hp (by linarith : 0 < 2 * u) hv hZvar
  have ht := integral_norm_sum_le_centeredTruncation_add_tail hY hcenter hu hqone hmoment A hbudget
  have hid := envelope_cutoff_rate_identities hApos hL hqone
  have hul : u * L = A * L ^ (1 - 1 / q) := hid.1
  have hrest : A ^ q / u ^ (q - 1) = A * L ^ (1 - 1 / q) := hid.2
  calc
    _ ≤ (∫ ω, ‖sumVector Z ω‖ ∂μ) + 2 * A ^ q / u ^ (q - 1) := ht
    _ ≤ (1 + Real.exp 1) * (Real.sqrt (v * L) + (2 * u) * L) +
        2 * A ^ q / u ^ (q - 1) := add_le_add_right hb _
    _ = (1 + Real.exp 1) * (Real.sqrt (v * L) + 2 * (A * L ^ (1 - 1 / q))) +
        2 * (A * L ^ (1 - 1 / q)) := by
      rw [mul_assoc, hul, mul_div_assoc, hrest]
    _ ≤ _ := by
      unfold envelopeMaximumConstant
      change _ ≤ (4 + 2 * Real.exp 1) * (Real.sqrt (v * L) + A * L ^ (1 - 1 / q))
      nlinarith [Real.sqrt_nonneg (v * L),
        mul_nonneg (Real.exp_nonneg 1) (Real.sqrt_nonneg (v * L))]

end
end RectangleCLT.Companion.SplitV4
