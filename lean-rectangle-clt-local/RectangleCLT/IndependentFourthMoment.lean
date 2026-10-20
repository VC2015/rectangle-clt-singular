import RectangleCLT.PositiveTail
import RectangleCLT.Normalization
import Mathlib.Probability.Integration

/-! A fourth-moment bound for genuinely independent centered bounded scalar
summands. This supplies the one-sided crossing estimate without a CLT. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

theorem integral_pow_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {B : ℝ}
    (hm : Measurable X) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ B) (r : ℕ) :
    Integrable (fun ω => X ω ^ r) μ := by
  apply (integrable_const (B ^ r)).mono' (hm.pow_const r).aestronglyMeasurable
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs, abs_pow] using
    pow_le_pow_left₀ (abs_nonneg (X ω)) hω r

theorem integral_fourth_add_of_indep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hi : IndepFun X Y μ)
    (hX : ∀ r : ℕ, Integrable (fun ω => X ω ^ r) μ)
    (hY : ∀ r : ℕ, Integrable (fun ω => Y ω ^ r) μ)
    (hmX : (∫ ω, X ω ∂μ) = 0) (hmY : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, (X ω + Y ω) ^ 4 ∂μ) = (∫ ω, X ω ^ 4 ∂μ) +
      6 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) +
      (∫ ω, Y ω ^ 4 ∂μ) := by
  have hp (a b : ℕ) : IndepFun (fun ω => X ω ^ a) (fun ω => Y ω ^ b) μ :=
    hi.comp (measurable_id.pow_const a) (measurable_id.pow_const b)
  have hip (a b : ℕ) : Integrable (fun ω => X ω ^ a * Y ω ^ b) μ :=
    (hp a b).integrable_mul (hX a) (hY b)
  have heq : (fun ω => (X ω + Y ω) ^ 4) =
      (fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1) +
        6 * (X ω ^ 2 * Y ω ^ 2) + 4 * (X ω ^ 1 * Y ω ^ 3) + Y ω ^ 4) := by
    funext ω
    ring
  rw [heq,
    integral_add (f := fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1) +
      6 * (X ω ^ 2 * Y ω ^ 2) + 4 * (X ω ^ 1 * Y ω ^ 3))
      ((((hX 4).add ((hip 3 1).const_mul 4)).add ((hip 2 2).const_mul 6)).add
        ((hip 1 3).const_mul 4)) (hY 4),
    integral_add (f := fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1) +
      6 * (X ω ^ 2 * Y ω ^ 2))
      (((hX 4).add ((hip 3 1).const_mul 4)).add ((hip 2 2).const_mul 6))
      ((hip 1 3).const_mul 4),
    integral_add (f := fun ω => X ω ^ 4 + 4 * (X ω ^ 3 * Y ω ^ 1))
      ((hX 4).add ((hip 3 1).const_mul 4)) ((hip 2 2).const_mul 6),
    integral_add (hX 4) ((hip 3 1).const_mul 4)]
  have h31 : (∫ ω, X ω ^ 3 * Y ω ∂μ) = 0 := by
    simpa only [pow_one, hmY, mul_zero] using
      (hp 3 1).integral_mul_of_integrable (hX 3) (hY 1)
  have h13 : (∫ ω, X ω * Y ω ^ 3 ∂μ) = 0 := by
    simpa only [pow_one, hmX, zero_mul] using
      (hp 1 3).integral_mul_of_integrable (hX 1) (hY 3)
  have h22 : (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ) =
      (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) :=
    (hp 2 2).integral_mul_of_integrable (hX 2) (hY 2)
  simp only [integral_const_mul, pow_one, h31, h13, h22, mul_zero, add_zero]
  ring

/-- An explicit independent-sum fourth-moment estimate, with no normal
approximation assumption. The bound uses the actual second moment. -/
theorem independent_sum_fourth_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {B : ℝ}
    (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ B)
    (hcenter : ∀ i, (∫ ω, X i ω ∂μ) = 0) :
    (∫ ω, (∑ i, X i ω) ^ 4 ∂μ) ≤
      3 * (∫ ω, (∑ i, X i ω) ^ 2 ∂μ) ^ 2 +
        B ^ 2 * (∫ ω, (∑ i, X i ω) ^ 2 ∂μ) := by
  classical
  have hi (i : Fin n) (r : ℕ) := integral_pow_of_bounded (hm i) (hb i) r
  have hi1 (i : Fin n) : Integrable (X i) μ := by simpa using hi i 1
  have hsm (s : Finset (Fin n)) : Measurable (fun ω => ∑ i ∈ s, X i ω) :=
    Finset.measurable_sum s (fun i _ => hm i)
  have hsb (s : Finset (Fin n)) :
      ∀ᵐ ω ∂μ, |∑ i ∈ s, X i ω| ≤ (s.card : ℝ) * B := by
    filter_upwards [ae_all_iff.mpr hb] with ω hω
    calc
      _ ≤ ∑ i ∈ s, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum (fun i _ => hω i)
      _ = _ := by simp
  have hsi (s : Finset (Fin n)) (r : ℕ) := integral_pow_of_bounded (hsm s) (hsb s) r
  have hsc (s : Finset (Fin n)) : (∫ ω, ∑ i ∈ s, X i ω ∂μ) = 0 := by
    rw [integral_finset_sum s (fun i _ => hi1 i)]
    simp only [hcenter, Finset.sum_const_zero]
  have hLp (i : Fin n) : MemLp (X i) 2 μ := by
    apply MemLp.of_bound (hm i).aestronglyMeasurable B
    simpa only [Real.norm_eq_abs] using hb i
  have hs2 (s : Finset (Fin n)) :
      (∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂μ) = ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ := by
    have hv := IndepFun.variance_sum (s := s) (X := X) (fun i _ => hLp i)
      (fun i _ j _ hij => hind.indepFun hij)
    have hvs (i : Fin n) : variance (X i) μ = (∫ ω, X i ω ^ 2 ∂μ) := by
      rw [variance_def' (hLp i), hcenter i]
      simp
    simp_rw [hvs] at hv
    rw [variance_def' (memLp_finset_sum' s (fun i _ => hLp i))] at hv
    simpa only [Finset.sum_apply, Pi.pow_apply, hsc s, zero_pow (by decide : 2 ≠ 0),
      sub_zero] using hv
  have hf4 (i : Fin n) : (∫ ω, X i ω ^ 4 ∂μ) ≤ B ^ 2 * (∫ ω, X i ω ^ 2 ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hi i 4) ((hi i 2).const_mul _)
    filter_upwards [hb i] with ω hω
    have hsq : X i ω ^ 2 ≤ B ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hω 2
    nlinarith [mul_nonneg (sq_nonneg (X i ω)) (sub_nonneg.mpr hsq)]
  have hfin (s : Finset (Fin n)) :
      (∫ ω, (∑ i ∈ s, X i ω) ^ 4 ∂μ) ≤
        3 * (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) ^ 2 +
          B ^ 2 * (∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
      have hIs : IndepFun (fun ω => ∑ l ∈ s, X l ω) (X i) μ := by
        convert hind.indepFun_finset_sum_of_not_mem hm his using 1
        funext ω
        simp only [Finset.sum_apply]
      have hfour := integral_fourth_add_of_indep hIs (hsi s) (hi i) (hsc s) (hcenter i)
      have hEq : (∫ ω, (∑ l ∈ insert i s, X l ω) ^ 4 ∂μ) =
          (∫ ω, (∑ l ∈ s, X l ω) ^ 4 ∂μ) +
            6 * (∑ l ∈ s, ∫ ω, X l ω ^ 2 ∂μ) * (∫ ω, X i ω ^ 2 ∂μ) +
            (∫ ω, X i ω ^ 4 ∂μ) := by
        simpa only [Finset.sum_insert his, add_comm (X i _), hs2 s] using hfour
      rw [hEq, Finset.sum_insert his]
      nlinarith [hf4 i, sq_nonneg (∫ ω, X i ω ^ 2 ∂μ)]
  simpa only [hs2 Finset.univ] using hfin Finset.univ

end RectangleCLT
