import RectangleCLTCompanion.SplitV4.SeededFourthLaw
import RectangleCLTCompanion.SplitV4.SeededRestorationRates

open MeasureTheory Set
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def seededFourthRemainder {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε t : ℝ) : ℝ :=
  (∫ r in (0 : ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) r *
    s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
      (thinningProbability t) (1 + t) r) +
  (1 - t) / 2 * (∫ r in (0 : ℝ)..1, (1 - r) *
    s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
      (thinningProbability t) (1 + t) r) +
  (t * (1 - t) / (3 * (1 + t))) * (∫ r in (0 : ℝ)..1,
    s.variableFourthPathIntegrandC (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
      (thinningProbability t) (1 + t) r)

theorem abs_unit_intervalIntegral_le_const {f : ℝ → ℝ} {B : ℝ}
    (hf : ∀ r ∈ Icc (0 : ℝ) 1, |f r| ≤ B) : |∫ r in (0 : ℝ)..1, f r| ≤ B := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := f) (C := B) (fun r hr => by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
      simpa only [Real.norm_eq_abs] using hf r ⟨hr.1.le, hr.2⟩)
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh

theorem seeded_fourth_remainder_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {h₀ t : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : seededRestorationBandwidth * δ ≤ h₀) :
    |seededFourthRemainder s μ ξ A x (dimensionLog p * h₀ ^ 2) t| ≤
      seededDerivativeConstant * M₄ * (dimensionLog p * Real.sqrt (dimensionLog p)) /
        (h₀ * (t + dimensionLog p * h₀ ^ 2)) := by
  let ε := dimensionLog p * h₀ ^ 2
  let N := (2 * seededRestorationConstant) * M₄ * (dimensionLog p * Real.sqrt (dimensionLog p)) /
    (h₀ * (t + ε))
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ ε := mul_nonneg hL (sq_nonneg _)
  have hsum : 0 < t + ε := add_pos_of_pos_of_nonneg ht.1 hε
  have hN : 0 ≤ N := div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) seededRestorationConstant_pos.le) hrel.s₄_nonneg)
      (mul_nonneg hL (Real.sqrt_nonneg _))) (mul_nonneg hh₀.le hsum.le)
  have hA' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      |s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    rw [variableFourthPathIntegrandA_eq_seeded_product s μ ξ h A hA x ht.1.le ht.2.le hsum]
    exact seeded_relative_fourth_product_rate μ ξ h hrel hp hunit A hA s x hh₀ hwidth ht hr hband false false false
  have hB' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      |s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    rw [variableFourthPathIntegrandB_eq_seeded_product s μ ξ h A hA x ht.1.le ht.2.le hsum]
    exact seeded_relative_fourth_product_rate μ ξ h hrel hp hunit A hA s x hh₀ hwidth ht hr hband true true true
  have hC' (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      |s.variableFourthPathIntegrandC (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    rw [variableFourthPathIntegrandC_eq_seeded_product s μ ξ h A hA x ht.1.le ht.2.le hsum]
    exact seeded_relative_fourth_product_rate μ ξ h hrel hp hunit A hA s x hh₀ hwidth ht hr hband false true true
  have hIA : |∫ r in (0 : ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) r *
      s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    apply abs_unit_intervalIntegral_le_const
    intro r hr
    rw [abs_mul]
    exact (mul_le_mul (calibrated_fourth_kernel_abs_le_one ⟨ht.1.le, ht.2.le⟩ hr)
      (hA' r hr) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hIB : |∫ r in (0 : ℝ)..1, (1 - r) *
      s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
        (thinningProbability t) (1 + t) r| ≤ N := by
    apply abs_unit_intervalIntegral_le_const
    intro r hr
    rw [abs_mul]
    exact (mul_le_mul (show |1 - r| ≤ 1 by rw [abs_le]; constructor <;> linarith [hr.1, hr.2])
      (hB' r hr) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hIC : |∫ r in (0 : ℝ)..1, s.variableFourthPathIntegrandC
      (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x (thinningProbability t) (1 + t) r| ≤ N :=
    abs_unit_intervalIntegral_le_const hC'
  have hb : |(1 - t) / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hc : |t * (1 - t) / (3 * (1 + t))| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg ht.1.le (by linarith [ht.2])) (by linarith [ht.1]))]
    apply (div_le_one (by linarith [ht.1] : 0 < 3 * (1 + t))).mpr
    nlinarith [sq_nonneg t]
  have htriangle (a b c : ℝ) : |(a + b) + c| ≤ (|a| + |b|) + |c| :=
    (abs_add (a + b) c).trans (add_le_add_right (abs_add a b) |c|)
  unfold seededFourthRemainder
  change |(_ + _) + _| ≤ _
  calc
    _ ≤ |∫ r in (0 : ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) r *
        s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
          (thinningProbability t) (1 + t) r| +
      |(1 - t) / 2| * |∫ r in (0 : ℝ)..1, (1 - r) *
        s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
          (thinningProbability t) (1 + t) r| +
      |t * (1 - t) / (3 * (1 + t))| * |∫ r in (0 : ℝ)..1,
        s.variableFourthPathIntegrandC (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
          (thinningProbability t) (1 + t) r| := by
      simpa only [abs_mul] using htriangle
        (∫ r in (0 : ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) r *
          s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
            (thinningProbability t) (1 + t) r)
        ((1 - t) / 2 * (∫ r in (0 : ℝ)..1, (1 - r) *
          s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
            (thinningProbability t) (1 + t) r))
        ((t * (1 - t) / (3 * (1 + t))) * (∫ r in (0 : ℝ)..1,
          s.variableFourthPathIntegrandC (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
            (thinningProbability t) (1 + t) r))
    _ ≤ N + 1 * N + 1 * N := add_le_add
      (add_le_add hIA (mul_le_mul hb hIB (abs_nonneg _) zero_le_one))
      (mul_le_mul hc hIC (abs_nonneg _) zero_le_one)
    _ = _ := by unfold N ε seededDerivativeConstant; ring

end

end RectangleCLT.Companion.SplitV4
