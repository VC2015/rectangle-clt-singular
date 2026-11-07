import RectangleCLTCompanion.SplitV4.SeededRestorationBounds

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def seededDerivativeConstant : ℝ := 6 * seededRestorationConstant

theorem seededDerivativeConstant_pos : 0 < seededDerivativeConstant :=
  mul_pos (by norm_num) seededRestorationConstant_pos

theorem seeded_width_scale_conditions {p : ℕ} (hp : 1 ≤ p)
    {δ h t : ℝ} (hδ : 0 ≤ δ) (hh : 0 < h) (ht : 0 ≤ t)
    (hband : seededRestorationBandwidth * δ ≤ h) :
    δ ≤ h ∧ δ * Real.sqrt (dimensionLog p) ≤
      seededSplitGaussianScale (dimensionLog p * h ^ 2) t ∧
    restorationPairedBandwidth logisticMatrixConstant 4 * δ ≤ h := by
  have hb2 : 2 * δ ≤ h :=
    (mul_le_mul_of_nonneg_right seededRestorationBandwidth_ge_two hδ).trans hband
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  refine ⟨by linarith, seededSplitGaussianScale_ge_delta_sqrt hδ hh.le hL ht hb2, ?_⟩
  exact (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ).trans hband

theorem seeded_relative_cubic_product_rate
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {h₀ t : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hband : seededRestorationBandwidth * δ ≤ h₀) :
    |(-(t / 3)) * restorationThirdExpectation s
      ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
      (fun z => seededSplitBaseValue A x (dimensionLog p * h₀ ^ 2) t z.1)
      (seededCopyWhitened A ξ) (seededCopyOriginal ξ) (fun _ _ => 0)
      (seededSplitGaussianScale (dimensionLog p * h₀ ^ 2) t)| ≤
        seededDerivativeConstant * M₃ * (dimensionLog p * Real.sqrt (dimensionLog p)) *
          t / (t + dimensionLog p * h₀ ^ 2) := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1.le ht.2.le
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ dimensionLog p * h₀ ^ 2 := mul_nonneg hL (sq_nonneg _)
  have hcond := seeded_width_scale_conditions hp h.delta_nonneg hh₀ ht.1.le hband
  have hb := seeded_relative_cubic_product_bound μ ξ h hrel hp hunit A hA s x hε
    ⟨ht.1.le, ht.2.le⟩ (hcond.1.trans hwidth) hcond.2.1
  have hsq := seededSplitGaussianScale_sq hε ht.1.le
  have hsum : 0 < t + dimensionLog p * h₀ ^ 2 := add_pos_of_pos_of_nonneg ht.1 hε
  rw [abs_mul, abs_neg, abs_of_nonneg (div_nonneg ht.1.le (by norm_num))]
  apply (mul_le_mul_of_nonneg_left hb (div_nonneg ht.1.le (by norm_num))).trans
  rw [hsq]
  have hrhs : 0 ≤ seededRestorationConstant * M₃ *
      (dimensionLog p * Real.sqrt (dimensionLog p)) * t :=
    mul_nonneg (mul_nonneg (mul_nonneg seededRestorationConstant_pos.le hrel.s₃_nonneg)
      (mul_nonneg hL (Real.sqrt_nonneg _))) ht.1.le
  unfold seededDerivativeConstant
  calc
    _ = ((2 / 3 : ℝ) * (seededRestorationConstant * M₃ *
        (dimensionLog p * Real.sqrt (dimensionLog p)) * t)) /
          (t + dimensionLog p * h₀ ^ 2) := by field_simp; ring
    _ ≤ (6 * (seededRestorationConstant * M₃ *
        (dimensionLog p * Real.sqrt (dimensionLog p)) * t)) /
          (t + dimensionLog p * h₀ ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hrhs) hsum.le
    _ = _ := by ring

theorem seeded_relative_fourth_product_rate
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {h₀ t r : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (ht : t ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1)
    (hband : seededRestorationBandwidth * δ ≤ h₀) (freshY freshW freshShift : Bool) :
    |restorationFourthExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
      (fun z => seededSplitBaseValue A x (dimensionLog p * h₀ ^ 2) t z.1)
      (seededCopyWhitened A ξ) (seededCopyDirection ξ freshY) (seededCopyDirection ξ freshW)
      (seededCopyShift ξ freshShift t r) (seededSplitGaussianScale (dimensionLog p * h₀ ^ 2) t)| ≤
        (2 * seededRestorationConstant) * M₄ * (dimensionLog p * Real.sqrt (dimensionLog p)) /
          (h₀ * (t + dimensionLog p * h₀ ^ 2)) := by
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht.1.le ht.2.le
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ dimensionLog p * h₀ ^ 2 := mul_nonneg hL (sq_nonneg _)
  have hcond := seeded_width_scale_conditions hp h.delta_nonneg hh₀ ht.1.le hband
  have hb := seeded_relative_fourth_product_bound μ ξ h hrel hp hunit A hA s x hε
    ⟨ht.1.le, ht.2.le⟩ hr hcond.2.1 (hcond.2.2.trans hwidth) freshY freshW freshShift
  have hsq := seededSplitGaussianScale_sq hε ht.1.le
  have hsum : 0 < t + dimensionLog p * h₀ ^ 2 := add_pos_of_pos_of_nonneg ht.1 hε
  apply hb.trans
  rw [hsq]
  have hnum : 0 ≤ (2 * seededRestorationConstant) * M₄ *
      (dimensionLog p * Real.sqrt (dimensionLog p)) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) seededRestorationConstant_pos.le)
      hrel.s₄_nonneg) (mul_nonneg hL (Real.sqrt_nonneg _))
  have hh := div_le_div_of_nonneg_left hnum hh₀ (hwidth)
  have hh' := div_le_div_of_nonneg_right hh hsum.le
  convert hh' using 1 <;> field_simp <;> ring

end

end RectangleCLT.Companion.SplitV4
