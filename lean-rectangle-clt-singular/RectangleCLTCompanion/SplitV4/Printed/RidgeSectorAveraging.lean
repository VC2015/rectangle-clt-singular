import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorBound

/-! Averaging the sector-derived adaptive layer with the radius moments
obtained by radial Gaussian tail integration. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem projectionRadiusMomentConstant_pos : 0 < projectionRadiusMomentConstant :=
  zero_lt_one.trans_le projectionRadiusMomentConstant_ge_one

theorem concentratedBase_sector_adaptiveLayer_average
    (hm : 1 ≤ m) (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) {C δ L σ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ L) (hc : ConcentratedThresholdBase μ u C δ L) :
    (∫ v, ∫ g, (adaptiveThresholdEvent u a σ (thresholdProjectionRadius u)).indicator
      (fun vg => thresholdProjectionRadius u vg.2 ^ 3) (v, g) ∂standardGaussian r ∂μ) ≤
      C * projectionRadiusMomentConstant * (σ * L * Real.sqrt L + δ * L ^ 2) := by
  have hL0 : 0 ≤ L := (zero_le_one.trans (log_exp_mul_nat_ge_one hm)).trans hL
  obtain ⟨h2, h3, h2bound, h3bound⟩ := thresholdProjectionRadius_second_third_moments_from_radial_tail hm u
  have h2final : (∫ g, thresholdProjectionRadius u g ^ 2 ∂standardGaussian r) ≤
      projectionRadiusMomentConstant * L := h2bound.trans (mul_le_mul_of_nonneg_left hL projectionRadiusMomentConstant_pos.le)
  have h3final : (∫ g, thresholdProjectionRadius u g ^ 3 ∂standardGaussian r) ≤
      projectionRadiusMomentConstant * L * Real.sqrt L := by
    apply h3bound.trans
    simpa only [mul_assoc] using
      mul_le_mul (mul_le_mul_of_nonneg_left hL projectionRadiusMomentConstant_pos.le)
        (Real.sqrt_le_sqrt hL) (Real.sqrt_nonneg _)
        (mul_nonneg projectionRadiusMomentConstant_pos.le hL0)
  have hh := concentratedBase_adaptiveLayer_average μ (standardGaussian r) u a hσ hc
    (thresholdProjectionRadius u) (measurable_thresholdProjectionRadius u)
    (fun g => zero_lt_one.trans_le (thresholdProjectionRadius_ge_one u g)) h2 h3
  apply hh.trans
  have hsq := Real.sq_sqrt hL0
  calc
    _ ≤ C * Real.sqrt L * (σ * (projectionRadiusMomentConstant * L) + δ * (projectionRadiusMomentConstant * L * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left h2final hσ.le)
        (mul_le_mul_of_nonneg_left h3final hδ)) (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = C * projectionRadiusMomentConstant * (σ * L * Real.sqrt L + δ * L * (Real.sqrt L ^ 2)) := by ring
    _ = _ := by rw [hsq]; ring


theorem gaussianThresholdDerivative_abs_le_sector_radius_moment {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    |gaussianThresholdDerivative u b| ≤ (2 * sectorThresholdGeometryConstant) *
      ∫ g, thresholdProjectionRadius u g ^ 3 ∂standardGaussian (n + 1) := by
  have h3 := (thresholdProjectionRadius_second_third_moments_from_radial_tail hm u).2.1
  apply (gaussianThresholdDerivative_le_sectorAdaptiveLayer hm u b hu hi).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) sectorThresholdGeometryConstant_pos.le)
  apply integral_mono (h3.indicator (measurableSet_gaussianAdaptiveOuterEvent u b)) h3
  intro g
  by_cases hg : g ∈ gaussianAdaptiveOuterEvent u b
  · simp only [Set.indicator_of_mem hg, le_refl]
  · simp only [Set.indicator_of_not_mem hg]
    exact pow_nonneg (zero_le_one.trans (thresholdProjectionRadius_ge_one u g)) 3

theorem integrable_gaussianThresholdDerivative_sector_base_succ {m n : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector (n + 1))) [IsProbabilityMeasure μ]
    (u : Fin m → Vector (n + 1)) (a : Vector m) (σ : ℝ)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Integrable (fun v => gaussianThresholdDerivative u (thresholdsFromBase u a σ v)) μ := by
  have hb : Measurable (fun v => thresholdsFromBase u a σ v) :=
    measurable_pi_lambda _ (fun j => (measurable_const.sub (measurable_thresholdDot (u j))).div_const σ)
  have hd := (continuous_gaussianThresholdDerivative_for_averaging u hu hi).measurable.comp hb
  apply (integrable_const ((2 * sectorThresholdGeometryConstant) *
    ∫ g, thresholdProjectionRadius u g ^ 3 ∂standardGaussian (n + 1))).mono' hd.aestronglyMeasurable
  exact ae_of_all _ (fun v => by
    rw [Real.norm_eq_abs]
    exact gaussianThresholdDerivative_abs_le_sector_radius_moment hm u _ hu hi)

/-- Genuine integrability needs no moment assumption on the base and no
lower bound on the Gaussian scale. -/
theorem integrable_gaussianThresholdDerivative_sector_base {m r : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (σ : ℝ)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Integrable (fun v => gaussianThresholdDerivative u (thresholdsFromBase u a σ v)) μ := by
  cases r with
  | zero =>
      let j : Fin m := ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hm⟩
      have hh := hu j
      simp [vectorNormSq] at hh
  | succ n => exact integrable_gaussianThresholdDerivative_sector_base_succ hm μ u a σ hu hi


def sectorAveragedThresholdConstant : ℝ := 2 * sectorThresholdGeometryConstant * projectionRadiusMomentConstant

theorem sectorAveragedThresholdConstant_pos : 0 < sectorAveragedThresholdConstant := by
  unfold sectorAveragedThresholdConstant
  exact mul_pos (mul_pos (by norm_num) sectorThresholdGeometryConstant_pos) projectionRadiusMomentConstant_pos

theorem averagedGaussianThresholdDerivative_sector_bound_succ {m n : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector (n + 1))) [IsProbabilityMeasure μ]
    (u : Fin m → Vector (n + 1)) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ L) (hc : ConcentratedThresholdBase μ u C δ L) :
    (∫ v, |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ∂μ) ≤
      sectorAveragedThresholdConstant * C * (σ * L * Real.sqrt L + δ * L ^ 2) := by
  let γ := standardGaussian (n + 1)
  let R := thresholdProjectionRadius u
  let K : Vector (n + 1) × Vector (n + 1) → ℝ :=
    (adaptiveThresholdEvent u a σ R).indicator (fun vg => R vg.2 ^ 3)
  have h3 : Integrable (fun g => R g ^ 3) γ := (thresholdProjectionRadius_second_third_moments_from_radial_tail hm u).2.1
  have hw : Integrable (fun vg : Vector (n + 1) × Vector (n + 1) => R vg.2 ^ 3) (μ.prod γ) := by
    simpa only [one_mul] using (integrable_const (μ := μ) (1 : ℝ)).mul_prod h3
  have hK : Integrable K (μ.prod γ) :=
    hw.indicator (measurableSet_adaptiveThresholdEvent u a σ (measurable_thresholdProjectionRadius u))
  have hpoint (v : Vector (n + 1)) : |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ≤
      (2 * sectorThresholdGeometryConstant) * ∫ g, K (v, g) ∂γ := by
    have hh := gaussianThresholdDerivative_le_sectorAdaptiveLayer hm u (thresholdsFromBase u a σ v) hu hi
    apply hh.trans_eq
    congr 1
    apply integral_congr_ae
    filter_upwards [] with g
    by_cases hg : g ∈ gaussianAdaptiveOuterEvent u (thresholdsFromBase u a σ v)
    · have hg' : (v, g) ∈ adaptiveThresholdEvent u a σ R :=
        (mem_gaussianAdaptiveOuterEvent u (thresholdsFromBase u a σ v) g).mp hg
      simp only [K, Set.indicator_of_mem hg, Set.indicator_of_mem hg']
      rfl
    · have hg' : (v, g) ∉ adaptiveThresholdEvent u a σ R := fun h =>
        hg ((mem_gaussianAdaptiveOuterEvent u (thresholdsFromBase u a σ v) g).mpr h)
      simp only [K, Set.indicator_of_not_mem hg, Set.indicator_of_not_mem hg']
  have hdi := (integrable_gaussianThresholdDerivative_sector_base_succ hm μ u a σ hu hi).abs
  have hh := integral_mono hdi (hK.integral_prod_left.const_mul (2 * sectorThresholdGeometryConstant)) hpoint
  rw [integral_const_mul] at hh
  have ha := concentratedBase_sector_adaptiveLayer_average hm μ u a hC hδ hσ hL hc
  calc
    _ ≤ (2 * sectorThresholdGeometryConstant) * ∫ v, ∫ g, K (v, g) ∂γ ∂μ := hh
    _ ≤ (2 * sectorThresholdGeometryConstant) *
        (C * projectionRadiusMomentConstant * (σ * L * Real.sqrt L + δ * L ^ 2)) :=
      mul_le_mul_of_nonneg_left ha (mul_nonneg (by norm_num) sectorThresholdGeometryConstant_pos.le)
    _ = _ := by unfold sectorAveragedThresholdConstant; ring

/-- Appendix B.5: the actual common-threshold derivative, averaged over a
concentrated base. The numerical constant is fixed before every law,
dimension, threshold, scale and concentration parameter. -/
theorem averagedGaussianThresholdDerivative_sector_bound {m r : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ L) (hc : ConcentratedThresholdBase μ u C δ L) :
    (∫ v, |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ∂μ) ≤
      sectorAveragedThresholdConstant * C * (σ * L * Real.sqrt L + δ * L ^ 2) := by
  cases r with
  | zero =>
      let j : Fin m := ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hm⟩
      have hh := hu j
      simp [vectorNormSq] at hh
  | succ n => exact averagedGaussianThresholdDerivative_sector_bound_succ hm μ u a hu hi hC hδ hσ hL hc


def sectorAveragedThresholdPaperConstant : ℝ := 4 * sectorAveragedThresholdConstant

theorem sectorAveragedThresholdPaperConstant_pos : 0 < sectorAveragedThresholdPaperConstant :=
  mul_pos (by norm_num) sectorAveragedThresholdConstant_pos

/-- Face-count normalization permits `log(e m) ≤ 2L`, retaining the
original concentration parameter `L` and changing only a fixed constant. -/
theorem averagedGaussianThresholdDerivative_sector_bound_of_log_le_two {m r : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ 2 * L) (hc : ConcentratedThresholdBase μ u C δ L) :
    (∫ v, |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ∂μ) ≤
      sectorAveragedThresholdPaperConstant * C * (σ * L * Real.sqrt L + δ * L ^ 2) := by
  have hL0 : 0 ≤ L := by
    have hh : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
    linarith only [hh, hL]
  have hc' : ConcentratedThresholdBase μ u C δ (2 * L) :=
    hc.mono_log hC hδ (by linarith only [hL0])
  have hh := averagedGaussianThresholdDerivative_sector_bound hm μ u a hu hi hC hδ hσ hL hc'
  have hroot : Real.sqrt (2 * L) ≤ 2 * Real.sqrt L := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg L)
    exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hcost : σ * (2 * L) * Real.sqrt (2 * L) + δ * (2 * L) ^ 2 ≤
      4 * (σ * L * Real.sqrt L + δ * L ^ 2) := by
    calc
      _ ≤ σ * (2 * L) * (2 * Real.sqrt L) + δ * (2 * L) ^ 2 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hroot
          (mul_nonneg hσ.le (mul_nonneg (by norm_num) hL0))) _
      _ = _ := by ring
  calc
    _ ≤ sectorAveragedThresholdConstant * C *
        (σ * (2 * L) * Real.sqrt (2 * L) + δ * (2 * L) ^ 2) := hh
    _ ≤ sectorAveragedThresholdConstant * C * (4 * (σ * L * Real.sqrt L + δ * L ^ 2)) :=
      mul_le_mul_of_nonneg_left hcost (mul_nonneg sectorAveragedThresholdConstant_pos.le hC)
    _ = _ := by unfold sectorAveragedThresholdPaperConstant; ring


end
end RectangleCLT.Companion.SplitV4.Printed
