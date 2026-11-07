import RectangleCLTCompanion.SplitV4.GaussianThresholdCommonShift
import RectangleCLTCompanion.SplitV4.AveragedDerivativeBound
import RectangleCLTCompanion.SplitV4.LogisticMatrixEstimate
import RectangleCLTCompanion.GaussianConcentration

/-! Signed Gamma differentiation. All Gaussian score weights remain signed
until the final scalar derivative estimate. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem hasDerivAt_integral_signed_smoother_power
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (V : Ω → Vector m) (hV : Measurable V)
    (P : Ω → ℝ) (hP : Integrable P μ) (s : FaceSmoother m) (a : ℕ) (t : ℝ) :
    HasDerivAt (fun z => ∫ ω, P ω * (s.shiftOffsets z).F (V ω) ^ (a + 1) ∂μ)
      (((a : ℝ) + 1) / s.bandwidth *
        ∫ ω, P ω * ((s.shiftOffsets t).F (V ω) ^ (a + 1) *
          (s.shiftOffsets t).theta (V ω)) ∂μ) t := by
  let F : ℝ → Ω → ℝ := fun z ω => P ω * (s.shiftOffsets z).F (V ω) ^ (a + 1)
  let D : ℝ → Ω → ℝ := fun z ω => (((a : ℝ) + 1) / s.bandwidth) *
    (P ω * ((s.shiftOffsets z).F (V ω) ^ (a + 1) * (s.shiftOffsets z).theta (V ω)))
  have hm (z : ℝ) : Measurable (fun ω => (s.shiftOffsets z).F (V ω)) :=
    (s.shiftOffsets z).continuous_F.measurable.comp hV
  have hθm (z : ℝ) : Measurable (fun ω => (s.shiftOffsets z).theta (V ω)) :=
    (SignedSurface.continuous_smoother_theta _).measurable.comp hV
  have hc : 0 ≤ ((a : ℝ) + 1) / s.bandwidth :=
    div_nonneg (by positivity) s.bandwidth_pos.le
  have hi (z : ℝ) : Integrable (F z) μ := hP.norm.mono'
    (hP.aestronglyMeasurable.mul ((hm z).pow_const _).aestronglyMeasurable)
    (ae_of_all _ (fun ω => by
      dsimp only [F]
      simp only [norm_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (pow_nonneg ((s.shiftOffsets z).F_pos _).le _)]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (pow_le_one₀ ((s.shiftOffsets z).F_pos _).le ((s.shiftOffsets z).F_le_one _))))
  have hd (ω : Ω) (z : ℝ) : HasDerivAt (fun z => F z ω) (D z ω) z := by
    have hh := ((s.hasDerivAt_shiftOffsets_F (V ω) z).pow (a + 1)).const_mul (P ω)
    convert hh using 1
    dsimp only [D]
    change (((a : ℝ) + 1) / s.bandwidth) *
      (P ω * ((s.shiftOffsets z).F (V ω) ^ (a + 1) * (1 - (s.shiftOffsets z).F (V ω)))) = _
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    rw [pow_succ]
    ring
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (ε := 1) (bound := fun ω => (((a : ℝ) + 1) / s.bandwidth) * ‖P ω‖)
    (F := F) (F' := D) (x₀ := t) (by norm_num)
    (Eventually.of_forall (fun z => (hi z).aestronglyMeasurable)) (hi t)
    ((hP.aestronglyMeasurable.mul (((hm t).pow_const _).mul (hθm t)).aestronglyMeasurable).const_mul _)
    (ae_of_all _ (fun ω z _ => by
      dsimp only [D]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc, norm_mul]
      have hw := SignedSurface.smoother_power_weight_bounds (s.shiftOffsets z) a (V ω)
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg hw.1]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _) hw.2) hc))
    (hP.norm.const_mul _) (ae_of_all _ (fun ω z _ => hd ω z))
  convert hh.2 using 1
  exact (integral_const_mul _ _).symm

def gammaAdjustedThreshold {m : ℕ} (a : Vector m) (h : ℝ)
    (e : ℝ × (Face m → ℝ)) : Vector m :=
  fun j => a j + h * Real.log (e.2 (j, true) / e.1)

@[fun_prop] theorem measurable_gammaAdjustedThreshold {m : ℕ} (a : Vector m) (h : ℝ) :
    Measurable (gammaAdjustedThreshold a h) := by
  unfold gammaAdjustedThreshold
  fun_prop

theorem upper_randomRectangle_inside_iff {m r : ℕ} (u : Fin m → Vector r)
    (a : Vector m) {h : ℝ} (hh : 0 < h) (e : ℝ × (Face m → ℝ)) (x : Vector r) :
    ((upperFaceSmoother a h hh).randomRectangle e).Inside (Matrix.mulVec u x) ↔
      ∀ j, faceDot (u j) x ≤ gammaAdjustedThreshold a h e j := by
  simp only [FaceSmoother.Inside, FaceSmoother.randomRectangle, upperFaceSmoother,
    Finset.mem_filter, Finset.mem_univ, true_and, FaceSmoother.faceScore,
    gammaAdjustedThreshold]
  constructor
  · intro hx j
    have h := hx (j, true) rfl
    simpa only [FaceSmoother.normalDot, Bool.true_eq, if_true, one_mul, Matrix.mulVec,
      dotProduct, faceDot] using (sub_nonpos.mp h)
  · intro hx f hf
    rcases f with ⟨j, c⟩
    change c = true at hf
    subst c
    have h := hx j
    simpa only [FaceSmoother.normalDot, Bool.true_eq, if_true, one_mul, Matrix.mulVec,
      dotProduct, faceDot] using (sub_nonpos.mpr h)

theorem signed_logistic_power_eq_gamma_hard_trace {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ)
    (x : Vector r) (n : ℕ) :
    (∫ g, (vectorNormSq g - (r : ℝ)) *
      (upperFaceSmoother a h hh).F (Matrix.mulVec u (x + σ • g)) ^ (n + 1)
        ∂standardGaussian r) =
      ∫ e, gaussianThresholdTrace u
        (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ)
          ∂gammaRectangleLaw m n := by
  have hp : Integrable (fun g : Vector r => vectorNormSq g - (r : ℝ))
      (standardGaussian r) :=
    (SignedSurface.standardGaussian_integrable_vectorNormSq r).sub (integrable_const _)
  rw [gammaMixture_integral_signed_test (standardGaussian r)
    (fun g => Matrix.mulVec u (x + σ • g)) (by fun_prop) _ hp (upperFaceSmoother a h hh) n]
  apply integral_congr_ae
  apply ae_of_all
  intro e
  unfold gaussianThresholdTrace
  change (∫ g, {g | ((upperFaceSmoother a h hh).randomRectangle e).Inside
      (Matrix.mulVec u (x + σ • g))}.indicator (fun g => vectorNormSq g - (r : ℝ)) g
        ∂standardGaussian r) = _
  have hs : {g | ((upperFaceSmoother a h hh).randomRectangle e).Inside
      (Matrix.mulVec u (x + σ • g))} =
      {g | ∀ j, faceDot (u j) g ≤
        (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ} := by
    ext g
    rw [Set.mem_setOf_eq, upper_randomRectangle_inside_iff]
    have he (j : Fin m) : faceDot (u j) (x + σ • g) =
        faceDot (u j) x + σ * faceDot (u j) g := by
      unfold faceDot
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    constructor
    · intro hg j
      apply (le_div_iff₀ hσ).mpr
      have hj := hg j
      nlinarith
    · intro hg j
      have hj := (le_div_iff₀ hσ).mp (hg j)
      nlinarith
  rw [hs]

theorem averaged_hard_trace_increment_le_of_L1_budget {m r : ℕ}
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (a : Vector m) (σ B : ℝ) (hσ : σ ≠ 0)
    (hDi : ∀ b : Vector m, Integrable (fun x => gaussianThresholdDerivative u
      (fun j => (b j - faceDot (u j) x) / σ)) μ)
    (hB : ∀ b : Vector m, (∫ x, |gaussianThresholdDerivative u
      (fun j => (b j - faceDot (u j) x) / σ)| ∂μ) ≤ B) (c d : ℝ) :
    |(∫ x, gaussianThresholdTrace u (fun j => (a j - faceDot (u j) x) / σ + d) ∂μ) -
      ∫ x, gaussianThresholdTrace u (fun j => (a j - faceDot (u j) x) / σ + c) ∂μ| ≤
        B * |d - c| := by
  have he (t : ℝ) (x : Vector r) :
      (fun j => (a j - faceDot (u j) x) / σ + t) =
        (fun j => ((a j + σ * t) - faceDot (u j) x) / σ) := by
    funext j
    field_simp
    ring
  apply averaged_increment_le_of_uniform_L1_derivative μ
    (fun t x => gaussianThresholdTrace u (fun j => (a j - faceDot (u j) x) / σ + t))
    (fun t x => gaussianThresholdDerivative u (fun j => (a j - faceDot (u j) x) / σ + t))
  · exact (continuous_gaussianThresholdDerivative u hu hi).measurable.comp (by unfold faceDot; fun_prop)
  · intro t
    exact integrable_gaussianThresholdTrace_parameter μ u hu hi _ (by unfold faceDot; fun_prop)
  · intro t
    simpa only [he] using hDi (fun j => a j + σ * t)
  · intro x
    exact (continuous_gaussianThresholdDerivative u hu hi).comp (by fun_prop)
  · intro x t
    exact hasDerivAt_gaussianThresholdTrace_commonShift u _ hu hi t
  · intro t
    simpa only [he] using hB (fun j => a j + σ * t)

theorem averaged_signed_logistic_power_eq_gamma_hard_trace {m r : ℕ}
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (a : Vector m) {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ)
    (n : ℕ) :
    (∫ x, ∫ g, (vectorNormSq g - (r : ℝ)) *
      (upperFaceSmoother a h hh).F (Matrix.mulVec u (x + σ • g)) ^ (n + 1)
        ∂standardGaussian r ∂μ) =
      ∫ e, ∫ x, gaussianThresholdTrace u
        (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ)
          ∂μ ∂gammaRectangleLaw m n := by
  have hm : Measurable (fun z : Vector r × (ℝ × (Face m → ℝ)) =>
      gaussianThresholdTrace u
        (fun j => (gammaAdjustedThreshold a h z.2 j - faceDot (u j) z.1) / σ)) :=
    (continuous_gaussianThresholdTrace u hu hi).measurable.comp (by
      unfold gammaAdjustedThreshold faceDot
      fun_prop)
  have hji : Integrable (fun z : Vector r × (ℝ × (Face m → ℝ)) =>
      gaussianThresholdTrace u
        (fun j => (gammaAdjustedThreshold a h z.2 j - faceDot (u j) z.1) / σ))
      (μ.prod (gammaRectangleLaw m n)) :=
    (integrable_const ((2 : ℝ) * r)).mono' hm.aestronglyMeasurable (ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using abs_gaussianThresholdTrace_le_twice_dimension u _))
  calc
    _ = ∫ x, ∫ e, gaussianThresholdTrace u
        (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ)
          ∂gammaRectangleLaw m n ∂μ :=
      integral_congr_ae (ae_of_all _ (fun x => signed_logistic_power_eq_gamma_hard_trace u a hh hσ x n))
    _ = _ := integral_integral_swap hji

theorem upperFaceSmoother_shiftOffsets {m : ℕ} (a : Vector m) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    (upperFaceSmoother a h hh).shiftOffsets t = upperFaceSmoother (fun j => a j + t) h hh := rfl

theorem averaged_signed_logistic_power_shift_eq_gamma {m r : ℕ}
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (a : Vector m) {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ)
    (n : ℕ) (t : ℝ) :
    (∫ x, ∫ g, (vectorNormSq g - (r : ℝ)) *
      ((upperFaceSmoother a h hh).shiftOffsets (σ * t)).F
        (Matrix.mulVec u (x + σ • g)) ^ (n + 1) ∂standardGaussian r ∂μ) =
      ∫ e, ∫ x, gaussianThresholdTrace u
        (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ + t)
          ∂μ ∂gammaRectangleLaw m n := by
  rw [upperFaceSmoother_shiftOffsets,
    averaged_signed_logistic_power_eq_gamma_hard_trace μ u hu hi _ hh hσ]
  apply integral_congr_ae
  apply ae_of_all
  intro e
  apply integral_congr_ae
  apply ae_of_all
  intro x
  apply congrArg (gaussianThresholdTrace u)
  funext j
  unfold gammaAdjustedThreshold
  field_simp
  ring

theorem averaged_signed_logistic_power_increment_le_of_L1_budget {m r : ℕ}
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (a : Vector m) {h σ B : ℝ} (hh : 0 < h) (hσ : 0 < σ)
    (hDi : ∀ b : Vector m, Integrable (fun x => gaussianThresholdDerivative u
      (fun j => (b j - faceDot (u j) x) / σ)) μ)
    (hB : ∀ b : Vector m, (∫ x, |gaussianThresholdDerivative u
      (fun j => (b j - faceDot (u j) x) / σ)| ∂μ) ≤ B) (n : ℕ) (c d : ℝ) :
    |(∫ x, ∫ g, (vectorNormSq g - (r : ℝ)) *
      ((upperFaceSmoother a h hh).shiftOffsets (σ * d)).F
        (Matrix.mulVec u (x + σ • g)) ^ (n + 1) ∂standardGaussian r ∂μ) -
      ∫ x, ∫ g, (vectorNormSq g - (r : ℝ)) *
      ((upperFaceSmoother a h hh).shiftOffsets (σ * c)).F
        (Matrix.mulVec u (x + σ • g)) ^ (n + 1) ∂standardGaussian r ∂μ| ≤ B * |d - c| := by
  rw [averaged_signed_logistic_power_shift_eq_gamma μ u hu hi a hh hσ,
    averaged_signed_logistic_power_shift_eq_gamma μ u hu hi a hh hσ]
  have hK (t : ℝ) : Integrable (fun e => ∫ x, gaussianThresholdTrace u
      (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ + t) ∂μ)
      (gammaRectangleLaw m n) := by
    apply (integrable_const ((2 : ℝ) * r)).mono'
    · exact ((continuous_gaussianThresholdTrace u hu hi).measurable.comp
        (show Measurable (fun z : (ℝ × (Face m → ℝ)) × Vector r =>
          fun j => (gammaAdjustedThreshold a h z.1 j - faceDot (u j) z.2) / σ + t) from by
          unfold gammaAdjustedThreshold faceDot
          fun_prop)).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · exact ae_of_all _ (fun e => by
        have hh := norm_integral_le_of_norm_le (μ := μ)
          (f := fun x => gaussianThresholdTrace u
            (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ + t))
          (integrable_const ((2 : ℝ) * r)) (ae_of_all _ (fun x => by
            simpa only [Real.norm_eq_abs] using abs_gaussianThresholdTrace_le_twice_dimension u _))
        simpa using hh)
  rw [← integral_sub (hK d) (hK c)]
  calc
    _ ≤ ∫ e, ‖(∫ x, gaussianThresholdTrace u
          (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ + d) ∂μ) -
        ∫ x, gaussianThresholdTrace u
          (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ + c) ∂μ‖
          ∂gammaRectangleLaw m n := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := gammaRectangleLaw m n) (fun e => (∫ x, gaussianThresholdTrace u
          (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ + d) ∂μ) -
        ∫ x, gaussianThresholdTrace u
          (fun j => (gammaAdjustedThreshold a h e j - faceDot (u j) x) / σ + c) ∂μ)
    _ ≤ ∫ _e, B * |d - c| ∂gammaRectangleLaw m n :=
      integral_mono ((hK d).sub (hK c)).norm (integrable_const _) (fun e => by
        simpa only [Real.norm_eq_abs] using averaged_hard_trace_increment_le_of_L1_budget
          μ u hu hi (gammaAdjustedThreshold a h e) σ B hσ.ne' hDi hB c d)
    _ = _ := by simp

theorem integrable_gaussian_radial_product_weight {r : ℕ}
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (W : Vector r × Vector r → ℝ) (hW : Measurable W) (hWb : ∀ z, ‖W z‖ ≤ 1) :
    Integrable (fun z => (vectorNormSq z.2 - (r : ℝ)) * W z)
      (μ.prod (standardGaussian r)) := by
  have hp : Integrable (fun z : Vector r × Vector r => vectorNormSq z.2 - (r : ℝ))
      (μ.prod (standardGaussian r)) := by
    simpa only [one_mul] using (integrable_const (μ := μ) (1 : ℝ)).mul_prod
      ((SignedSurface.standardGaussian_integrable_vectorNormSq r).sub (integrable_const (r : ℝ)))
  apply hp.norm.mono' (hp.aestronglyMeasurable.mul hW.aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    change ‖(vectorNormSq z.2 - (r : ℝ)) * W z‖ ≤ ‖vectorNormSq z.2 - (r : ℝ)‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hWb z))

theorem hasDerivAt_averaged_signed_logistic_power {m r : ℕ}
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0 < h) (σ : ℝ) (n : ℕ) :
    HasDerivAt (fun t => ∫ x, ∫ g, (vectorNormSq g - (r : ℝ)) *
      ((upperFaceSmoother a h hh).shiftOffsets (σ * t)).F
        (Matrix.mulVec u (x + σ • g)) ^ (n + 1) ∂standardGaussian r ∂μ)
      ((((n : ℝ) + 1) / h * ∫ x, ∫ g, (vectorNormSq g - (r : ℝ)) *
        ((upperFaceSmoother a h hh).F (Matrix.mulVec u (x + σ • g)) ^ (n + 1) *
          (upperFaceSmoother a h hh).theta (Matrix.mulVec u (x + σ • g)))
            ∂standardGaussian r ∂μ) * σ) 0 := by
  let s := upperFaceSmoother a h hh
  let V : Vector r × Vector r → Vector m := fun z => Matrix.mulVec u (z.1 + σ • z.2)
  let P : Vector r × Vector r → ℝ := fun z => vectorNormSq z.2 - (r : ℝ)
  have hp : Integrable P (μ.prod (standardGaussian r)) := by
    simpa only [one_mul] using (integrable_const (μ := μ) (1 : ℝ)).mul_prod
      ((SignedSurface.standardGaussian_integrable_vectorNormSq r).sub (integrable_const (r : ℝ)))
  have hFi (t : ℝ) : Integrable (fun z => P z * (s.shiftOffsets t).F (V z) ^ (n + 1))
      (μ.prod (standardGaussian r)) := by
    apply integrable_gaussian_radial_product_weight μ
      (fun z => (s.shiftOffsets t).F (V z) ^ (n + 1)) (by
        exact (((s.shiftOffsets t).continuous_F.measurable.comp (by fun_prop)).pow_const _))
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ((s.shiftOffsets t).F_pos _).le _)]
    exact pow_le_one₀ ((s.shiftOffsets t).F_pos _).le ((s.shiftOffsets t).F_le_one _)
  have hWi : Integrable (fun z => P z * (s.F (V z) ^ (n + 1) * s.theta (V z)))
      (μ.prod (standardGaussian r)) := by
    apply integrable_gaussian_radial_product_weight μ _
      (((s.continuous_F.measurable.comp (by fun_prop)).pow_const _).mul
        ((SignedSurface.continuous_smoother_theta s).measurable.comp (by fun_prop)))
    intro z
    have hw := SignedSurface.smoother_power_weight_bounds s n (V z)
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hw.1] using hw.2
  have hd := (hasDerivAt_integral_signed_smoother_power (μ.prod (standardGaussian r)) V
    (by fun_prop) P hp s n (σ * 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul σ)
  have hs0 : s.shiftOffsets 0 = s := by
    cases s
    simp [FaceSmoother.shiftOffsets]
  simp only [mul_zero, mul_one, hs0] at hd
  convert hd using 1
  · funext t
    exact (integral_prod _ (hFi (σ * t))).symm
  · rw [integral_prod _ hWi]
    rfl

theorem averaged_logistic_power_trace_le_of_L1_budget {m r : ℕ}
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (a : Vector m) {h σ B : ℝ} (hh : 0 < h) (hσ : 0 < σ)
    (hDi : ∀ b : Vector m, Integrable (fun x => gaussianThresholdDerivative u
      (fun j => (b j - faceDot (u j) x) / σ)) μ)
    (hB : ∀ b : Vector m, (∫ x, |gaussianThresholdDerivative u
      (fun j => (b j - faceDot (u j) x) / σ)| ∂μ) ≤ B) (n : ℕ) :
    |∫ x, ∫ g, (vectorNormSq g - (r : ℝ)) *
      ((upperFaceSmoother a h hh).F (Matrix.mulVec u (x + σ • g)) ^ (n + 1) *
        (upperFaceSmoother a h hh).theta (Matrix.mulVec u (x + σ • g)))
          ∂standardGaussian r ∂μ| ≤ h * B / (σ * ((n : ℝ) + 1)) := by
  let H : ℝ → ℝ := fun t => ∫ x, ∫ g, (vectorNormSq g - (r : ℝ)) *
    ((upperFaceSmoother a h hh).shiftOffsets (σ * t)).F
      (Matrix.mulVec u (x + σ • g)) ^ (n + 1) ∂standardGaussian r ∂μ
  have hb0 : 0 ≤ B := (integral_nonneg (fun _ => abs_nonneg _)).trans (hB a)
  have hder := hasDerivAt_averaged_signed_logistic_power μ u a hh σ n
  have hd : |deriv H 0| ≤ B := by
    change ‖deriv H 0‖ ≤ B
    apply norm_deriv_le_of_lip' hb0
    exact Eventually.of_forall (fun t => by
      simpa only [H, Real.norm_eq_abs, sub_zero] using
        averaged_signed_logistic_power_increment_le_of_L1_budget μ u hu hi a hh hσ hDi hB n 0 t)
  change |deriv H 0| ≤ B at hd
  rw [hder.deriv] at hd
  rw [abs_mul, abs_mul, abs_of_pos hσ, abs_of_pos (div_pos (by positivity) hh)] at hd
  apply (le_div_iff₀ (mul_pos hσ (by positivity))).mpr
  have hx := mul_le_mul_of_nonneg_right hd hh.le
  convert hx using 1 <;> (try field_simp [hh.ne']) <;> ring

end

end RectangleCLT.Companion.SplitV4
