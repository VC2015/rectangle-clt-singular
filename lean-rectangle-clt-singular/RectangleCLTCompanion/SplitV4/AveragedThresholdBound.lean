import RectangleCLTCompanion.SplitV4.AveragedThreshold
import RectangleCLTCompanion.SplitV4.GaussianThresholdIdentity
import RectangleCLTCompanion.SplitV4.GaussianThresholdPairTubes

/-! The averaged Gaussian threshold derivative of Appendix B.5. The layer
estimate is proved from the actual hard-CDF identities and disjoint genuine
facet/ridge events, then integrated against the actual concentrated base. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option maxHeartbeats 1000000

def thresholdGeometryConstant : ℝ := 2048 * Real.exp ((3 : ℝ) / 2)

theorem thresholdGeometryConstant_pos : 0 < thresholdGeometryConstant := by
  unfold thresholdGeometryConstant
  positivity

def gaussianAdaptiveOuterEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : Set (Vector r) :=
  (fun g : Vector r => ((0 : Vector r), g)) ⁻¹' adaptiveThresholdEvent u b 1 (thresholdProjectionRadius u)

theorem measurableSet_gaussianAdaptiveOuterEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) :
    MeasurableSet (gaussianAdaptiveOuterEvent u b) := by
  have hmap : Measurable (fun g : Vector r => ((0 : Vector r), g)) :=
    measurable_const.prodMk measurable_id
  exact (measurableSet_adaptiveThresholdEvent u b 1 (measurable_thresholdProjectionRadius u)).preimage hmap

theorem thresholdsFromBase_one_zero {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) :
    thresholdsFromBase u b 1 (0 : Vector r) = b := by
  funext j
  have hz : faceDot (u j) (0 : Vector r) = 0 := by
    simp only [faceDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  change (b j - faceDot (u j) (0 : Vector r)) / 1 = b j
  rw [hz, sub_zero, div_one]

theorem mem_gaussianAdaptiveOuterEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (g : Vector r) :
    g ∈ gaussianAdaptiveOuterEvent u b ↔ g ∈ thresholdOuterLayer u b (1 / thresholdProjectionRadius u g) := by
  unfold gaussianAdaptiveOuterEvent
  rw [Set.mem_preimage]
  unfold adaptiveThresholdEvent
  rw [Set.mem_setOf_eq, thresholdsFromBase_one_zero]

private theorem threshold_exp_cancel : Real.exp ((3 : ℝ) / 2) * Real.exp (-(3 : ℝ) / 2) = 1 := by
  rw [← Real.exp_add]
  norm_num

theorem abs_gaussianThreshold_facet_term_le_mass {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    |(b j ^ 2 - 1) * gaussianThresholdFirst u b j| ≤ thresholdGeometryConstant *
      ∫ g, (gaussianFacetEvent u b j).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  have hfirst : 0 ≤ gaussianThresholdFirst u b j := by
    rw [gaussianThresholdFirst_eq_section u b j hu hi]
    exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)
  have hmass := gaussianThresholdFirst_le_weighted_facet_event hm u b j hu hi
  have hM : 0 ≤ ∫ g, (gaussianFacetEvent u b j).indicator
      (fun g => thresholdProjectionRadius u g ^ 3) g ∂standardGaussian (n + 1) := by
    apply integral_nonneg
    intro g
    exact Set.indicator_nonneg (fun x _ => pow_nonneg
      (zero_le_one.trans (thresholdProjectionRadius_ge_one u x)) 3) g
  have hc := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 32 * Real.exp ((3 : ℝ) / 2) by positivity)
  have hcancel : (32 * Real.exp ((3 : ℝ) / 2)) *
      (Real.exp (-(3 : ℝ) / 2) * (1 + b j ^ 2) * gaussianThresholdFirst u b j / 32) =
      (1 + b j ^ 2) * gaussianThresholdFirst u b j := by
    calc
      _ = (Real.exp ((3 : ℝ) / 2) * Real.exp (-(3 : ℝ) / 2)) *
          ((1 + b j ^ 2) * gaussianThresholdFirst u b j) := by ring
      _ = _ := by rw [threshold_exp_cancel, one_mul]
  rw [hcancel] at hc
  calc
    _ ≤ (1 + b j ^ 2) * gaussianThresholdFirst u b j := by
      rw [abs_mul, abs_of_nonneg hfirst]
      apply mul_le_mul_of_nonneg_right _ hfirst
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (sq_nonneg _), abs_one]; ring)
    _ ≤ _ := hc.trans (mul_le_mul_of_nonneg_right
      (show 32 * Real.exp ((3 : ℝ) / 2) ≤ thresholdGeometryConstant by
        unfold thresholdGeometryConstant
        exact mul_le_mul_of_nonneg_right (by norm_num : (32 : ℝ) ≤ 2048) (Real.exp_nonneg _)) hM)

theorem abs_gaussianThreshold_pair_term_le_mass {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m)
    (hu : ∀ k, vectorNormSq (u k) = 1) (hi : LinearIndependent ℝ u) :
    |(1 - faceDot (u j) (u l)) * (b j + b l) * gaussianThresholdMixed u b j l| ≤
      thresholdGeometryConstant * (if j = l then 0 else
        ∫ g, (gaussianPairEvent u b j l).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
          ∂standardGaussian (n + 1)) := by
  classical
  by_cases hjl : j = l
  · subst l
    have hself : faceDot (u j) (u j) = 1 := by simpa only [faceDot, vectorNormSq, pow_two] using hu j
    simp [hself]
  · rw [if_neg hjl]
    have hρ : 0 ≤ 1 - faceDot (u j) (u l) := by
      have hh := abs_real_inner_le_norm (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
      have hdot := SignedSurface.faceDot_eq_euclidean_inner (u j) (u l)
      change faceDot (u j) (u l) = ⟪projectionEuclideanVector (u j), projectionEuclideanVector (u l)⟫_ℝ at hdot
      rw [← hdot, thresholdEuclideanNormal_unit _ (hu j),
        thresholdEuclideanNormal_unit _ (hu l), mul_one] at hh
      exact sub_nonneg.mpr ((le_abs_self _).trans hh)
    have hmix := gaussianThresholdMixed_nonneg_of_ne u b j l hjl (hu j) hi
    have hmass := gaussianThresholdMixed_le_weighted_pair_event hm u b j l hjl (hu j) (hu l) hi
    have hc := mul_le_mul_of_nonneg_left hmass
      (show 0 ≤ thresholdGeometryConstant from thresholdGeometryConstant_pos.le)
    have hcancel : thresholdGeometryConstant *
        (Real.exp (-(3 : ℝ) / 2) * (1 - faceDot (u j) (u l)) * |b j + b l| *
          gaussianThresholdMixed u b j l / 2048) =
        (1 - faceDot (u j) (u l)) * |b j + b l| * gaussianThresholdMixed u b j l := by
      unfold thresholdGeometryConstant
      calc
        _ = (Real.exp ((3 : ℝ) / 2) * Real.exp (-(3 : ℝ) / 2)) *
            ((1 - faceDot (u j) (u l)) * |b j + b l| * gaussianThresholdMixed u b j l) := by ring
        _ = _ := by rw [threshold_exp_cancel, one_mul]
    rw [hcancel] at hc
    simpa only [abs_mul, abs_of_nonneg hρ, abs_of_nonneg hmix] using hc

theorem continuous_gaussianThresholdDerivative_for_averaging {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Continuous (gaussianThresholdDerivative u) := by
  have he : gaussianThresholdDerivative u = fun b =>
      (∑ j, (b j ^ 2 - 1) * gaussianThresholdFirst u b j) - (1 / 2 : ℝ) *
        ∑ j, ∑ l, (1 - faceDot (u j) (u l)) * (b j + b l) * gaussianThresholdMixed u b j l :=
    funext (fun b => gaussianThresholdDerivative_identity u b hu hi)
  rw [he]
  apply Continuous.sub
  · exact continuous_finset_sum _ (fun j _ =>
      ((continuous_apply j).pow 2 |>.sub continuous_const).mul (continuous_gaussianThresholdFirst u j (hu j) hi))
  · apply continuous_const.mul
    apply continuous_finset_sum
    intro j _
    apply continuous_finset_sum
    intro l _
    exact (continuous_const.mul ((continuous_apply j).add (continuous_apply l))).mul
      (continuous_gaussianThresholdMixed u j l (hu j) hi)

/-- The genuine adaptive-layer estimate. It follows from the actual radial
trace identity, actual mixed derivatives and disjoint outward tube masses. -/
theorem gaussianThresholdDerivative_le_adaptiveLayer {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    |gaussianThresholdDerivative u b| ≤ (2 * thresholdGeometryConstant) *
      ∫ g, (gaussianAdaptiveOuterEvent u b).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  classical
  let γ := standardGaussian (n + 1)
  let W : Vector (n + 1) → ℝ := fun g => thresholdProjectionRadius u g ^ 3
  let F : Fin m → Vector (n + 1) → ℝ := fun j => (gaussianFacetEvent u b j).indicator W
  let P : Fin m → Fin m → Vector (n + 1) → ℝ := fun j l =>
    if j = l then 0 else (gaussianPairEvent u b j l).indicator W
  have hW : Integrable W γ := (thresholdProjectionRadius_moment hm u 3).1
  have hW0 (g) : 0 ≤ W g := pow_nonneg
    (zero_le_one.trans (thresholdProjectionRadius_ge_one u g)) 3
  have hF (j : Fin m) : Integrable (F j) γ := hW.indicator (measurableSet_gaussianFacetEvent u b j)
  have hP (j l : Fin m) : Integrable (P j l) γ := by
    by_cases h : j = l
    · simpa only [P, if_pos h] using (integrable_zero (Vector (n + 1)) ℝ γ)
    · simpa only [P, if_neg h] using hW.indicator (measurableSet_gaussianPairEvent u b j l)
  have hP0 (j l : Fin m) (g) : 0 ≤ P j l g := by
    by_cases h : j = l
    · simp only [P, if_pos h, Pi.zero_apply, le_refl]
    · simp only [P, if_neg h]
      exact Set.indicator_nonneg (fun x _ => hW0 x) g
  have hpmass (j l : Fin m) : (∫ g, P j l g ∂γ) =
      if j = l then 0 else ∫ g, (gaussianPairEvent u b j l).indicator W g ∂γ := by
    by_cases h : j = l
    · simp only [P, if_pos h, Pi.zero_apply, integral_zero]
    · simp only [P, if_neg h]
  let A : Fin m → ℝ := fun j => (b j ^ 2 - 1) * gaussianThresholdFirst u b j
  let B : Fin m → Fin m → ℝ := fun j l =>
    (1 - faceDot (u j) (u l)) * (b j + b l) * gaussianThresholdMixed u b j l
  have hA : (∑ j, |A j|) ≤ thresholdGeometryConstant * ∑ j, ∫ g, F j g ∂γ := by
    calc
      _ ≤ ∑ j, thresholdGeometryConstant * ∫ g, F j g ∂γ :=
        Finset.sum_le_sum (fun j _ => by
          simpa only [A, F, γ, W] using abs_gaussianThreshold_facet_term_le_mass hm u b j (hu j) hi)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hB : (∑ j, ∑ l, |B j l|) ≤ thresholdGeometryConstant * ∑ j, ∑ l, ∫ g, P j l g ∂γ := by
    calc
      _ ≤ ∑ j, ∑ l, thresholdGeometryConstant * ∫ g, P j l g ∂γ := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro l _
        rw [hpmass]
        simpa only [B, γ, W] using abs_gaussianThreshold_pair_term_le_mass hm u b j l hu hi
      _ = _ := by simp only [Finset.mul_sum]
  have hdouble : |∑ j, ∑ l, B j l| ≤ ∑ j, ∑ l, |B j l| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))
  have htri : |gaussianThresholdDerivative u b| ≤ (∑ j, |A j|) + ∑ j, ∑ l, |B j l| := by
    have hid : gaussianThresholdDerivative u b = (∑ j, A j) - (1 / 2 : ℝ) * (∑ j, ∑ l, B j l) :=
      gaussianThresholdDerivative_identity u b hu hi
    rw [hid]
    apply (abs_sub (∑ j, A j) ((1 / 2 : ℝ) * (∑ j, ∑ l, B j l))).trans
    apply add_le_add
    · exact Finset.abs_sum_le_sum_abs _ _
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      apply (mul_le_mul_of_nonneg_left hdouble (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
      exact mul_le_of_le_one_left (Finset.sum_nonneg (fun j _ =>
        Finset.sum_nonneg (fun l _ => abs_nonneg (B j l)))) (by norm_num)
  have hFsum : Integrable (fun g => ∑ j, F j g) γ := integrable_finset_sum _ (fun j _ => hF j)
  have hPsum : Integrable (fun g => ∑ j, ∑ l, P j l g) γ :=
    integrable_finset_sum _ (fun j _ => integrable_finset_sum _ (fun l _ => hP j l))
  have hOuter : Integrable ((gaussianAdaptiveOuterEvent u b).indicator W) γ :=
    hW.indicator (measurableSet_gaussianAdaptiveOuterEvent u b)
  have hhp (j l : Fin m) (h : j ≠ l) :
      projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0 :=
    (thresholdPair_sum_sub_ne_zero_of_independent u hi j l h).1
  have hhm (j l : Fin m) (h : j ≠ l) :
      projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0 :=
    (thresholdPair_sum_sub_ne_zero_of_independent u hi j l h).2
  have hpoint (g : Vector (n + 1)) : (∑ j, F j g) + (∑ j, ∑ l, P j l g) ≤
      2 * (gaussianAdaptiveOuterEvent u b).indicator W g := by
    have hh := gaussianThreshold_facet_pair_weighted_sum_le u b hu hhp hhm W hW0 g
    have heval : (thresholdOuterLayer u b (1 / thresholdProjectionRadius u g)).indicator W g =
        (gaussianAdaptiveOuterEvent u b).indicator W g := by
      by_cases hg : g ∈ gaussianAdaptiveOuterEvent u b
      · have hg' : g ∈ thresholdOuterLayer u b (1 / thresholdProjectionRadius u g) :=
          (mem_gaussianAdaptiveOuterEvent u b g).mp hg
        rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg']
      · have hg' : g ∉ thresholdOuterLayer u b (1 / thresholdProjectionRadius u g) :=
          fun h => hg ((mem_gaussianAdaptiveOuterEvent u b g).mpr h)
        rw [Set.indicator_of_not_mem hg, Set.indicator_of_not_mem hg']
    rw [heval] at hh
    simpa only [F, P, ite_apply, Pi.zero_apply] using hh
  have hmass : (∑ j, ∫ g, F j g ∂γ) + (∑ j, ∑ l, ∫ g, P j l g ∂γ) ≤
      2 * ∫ g, (gaussianAdaptiveOuterEvent u b).indicator W g ∂γ := by
    calc
      _ = ∫ g, (∑ j, F j g) + ∑ j, ∑ l, P j l g ∂γ := by
        rw [integral_add hFsum hPsum, integral_finset_sum _ (fun j _ => hF j),
          integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun l _ => hP j l))]
        simp_rw [integral_finset_sum _ (fun l _ => hP _ l)]
      _ ≤ ∫ g, 2 * (gaussianAdaptiveOuterEvent u b).indicator W g ∂γ :=
        integral_mono (hFsum.add hPsum) (hOuter.const_mul 2) hpoint
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ thresholdGeometryConstant *
        ((∑ j, ∫ g, F j g ∂γ) + ∑ j, ∑ l, ∫ g, P j l g ∂γ) :=
      htri.trans ((add_le_add hA hB).trans_eq (by ring))
    _ ≤ thresholdGeometryConstant * (2 * ∫ g, (gaussianAdaptiveOuterEvent u b).indicator W g ∂γ) :=
      mul_le_mul_of_nonneg_left hmass thresholdGeometryConstant_pos.le
    _ = _ := by ring

theorem gaussianThresholdDerivative_abs_le_radius_moment {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    |gaussianThresholdDerivative u b| ≤ (2 * thresholdGeometryConstant) *
      ∫ g, thresholdProjectionRadius u g ^ 3 ∂standardGaussian (n + 1) := by
  have h3 := (thresholdProjectionRadius_moment hm u 3).1
  apply (gaussianThresholdDerivative_le_adaptiveLayer hm u b hu hi).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) thresholdGeometryConstant_pos.le)
  apply integral_mono (h3.indicator (measurableSet_gaussianAdaptiveOuterEvent u b)) h3
  intro g
  by_cases hg : g ∈ gaussianAdaptiveOuterEvent u b
  · simp only [Set.indicator_of_mem hg, le_refl]
  · simp only [Set.indicator_of_not_mem hg]
    exact pow_nonneg (zero_le_one.trans (thresholdProjectionRadius_ge_one u g)) 3

theorem integrable_gaussianThresholdDerivative_base_succ {m n : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector (n + 1))) [IsProbabilityMeasure μ]
    (u : Fin m → Vector (n + 1)) (a : Vector m) (σ : ℝ)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Integrable (fun v => gaussianThresholdDerivative u (thresholdsFromBase u a σ v)) μ := by
  have hb : Measurable (fun v => thresholdsFromBase u a σ v) :=
    measurable_pi_lambda _ (fun j => (measurable_const.sub (measurable_thresholdDot (u j))).div_const σ)
  have hd := (continuous_gaussianThresholdDerivative_for_averaging u hu hi).measurable.comp hb
  apply (integrable_const ((2 * thresholdGeometryConstant) *
    ∫ g, thresholdProjectionRadius u g ^ 3 ∂standardGaussian (n + 1))).mono' hd.aestronglyMeasurable
  exact ae_of_all _ (fun v => by
    rw [Real.norm_eq_abs]
    exact gaussianThresholdDerivative_abs_le_radius_moment hm u _ hu hi)

/-- Genuine integrability needs no moment assumption on the base and no
lower bound on the Gaussian scale. -/
theorem integrable_gaussianThresholdDerivative_base {m r : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (σ : ℝ)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Integrable (fun v => gaussianThresholdDerivative u (thresholdsFromBase u a σ v)) μ := by
  cases r with
  | zero =>
      let j : Fin m := ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hm⟩
      have hh := hu j
      simp [vectorNormSq] at hh
  | succ n => exact integrable_gaussianThresholdDerivative_base_succ hm μ u a σ hu hi

def averagedThresholdConstant : ℝ := 2 * thresholdGeometryConstant * Real.exp 36

theorem averagedThresholdConstant_pos : 0 < averagedThresholdConstant := by
  unfold averagedThresholdConstant
  exact mul_pos (mul_pos (by norm_num) thresholdGeometryConstant_pos) (Real.exp_pos _)

theorem averagedGaussianThresholdDerivative_bound_succ {m n : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector (n + 1))) [IsProbabilityMeasure μ]
    (u : Fin m → Vector (n + 1)) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ L) (hc : ConcentratedThresholdBase μ u C δ L) :
    (∫ v, |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ∂μ) ≤
      averagedThresholdConstant * C * (σ * L * Real.sqrt L + δ * L ^ 2) := by
  let γ := standardGaussian (n + 1)
  let R := thresholdProjectionRadius u
  let K : Vector (n + 1) × Vector (n + 1) → ℝ :=
    (adaptiveThresholdEvent u a σ R).indicator (fun vg => R vg.2 ^ 3)
  have h3 : Integrable (fun g => R g ^ 3) γ := (thresholdProjectionRadius_moment hm u 3).1
  have hw : Integrable (fun vg : Vector (n + 1) × Vector (n + 1) => R vg.2 ^ 3) (μ.prod γ) := by
    simpa only [one_mul] using (integrable_const (μ := μ) (1 : ℝ)).mul_prod h3
  have hK : Integrable K (μ.prod γ) :=
    hw.indicator (measurableSet_adaptiveThresholdEvent u a σ (measurable_thresholdProjectionRadius u))
  have hpoint (v : Vector (n + 1)) : |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ≤
      (2 * thresholdGeometryConstant) * ∫ g, K (v, g) ∂γ := by
    have hh := gaussianThresholdDerivative_le_adaptiveLayer hm u (thresholdsFromBase u a σ v) hu hi
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
  have hdi := (integrable_gaussianThresholdDerivative_base_succ hm μ u a σ hu hi).abs
  have hh := integral_mono hdi (hK.integral_prod_left.const_mul (2 * thresholdGeometryConstant)) hpoint
  rw [integral_const_mul] at hh
  have ha := concentratedBase_gaussian_adaptiveLayer_average hm μ u a hC hδ hσ hL hc
  calc
    _ ≤ (2 * thresholdGeometryConstant) * ∫ v, ∫ g, K (v, g) ∂γ ∂μ := hh
    _ ≤ (2 * thresholdGeometryConstant) *
        (C * Real.exp 36 * (σ * L * Real.sqrt L + δ * L ^ 2)) :=
      mul_le_mul_of_nonneg_left ha (mul_nonneg (by norm_num) thresholdGeometryConstant_pos.le)
    _ = _ := by unfold averagedThresholdConstant; ring

/-- Appendix B.5: the actual common-threshold derivative, averaged over a
concentrated base. The numerical constant is fixed before every law,
dimension, threshold, scale and concentration parameter. -/
theorem averagedGaussianThresholdDerivative_bound {m r : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ L) (hc : ConcentratedThresholdBase μ u C δ L) :
    (∫ v, |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ∂μ) ≤
      averagedThresholdConstant * C * (σ * L * Real.sqrt L + δ * L ^ 2) := by
  cases r with
  | zero =>
      let j : Fin m := ⟨0, lt_of_lt_of_le (by decide : 0 < 1) hm⟩
      have hh := hu j
      simp [vectorNormSq] at hh
  | succ n => exact averagedGaussianThresholdDerivative_bound_succ hm μ u a hu hi hC hδ hσ hL hc

theorem ConcentratedThresholdBase.mono_log {m r : ℕ} {μ : Measure (Vector r)}
    {u : Fin m → Vector r} {C δ L L' : ℝ}
    (hc : ConcentratedThresholdBase μ u C δ L) (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hL : L ≤ L') :
    ConcentratedThresholdBase μ u C δ L' := by
  intro a s hs
  exact (hc a s hs).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL)
    (mul_nonneg hC (add_nonneg hs.le hδ)))

def averagedThresholdPaperConstant : ℝ := 4 * averagedThresholdConstant

theorem averagedThresholdPaperConstant_pos : 0 < averagedThresholdPaperConstant :=
  mul_pos (by norm_num) averagedThresholdConstant_pos

/-- Face-count normalization permits `log(e m) ≤ 2L`, retaining the
original concentration parameter `L` and changing only a fixed constant. -/
theorem averagedGaussianThresholdDerivative_bound_of_log_le_two {m r : ℕ}
    (hm : 1 ≤ m) (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ 2 * L) (hc : ConcentratedThresholdBase μ u C δ L) :
    (∫ v, |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ∂μ) ≤
      averagedThresholdPaperConstant * C * (σ * L * Real.sqrt L + δ * L ^ 2) := by
  have hL0 : 0 ≤ L := by
    have hh : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
    linarith only [hh, hL]
  have hc' : ConcentratedThresholdBase μ u C δ (2 * L) :=
    hc.mono_log hC hδ (by linarith only [hL0])
  have hh := averagedGaussianThresholdDerivative_bound hm μ u a hu hi hC hδ hσ hL hc'
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
    _ ≤ averagedThresholdConstant * C *
        (σ * (2 * L) * Real.sqrt (2 * L) + δ * (2 * L) ^ 2) := hh
    _ ≤ averagedThresholdConstant * C * (4 * (σ * L * Real.sqrt L + δ * L ^ 2)) :=
      mul_le_mul_of_nonneg_left hcost (mul_nonneg averagedThresholdConstant_pos.le hC)
    _ = _ := by unfold averagedThresholdPaperConstant; ring

theorem threshold_dimensionLog_faces_le {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m ≤ 2 * p) :
    dimensionLog m ≤ 2 * dimensionLog p := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hmR : (m : ℝ) ≤ 2 * p := by exact_mod_cast hmp
  have hmono : dimensionLog m ≤ Real.log 2 + dimensionLog p := by
    unfold dimensionLog
    have hh := Real.log_le_log (mul_pos (Real.exp_pos 1) hm0)
      (mul_le_mul_of_nonneg_left hmR (Real.exp_pos 1).le)
    have he : Real.exp 1 * (2 * (p : ℝ)) = 2 * (Real.exp 1 * p) := by ring
    rw [he, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (mul_pos (Real.exp_pos 1) hp0).ne'] at hh
    exact hh
  have hlog : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh]
  have hpL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  linarith only [hmono, hlog, hpL]

/-- Exact rectangle-face normalization: up to `2p` actual faces use the
paper's original `L=log(e p)`, with no extra logarithmic hypothesis. -/
theorem averagedGaussianThresholdDerivative_rectangle_bound {m r p : ℕ}
    (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m ≤ 2 * p)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hc : ConcentratedThresholdBase μ u C δ (dimensionLog p)) :
    (∫ v, |gaussianThresholdDerivative u (thresholdsFromBase u a σ v)| ∂μ) ≤
      averagedThresholdPaperConstant * C *
        (σ * dimensionLog p * Real.sqrt (dimensionLog p) + δ * dimensionLog p ^ 2) :=
  averagedGaussianThresholdDerivative_bound_of_log_le_two hm μ u a hu hi hC hδ hσ
    (threshold_dimensionLog_faces_le hm hp hmp) hc

end
end RectangleCLT.Companion.SplitV4
