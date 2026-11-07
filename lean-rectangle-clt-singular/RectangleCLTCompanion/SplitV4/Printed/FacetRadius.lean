import RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusMoments
import RectangleCLTCompanion.SplitV4.AveragedThresholdBound

/-! The printed facet fiber with L1 furnished by the rank-two radial tail. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
theorem gaussianThresholdFirst_le_weighted_facet_event_from_radial_tail {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Real.exp (-(3 : ℝ) / 2) * (1 + b j ^ 2) * gaussianThresholdFirst u b j / 32 ≤
      ∫ g, (gaussianFacetEvent u b j).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  let F : Vector (n + 1) → ℝ :=
    (gaussianFacetEvent u b j).indicator (fun g => thresholdProjectionRadius u g ^ 3)
  have hF : Measurable F := ((measurable_thresholdProjectionRadius u).pow_const 3).indicator
    (measurableSet_gaussianFacetEvent u b j)
  have hFi : Integrable F (standardGaussian (n + 1)) :=
    (thresholdProjectionRadius_second_third_moments_from_radial_tail hm u).2.1.indicator (measurableSet_gaussianFacetEvent u b j)
  have hF0 (g) : 0 ≤ F g := Set.indicator_nonneg (fun x _ =>
    pow_nonneg (zero_le_one.trans (thresholdProjectionRadius_ge_one u x)) 3) g
  have hprod := (integrable_gaussianNormalSectionMap_iff (u j) hu F hF).mpr hFi
  let V : Set (Vector (n + 1)) := {z | ∀ l, l ≠ j → faceDot (u l) (gaussianFacetBase u b j z) < b l}
  have hV : MeasurableSet V := by
    unfold V
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun l => MeasurableSet.iInter (fun _ =>
      measurableSet_lt ((measurable_thresholdDot _).comp
        (SignedSurface.measurable_gaussianSectionPoint _ _)) measurable_const))
  let c := Real.exp (-(3 : ℝ) / 2) * (1 + b j ^ 2) * gaussianPDFReal 0 1 (b j) / 32
  have hpoint : ∀ᵐ z ∂standardGaussian (n + 1),
      V.indicator (fun _ => c) z ≤ ∫ t, F (SignedSurface.gaussianSectionPoint (u j) t z)
        ∂gaussianReal 0 1 := by
    filter_upwards [hprod.prod_left_ae] with z hz
    by_cases hv : z ∈ V
    · rw [Set.indicator_of_mem hv]
      have hbnd := thresholdFacet_fiber_lower u j hu (b j) (gaussianFacetBase u b j z)
        (SignedSurface.gaussianSectionPoint_on_hyperplane _ _ hu z)
      apply hbnd.trans
      apply normal_integral_dominates_translated_fiber
        (fun t => F (SignedSurface.gaussianSectionPoint (u j) t z))
        (fun t => thresholdProjectionRadius u (gaussianFacetBase u b j z + t • u j) ^ 3)
        hz (fun t => hF0 _) (b j) (1 / (4 * thresholdProjectionRadius u (gaussianFacetBase u b j z)))
      intro t ht
      have he : SignedSurface.gaussianSectionPoint (u j) (b j + t) z ∈ gaussianFacetEvent u b j := by
        rw [gaussianFacetEvent_section u b j hu]
        exact ⟨hv, by simpa only [add_sub_cancel_left] using ht⟩
      dsimp only [F]
      rw [Set.indicator_of_mem he, gaussianSectionPoint_add_parameter]
      rfl
    · rw [Set.indicator_of_not_mem hv]
      exact integral_nonneg (fun t => hF0 _)
  have hmineq := integral_mono_ae
    ((integrable_const c).indicator hV) hprod.integral_prod_right hpoint
  have hmass : (∫ z, V.indicator (fun _ => c) z ∂standardGaussian (n + 1)) =
      Real.exp (-(3 : ℝ) / 2) * (1 + b j ^ 2) * gaussianThresholdFirst u b j / 32 := by
    rw [integral_indicator_const _ hV, gaussianThresholdFirst_eq_section u b j hu hi,
      gaussianThresholdSectionProbability_eq_strict u b j hi]
    change (standardGaussian (n + 1)).real V * c = _
    dsimp only [c, V, gaussianFacetBase]
    ring
  rw [hmass] at hmineq
  apply hmineq.trans_eq
  rw [← integral_prod_symm _ hprod]
  exact integral_gaussianNormalSectionMap (u j) hu F hF

theorem abs_gaussianThreshold_facet_term_le_mass_from_radial_tail {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    |(b j ^ 2 - 1) * gaussianThresholdFirst u b j| ≤ thresholdGeometryConstant *
      ∫ g, (gaussianFacetEvent u b j).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  have hfirst : 0 ≤ gaussianThresholdFirst u b j := by
    rw [gaussianThresholdFirst_eq_section u b j hu hi]
    exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)
  have hmass := gaussianThresholdFirst_le_weighted_facet_event_from_radial_tail hm u b j hu hi
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
      _ = _ := by rw [show Real.exp ((3 : ℝ) / 2) * Real.exp (-(3 : ℝ) / 2) = 1 by rw [← Real.exp_add]; norm_num, one_mul]
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


end
end RectangleCLT.Companion.SplitV4.Printed
