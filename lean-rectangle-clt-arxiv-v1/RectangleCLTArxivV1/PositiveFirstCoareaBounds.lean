import RectangleCLTArxivV1.PositiveFirstCoarea
import RectangleCLTArxivV1.PositiveMixedCoareaBounds

/-! Global first-primitive bounds for positive mass and pair-plane tests.
These estimates hold at every threshold, without boundary slack. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology NNReal
noncomputable section
set_option maxHeartbeats 1000000

theorem norm_positivePlaneThreshold_le_two {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (e q : Vector r)
    (he : vectorNormSq e=1) (hq : vectorNormSq q=1) :
    ‖gaussianFiniteWeightedThreshold s u b (positiveGaussianPlaneTest e q)‖≤2 := by
  rw [Real.norm_eq_abs]
  exact (abs_gaussianFiniteWeightedThreshold_le s u b _ (integrable_positiveGaussianPlaneTest e q)).trans_eq
    (integral_positiveGaussianPlaneTest e q he hq)

theorem norm_positiveMassThreshold_le_one {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) :
    ‖gaussianFiniteWeightedThreshold s u b (fun _ => 1)‖≤1 := by
  have hb := gaussianFiniteWeightedThreshold_one_bounds s u b
  simpa only [Real.norm_eq_abs,abs_of_nonneg hb.1] using hb.2

theorem norm_positivePlaneFirstSection_density_le {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (e q : Vector r)
    (he : vectorNormSq e=1) (hq : vectorNormSq q=1) (heq : faceDot e q=0) (t : ℝ) :
    ‖gaussianPDFReal 0 1 t*gaussianFiniteWeightedSection s u b e (positiveGaussianPlaneTest e q) t‖≤
      3*positiveMixedGaussianPeak := by
  rw [gaussianFiniteWeightedSection_planeTest_eq s u b e q he heq t]
  unfold positiveMixedPlaneFacetWeight
  have hb := gaussianFiniteWeightedThreshold_plane_bounds s
    (fun k => gaussianNormalProjection e (u k)) (fun k => b k-t*faceDot (u k) e) q t
  rw [hq] at hb
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),abs_of_nonneg hb.1]
  have hh := mul_le_mul_of_nonneg_left hb.2 (gaussianPDFReal_nonneg 0 1 t)
  have h1 := gaussianPDFReal_le_positiveMixedGaussianPeak t
  have h2 := gaussianPDFReal_sq_le_positiveMixedGaussianPeak t
  exact hh.trans (by nlinarith)

theorem norm_positiveMassFirstSection_density_le {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (e : Vector r) (t : ℝ) :
    ‖gaussianPDFReal 0 1 t*gaussianFiniteWeightedSection s u b e (fun _ => 1) t‖≤positiveMixedGaussianPeak := by
  rw [gaussianFiniteWeightedSection_one_eq_sectionProbability,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
    abs_of_nonneg (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)]
  exact (mul_le_mul_of_nonneg_left (gaussianThresholdSectionProbability_le_one s u b e t)
    (gaussianPDFReal_nonneg 0 1 t)).trans (by simpa only [mul_one] using gaussianPDFReal_le_positiveMixedGaussianPeak t)

/-- Uniform first-coordinate Lipschitz from genuine weighted Fubini and
an actual normal slice-density bound. -/
theorem lipschitzWith_weightedThreshold_update_of_section_bound {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hj : j∈s)
    (hu : vectorNormSq (u j)=1) (P : Vector (n+1) → ℝ) (hPm : Measurable P)
    (hPi : Integrable P (standardGaussian (n+1))) (C : ℝ≥0)
    (hC : ∀ t,‖gaussianPDFReal 0 1 t*gaussianFiniteWeightedSection (s.erase j) u b (u j) P t‖≤C) :
    LipschitzWith C (fun z => gaussianFiniteWeightedThreshold s u (Function.update b j z) P) := by
  have hi := standardRealGaussian_integrable_density_mul
    (integrable_gaussianFiniteWeightedSection (s.erase j) u b (u j) hu P hPm hPi)
  apply LipschitzWith.of_dist_le_mul
  intro c d
  rw [dist_eq_norm,gaussianFiniteWeightedThreshold_update_eq_section_integral s u b j hj (u j) hu
    (show (0:ℝ)<1 by norm_num) (by simp) P hPm hPi c,
    gaussianFiniteWeightedThreshold_update_eq_section_integral s u b j hj (u j) hu
      (show (0:ℝ)<1 by norm_num) (by simp) P hPm hPi d]
  simp only [div_one]
  rw [intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
  simpa only [Real.dist_eq] using intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hC t)

theorem lipschitzWith_positivePlaneThreshold_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (q : Vector (n+1))
    (hu : vectorNormSq (u j)=1) (hq : vectorNormSq q=1) (heq : faceDot (u j) q=0) :
    LipschitzWith ⟨3*positiveMixedGaussianPeak,mul_nonneg (by norm_num) positiveMixedGaussianPeak_nonneg⟩
      (fun z => gaussianFiniteWeightedThreshold Finset.univ u (Function.update b j z)
        (positiveGaussianPlaneTest (u j) q)) :=
  lipschitzWith_weightedThreshold_update_of_section_bound Finset.univ u b j (Finset.mem_univ _) hu _
    (measurable_positiveGaussianPlaneTest _ _) (integrable_positiveGaussianPlaneTest _ _) _
    (norm_positivePlaneFirstSection_density_le _ _ _ _ _ hu hq heq)

theorem lipschitzWith_positiveMassThreshold_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1) :
    LipschitzWith ⟨positiveMixedGaussianPeak,positiveMixedGaussianPeak_nonneg⟩
      (fun z => gaussianFiniteWeightedThreshold Finset.univ u (Function.update b j z) (fun _ => 1)) :=
  lipschitzWith_weightedThreshold_update_of_section_bound Finset.univ u b j (Finset.mem_univ _) hu _
    measurable_const (integrable_const _) _ (norm_positiveMassFirstSection_density_le _ _ _ _)

end
end RectangleCLTArxivV1
