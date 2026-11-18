import RectangleCLTArxivV1.SupplementalHGammaAbsoluteFace
import RectangleCLTArxivV1.SupplementalHGammaFacetBudget

/-! The actual first-face sum in the cubic signed radial trace. Gamma
coarea is used before absolute values and before averaging the base. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem supplementalH_logistic_power_face_bounds {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0<h)
    (x : Vector r) (j : Fin m) (q : ℕ) :
    0≤logisticNullWeight u a h x^(q+1)*logisticFaceWeight u a h x j ∧
      logisticNullWeight u a h x^(q+1)*logisticFaceWeight u a h x j≤1 := by
  have hF : 0≤logisticNullWeight u a h x ∧ logisticNullWeight u a h x≤1 := by
    rw [←upperFaceSmoother_F u a h hh]
    exact ⟨(FaceSmoother.F_pos _ _).le,FaceSmoother.F_le_one _ _⟩
  have hP : 0≤logisticFaceWeight u a h x j ∧ logisticFaceWeight u a h x j≤1 := by
    rw [←upperFaceSmoother_pi u a h hh]
    exact ⟨(FaceSmoother.weights _ _).pi_nonneg _,
      ((FaceSmoother.weights _ _).pi_le_theta _).trans (FaceSmoother.weights _ _).theta_lt_one.le⟩
  exact ⟨mul_nonneg (pow_nonneg hF.1 _) hP.1,
    mul_le_one₀ (pow_le_one₀ hF.1 hF.2) hP.1 hP.2⟩

theorem integrable_gaussianAbsoluteFace_logistic_power {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0<h)
    (σ : ℝ) (x : Vector r) (j : Fin m) (q : ℕ) :
    Integrable (fun g => ((vectorNormSq g-(r:ℝ))*|faceDot (u j) g|)*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*
        logisticFaceWeight u a h (x+σ • g) j)) (standardGaussian r) := by
  have hm : Measurable (fun g => ((vectorNormSq g-(r:ℝ))*|faceDot (u j) g|)*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*logisticFaceWeight u a h (x+σ • g) j)) := by
    unfold logisticFaceWeight logisticNullWeight vectorNormSq faceDot
    fun_prop
  apply (integrable_gaussianAbsoluteFaceScore (u j)).norm.mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun g => by
    change |((vectorNormSq g-(r:ℝ))*|faceDot (u j) g|)*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*logisticFaceWeight u a h (x+σ • g) j)|≤
      |(vectorNormSq g-(r:ℝ))*(|faceDot (u j) g|)|
    rw [abs_mul]
    rw [abs_of_nonneg (supplementalH_logistic_power_face_bounds u a hh (x+σ • g) j q).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (supplementalH_logistic_power_face_bounds u a hh (x+σ • g) j q).2)

theorem integrable_gamma_absoluteFace_facet {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) (h σ : ℝ) (x : Vector (n+1)) (j : Fin m) (q : ℕ) :
    Integrable (fun e => |(gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ| *
      (gaussianPDFReal 0 1 ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)*
        Printed.thresholdSignedSection u
          (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j
          ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ))) (gammaRectangleLaw m q) := by
  let b := fun e k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ
  have hb : Measurable b := by unfold b gammaAdjustedThreshold faceDot; fun_prop
  have hm : Measurable (fun e => |b e j| *
      (gaussianPDFReal 0 1 (b e j)*Printed.thresholdSignedSection u (b e) j (b e j))) :=
    (((measurable_pi_apply j).comp hb).abs).mul
      (((measurable_gaussianPDFReal 0 1).comp ((measurable_pi_apply j).comp hb)).mul
        ((measurable_thresholdSignedSection_threshold u j).comp hb))
  apply (integrable_const (gaussianAbsoluteFaceDensityBudget (n+1))).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun e => by
    have ht := norm_gaussianAbsoluteFace_section_density_le u (b e) j (hu j) (b e j)
    convert ht using 1 <;> congr 1 <;> ring)

/-- Sum the original first faces before taking absolute values. The
right side is precisely the literal native J_f, with all hard faces kept. -/
theorem supplementalH_absoluteFace_soft_sum_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ) (x : Vector (n+1)) (q : ℕ) :
    (∫ g, ∑ j, ((vectorNormSq g-((n+1:ℕ):ℝ))*|faceDot (u j) g|)*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*logisticFaceWeight u a h (x+σ • g) j)
      ∂standardGaussian (n+1)) =
    (h/((q:ℝ)+1)/σ)*(∫ e, hardGaussianWeightedFacetIntegral u
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) ∂gammaRectangleLaw m q) := by
  classical
  rw [integral_finset_sum _ (fun j _ => integrable_gaussianAbsoluteFace_logistic_power u a hh σ x j q)]
  have hq : 0<(q:ℝ)+1 := by positivity
  have hj (j : Fin m) :
      (∫ g, ((vectorNormSq g-((n+1:ℕ):ℝ))*|faceDot (u j) g|)*
        (logisticNullWeight u a h (x+σ • g)^(q+1)*logisticFaceWeight u a h (x+σ • g) j)
        ∂standardGaussian (n+1)) =
      (h/((q:ℝ)+1)/σ)*(∫ e,
        |(gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ| *
          (gaussianPDFReal 0 1 ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)*
            Printed.thresholdSignedSection u
              (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j
              ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)) ∂gammaRectangleLaw m q) := by
    have he := supplementalH_absoluteFace_soft_coarea u hu a hh hσ x j q
    have hc : ((q:ℝ)+1)/h≠0 := (div_pos hq hh).ne'
    calc
      _ = (σ⁻¹*(∫ e,
        |(gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ| *
          (gaussianPDFReal 0 1 ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)*
            Printed.thresholdSignedSection u
              (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j
              ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)) ∂gammaRectangleLaw m q))/(((q:ℝ)+1)/h) :=
        (eq_div_iff hc).mpr (by simpa only [mul_comm] using he)
      _ = _ := by field_simp; ring
  simp_rw [hj]
  rw [←Finset.mul_sum,←integral_finset_sum _ (fun j _ => integrable_gamma_absoluteFace_facet u hu a h σ x j q)]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun e => by
    unfold hardGaussianWeightedFacetIntegral
    apply Finset.sum_congr rfl
    intro j _
    rw [hardGaussianFacetIntegral_eq_signedSection u _ j (hu j)])

end
end RectangleCLTArxivV1
