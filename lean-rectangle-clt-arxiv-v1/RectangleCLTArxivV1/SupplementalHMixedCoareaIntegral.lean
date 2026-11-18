import RectangleCLTArxivV1.SupplementalHWeightedThresholdDerivative
import RectangleCLTArxivV1.SupplementalHPairSectionTrace

/-! Genuine weighted one-normal Gaussian disintegration, retaining an
arbitrary finite family and the exact nonunit normal Jacobian. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def gaussianFiniteWeightedThreshold {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (F : Vector r → ℝ) : ℝ :=
  ∫ g,(gaussianFiniteThresholdEvent s u b).indicator F g ∂standardGaussian r

def gaussianFiniteWeightedSection {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (q : Vector r) (F : Vector r → ℝ) (t : ℝ) : ℝ :=
  ∫ g,(gaussianFiniteThresholdEvent s u b).indicator F (gaussianSectionPoint q t g) ∂standardGaussian r

theorem measurable_gaussianFiniteWeightedSection {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (q : Vector r) (F : Vector r → ℝ)
    (hF : Measurable F) : Measurable (gaussianFiniteWeightedSection s u b q F) := by
  exact (((hF.indicator (measurableSet_gaussianFiniteThresholdEvent s u b)).comp
    (measurable_gaussianNormalSectionMap q)).stronglyMeasurable.integral_prod_right').measurable

theorem integrable_gaussianFiniteWeightedSection {m n : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector (n+1)) (b : Vector m) (q : Vector (n+1))
    (hq : vectorNormSq q=1) (F : Vector (n+1) → ℝ) (hF : Measurable F)
    (hFi : Integrable F (standardGaussian (n+1))) :
    Integrable (gaussianFiniteWeightedSection s u b q F) (gaussianReal 0 1) := by
  have hi := (integrable_gaussianNormalSectionMap_iff q hq
    ((gaussianFiniteThresholdEvent s u b).indicator F)
    (hF.indicator (measurableSet_gaussianFiniteThresholdEvent s u b))).mpr
      (hFi.indicator (measurableSet_gaussianFiniteThresholdEvent s u b))
  exact hi.integral_prod_left

/-- Actual weighted Gaussian Fubini with the selected constraint's
positive normal scale kept in the integration endpoint. -/
theorem gaussianFiniteWeightedThreshold_update_eq_section_integral {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m) (l : Fin m) (hl : l∈s)
    (q : Vector (n+1)) (hq : vectorNormSq q=1) {σ : ℝ} (hσ : 0<σ)
    (hul : u l=σ • q) (F : Vector (n+1) → ℝ) (hF : Measurable F)
    (hFi : Integrable F (standardGaussian (n+1))) (c : ℝ) :
    gaussianFiniteWeightedThreshold s u (Function.update b l c) F=
      ∫ t in Iic (c/σ),gaussianPDFReal 0 1 t*gaussianFiniteWeightedSection (s.erase l) u b q F t := by
  classical
  let E := gaussianFiniteThresholdEvent s u (Function.update b l c)
  let f := E.indicator F
  have hE : MeasurableSet E := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have hf : Measurable f := hF.indicator hE
  have hfi : Integrable f (standardGaussian (n+1)) := hFi.indicator hE
  have hmap := (integrable_gaussianNormalSectionMap_iff q hq f hf).mpr hfi
  change (∫ g,f g ∂standardGaussian (n+1))=_
  rw [← integral_gaussianNormalSectionMap q hq f hf,integral_prod _ hmap]
  have hinner (t : ℝ) : (∫ g,f (gaussianNormalSectionMap q (t,g)) ∂standardGaussian (n+1))=
      (Iic (c/σ)).indicator (gaussianFiniteWeightedSection (s.erase l) u b q F) t := by
    have hiff (g : Vector (n+1)) : gaussianSectionPoint q t g∈E ↔
        t≤c/σ ∧ gaussianSectionPoint q t g∈gaussianFiniteThresholdEvent (s.erase l) u b := by
      constructor
      · intro h
        refine ⟨?_,fun k hk => ?_⟩
        · have hh := h l hl
          rw [Function.update_self,hul,threshold_faceDot_smul_left,gaussianSectionPoint_on_hyperplane q t hq] at hh
          exact (le_div_iff₀ hσ).mpr (by simpa only [mul_comm] using hh)
        · simpa only [Function.update_of_ne (Finset.mem_erase.mp hk).1] using h k (Finset.mem_erase.mp hk).2
      · rintro ⟨ht,h⟩ k hk
        by_cases hkl : k=l
        · subst k
          rw [Function.update_self,hul,threshold_faceDot_smul_left,gaussianSectionPoint_on_hyperplane q t hq]
          simpa only [mul_comm] using (le_div_iff₀ hσ).mp ht
        · simpa only [Function.update_of_ne hkl] using h k (Finset.mem_erase.mpr ⟨hkl,hk⟩)
    by_cases ht : t≤c/σ
    · rw [indicator_of_mem (show t∈Iic (c/σ) from ht)]
      apply integral_congr_ae
      exact ae_of_all _ (fun g => by
        change E.indicator F (gaussianSectionPoint q t g)=_
        dsimp only
        have hh := hiff g
        by_cases hg : gaussianSectionPoint q t g∈gaussianFiniteThresholdEvent (s.erase l) u b
        · rw [indicator_of_mem (hh.mpr ⟨ht,hg⟩),indicator_of_mem hg]
        · rw [indicator_of_not_mem (fun h => hg (hh.mp h).2),indicator_of_not_mem hg])
    · rw [indicator_of_not_mem (show t∉Iic (c/σ) from ht)]
      have he (g : Vector (n+1)) : gaussianSectionPoint q t g∉E := fun h => ht (hiff g |>.mp h).1
      simp only [f,gaussianNormalSectionMap,indicator_of_not_mem (he _),integral_zero]
  rw [integral_congr_ae (ae_of_all _ hinner),
    integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num),← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by by_cases ht : t∈Iic (c/σ) <;> simp [ht,smul_eq_mul])

/-- Local weighted coarea from genuine Fubini and continuity of the
actual remaining section, with exact inverse normal scale. -/
theorem hasDerivAt_gaussianFiniteWeightedThreshold_update {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m) (l : Fin m) (hl : l∈s)
    (q : Vector (n+1)) (hq : vectorNormSq q=1) {σ : ℝ} (hσ : 0<σ)
    (hul : u l=σ • q) (F : Vector (n+1) → ℝ) (hF : Measurable F)
    (hFi : Integrable F (standardGaussian (n+1))) (c : ℝ)
    (hcont : ContinuousAt (gaussianFiniteWeightedSection (s.erase l) u b q F) (c/σ)) :
    HasDerivAt (fun t => gaussianFiniteWeightedThreshold s u (Function.update b l t) F)
      ((gaussianPDFReal 0 1 (c/σ)/σ)*gaussianFiniteWeightedSection (s.erase l) u b q F (c/σ)) c := by
  have hm := (measurable_gaussianPDFReal 0 1).mul (measurable_gaussianFiniteWeightedSection (s.erase l) u b q F hF)
  have hi := standardRealGaussian_integrable_density_mul
    (integrable_gaussianFiniteWeightedSection (s.erase l) u b q hq F hF hFi)
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have hd := hasDerivAt_integral_Iic_of_continuousAt_integrable _ hm.stronglyMeasurable hi (c/σ)
    (hpdf.continuousAt.mul hcont)
  have hd' := hd.comp c ((hasDerivAt_id c).div_const σ)
  have hh := hd'.congr_of_eventuallyEq (Eventually.of_forall
    (fun t => gaussianFiniteWeightedThreshold_update_eq_section_integral s u b l hl q hq hσ hul F hF hFi t))
  convert hh using 1 <;> ring

end
end RectangleCLTArxivV1
