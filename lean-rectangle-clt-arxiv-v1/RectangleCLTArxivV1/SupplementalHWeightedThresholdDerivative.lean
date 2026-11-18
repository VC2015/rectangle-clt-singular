import RectangleCLTArxivV1.SupplementalHSectionTrace
import RectangleCLTArxivV1.SupplementalHGenericThreshold
import RectangleCLTArxivV1.SupplementalHCubicMoments

/-! Actual weighted first coarea derivative with local residual slack. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem continuousAt_weighted_gaussianFiniteThreshold_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hreg : ∀ j∈s, u j≠0 ∨ b j≠0) (f : Vector r → ℝ)
    (hf : Measurable f) (hfi : Integrable f (standardGaussian r)) :
    ContinuousAt (fun c : Vector m => ∫ g,
      (gaussianFiniteThresholdEvent s u c).indicator f g ∂standardGaussian r) b := by
  apply tendsto_integral_filter_of_dominated_convergence (fun g => ‖f g‖)
  · exact Eventually.of_forall (fun c =>
      (hf.indicator (measurableSet_gaussianFiniteThresholdEvent s u c)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun c => ae_of_all _ fun g => by
      by_cases hg : g ∈ gaussianFiniteThresholdEvent s u c <;> simp [hg])
  · exact hfi.norm
  · exact (gaussianFiniteThreshold_ae_no_boundary_of_slack s u b hreg).mono (fun g hg => by
      have hh := (gaussianFiniteThreshold_indicator_tendsto s u b g hg).mul_const (f g)
      have he (c : Vector m) : (gaussianFiniteThresholdEvent s u c).indicator f g =
          (gaussianFiniteThresholdEvent s u c).indicator (fun _ => (1 : ℝ)) g * f g := by
        by_cases hc : g ∈ gaussianFiniteThresholdEvent s u c <;> simp [hc]
      simpa only [← he] using hh)

theorem continuousAt_thresholdSignedSection_of_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (c₀ : ℝ)
    (hreg : ∀ l∈Finset.univ.erase j,
      gaussianNormalProjection (u j) (u l)≠0 ∨ b l-c₀*faceDot (u l) (u j)≠0) :
    ContinuousAt (Printed.thresholdSignedSection u b j) c₀ := by
  let s := Finset.univ.erase j
  let v := fun l => gaussianNormalProjection (u j) (u l)
  let c := fun t : ℝ => fun l => b l - t * faceDot (u l) (u j)
  let f := fun g => vectorNormSq (SignedSurface.gaussianSectionResidual (u j) g) - (r : ℝ)
  have hf : Measurable f := by
    exact (Finset.measurable_sum _ (fun k _ =>
      ((measurable_pi_apply k).comp (SignedSurface.measurable_gaussianSectionResidual (u j))).pow_const 2)).sub_const _
  have hfi : Integrable f (standardGaussian r) :=
    (SignedSurface.standardGaussian_integrable_sectionResidual_normSq (u j) hu).sub (integrable_const _)
  have hc : Continuous c := by fun_prop
  have he (t : ℝ) : Printed.thresholdSignedSection u b j t =
      (∫ g, (gaussianFiniteThresholdEvent s v (c t)).indicator f g ∂standardGaussian r) +
      t ^ 2 * gaussianFiniteThresholdCDF s v (c t) := by
    rw [gaussianFiniteThresholdCDF_eq_integral]
    rw [← integral_const_mul,
      ← integral_add (hfi.indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _))
        (((integrable_const (1 : ℝ)).indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _)).const_mul _)]
    unfold Printed.thresholdSignedSection
    change (∫ g, (gaussianFiniteThresholdEvent s v (c t)).indicator
      (fun g => vectorNormSq (SignedSurface.gaussianSectionPoint (u j) t g) - (r : ℝ)) g
      ∂standardGaussian r) = _
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by
      by_cases hg : g ∈ gaussianFiniteThresholdEvent s v (c t)
      · simp only [Printed.thresholdSignedSection, Set.indicator_of_mem hg]
        have hq := SignedSurface.vectorNormSq_gaussianSectionPoint (u j) t hu g
        have hr := SignedSurface.vectorNormSq_gaussianSectionResidual (u j) g hu
        dsimp only [f]
        linarith
      · simp only [Set.indicator_of_not_mem hg, mul_zero, add_zero])
  have hefun : Printed.thresholdSignedSection u b j = fun t =>
      (∫ g, (gaussianFiniteThresholdEvent s v (c t)).indicator f g ∂standardGaussian r) +
      t ^ 2 * gaussianFiniteThresholdCDF s v (c t) := funext he
  rw [hefun]
  exact ((continuousAt_weighted_gaussianFiniteThreshold_of_slack s v (c c₀) hreg f hf hfi).comp hc.continuousAt).add
    ((continuousAt_id.pow 2).mul
      ((continuousAt_gaussianFiniteThresholdCDF_of_slack s v (c c₀) hreg).comp hc.continuousAt))

theorem measurable_thresholdSignedSection_parameter {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) :
    Measurable (Printed.thresholdSignedSection u b j) := by
  let E : Set (ℝ × Vector r) := {z | ∀ l∈Finset.univ.erase j,
    faceDot (gaussianNormalProjection (u j) (u l)) z.2≤b l-z.1*faceDot (u l) (u j)}
  have hE : MeasurableSet E := by
    unfold E
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro l
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le ((continuous_faceDot_left _).measurable.comp measurable_snd)
      (measurable_const.sub (measurable_fst.mul_const _))
  let S := fun z : ℝ × Vector r => vectorNormSq (gaussianSectionPoint (u j) z.1 z.2)-(r:ℝ)
  have hS : Measurable S := by
    unfold S gaussianSectionPoint gaussianSectionResidual vectorNormSq faceDot
    fun_prop
  exact (hS.indicator hE).stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_gaussianAbsoluteFaceScore {r : ℕ} (u : Vector r) :
    Integrable (fun g => (vectorNormSq g-(r:ℝ))*|faceDot u g|) (standardGaussian r) := by
  have hi := (supplementalH_integrable_abs_linear_normSq u).sub
    ((standardGaussian_integrable_faceDot u).abs.const_mul (r:ℝ))
  convert hi using 1
  funext g
  change (vectorNormSq g-(r:ℝ))*|faceDot u g| =
    |faceDot u g| *vectorNormSq g-(r:ℝ)*|faceDot u g|
  ring

/-- The actual weighted hard-threshold functional for the first facet. -/
def gaussianThresholdAbsoluteFaceTrace {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) : ℝ :=
  ∫ g,(gaussianFiniteThresholdEvent Finset.univ u b).indicator
    (fun g => (vectorNormSq g-(r:ℝ))*|faceDot (u j) g|) g ∂standardGaussian r

/-- Exact one-coordinate Gaussian disintegration, including the absolute
first-normal weight in the actual signed integrand. -/
theorem gaussianThresholdAbsoluteFaceTrace_update_eq_section_integral {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (c : ℝ) :
    gaussianThresholdAbsoluteFaceTrace u (Function.update b j c) j =
      ∫ t in Iic c, gaussianPDFReal 0 1 t*(|t| *Printed.thresholdSignedSection u b j t) := by
  classical
  let E := gaussianFiniteThresholdEvent Finset.univ u (Function.update b j c)
  let f := E.indicator (fun g => (vectorNormSq g - ((n + 1 : ℕ) : ℝ))*|faceDot (u j) g|)
  have hE : MeasurableSet E := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have hf : Measurable f := by
    apply Measurable.indicator _ hE
    unfold vectorNormSq faceDot
    fun_prop
  have hfi : Integrable f (standardGaussian (n+1)) :=
    (integrable_gaussianAbsoluteFaceScore (u j)).indicator hE
  have hmap : Integrable (fun z : ℝ × Vector (n + 1) => f (gaussianNormalSectionMap (u j) z))
      ((gaussianReal 0 1).prod (standardGaussian (n + 1))) :=
    (integrable_gaussianNormalSectionMap_iff (u j) hu f hf).mpr hfi
  have hleft : gaussianThresholdAbsoluteFaceTrace u (Function.update b j c) j =
      ∫ z, f z ∂standardGaussian (n + 1) := by
    simp only [gaussianThresholdAbsoluteFaceTrace, f, E, gaussianFiniteThresholdEvent,
      Finset.mem_univ, forall_true_left]
  rw [hleft, ← integral_gaussianNormalSectionMap (u j) hu f hf, integral_prod _ hmap]
  have hinner (t : ℝ) : (∫ z, f (gaussianNormalSectionMap (u j) (t, z))
      ∂standardGaussian (n + 1)) =
      (Iic c).indicator (fun t => |t| *Printed.thresholdSignedSection u b j t) t := by
    by_cases htc : t ≤ c
    · rw [Set.indicator_of_mem (show t ∈ Iic c from htc)]
      unfold Printed.thresholdSignedSection
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        have he : SignedSurface.gaussianSectionPoint (u j) t z ∈ E ↔
            z ∈ gaussianFiniteThresholdEvent (Finset.univ.erase j)
              (fun l => gaussianNormalProjection (u j) (u l))
              (fun l => b l - t * faceDot (u l) (u j)) := by
          constructor
          · intro hz l hl
            have hh := hz l (Finset.mem_univ l)
            rw [Function.update_of_ne (Finset.mem_erase.mp hl).1, gaussianSectionPoint_faceDot] at hh
            dsimp only
            linarith
          · intro hz l _
            by_cases hlj : l = j
            · subst l
              simpa only [Function.update_self,
                SignedSurface.gaussianSectionPoint_on_hyperplane (u j) t hu] using htc
            · have hh := hz l (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ l⟩)
              rw [Function.update_of_ne hlj, gaussianSectionPoint_faceDot]
              dsimp only at hh
              linarith
        change E.indicator _ (SignedSurface.gaussianSectionPoint (u j) t z) = _
        by_cases hz : SignedSurface.gaussianSectionPoint (u j) t z ∈ E
        · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem (he.mp hz),
            gaussianSectionPoint_on_hyperplane (u j) t hu]
          ring
        · simp only [Set.indicator_of_not_mem hz,
            Set.indicator_of_not_mem (fun h => hz (he.mpr h)),mul_zero])
    · rw [Set.indicator_of_not_mem (show t ∉ Iic c from htc)]
      have he (z : Vector (n + 1)) : SignedSurface.gaussianSectionPoint (u j) t z ∉ E := by
        intro hz
        have hj := hz j (Finset.mem_univ j)
        rw [Function.update_self, SignedSurface.gaussianSectionPoint_on_hyperplane (u j) t hu] at hj
        exact htc hj
      simp only [f, gaussianNormalSectionMap, Set.indicator_of_not_mem (he _), integral_zero]
  rw [integral_congr_ae (ae_of_all _ hinner),
    integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num),
    ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by by_cases ht : t ∈ Iic c <;> simp [ht, smul_eq_mul])

theorem integrable_abs_mul_thresholdSignedSection {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1) :
    Integrable (fun t => |t| * Printed.thresholdSignedSection u b j t) (gaussianReal 0 1) := by
  have hP : Integrable (fun t : ℝ => |t^3|+(2*(r:ℝ))*|t|) (gaussianReal 0 1) := by
    simpa only [pow_one] using (standardRealGaussian_integrable_pow 3).abs.add
      ((standardRealGaussian_integrable_pow 1).abs.const_mul (2*(r:ℝ)))
  apply hP.mono'
    (measurable_id.abs.mul (measurable_thresholdSignedSection_parameter u b j)).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    change ‖|t| * Printed.thresholdSignedSection u b j t‖ ≤ |t^3|+(2*(r:ℝ))*|t|
    rw [Real.norm_eq_abs,abs_mul,abs_abs]
    have hh := mul_le_mul_of_nonneg_left (Printed.abs_thresholdSignedSection_le u b j hu t) (abs_nonneg t)
    apply hh.trans_eq
    rw [show |t^3|=|t| *t^2 by rw [pow_succ,abs_mul,abs_of_nonneg (sq_nonneg t)]; ring]
    ring)

/-- First coarea derivative of the actual signed absolute-face Gaussian
trace. Only the local projected residual slack is required. -/
theorem hasDerivAt_gaussianThresholdAbsoluteFaceTrace_update_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (c : ℝ)
    (hreg : ∀ l∈Finset.univ.erase j,
      gaussianNormalProjection (u j) (u l)≠0 ∨ b l-c*faceDot (u l) (u j)≠0) :
    HasDerivAt (fun t => gaussianThresholdAbsoluteFaceTrace u (Function.update b j t) j)
      (|c| * (gaussianPDFReal 0 1 c*Printed.thresholdSignedSection u b j c)) c := by
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have hm : Measurable (fun t => gaussianPDFReal 0 1 t*(|t| * Printed.thresholdSignedSection u b j t)) :=
    (measurable_gaussianPDFReal 0 1).mul
      (measurable_id.abs.mul (measurable_thresholdSignedSection_parameter u b j))
  have hi := standardRealGaussian_integrable_density_mul (integrable_abs_mul_thresholdSignedSection u b j hu)
  have hc := hpdf.continuousAt.mul (continuous_abs.continuousAt.mul
    (continuousAt_thresholdSignedSection_of_slack u b j hu c hreg))
  have hd := hasDerivAt_integral_Iic_of_continuousAt_integrable _ hm.stronglyMeasurable hi c hc
  have hh := hd.congr_of_eventuallyEq (Eventually.of_forall
    (fun t => gaussianThresholdAbsoluteFaceTrace_update_eq_section_integral u b j hu t))
  convert hh using 1 <;> ring

/-- All first-facet coarea derivatives hold simultaneously outside an
ordinary threshold-volume null set, for any dependent unit normal family. -/
theorem ae_hasDerivAt_gaussianThresholdAbsoluteFaceTrace_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j,vectorNormSq (u j)=1) :
    ∀ᵐ b : Vector m ∂volume, ∀ j,
      HasDerivAt (fun t => gaussianThresholdAbsoluteFaceTrace u (Function.update b j t) j)
        (|b j| * (gaussianPDFReal 0 1 (b j)*Printed.thresholdSignedSection u b j (b j))) (b j) := by
  filter_upwards [ae_localThresholdRegularity u] with b hb
  intro j
  exact hasDerivAt_gaussianThresholdAbsoluteFaceTrace_update_of_slack u b j (hu j) (b j)
    (fun l hl => hb j l (Finset.mem_erase.mp hl).1)

end
end RectangleCLTArxivV1
