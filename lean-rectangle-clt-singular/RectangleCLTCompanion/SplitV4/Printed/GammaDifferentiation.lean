import RectangleCLTCompanion.SplitV4.LogisticGammaTrace
import RectangleCLTCompanion.SplitV4.GaussianThresholdTubes

/-!
# Printed B.4: differentiating the Gamma mixture

This file supplies the dimension-dependent conditional bound used solely
to justify differentiation under the outer expectation. It is independent
of the quantitative threshold estimate in B.5.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- Hard-threshold integrals with a fixed, genuinely integrable signed test
are continuous when each retained normal is nonzero. -/
theorem continuous_weighted_gaussianFiniteThreshold {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r)
    (hu : ∀ j ∈ s, u j ≠ 0) (f : Vector r → ℝ)
    (hf : Measurable f) (hfi : Integrable f (standardGaussian r)) :
    Continuous (fun b : Vector m => ∫ g,
      (gaussianFiniteThresholdEvent s u b).indicator f g ∂standardGaussian r) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  apply tendsto_integral_filter_of_dominated_convergence (fun g => ‖f g‖)
  · exact Eventually.of_forall (fun c =>
      (hf.indicator (measurableSet_gaussianFiniteThresholdEvent s u c)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun c => ae_of_all _ fun g => by
      by_cases hg : g ∈ gaussianFiniteThresholdEvent s u c <;> simp [hg])
  · exact hfi.norm
  · exact (gaussianFiniteThresholdEvent_ae_no_boundary s u hu b).mono (fun g hg => by
      have hh := (gaussianFiniteThreshold_indicator_tendsto s u b g hg).mul_const (f g)
      have he (c : Vector m) : (gaussianFiniteThresholdEvent s u c).indicator f g =
          (gaussianFiniteThresholdEvent s u c).indicator (fun _ => (1 : ℝ)) g * f g := by
        by_cases hc : g ∈ gaussianFiniteThresholdEvent s u c <;> simp [hc]
      simpa only [← he] using hh)

/-- The actual signed radial score on the conditional normal section. -/
def thresholdSignedSection {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (j : Fin m) (t : ℝ) : ℝ :=
  ∫ g, (gaussianFiniteThresholdEvent (Finset.univ.erase j)
      (fun l => gaussianNormalProjection (u j) (u l))
      (fun l => b l - t * faceDot (u l) (u j))).indicator
    (fun g => vectorNormSq (SignedSurface.gaussianSectionPoint (u j) t g) - (r : ℝ)) g
      ∂standardGaussian r

private theorem thresholdSignedSection_integrable {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (t : ℝ) :
    Integrable ((gaussianFiniteThresholdEvent (Finset.univ.erase j)
      (fun l => gaussianNormalProjection (u j) (u l))
      (fun l => b l - t * faceDot (u l) (u j))).indicator
      (fun g => vectorNormSq (SignedSurface.gaussianSectionPoint (u j) t g) - (r : ℝ)))
      (standardGaussian r) :=
  ((SignedSurface.standardGaussian_integrable_sectionPoint_normSq (u j) t hu).sub
    (integrable_const _)).indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _)

/-- The conditional estimate printed before the derivative exchange.
Its dimension dependence is harmless: it is a dominating function, not
the final quantitative matrix estimate. -/
theorem abs_thresholdSignedSection_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (t : ℝ) :
    |thresholdSignedSection u b j t| ≤ t ^ 2 + 2 * r := by
  have hi := (SignedSurface.standardGaussian_integrable_sectionPoint_normSq (u j) t hu).add
    (integrable_const (r : ℝ))
  have hpoint (g : Vector r) : ‖(gaussianFiniteThresholdEvent (Finset.univ.erase j)
      (fun l => gaussianNormalProjection (u j) (u l))
      (fun l => b l - t * faceDot (u l) (u j))).indicator
      (fun g => vectorNormSq (SignedSurface.gaussianSectionPoint (u j) t g) - (r : ℝ)) g‖ ≤
      vectorNormSq (SignedSurface.gaussianSectionPoint (u j) t g) + r := by
    by_cases hg : g ∈ gaussianFiniteThresholdEvent (Finset.univ.erase j)
      (fun l => gaussianNormalProjection (u j) (u l))
      (fun l => b l - t * faceDot (u l) (u j))
    · rw [Set.indicator_of_mem hg, Real.norm_eq_abs]
      exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (vectorNormSq_nonneg _),
        abs_of_nonneg (Nat.cast_nonneg r)])
    · rw [Set.indicator_of_not_mem hg, norm_zero]
      exact add_nonneg (vectorNormSq_nonneg _) (Nat.cast_nonneg r)
  have hh := norm_integral_le_of_norm_le hi (ae_of_all _ hpoint)
  change ‖thresholdSignedSection u b j t‖ ≤ _ at hh
  have hmoment : (∫ g, vectorNormSq (SignedSurface.gaussianSectionPoint (u j) t g) + (r : ℝ)
      ∂standardGaussian r) = t ^ 2 + 2 * r - 1 := by
    have h₀ := integral_add (SignedSurface.standardGaussian_integrable_sectionPoint_normSq (u j) t hu)
      (integrable_const (r : ℝ))
    simp only [Pi.add_apply, integral_const, measureReal_univ_eq_one, one_smul] at h₀
    rw [h₀]
    simp_rw [SignedSurface.vectorNormSq_gaussianSectionPoint (u j) t hu]
    have h₁ := integral_add ((SignedSurface.standardGaussian_integrable_vectorNormSq r).sub
      (SignedSurface.standardGaussian_integrable_faceDot_sq (u j))) (integrable_const (t ^ 2))
    simp only [Pi.add_apply, Pi.sub_apply, integral_const, measureReal_univ_eq_one, one_smul] at h₁
    rw [h₁, integral_sub (SignedSurface.standardGaussian_integrable_vectorNormSq r)
      (SignedSurface.standardGaussian_integrable_faceDot_sq (u j)),
      SignedSurface.standardGaussian_integral_vectorNormSq,
      SignedSurface.standardGaussian_integral_faceDot_sq, hu]
    ring
  simp only [Pi.add_apply] at hh
  rw [hmoment, Real.norm_eq_abs] at hh
  linarith

/-- Continuity of the signed section integrand. Its unbounded polynomial
part is integrable, and the moving boundaries are Gaussian null hyperplanes. -/
theorem continuous_thresholdSignedSection {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Continuous (thresholdSignedSection u b j) := by
  let s := Finset.univ.erase j
  let v := fun l => gaussianNormalProjection (u j) (u l)
  let c := fun t : ℝ => fun l => b l - t * faceDot (u l) (u j)
  let f := fun g => vectorNormSq (SignedSurface.gaussianSectionResidual (u j) g) - (r : ℝ)
  have hf : Measurable f := by
    exact (Finset.measurable_sum _ (fun k _ =>
      ((measurable_pi_apply k).comp (SignedSurface.measurable_gaussianSectionResidual (u j))).pow_const 2)).sub_const _
  have hfi : Integrable f (standardGaussian r) :=
    (SignedSurface.standardGaussian_integrable_sectionResidual_normSq (u j) hu).sub (integrable_const _)
  have hv : ∀ l ∈ s, v l ≠ 0 := fun l hl =>
    gaussianNormalProjection_ne_zero_of_independent u hi j l (Finset.mem_erase.mp hl).1
  have hc : Continuous c := by fun_prop
  have he (t : ℝ) : thresholdSignedSection u b j t =
      (∫ g, (gaussianFiniteThresholdEvent s v (c t)).indicator f g ∂standardGaussian r) +
      t ^ 2 * gaussianFiniteThresholdCDF s v (c t) := by
    rw [gaussianFiniteThresholdCDF_eq_integral]
    rw [← integral_const_mul,
      ← integral_add (hfi.indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _))
        (((integrable_const (1 : ℝ)).indicator (measurableSet_gaussianFiniteThresholdEvent _ _ _)).const_mul _)]
    unfold thresholdSignedSection
    change (∫ g, (gaussianFiniteThresholdEvent s v (c t)).indicator
      (fun g => vectorNormSq (SignedSurface.gaussianSectionPoint (u j) t g) - (r : ℝ)) g
      ∂standardGaussian r) = _
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by
      by_cases hg : g ∈ gaussianFiniteThresholdEvent s v (c t)
      · simp only [thresholdSignedSection, Set.indicator_of_mem hg]
        have hq := SignedSurface.vectorNormSq_gaussianSectionPoint (u j) t hu g
        have hr := SignedSurface.vectorNormSq_gaussianSectionResidual (u j) g hu
        dsimp only [f]
        linarith
      · simp only [Set.indicator_of_not_mem hg, mul_zero, add_zero])
  have hefun : thresholdSignedSection u b j = fun t =>
      (∫ g, (gaussianFiniteThresholdEvent s v (c t)).indicator f g ∂standardGaussian r) +
      t ^ 2 * gaussianFiniteThresholdCDF s v (c t) := funext he
  rw [hefun]
  exact ((continuous_weighted_gaussianFiniteThreshold s v hv f hf hfi).comp hc).add
    ((continuous_id.pow 2).mul ((continuous_gaussianFiniteThresholdCDF s v hv).comp hc))

/-- Exact signed one-coordinate disintegration of the hard Gaussian trace.
The other inequalities remain hard constraints. -/
theorem gaussianThresholdTrace_update_eq_signed_section_integral {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (c : ℝ) :
    gaussianThresholdTrace u (Function.update b j c) =
      ∫ t in Iic c, gaussianPDFReal 0 1 t * thresholdSignedSection u b j t := by
  classical
  let E := gaussianFiniteThresholdEvent Finset.univ u (Function.update b j c)
  let f := E.indicator (fun g => vectorNormSq g - ((n + 1 : ℕ) : ℝ))
  have hE : MeasurableSet E := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have hf : Measurable f := by
    apply Measurable.indicator _ hE
    unfold vectorNormSq
    fun_prop
  have hfi : Integrable f (standardGaussian (n + 1)) :=
    ((SignedSurface.standardGaussian_integrable_vectorNormSq _).sub (integrable_const _)).indicator hE
  have hmap : Integrable (fun z : ℝ × Vector (n + 1) => f (gaussianNormalSectionMap (u j) z))
      ((gaussianReal 0 1).prod (standardGaussian (n + 1))) :=
    (integrable_gaussianNormalSectionMap_iff (u j) hu f hf).mpr hfi
  have hleft : gaussianThresholdTrace u (Function.update b j c) =
      ∫ z, f z ∂standardGaussian (n + 1) := by
    simp only [gaussianThresholdTrace, f, E, gaussianFiniteThresholdEvent,
      Finset.mem_univ, forall_true_left]
  rw [hleft, ← integral_gaussianNormalSectionMap (u j) hu f hf, integral_prod _ hmap]
  have hinner (t : ℝ) : (∫ z, f (gaussianNormalSectionMap (u j) (t, z))
      ∂standardGaussian (n + 1)) =
      (Iic c).indicator (thresholdSignedSection u b j) t := by
    by_cases htc : t ≤ c
    · rw [Set.indicator_of_mem (show t ∈ Iic c from htc)]
      unfold thresholdSignedSection
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
        · simp only [Set.indicator_of_mem hz, Set.indicator_of_mem (he.mp hz)]
        · simp only [Set.indicator_of_not_mem hz,
            Set.indicator_of_not_mem (fun h => hz (he.mpr h))])
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

/-- Integrability of the actual signed section follows from its explicit
polynomial bound, with no estimate from B.5. -/
theorem integrable_thresholdSignedSection {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Integrable (thresholdSignedSection u b j) (gaussianReal 0 1) := by
  apply ((standardRealGaussian_integrable_pow 2).add (integrable_const (2 * (r : ℝ)))).mono'
    (continuous_thresholdSignedSection u b j hu hi).aestronglyMeasurable
  exact ae_of_all _ (fun t => by simpa only [Real.norm_eq_abs] using abs_thresholdSignedSection_le u b j hu t)

/-- The actual coordinate derivative is its actual conditional section
integral times the normal density. -/
theorem hasDerivAt_gaussianThresholdTrace_update_printed {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) (c : ℝ) :
    HasDerivAt (fun t => gaussianThresholdTrace u (Function.update b j t))
      (gaussianPDFReal 0 1 c * thresholdSignedSection u b j c) c := by
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have hd := hasDerivAt_integral_Iic_of_continuous_integrable _
    (hpdf.mul (continuous_thresholdSignedSection u b j hu hi))
    (standardRealGaussian_integrable_density_mul (integrable_thresholdSignedSection u b j hu hi)) c
  exact hd.congr_of_eventuallyEq (Eventually.of_forall
    (fun t => gaussianThresholdTrace_update_eq_signed_section_integral u b j hu t))

/-- The paper's uniform-in-the-other-thresholds domination:
`|partial_j J(b)| ≤ phi(b_j) (b_j² + 2r)`. -/
theorem abs_gaussianThresholdTrace_partial_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    |deriv (fun t => gaussianThresholdTrace u (Function.update b j t)) (b j)| ≤
      gaussianPDFReal 0 1 (b j) * (b j ^ 2 + 2 * r) := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n =>
    rw [(hasDerivAt_gaussianThresholdTrace_update_printed u b j hu hi (b j)).deriv,
      abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_left (abs_thresholdSignedSection_le u b j hu (b j))
      (gaussianPDFReal_nonneg _ _ _)

/-- A finite uniform majorant for the conditional derivative bound.
The exact value is used only for dominated differentiation. -/
theorem gaussianPDFReal_mul_sq_add_dimension_le (r : ℕ) (t : ℝ) :
    gaussianPDFReal 0 1 t * (t ^ 2 + 2 * r) ≤
      (Real.sqrt (2 * Real.pi))⁻¹ * (2 + 2 * r) := by
  have he : Real.exp (-(t ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have hsq : t ^ 2 * Real.exp (-(t ^ 2 / 2)) ≤ 2 := by
    have h := Real.add_one_le_exp (t ^ 2 / 2)
    have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(t ^ 2 / 2))).le
    have heq : Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2 / 2)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [heq] at hm
    nlinarith [Real.exp_pos (-(t ^ 2 / 2))]
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hd : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hq : Real.exp (-(t ^ 2 / 2)) * (t ^ 2 + 2 * r) ≤ 2 + 2 * r := by
    nlinarith
  have hp : gaussianPDFReal 0 1 t = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2 / 2)) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, neg_div]
  rw [hp, mul_assoc]
  exact mul_le_mul_of_nonneg_left hq hc

/-- The sum of genuine coordinate derivatives has a fixed finite bound,
independent of every threshold and of the outer random variables. -/
theorem abs_gaussianThresholdDerivative_le_dimension {m r : ℕ}
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (b : Vector m) :
    |gaussianThresholdDerivative u b| ≤
      (m : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * (2 + 2 * r)) := by
  unfold gaussianThresholdDerivative
  calc
    _ ≤ ∑ j : Fin m,
        |deriv (fun t => gaussianThresholdTrace u (Function.update b j t)) (b j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin m, (Real.sqrt (2 * Real.pi))⁻¹ * (2 + 2 * r) :=
      Finset.sum_le_sum (fun j _ => (abs_gaussianThresholdTrace_partial_le u b j (hu j) hi).trans
        (gaussianPDFReal_mul_sq_add_dimension_le r (b j)))
    _ = _ := by simp

/-- The derivative exchange printed in B.4 for an arbitrary outer
probability space, hence also for the joint base/Gamma/exponential law.
The domination is proved above from actual conditional moments. -/
theorem hasDerivAt_integral_gaussianThresholdTrace_commonShift_printed
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m r : ℕ} (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (b : Ω → Vector m) (hb : Measurable b)
    (σ : ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, gaussianThresholdTrace u (fun j => b ω j + s / σ) ∂μ)
      (σ⁻¹ * ∫ ω, gaussianThresholdDerivative u (fun j => b ω j + t / σ) ∂μ) t := by
  let F : ℝ → Ω → ℝ := fun s ω => gaussianThresholdTrace u (fun j => b ω j + s / σ)
  let D : ℝ → Ω → ℝ := fun s ω => σ⁻¹ * gaussianThresholdDerivative u (fun j => b ω j + s / σ)
  let B : ℝ := (m : ℝ) * ((Real.sqrt (2 * Real.pi))⁻¹ * (2 + 2 * r))
  have hbm (s : ℝ) : Measurable (fun ω => fun j => b ω j + s / σ) := by fun_prop
  have hFi (s : ℝ) : Integrable (F s) μ :=
    integrable_gaussianThresholdTrace_parameter μ u hu hi _ (hbm s)
  have hDm (s : ℝ) : Measurable (D s) := by
    exact ((continuous_gaussianThresholdDerivative u hu hi).measurable.comp (hbm s)).const_mul _
  have hbound (s : ℝ) (ω : Ω) : ‖D s ω‖ ≤ |σ⁻¹| * B := by
    dsimp only [D]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_gaussianThresholdDerivative_le_dimension u hu hi _)
      (abs_nonneg _)
  have hd (ω : Ω) (s : ℝ) : HasDerivAt (fun z => F z ω) (D s ω) s := by
    have hh := (hasDerivAt_gaussianThresholdTrace_commonShift u (b ω) hu hi (s / σ)).comp s
      ((hasDerivAt_id s).div_const σ)
    simpa only [F, D, Function.comp_def, one_div, mul_comm] using hh
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (ε := 1) (bound := fun _ => |σ⁻¹| * B) (F := F) (F' := D) (x₀ := t)
    (by norm_num) (Eventually.of_forall (fun s => (hFi s).aestronglyMeasurable))
    (hFi t) (hDm t).aestronglyMeasurable (ae_of_all _ (fun ω s _ => hbound s ω))
    (integrable_const _) (ae_of_all _ (fun ω s _ => hd ω s))
  have hh := hres.2
  dsimp only [D] at hh
  rw [integral_const_mul] at hh
  exact hh

end
end RectangleCLT.Companion.SplitV4.Printed
