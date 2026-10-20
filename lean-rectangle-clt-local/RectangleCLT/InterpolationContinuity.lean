import RectangleCLT.BernoulliPathDerivative

/-! Continuity through both endpoints of the actual interpolation law. This
uses bounded dominated convergence, not derivative estimates at time zero. -/

open MeasureTheory
open scoped BigOperators Topology

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem continuous_gaussianHeat (A : Matrix (Fin p) (Fin p) ℝ) :
    Continuous (fun y : Vector p × ℝ => s.gaussianHeat A y.1 y.2) := by
  have heq : (fun y : Vector p × ℝ => s.gaussianHeat A y.1 y.2) =
      (fun y => ∫ z, s.F (y.1 + Real.sqrt y.2 • A.mulVec z) ∂standardGaussian p) := by
    funext y
    exact s.gaussianHeat_eq_standardIntegral A y.1 y.2
  rw [heq]
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (F := fun y : Vector p × ℝ => fun z => s.F (y.1 + Real.sqrt y.2 • A.mulVec z))
  · intro y
    apply Continuous.aestronglyMeasurable
    apply s.continuous_F.comp
    fun_prop
  · intro y
    exact Filter.Eventually.of_forall fun z => s.norm_F_le_one _
  · exact integrable_const _
  · filter_upwards [] with z
    apply s.continuous_F.comp
    fun_prop

theorem norm_gaussianHeat_le_one (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (t : ℝ) : ‖s.gaussianHeat A x t‖ ≤ 1 := by
  rw [s.gaussianHeat_eq_standardIntegral]
  simpa only [measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := standardGaussian p)
      (Filter.Eventually.of_forall fun z => s.norm_F_le_one (x + Real.sqrt t • A.mulVec z))

theorem continuous_heatShiftExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Ω → Vector p) (hζ : Measurable ζ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    Continuous (s.heatShiftExpectation μ ζ A x) := by
  unfold heatShiftExpectation
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (F := fun t : ℝ => fun ω => s.gaussianHeat A (x + thinningScale t • ζ ω) t)
  · intro t
    exact ((s.continuous_gaussianHeat A).measurable.comp
      ((measurable_const.add (measurable_const.smul hζ)).prodMk measurable_const)).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall fun ω => s.norm_gaussianHeat_le_one A _ t
  · exact integrable_const _
  · filter_upwards [] with ω
    have harg : Continuous (fun t : ℝ => (x + thinningScale t • ζ ω, t)) := by
      change Continuous (fun t : ℝ => (x + (1 + t) • ζ ω, t))
      fun_prop
    simpa only [Function.comp_def] using (s.continuous_gaussianHeat A).comp harg

theorem continuousOn_selectorHeatExpectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    ContinuousOn (s.selectorHeatExpectation μ ξ A x) (Set.Icc 0 1) := by
  classical
  unfold selectorHeatExpectation
  apply continuousOn_finset_sum
  intro mask _
  apply ContinuousOn.mul
  · have hp : ContinuousOn thinningProbability (Set.Icc (0 : ℝ) 1) := by
      apply ContinuousOn.div (continuous_const.sub continuous_id).continuousOn
        ((continuous_const.add continuous_id).pow 2).continuousOn
      intro t ht
      simp only [id_eq]
      exact pow_ne_zero 2 (by linarith [ht.1])
    unfold Kane.maskWeight
    apply continuousOn_finset_prod
    intro i _
    cases hmi : mask i
    · simpa only [hmi, Bool.false_eq_true, ↓reduceIte] using continuousOn_const.sub hp
    · simpa only [hmi, ↓reduceIte] using hp
  · exact (s.continuous_heatShiftExpectation μ _ (measurable_maskObservationSum ξ hξ mask) A x).continuousOn

theorem continuousOn_integral_interpolationLaw
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) :
    ContinuousOn (fun t => ∫ z, s.F z ∂interpolationLaw μ ξ A t) (Set.Icc 0 1) := by
  apply (s.continuousOn_selectorHeatExpectation μ ξ hξ A 0).congr
  intro t ht
  exact s.integral_interpolationLaw_eq_selectorHeatExpectation μ ξ hξ A ht.1 ht.2

end RectangleCLT.FaceSmoother
