import RectangleCLTCompanion.ConsistencyStatement
import RectangleCLT.InterpolationCovariance

/-! Exact universe transport for the uniform model classes. Lifting a
sample space changes neither its joint observation law nor its moments,
covariance, or rectangle probabilities. Thus a class bound in an arbitrary
universe applies to the concrete Euclidean lower constructions as well. -/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

universe u v

namespace RectangleCLT.Companion

noncomputable section

def uniformLiftMeasure {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) :
    Measure (ULift.{u} Ω) := μ.map ULift.up

instance uniformLiftMeasure_isProbability {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] : IsProbabilityMeasure (uniformLiftMeasure.{u, v} μ) :=
  isProbabilityMeasure_map measurable_up.aemeasurable

def uniformLiftArray {Ω : Type v} {p n : ℕ} (ξ : Fin n → Ω → Vector p) :
    Fin n → ULift.{u} Ω → Vector p := fun i ω => ξ i ω.down

theorem uniformLift_integral {Ω : Type v} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) :
    (∫ ω, f ω.down ∂uniformLiftMeasure.{u, v} μ) = ∫ ω, f ω ∂μ := by
  have hlf : Measurable (fun ω : ULift.{u} Ω => f ω.down) := hf.comp measurable_down
  simpa only [uniformLiftMeasure, ULift.down_up] using
    (integral_map measurable_up.aemeasurable hlf.aestronglyMeasurable)

theorem uniformLiftArray_boundedIndependent
    {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) :
    BoundedIndependentHypotheses (uniformLiftMeasure.{u, v} μ) (uniformLiftArray ξ) δ := by
  have hmeas (i : Fin n) : Measurable (uniformLiftArray.{u, v} ξ i) :=
    (h.measurable i).comp measurable_down
  refine ⟨hmeas, ?_, ?_, ?_, h.delta_nonneg⟩
  · apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hmeas i).aemeasurable)).mpr
    have hmap (i : Fin n) : (uniformLiftMeasure.{u, v} μ).map (uniformLiftArray ξ i) =
        μ.map (ξ i) := by
      rw [uniformLiftMeasure, Measure.map_map (hmeas i) measurable_up]
      rfl
    have hmapall : (uniformLiftMeasure.{u, v} μ).map (fun ω i => uniformLiftArray ξ i ω) =
        μ.map (fun ω i => ξ i ω) := by
      rw [uniformLiftMeasure, Measure.map_map (measurable_pi_lambda _ hmeas) measurable_up]
      rfl
    rw [hmapall]
    simp_rw [hmap]
    exact (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (h.measurable i).aemeasurable)).mp h.independent
  · intro i j
    exact (uniformLift_integral μ (fun ω => ξ i ω j)
      ((measurable_pi_apply j).comp (h.measurable i))).trans (h.centered i j)
  · intro i
    apply (ae_map_iff measurable_up.aemeasurable
      (measurableSet_le (hmeas i).norm measurable_const)).mpr
    exact h.bounded i

theorem uniformLiftArray_covariance
    {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω}
    {p n : ℕ} {ξ : Fin n → Ω → Vector p} (hξ : ∀ i, Measurable (ξ i)) :
    covariance (uniformLiftMeasure.{u, v} μ) (sumVector (uniformLiftArray ξ)) =
      covariance μ (sumVector ξ) := by
  have hW : Measurable (sumVector ξ) := by
    unfold sumVector
    exact Finset.measurable_sum Finset.univ (fun i _ => hξ i)
  have hsum : sumVector (uniformLiftArray.{u, v} ξ) =
      fun ω => sumVector ξ ω.down := rfl
  rw [hsum]
  ext j k
  unfold covariance
  have hj : (∫ ω : ULift.{u} Ω, sumVector ξ ω.down j ∂uniformLiftMeasure μ) =
      ∫ ω, sumVector ξ ω j ∂μ :=
    uniformLift_integral μ (fun ω => sumVector ξ ω j) ((measurable_pi_apply j).comp hW)
  have hk : (∫ ω : ULift.{u} Ω, sumVector ξ ω.down k ∂uniformLiftMeasure μ) =
      ∫ ω, sumVector ξ ω k ∂μ :=
    uniformLift_integral μ (fun ω => sumVector ξ ω k) ((measurable_pi_apply k).comp hW)
  have hjk : (∫ ω : ULift.{u} Ω, sumVector ξ ω.down j * sumVector ξ ω.down k ∂uniformLiftMeasure μ) =
      ∫ ω, sumVector ξ ω j * sumVector ξ ω k ∂μ :=
    uniformLift_integral μ (fun ω => sumVector ξ ω j * sumVector ξ ω k)
      (((measurable_pi_apply j).comp hW).mul ((measurable_pi_apply k).comp hW))
  change (∫ ω : ULift.{u} Ω, sumVector ξ ω.down j * sumVector ξ ω.down k ∂uniformLiftMeasure μ) -
    (∫ ω : ULift.{u} Ω, sumVector ξ ω.down j ∂uniformLiftMeasure μ) *
      (∫ ω : ULift.{u} Ω, sumVector ξ ω.down k ∂uniformLiftMeasure μ) = _
  rw [hjk, hj, hk]

theorem uniformLiftArray_cancellation
    {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω}
    {p n : ℕ} {ξ : Fin n → Ω → Vector p} (hξ : ∀ i, Measurable (ξ i))
    (hc : AggregateThirdMomentsVanish μ ξ) :
    AggregateThirdMomentsVanish (uniformLiftMeasure.{u, v} μ) (uniformLiftArray ξ) := by
  intro j k l
  have heq (i : Fin n) :
      (∫ ω, uniformLiftArray.{u, v} ξ i ω j * uniformLiftArray ξ i ω k *
        uniformLiftArray ξ i ω l ∂uniformLiftMeasure μ) =
      ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ :=
    uniformLift_integral μ _ ((((measurable_pi_apply j).comp (hξ i)).mul
      ((measurable_pi_apply k).comp (hξ i))).mul ((measurable_pi_apply l).comp (hξ i)))
  simp_rw [heq]
  exact hc j k l

theorem uniformLift_rectangleError
    {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) :
    rectangleError (uniformLiftMeasure.{u, v} μ) (fun ω => W ω.down) A R =
      rectangleError μ W A R := by
  have hm : (uniformLiftMeasure.{u, v} μ).real ((fun ω => W ω.down) ⁻¹' R.carrier) =
      μ.real (W ⁻¹' R.carrier) := by
    have hset : MeasurableSet ((fun ω : ULift.{u} Ω => W ω.down) ⁻¹' R.carrier) :=
      (R.measurableSet_carrier).preimage (hW.comp measurable_down)
    have hup : Measurable (ULift.up : Ω → ULift.{u} Ω) := measurable_up
    have hh := Measure.map_apply (μ := μ) hup hset
    exact congrArg ENNReal.toReal hh
  unfold rectangleError
  rw [hm]

theorem fixedGapClassBound_universe_zero {c₀ B ε : ℝ} {p n : ℕ}
    (hclass : FixedGapClassBound.{u} c₀ B p n ε) : FixedGapClassBound.{0} c₀ B p n ε := by
  intro Ω _ μ _ ξ A h hunit hgap hfactor R
  let μ' : Measure (ULift.{u} Ω) := uniformLiftMeasure μ
  let η : Fin n → ULift.{u} Ω → Vector p := uniformLiftArray ξ
  have hη : BoundedIndependentHypotheses μ' η (B / Real.sqrt n) :=
    uniformLiftArray_boundedIndependent h
  have hcov : covariance μ' (sumVector η) = covariance μ (sumVector ξ) :=
    uniformLiftArray_covariance h.measurable
  have hb := hclass μ' η A hη (by simpa only [hcov] using hunit)
    (by simpa only [hcov] using hgap) (by simpa only [hcov] using hfactor) R
  have hW : Measurable (sumVector ξ) := by
    unfold sumVector
    exact Finset.measurable_sum Finset.univ (fun i _ => h.measurable i)
  exact (uniformLift_rectangleError μ (sumVector ξ) hW A R).ge.trans_lt hb

theorem zeroSkewFixedGapClassBound_universe_zero {c₀ B ε : ℝ} {p n : ℕ}
    (hclass : ZeroSkewFixedGapClassBound.{u} c₀ B p n ε) :
    ZeroSkewFixedGapClassBound.{0} c₀ B p n ε := by
  intro Ω _ μ _ ξ A h hunit hgap hfactor hcancel R
  let μ' : Measure (ULift.{u} Ω) := uniformLiftMeasure μ
  let η : Fin n → ULift.{u} Ω → Vector p := uniformLiftArray ξ
  have hη : BoundedIndependentHypotheses μ' η (B / Real.sqrt n) :=
    uniformLiftArray_boundedIndependent h
  have hcov : covariance μ' (sumVector η) = covariance μ (sumVector ξ) :=
    uniformLiftArray_covariance h.measurable
  have hb := hclass μ' η A hη (by simpa only [hcov] using hunit)
    (by simpa only [hcov] using hgap) (by simpa only [hcov] using hfactor)
    (uniformLiftArray_cancellation h.measurable hcancel) R
  have hW : Measurable (sumVector ξ) := by
    unfold sumVector
    exact Finset.measurable_sum Finset.univ (fun i _ => h.measurable i)
  exact (uniformLift_rectangleError μ (sumVector ξ) hW A R).ge.trans_lt hb

theorem fixedGapUniformConsistency_universe_zero {c₀ : ℝ}
    {B : ℕ → ℝ} {p : ℕ → ℕ} (h : FixedGapUniformConsistency.{u} c₀ B p) :
    FixedGapUniformConsistency.{0} c₀ B p := by
  intro ε hε
  filter_upwards [h ε hε] with n hn
  exact fixedGapClassBound_universe_zero hn

theorem zeroSkewFixedGapUniformConsistency_universe_zero {c₀ B : ℝ}
    {p : ℕ → ℕ} (h : ZeroSkewFixedGapUniformConsistency.{u} c₀ B p) :
    ZeroSkewFixedGapUniformConsistency.{0} c₀ B p := by
  intro ε hε
  filter_upwards [h ε hε] with n hn
  exact zeroSkewFixedGapClassBound_universe_zero hn

end

end RectangleCLT.Companion
