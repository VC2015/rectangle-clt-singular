import RectangleCLTCompanion.SelectorAveraging
import RectangleCLT.BoundedEnvelopeShift
import RectangleCLT.GaussianEnvelope

/-! Uniform transition mass for the actual base distributions. The bounded
case uses the proved Kane chain, and the Gaussian case allows singular
covariance. The same bound covers every one-face reference. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

/-- A uniform actual integral bound over all face systems of bandwidth `h`.
It includes one-face systems and arbitrary deterministic translations. -/
def TransitionMassBound {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (ν : Measure Ω) (V : Ω → Vector p) (h M : ℝ) : Prop :=
  ∀ s : FaceSmoother p, s.bandwidth = h → ∀ z : Vector p,
    (∫ ω, s.F (V ω + z) * s.theta (V ω + z) ∂ν) ≤ M

/-- The uniform transition bound for the actual bounded independent sum. -/
theorem transitionMassBound_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ v h : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) :
    TransitionMassBound μ (sumVector ξ) h
      (2147483648 * (h + δ) * Real.sqrt (dimensionLog p / v)) := by
  intro s hs z
  simpa only [FaceSmoother.theta, FaceWeights.theta, FaceSmoother.F, hs] using
    hdata.integral_smallerEnvelope_le hp hv hdiag s z

/-- The Gaussian version has no rank or positive-eigenvalue assumption. -/
theorem transitionMassBound_gaussian {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v h : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) :
    TransitionMassBound (gaussianLaw A) id h
      (Real.exp (3 / 2 : ℝ) * h * Real.sqrt (dimensionLog p / v)) := by
  intro s hs z
  simpa only [id_eq, FaceSmoother.theta, FaceWeights.theta, FaceSmoother.F, hs] using
    s.gaussian_expected_variance_le_of_diagonal hp A hv hdiag z

/-- The same actual bounded-base transition estimate after an arbitrary
independent measurable shift. -/
theorem transitionMassBound_bounded_shift
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ v h : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure E) [IsProbabilityMeasure ν] (R : E → Vector p) (hR : Measurable R) :
    TransitionMassBound (μ.prod ν) (fun z => sumVector ξ z.1 + R z.2) h
      (2147483648 * (h + δ) * Real.sqrt (dimensionLog p / v)) := by
  intro s hs z
  simpa only [FaceSmoother.theta, FaceWeights.theta, FaceSmoother.F, hs, add_assoc] using
    hdata.integral_smallerEnvelope_independent_shift_le hp hv hdiag s ν
      (fun ω => R ω + z) (hR.add_const z)

/-- Gaussian-base transition averaging after an arbitrary independent
measurable shift, with singular covariance allowed. -/
theorem transitionMassBound_gaussian_shift
    {E : Type*} [MeasurableSpace E] {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v h : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (ν : Measure E) [IsProbabilityMeasure ν] (R : E → Vector p) (hR : Measurable R) :
    TransitionMassBound ((gaussianLaw A).prod ν) (fun z => z.1 + R z.2) h
      (Real.exp (3 / 2 : ℝ) * h * Real.sqrt (dimensionLog p / v)) := by
  intro s hs z
  simpa only [FaceSmoother.theta, FaceWeights.theta, FaceSmoother.F, hs, add_assoc] using
    s.gaussian_expected_variance_independent_shift_le hp A hv hdiag ν
      (fun ω => R ω + z) (hR.add_const z)

/-- The one-face smoother uses exactly the same bandwidth and offset. -/
def singleFaceSmoother {p : ℕ} (s : FaceSmoother p) (f : Face p) : FaceSmoother p :=
  { s with faces := {f} }

lemma oneFaceReference_eq_single {p : ℕ} (s : FaceSmoother p) (f : Face p) (x : Vector p) :
    oneFaceReference s f x =
      (singleFaceSmoother s f).F x * (singleFaceSmoother s f).theta x := by
  classical
  have hT : ((singleFaceSmoother s f).weights x).T =
      Real.exp (s.faceScore f x / s.bandwidth) := by
    simp [FaceWeights.T, FaceSmoother.weights, singleFaceSmoother, FaceSmoother.faceScore]
  change _ = (1 / (1 + _)) * (1 - 1 / (1 + _))
  rw [hT]
  unfold oneFaceReference
  have he : 1 + Real.exp (s.faceScore f x / s.bandwidth) ≠ 0 := by positivity
  field_simp
  ring

lemma integrable_oneFaceReference {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (ν : Measure Ω) [IsFiniteMeasure ν] (s : FaceSmoother p) (f : Face p)
    (V : Ω → Vector p) (hV : Measurable V) :
    Integrable (fun ω => oneFaceReference s f (V ω)) ν := by
  have hm : Measurable (fun ω => oneFaceReference s f (V ω)) := by
    unfold oneFaceReference
    exact (((s.continuous_faceScore f).measurable.comp hV).div_const _).exp.div
      ((measurable_const.add (((s.continuous_faceScore f).measurable.comp hV).div_const _).exp).pow_const 2)
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (oneFaceReference_bounds s f _).1]
    exact (oneFaceReference_bounds s f _).2

/-- The bound for one-face reference masses is a proved consequence of the
same uniform transition estimate; it is not a new analytic premise. -/
theorem TransitionMassBound.oneFace {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    {ν : Measure Ω} {V : Ω → Vector p} {h M : ℝ}
    (hbound : TransitionMassBound ν V h M) (s : FaceSmoother p) (hs : s.bandwidth = h)
    (f : Face p) (z : Vector p) :
    (∫ ω, oneFaceReference s f (V ω + z) ∂ν) ≤ M := by
  simp_rw [oneFaceReference_eq_single]
  exact hbound (singleFaceSmoother s f) hs z

/-- Every summed nonempty selector tuple has the same transition cap. -/
theorem TransitionMassBound.selectorSum {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    {ν : Measure Ω} [IsFiniteMeasure ν] {V : Ω → Vector p} {h M : ℝ}
    (hV : Measurable V) (hbound : TransitionMassBound ν V h M)
    (s : FaceSmoother p) (hs : s.bandwidth = h) (k : ℕ) (z : Vector p) :
    (∫ ω, ∑ α : Fin (k + 1) → Face p, selectorWeight s α (V ω + z) ∂ν) ≤ M := by
  simp_rw [sum_selectorWeight_eq]
  have hW : Measurable (fun ω => V ω + z) := hV.add_const z
  have hi : Integrable (fun ω => s.F (V ω + z) * s.theta (V ω + z) ^ (k + 1)) ν := by
    apply (integrable_const (1 : ℝ)).mono'
    · have htheta : Measurable (fun ω => s.theta (V ω + z)) :=
        measurable_const.sub (s.continuous_F.measurable.comp hW)
      exact ((s.continuous_F.measurable.comp hW).mul (htheta.pow_const _)).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      have hnon : 0 ≤ s.F (V ω + z) * s.theta (V ω + z) ^ (k + 1) :=
        mul_nonneg (s.F_pos _).le (pow_nonneg (s.weights _).theta_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      exact mul_le_one₀ (s.F_le_one _) (pow_nonneg (s.weights _).theta_nonneg _)
        (pow_le_one₀ (s.weights _).theta_nonneg (s.weights _).theta_lt_one.le)
  have ht := s.integrable_smallerEnvelope (fun ω => V ω + z) hW (μ := ν)
  have hle (ω : Ω) : s.F (V ω + z) * s.theta (V ω + z) ^ (k + 1) ≤
      s.F (V ω + z) * s.theta (V ω + z) := by
    apply mul_le_mul_of_nonneg_left _ (s.F_pos _).le
    rw [pow_succ]
    exact mul_le_of_le_one_left (s.weights _).theta_nonneg
      (pow_le_one₀ (s.weights _).theta_nonneg (s.weights _).theta_lt_one.le)
  exact (integral_mono hi ht hle).trans (hbound s hs z)

end
end RectangleCLT.Companion
