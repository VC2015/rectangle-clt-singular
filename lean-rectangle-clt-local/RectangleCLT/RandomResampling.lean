import RectangleCLT.Resampling
import RectangleCLT.ThinningMoments

/-! A genuine resampling experiment: sample the two arrays, choose uniform
selector bits, and independently flip each selector with probability `θ`.
All selector averaging is an explicit finite mixture of pushforward measures.
The resulting disagreement bound is the upper-bound side of the AL argument;
it does not assert a boundary-crossing lower bound or concentration estimate. -/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable section

/-- The pair of selected sums before and after flipping the selector mask. -/
def resamplingPair {Ω : Type u} {p n : ℕ}
    (left right : Ω → Fin n → Vector p) (x mask : Kane.Cube n) (ω : Ω) :
    Vector p × Vector p :=
  (resampledSum (left ω) (right ω) x,
    resampledSum (left ω) (right ω) (Kane.maskedFlip mask x))

theorem measurable_random_resampledSum {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (left right : Ω → Fin n → Vector p) (hleft : Measurable left) (hright : Measurable right)
    (x : Kane.Cube n) : Measurable (fun ω => resampledSum (left ω) (right ω) x) := by
  apply measurable_pi_lambda
  intro j
  apply Finset.measurable_sum Finset.univ
  intro i _
  cases hx : x i
  · simpa only [hx, Bool.false_eq_true, ↓reduceIte] using
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hright)
  · simpa only [hx, ↓reduceIte] using
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hleft)

theorem measurable_resamplingPair {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (left right : Ω → Fin n → Vector p) (hleft : Measurable left) (hright : Measurable right)
    (x mask : Kane.Cube n) : Measurable (resamplingPair left right x mask) :=
  (measurable_random_resampledSum left right hleft hright x).prodMk
    (measurable_random_resampledSum left right hleft hright (Kane.maskedFlip mask x))

/-- The actual law of the pair of sums. Selector bits have uniform weights,
and flip masks have independent Bernoulli weights. -/
def randomResamplingLaw {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (left right : Ω → Fin n → Vector p) (θ : ℝ) :
    Measure (Vector p × Vector p) :=
  ∑ x : Kane.Cube n,
    ENNReal.ofReal ((Fintype.card (Kane.Cube n) : ℝ)⁻¹) •
      bernoulliMixtureLaw μ (resamplingPair left right x) θ

theorem randomResamplingLaw_isProbability {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (left right : Ω → Fin n → Vector p) (hleft : Measurable left) (hright : Measurable right)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (randomResamplingLaw μ left right θ) := by
  have hc : (Fintype.card (Kane.Cube n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := Kane.Cube n))
  constructor
  unfold randomResamplingLaw
  rw [Measure.finset_sum_apply]
  have hmass (x : Kane.Cube n) :
      bernoulliMixtureLaw μ (resamplingPair left right x) θ Set.univ = 1 := by
    letI := bernoulliMixtureLaw_isProbability μ (resamplingPair left right x)
      (measurable_resamplingPair left right hleft hright x) θ hθ hθone
    exact measure_univ
  simp_rw [Measure.smul_apply, smul_eq_mul, hmass, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_inv_cancel₀ hc]
  norm_num

/-- Integrating the pair law is exactly finite selector/noise averaging of
the underlying sample integrals. -/
theorem integral_randomResamplingLaw {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (left right : Ω → Fin n → Vector p)
    (hleft : Measurable left) (hright : Measurable right)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (g : Vector p × Vector p → ℝ)
    (hg : ∀ x mask, Integrable g (μ.map (resamplingPair left right x mask))) :
    (∫ z, g z ∂randomResamplingLaw μ left right θ) =
      Kane.avg (fun x : Kane.Cube n => ∑ mask : Kane.Cube n,
        Kane.maskWeight θ mask * ∫ ω, g (resamplingPair left right x mask ω) ∂μ) := by
  have hmixture (x : Kane.Cube n) :
      Integrable g (bernoulliMixtureLaw μ (resamplingPair left right x) θ) :=
    integrable_bernoulliMixtureLaw μ _ θ g (hg x)
  unfold randomResamplingLaw
  rw [integral_finset_sum_measure (fun x _ => (hmixture x).smul_measure ENNReal.ofReal_ne_top)]
  unfold Kane.avg
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg _)),
    integral_bernoulliMixtureLaw μ _ θ hθ hθone g (hg x)]
  congr 1
  apply Finset.sum_congr rfl
  intro mask _
  rw [integral_map (measurable_resamplingPair left right hleft hright x mask).aemeasurable
    (hg x mask).aestronglyMeasurable]

/-- Membership differs between the two output vectors. -/
def membershipDisagreement {p : ℕ} (A : Set (Vector p)) : Set (Vector p × Vector p) :=
  symmDiff (Prod.fst ⁻¹' A) (Prod.snd ⁻¹' A)

theorem measurableSet_membershipDisagreement {p : ℕ} {A : Set (Vector p)}
    (hA : MeasurableSet A) : MeasurableSet (membershipDisagreement A) :=
  (hA.preimage measurable_fst).symmDiff (hA.preimage measurable_snd)

private theorem integral_finite_avg {Ω : Type u} [MeasurableSpace Ω]
    {μ : Measure Ω} {α : Type*} [Fintype α] (H : α → Ω → ℝ)
    (hH : ∀ a, Integrable (H a) μ) :
    (∫ ω, Kane.avg (fun a => H a ω) ∂μ) = Kane.avg (fun a => ∫ ω, H a ω ∂μ) := by
  unfold Kane.avg
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun a _ => hH a)]

/-- Realize the sample-dependent Boolean selector function for an arbitrary
measurable target set. -/
def randomMembershipFunction {Ω : Type u} {p n : ℕ}
    (left right : Ω → Fin n → Vector p) (A : Set (Vector p))
    (ω : Ω) (x : Kane.Cube n) : Bool := by
  classical
  exact decide (resampledSum (left ω) (right ω) x ∈ A)

/-- The real indicator of the actual membership-disagreement event. -/
def disagreementValue {p : ℕ} (A : Set (Vector p)) : Vector p × Vector p → ℝ := by
  classical
  exact (membershipDisagreement A).indicator (fun _ => 1)

theorem measurable_disagreementValue {p : ℕ} {A : Set (Vector p)}
    (hA : MeasurableSet A) : Measurable (disagreementValue A) := by
  classical
  exact measurable_const.indicator (measurableSet_membershipDisagreement hA)

theorem integrable_disagreementValue {p : ℕ} (ν : Measure (Vector p × Vector p))
    [IsFiniteMeasure ν] {A : Set (Vector p)} (hA : MeasurableSet A) :
    Integrable (disagreementValue A) ν := by
  classical
  apply (integrable_const (1 : ℝ)).mono' (measurable_disagreementValue hA).aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : z ∈ membershipDisagreement A <;> simp [disagreementValue, hz]

theorem disagreementValue_resamplingPair {Ω : Type u} {p n : ℕ}
    (left right : Ω → Fin n → Vector p) (A : Set (Vector p))
    (x mask : Kane.Cube n) (ω : Ω) :
    disagreementValue A (resamplingPair left right x mask ω) =
      if randomMembershipFunction left right A ω x =
        randomMembershipFunction left right A ω (Kane.maskedFlip mask x) then (0 : ℝ) else 1 := by
  classical
  by_cases hx : resampledSum (left ω) (right ω) x ∈ A <;>
    by_cases hy : resampledSum (left ω) (right ω) (Kane.maskedFlip mask x) ∈ A <;>
    simp [disagreementValue, membershipDisagreement, Set.mem_symmDiff,
      resamplingPair, randomMembershipFunction, hx, hy]

private theorem randomNoise_integrand_eq {Ω : Type u} {p n : ℕ}
    (left right : Ω → Fin n → Vector p) (A : Set (Vector p)) (θ : ℝ) (ω : Ω) :
    Kane.avg (fun x : Kane.Cube n => ∑ mask : Kane.Cube n,
      Kane.maskWeight θ mask * disagreementValue A (resamplingPair left right x mask ω)) =
        Kane.noiseSensitivity (randomMembershipFunction left right A ω) θ := by
  unfold Kane.noiseSensitivity
  apply Kane.avg_congr
  intro x
  apply Finset.sum_congr rfl
  intro mask _
  rw [disagreementValue_resamplingPair]

private theorem integrable_disagreementValue_sample
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (left right : Ω → Fin n → Vector p) (hleft : Measurable left) (hright : Measurable right)
    {A : Set (Vector p)} (hA : MeasurableSet A) (x mask : Kane.Cube n) :
    Integrable (fun ω => disagreementValue A (resamplingPair left right x mask ω)) μ := by
  classical
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_disagreementValue hA).comp
      (measurable_resamplingPair left right hleft hright x mask)).aestronglyMeasurable
  filter_upwards [] with ω
  by_cases hz : resamplingPair left right x mask ω ∈ membershipDisagreement A <;>
    simp [disagreementValue, hz]

theorem integrable_random_noiseSensitivity
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (left right : Ω → Fin n → Vector p) (hleft : Measurable left) (hright : Measurable right)
    {A : Set (Vector p)} (hA : MeasurableSet A) (θ : ℝ) :
    Integrable (fun ω => Kane.noiseSensitivity (randomMembershipFunction left right A ω) θ) μ := by
  have hsum (x : Kane.Cube n) : Integrable (fun ω => ∑ mask : Kane.Cube n,
      Kane.maskWeight θ mask * disagreementValue A (resamplingPair left right x mask ω)) μ :=
    integrable_finset_sum Finset.univ (fun mask _ =>
      (integrable_disagreementValue_sample μ left right hleft hright hA x mask).const_mul _)
  have havg : Integrable (fun ω => Kane.avg (fun x : Kane.Cube n => ∑ mask : Kane.Cube n,
      Kane.maskWeight θ mask * disagreementValue A (resamplingPair left right x mask ω))) μ := by
    unfold Kane.avg
    exact (integrable_finset_sum Finset.univ (fun x _ => hsum x)).const_mul _
  have heq := funext (randomNoise_integrand_eq left right A θ)
  rwa [heq] at havg

/-- Exact finite conditioning identity: the disagreement probability in the
genuine experiment is the expectation of fixed-array Boolean noise sensitivity. -/
theorem randomResampling_disagreement_eq_integral_noiseSensitivity
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (left right : Ω → Fin n → Vector p) (hleft : Measurable left) (hright : Measurable right)
    {A : Set (Vector p)} (hA : MeasurableSet A) (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    (randomResamplingLaw μ left right θ).real (membershipDisagreement A) =
      ∫ ω, Kane.noiseSensitivity (randomMembershipFunction left right A ω) θ ∂μ := by
  have hg (x mask : Kane.Cube n) :
      Integrable (disagreementValue A) (μ.map (resamplingPair left right x mask)) := by
    letI := isProbabilityMeasure_map (μ := μ)
      (measurable_resamplingPair left right hleft hright x mask).aemeasurable
    exact integrable_disagreementValue _ hA
  have hcomp := integrable_disagreementValue_sample μ left right hleft hright hA
  have hsum (x : Kane.Cube n) : Integrable (fun ω => ∑ mask : Kane.Cube n,
      Kane.maskWeight θ mask * disagreementValue A (resamplingPair left right x mask ω)) μ :=
    integrable_finset_sum Finset.univ (fun mask _ => (hcomp x mask).const_mul _)
  calc
    _ = ∫ z, disagreementValue A z ∂randomResamplingLaw μ left right θ := by
      symm
      exact integral_indicator_one (measurableSet_membershipDisagreement hA)
    _ = Kane.avg (fun x : Kane.Cube n => ∑ mask : Kane.Cube n,
        Kane.maskWeight θ mask * ∫ ω, disagreementValue A
          (resamplingPair left right x mask ω) ∂μ) :=
      integral_randomResamplingLaw μ left right hleft hright θ hθ hθone _ hg
    _ = ∫ ω, Kane.avg (fun x : Kane.Cube n => ∑ mask : Kane.Cube n,
        Kane.maskWeight θ mask * disagreementValue A (resamplingPair left right x mask ω)) ∂μ := by
      rw [integral_finite_avg _ hsum]
      apply Kane.avg_congr
      intro x
      rw [integral_finset_sum Finset.univ (fun mask _ => (hcomp x mask).const_mul _)]
      simp_rw [integral_const_mul]
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (randomNoise_integrand_eq left right A θ))

namespace FaceSmoother

/-- The finite face family specifies a measurable closed rectangle. -/
theorem measurableSet_Inside {p : ℕ} (s : FaceSmoother p) :
    MeasurableSet {v : Vector p | s.Inside v} := by
  have hface (f : Face p) : Measurable (s.faceScore f) := by
    have hj : Measurable (fun v : Vector p => v f.1) := measurable_pi_apply f.1
    change Measurable (fun v : Vector p => (if f.2 then v f.1 else -v f.1) - s.offsets f)
    cases hf : f.2
    · simpa only [faceScore, normalDot, hf, Bool.false_eq_true, ↓reduceIte] using
        hj.neg.sub_const (s.offsets f)
    · simpa only [faceScore, normalDot, hf, ↓reduceIte] using
        hj.sub_const (s.offsets f)
  have hh := s.faces.measurableSet_biInter
    (fun f _ => measurableSet_le (hface f) (measurable_const : Measurable (fun _ : Vector p => (0 : ℝ))))
  convert hh using 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Inside]

/-- The fixed-pair Kane bound lifted to the actual random-array experiment.
This bound has no anti-concentration or crossing-lower-bound hypothesis. -/
theorem randomResampling_disagreement_le {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (left right : Ω → Fin n → Vector p) (hleft : Measurable left) (hright : Measurable right)
    (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    (randomResamplingLaw μ left right θ).real
        (membershipDisagreement {v : Vector p | s.Inside v}) ≤
      8 * Real.sqrt (θ * dimensionLog p) := by
  rw [randomResampling_disagreement_eq_integral_noiseSensitivity μ left right hleft hright
    s.measurableSet_Inside θ hθ.le hθone]
  have hpoint (ω : Ω) :
      Kane.noiseSensitivity
        (randomMembershipFunction left right {v : Vector p | s.Inside v} ω) θ ≤
          8 * Real.sqrt (θ * dimensionLog p) := by
    change Kane.noiseSensitivity (s.resampledMembership (left ω) (right ω)) θ ≤ _
    exact s.resampledMembership_noiseSensitivity_le_dimensionLog (left ω) (right ω) hp θ hθ hθone
  calc
    _ ≤ ∫ _ω, 8 * Real.sqrt (θ * dimensionLog p) ∂μ :=
      integral_mono_ae
        (integrable_random_noiseSensitivity μ left right hleft hright s.measurableSet_Inside θ)
        (integrable_const _) (Filter.Eventually.of_forall hpoint)
    _ = _ := by simp

end FaceSmoother

/-- A closed box as a measurable target set for the random experiment. -/
def resamplingClosedBox {p : ℕ} (lo hi : Vector p) : Set (Vector p) :=
  {v | ∀ j, lo j ≤ v j ∧ v j ≤ hi j}

theorem measurableSet_resamplingClosedBox {p : ℕ} (lo hi : Vector p) :
    MeasurableSet (resamplingClosedBox lo hi) := by
  have hh := MeasurableSet.iInter (fun j : Fin p =>
    (measurableSet_le (measurable_const : Measurable (fun _ : Vector p => lo j))
      (measurable_pi_apply j)).inter
      (measurableSet_le (measurable_pi_apply j)
        (measurable_const : Measurable (fun _ : Vector p => hi j))))
  convert hh using 1
  ext v
  simp [resamplingClosedBox]

theorem randomResampling_closedBox_disagreement_le
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (left right : Ω → Fin n → Vector p) (hleft : Measurable left) (hright : Measurable right)
    (lo hi : Vector p) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    (randomResamplingLaw μ left right θ).real (membershipDisagreement (resamplingClosedBox lo hi)) ≤
      8 * Real.sqrt (θ * dimensionLog p) := by
  rw [randomResampling_disagreement_eq_integral_noiseSensitivity μ left right hleft hright
    (measurableSet_resamplingClosedBox lo hi) θ hθ.le hθone]
  have hpoint (ω : Ω) :
      Kane.noiseSensitivity
        (randomMembershipFunction left right (resamplingClosedBox lo hi) ω) θ ≤
          8 * Real.sqrt (θ * dimensionLog p) := by
    have heq : randomMembershipFunction left right (resamplingClosedBox lo hi) ω =
        resampledClosedBox (left ω) (right ω) lo hi := by
      classical
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [randomMembershipFunction, resamplingClosedBox, resampledClosedBox,
        Set.mem_setOf_eq, decide_eq_true_eq]
    rw [heq]
    exact resampledClosedBox_noiseSensitivity_le_dimensionLog (left ω) (right ω) lo hi hp θ hθ hθone
  calc
    _ ≤ ∫ _ω, 8 * Real.sqrt (θ * dimensionLog p) ∂μ :=
      integral_mono_ae
        (integrable_random_noiseSensitivity μ left right hleft hright
          (measurableSet_resamplingClosedBox lo hi) θ)
        (integrable_const _) (Filter.Eventually.of_forall hpoint)
    _ = _ := by simp

/-- The same experiment built from two independent copies of the whole
observation array, represented by the actual product measure `μ.prod μ`. -/
def independentCopyResamplingLaw {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (θ : ℝ) : Measure (Vector p × Vector p) :=
  randomResamplingLaw (μ.prod μ) (fun ω i => ξ i ω.1) (fun ω i => ξ i ω.2) θ

theorem independentCopyResamplingLaw_isProbability
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (independentCopyResamplingLaw μ ξ θ) :=
  randomResamplingLaw_isProbability (μ.prod μ) _ _
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_fst))
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_snd)) θ hθ hθone

theorem FaceSmoother.independentCopyResampling_disagreement_le
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    (independentCopyResamplingLaw μ ξ θ).real
        (membershipDisagreement {v : Vector p | s.Inside v}) ≤
      8 * Real.sqrt (θ * dimensionLog p) :=
  s.randomResampling_disagreement_le (μ.prod μ) _ _
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_fst))
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_snd)) hp θ hθ hθone

theorem independentCopyResampling_closedBox_disagreement_le
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (lo hi : Vector p) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    (independentCopyResamplingLaw μ ξ θ).real (membershipDisagreement (resamplingClosedBox lo hi)) ≤
      8 * Real.sqrt (θ * dimensionLog p) :=
  randomResampling_closedBox_disagreement_le (μ.prod μ) _ _
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_fst))
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_snd)) lo hi hp θ hθ hθone

/-- The marginal selected-sum law, before applying any selector noise. -/
def uniformResampledSumLaw {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (left right : Ω → Fin n → Vector p) : Measure (Vector p) :=
  ∑ x : Kane.Cube n,
    ENNReal.ofReal ((Fintype.card (Kane.Cube n) : ℝ)⁻¹) •
      μ.map (fun ω => resampledSum (left ω) (right ω) x)

private theorem sum_maskWeight_ofReal {n : ℕ} (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    (∑ mask : Kane.Cube n, ENNReal.ofReal (Kane.maskWeight θ mask)) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun mask _ => Kane.maskWeight_nonneg hθ hθone mask),
    Kane.maskWeight_sum]
  norm_num

/-- The first output has precisely the uniform-selector sum law, independently
of the noise rate. This does not identify it with the original sum law without
additional assumptions on the observation array. -/
theorem randomResamplingLaw_fst {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (left right : Ω → Fin n → Vector p)
    (hleft : Measurable left) (hright : Measurable right)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    (randomResamplingLaw μ left right θ).map Prod.fst = uniformResampledSumLaw μ left right := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB]
  unfold randomResamplingLaw uniformResampledSumLaw
  rw [Measure.finset_sum_apply, Measure.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [Measure.map_apply (measurable_random_resampledSum left right hleft hright x) hB]
  unfold bernoulliMixtureLaw
  rw [Measure.finset_sum_apply]
  simp_rw [Measure.smul_apply, smul_eq_mul]
  have hmap (mask : Kane.Cube n) :
      μ.map (resamplingPair left right x mask) (Prod.fst ⁻¹' B) =
        μ ((fun ω => resampledSum (left ω) (right ω) x) ⁻¹' B) := by
    rw [Measure.map_apply (measurable_resamplingPair left right hleft hright x mask)
      (hB.preimage measurable_fst)]
    rfl
  simp_rw [hmap]
  rw [← Finset.sum_mul, sum_maskWeight_ofReal θ hθ hθone, one_mul]

/-- Flipping a fixed mask permutes the uniform selector cube. Consequently
the second output has the same selected-sum marginal as the first output. -/
theorem randomResamplingLaw_snd {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (left right : Ω → Fin n → Vector p)
    (hleft : Measurable left) (hright : Measurable right)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    (randomResamplingLaw μ left right θ).map Prod.snd = uniformResampledSumLaw μ left right := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB]
  unfold randomResamplingLaw uniformResampledSumLaw
  rw [Measure.finset_sum_apply, Measure.finset_sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hmap (x mask : Kane.Cube n) :
      μ.map (resamplingPair left right x mask) (Prod.snd ⁻¹' B) =
        μ ((fun ω => resampledSum (left ω) (right ω) (Kane.maskedFlip mask x)) ⁻¹' B) := by
    rw [Measure.map_apply (measurable_resamplingPair left right hleft hright x mask)
      (hB.preimage measurable_snd)]
    rfl
  have hplain (x : Kane.Cube n) :
      μ.map (fun ω => resampledSum (left ω) (right ω) x) B =
        μ ((fun ω => resampledSum (left ω) (right ω) x) ⁻¹' B) :=
    Measure.map_apply (measurable_random_resampledSum left right hleft hright x) hB
  simp only [bernoulliMixtureLaw, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [hmap, hplain]
  have hperm (mask : Kane.Cube n) :
      (∑ x : Kane.Cube n, μ ((fun ω => resampledSum (left ω) (right ω)
        (Kane.maskedFlip mask x)) ⁻¹' B)) =
        ∑ x : Kane.Cube n, μ ((fun ω => resampledSum (left ω) (right ω) x) ⁻¹' B) := by
    have hinv (x : Kane.Cube n) : Kane.maskedFlip mask (Kane.maskedFlip mask x) = x := by
      funext i
      cases hm : mask i <;> simp [Kane.maskedFlip, hm]
    let e : Kane.Cube n ≃ Kane.Cube n :=
      { toFun := Kane.maskedFlip mask
        invFun := Kane.maskedFlip mask
        left_inv := hinv
        right_inv := hinv }
    exact e.sum_comp (fun x => μ ((fun ω => resampledSum (left ω) (right ω) x) ⁻¹' B))
  calc
    _ = ENNReal.ofReal ((Fintype.card (Kane.Cube n) : ℝ)⁻¹) *
        ∑ mask : Kane.Cube n, ENNReal.ofReal (Kane.maskWeight θ mask) *
          ∑ x : Kane.Cube n, μ ((fun ω => resampledSum (left ω) (right ω)
            (Kane.maskedFlip mask x)) ⁻¹' B) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro mask _
      rw [← Finset.mul_sum]
    _ = _ := by
      simp_rw [hperm]
      rw [← Finset.sum_mul, sum_maskWeight_ofReal θ hθ hθone, one_mul, Finset.mul_sum]

end

end RectangleCLT
