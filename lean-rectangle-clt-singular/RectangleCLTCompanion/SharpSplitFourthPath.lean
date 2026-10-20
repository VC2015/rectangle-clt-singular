import RectangleCLTCompanion.RestorationFinal
import RectangleCLTCompanion.SharpRepresentatives
import RectangleCLTCompanion.SharpGaussianSplit
import RectangleCLTCompanion.SharpGaussianConvolution
import RectangleCLTCompanion.FourthIdentitySelectorFubini
import RectangleCLTCompanion.SharpFreshCopy

/-! Concrete fourth-order path restoration under the actual half-Gaussian
base law.  Fresh copies retain their genuine product law. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

def splitFourthSample {Ω : Type*} (b : Bool) (a : Ω × Ω) : Ω :=
  if b then a.2 else a.1

theorem measurable_splitFourthSample {Ω : Type*} [MeasurableSpace Ω] (b : Bool) :
    Measurable (splitFourthSample (Ω := Ω) b) := by
  cases b
  · exact measurable_fst
  · exact measurable_snd

def splitFourthObservable {Ω : Type*} {p n : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ξ : Fin n → Ω → Vector p) (δ : ℝ)
    (b : Bool) (i : Fin n) (a : Ω × Ω) : Vector p :=
  A.mulVec (boundedSupportObservation A ξ δ i (splitFourthSample b a))

def splitFourthShift {Ω : Type*} {p n : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ξ : Fin n → Ω → Vector p) (δ t r : ℝ)
    (b : Bool) (i : Fin n) (bg : (Fin n → Vector p) × Vector p) (a : Ω × Ω) : Vector p :=
  (thinningScale t * r) • splitFourthObservable A ξ δ b i a -
    boundedRetainedObservation δ bg.1 i

private theorem integral_fst_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    (∫ a : Ω × Ω, f a.1 ∂μ.prod μ) = ∫ ω, f ω ∂μ := by
  simpa only [mul_one, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
    integral_prod_mul (μ := μ) (ν := μ) f (fun _ : Ω => (1 : ℝ))

theorem splitFourthObservable_measurable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (b : Bool) (i : Fin n) :
    Measurable (splitFourthObservable A ξ δ b i) :=
  (measurable_mulVec A).comp
    ((boundedSupportObservation_measurable h A i).comp (measurable_splitFourthSample b))

theorem splitFourthObservable_norm_le {Ω : Type*} {p n : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (hδ : 0 ≤ δ) (b : Bool) (i : Fin n) (a : Ω × Ω) :
    ‖splitFourthObservable A ξ δ b i a‖ ≤ δ :=
  boundedSupportObservation_projected_le A ξ hδ i _

theorem splitFourthShift_norm_le {Ω : Type*} {p n : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ξ : Fin n → Ω → Vector p) {δ t r : ℝ}
    (hδ : 0 ≤ δ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (b : Bool) (i : Fin n) (bg : (Fin n → Vector p) × Vector p) (a : Ω × Ω) :
    ‖splitFourthShift A ξ δ t r b i bg a‖ ≤ 4 * δ := by
  have ha : 0 ≤ thinningScale t := by unfold thinningScale; linarith
  have ha2 : thinningScale t ≤ 2 := by unfold thinningScale; linarith
  have har : 0 ≤ thinningScale t * r := mul_nonneg ha hr.1
  have har2 : thinningScale t * r ≤ 2 :=
    (mul_le_of_le_one_right ha hr.2).trans ha2
  have hnorm : ‖(thinningScale t * r) • splitFourthObservable A ξ δ b i a‖ ≤ 2 * δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg har]
    exact mul_le_mul har2 (splitFourthObservable_norm_le A ξ hδ b i a)
      (norm_nonneg _) (by norm_num)
  exact (norm_sub_le _ _).trans ((add_le_add hnorm
    (boundedRetainedObservation_norm_le hδ bg.1 i)).trans (by ring_nf; rfl))

/-- The actual split-base experiment corresponding to A/B/C.  All three
use two independent fresh copies; A ignores the second copy. -/
def splitFourthRestorationExperiment
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (δ : ℝ) (x : Vector p) (t r : ℝ)
    (bY bW bShift : Bool) : ℝ :=
  ∫ bg, fixedRestorationFourthExpectation s (μ.prod μ) A (splitGaussianScale t)
    (splitBaseValue A x t bg)
    (fun i a => boundedSupportObservation A ξ δ i a.1)
    (fun i a => splitFourthObservable A ξ δ bY i a)
    (fun i a => splitFourthObservable A ξ δ bW i a)
    (fun i a => splitFourthShift A ξ δ t r bShift i bg a)
      ∂splitBaseLaw μ ξ t

/-- The canonical actual support rows and retained-row representatives
discharge every array premise of paired restoration. -/
theorem abs_splitFourthRestorationExperiment_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t r C T : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (bY bW bShift : Bool)
    (hmatrix : AveragedSelectorMatrixEstimate s (splitBaseLaw μ ξ t)
      (splitGaussianScale t • A) (splitBaseValue A x t) C T)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hband : 4 * δ * restorationBandwidthConstant C ≤ s.bandwidth) :
    |splitFourthRestorationExperiment s μ ξ A δ x t r bY bW bShift| ≤
      84 * C ^ 3 * δ ^ 2 * T / (s.bandwidth ^ 2 * t) := by
  let Z : ((Fin n → Vector p) × Vector p) → Fin n → (Ω × Ω) → Vector p :=
    fun _ i a => boundedSupportObservation A ξ δ i a.1
  let Y := fun (_ : (Fin n → Vector p) × Vector p) i a => splitFourthObservable A ξ δ bY i a
  let W := fun (_ : (Fin n → Vector p) × Vector p) i a => splitFourthObservable A ξ δ bW i a
  let v := fun i bg a => splitFourthShift A ξ δ t r bShift i bg a
  have hZm (i : Fin n) : Measurable
      (fun wa : (((Fin n → Vector p) × Vector p) × (Ω × Ω)) => Z wa.1 i wa.2) :=
    (boundedSupportObservation_measurable h A i).comp (measurable_fst.comp measurable_snd)
  have hZi (bg : (Fin n → Vector p) × Vector p) (i : Fin n) (j l : Fin p) :
      Integrable (fun a => Z bg i a j * Z bg i a l) (μ.prod μ) := by
    simpa only [mul_one, Z] using
      (boundedSupportObservation_second_moments_integrable h A hA i j l).mul_prod
        (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
  have hYm (i : Fin n) : Measurable
      (fun wa : (((Fin n → Vector p) × Vector p) × (Ω × Ω)) => Y wa.1 i wa.2) :=
    (splitFourthObservable_measurable h A bY i).comp measurable_snd
  have hWm (i : Fin n) : Measurable
      (fun wa : (((Fin n → Vector p) × Vector p) × (Ω × Ω)) => W wa.1 i wa.2) :=
    (splitFourthObservable_measurable h A bW i).comp measurable_snd
  have hvm (i : Fin n) : Measurable
      (fun wa : (((Fin n → Vector p) × Vector p) × (Ω × Ω)) => v i wa.1 wa.2) :=
    (((splitFourthObservable_measurable h A bShift i).comp measurable_snd).const_smul
      (thinningScale t * r)).sub
        ((boundedRetainedObservation_measurable δ i).comp (measurable_fst.comp measurable_fst))
  have hb (bg : (Fin n → Vector p) × Vector p) (u : Vector p) :
      (∑ i, ∫ a, (faceDot u (Z bg i a)) ^ 2 ∂μ.prod μ) ≤ 1 * vectorNormSq u := by
    calc
      _ = ∑ i, ∫ a, (faceDot u (boundedSupportObservation A ξ δ i a)) ^ 2 ∂μ := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_fst_probability μ (fun a => (faceDot u (boundedSupportObservation A ξ δ i a)) ^ 2)
      _ ≤ _ := by simpa only [one_mul] using boundedSupportObservation_covariance_budget h A hA u
  have hs := restorationFourth_le_of_matrixEstimate s (splitBaseLaw μ ξ t) (μ.prod μ) A
    (ne_of_gt (splitGaussianScale_pos ht)) (splitBaseValue A x t) Z Y W v
    hmatrix (measurable_splitBaseValue A x t) hZm hZi hYm hWm hvm h.delta_nonneg
    (fun _ i a => splitFourthObservable_norm_le A ξ h.delta_nonneg bY i a)
    (fun _ i a => splitFourthObservable_norm_le A ξ h.delta_nonneg bW i a)
    (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) h.delta_nonneg)
    (fun i bg a => splitFourthShift_norm_le A ξ h.delta_nonneg ht.le ht1 hr bShift i bg a)
    hb hC hT (by simpa only [mul_comm] using hband)
  have hs' := hs.2
  change |splitFourthRestorationExperiment s μ ξ A δ x t r bY bW bShift| ≤ _ at hs'
  apply hs'.trans_eq
  rw [splitGaussianScale_sq ht.le]
  field_simp [ne_of_gt ht, ne_of_gt s.bandwidth_pos]
  ring

private def fourthTensorDomination {p : ℕ} (s : FaceSmoother p) (δ : ℝ) : ℝ :=
  (p : ℝ) ^ 4 * (75 / s.bandwidth ^ 4) * δ ^ 4

private theorem norm_fourthTensor_le {p : ℕ} (s : FaceSmoother p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (x u v w z : Vector p)
    {δ : ℝ} (hδ : 0 ≤ δ) (hu : ‖u‖ ≤ δ) (hv : ‖v‖ ≤ δ)
    (hw : ‖w‖ ≤ δ) (hz : ‖z‖ ≤ δ) :
    ‖s.convolutionFourthTensor ν x u v w z‖ ≤ fourthTensorDomination s δ := by
  have hj (j k l m : Fin p) :
      ‖s.convolutionFourthDerivative ν x j k l m * u j * v k * w l * z m‖ ≤
        (75 / s.bandwidth ^ 4) * δ * δ * δ * δ := by
    have hD : 0 ≤ 75 / s.bandwidth ^ 4 := by positivity
    have h1 := mul_le_mul (s.norm_convolutionFourthDerivative_le ν x j k l m)
      ((norm_le_pi_norm u j).trans hu) (norm_nonneg _) hD
    have h2 := mul_le_mul h1 ((norm_le_pi_norm v k).trans hv) (norm_nonneg _)
      (mul_nonneg hD hδ)
    have h3 := mul_le_mul h2 ((norm_le_pi_norm w l).trans hw) (norm_nonneg _)
      (mul_nonneg (mul_nonneg hD hδ) hδ)
    have h4 := mul_le_mul h3 ((norm_le_pi_norm z m).trans hz) (norm_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hD hδ) hδ) hδ)
    simpa only [norm_mul] using h4
  unfold FaceSmoother.convolutionFourthTensor
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m, (75 / s.bandwidth ^ 4) * δ * δ * δ * δ := by
      apply norm_sum_le_of_le
      intro j _
      apply norm_sum_le_of_le
      intro k _
      apply norm_sum_le_of_le
      intro l _
      apply norm_sum_le_of_le
      intro m _
      exact hj j k l m
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, fourthTensorDomination]; ring

private theorem measurable_fourthTensor_comp
    {X : Type*} [MeasurableSpace X] {p : ℕ} (s : FaceSmoother p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (B U V W Z : X → Vector p) (hB : Measurable B) (hU : Measurable U)
    (hV : Measurable V) (hW : Measurable W) (hZ : Measurable Z) :
    Measurable (fun a => s.convolutionFourthTensor ν (B a) (U a) (V a) (W a) (Z a)) := by
  unfold FaceSmoother.convolutionFourthTensor
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro l _
  exact Finset.measurable_sum _ (fun m _ =>
    (((((s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).measurable.comp hB).mul
      ((measurable_pi_apply j).comp hU)).mul ((measurable_pi_apply k).comp hV)).mul
        ((measurable_pi_apply l).comp hW)).mul ((measurable_pi_apply m).comp hZ))

private theorem integrable_measurable_bounded
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsFiniteMeasure ρ]
    (f : X → ℝ) (hf : Measurable f) {D : ℝ} (hb : ∀ a, ‖f a‖ ≤ D) :
    Integrable f ρ := (integrable_const D).mono' hf.aestronglyMeasurable
      (ae_of_all _ hb)

private theorem measurable_integral_bounded
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ρ : Measure Y) [SFinite ρ] (f : X × Y → ℝ) (hf : Measurable f) :
    Measurable (fun x => ∫ y, f (x, y) ∂ρ) :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

private theorem norm_integral_bounded
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]
    (f : X → ℝ) {D : ℝ} (hb : ∀ x, ‖f x‖ ≤ D) : ‖∫ x, f x ∂ρ‖ ≤ D := by
  simpa only [measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := ρ) (ae_of_all _ hb)

def splitFourthArrayKernel
    {Ω : Type*} {p n : ℕ} (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (δ : ℝ) (x : Vector p) (t r : ℝ) (bY bW bShift : Bool)
    (i : Fin n) (b : Fin n → Vector p) (a : Ω × Ω) : ℝ :=
  s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • A))
    (x + arraySum b + ((thinningScale t * r) • splitFourthObservable A ξ δ bShift i a -
      boundedRetainedObservation δ b i))
    (splitFourthObservable A ξ δ false i a) (splitFourthObservable A ξ δ false i a)
    (splitFourthObservable A ξ δ bY i a) (splitFourthObservable A ξ δ bW i a)

def splitFourthArrayExperiment
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (δ : ℝ) (x : Vector p) (t r : ℝ) (bY bW bShift : Bool) : ℝ :=
  ∫ b, ∑ i, ∫ a, splitFourthArrayKernel s ξ A δ x t r bY bW bShift i b a
    ∂μ.prod μ ∂bernoulliArrayLaw μ ξ t

private theorem arraySum_update_zero {p n : ℕ} (b : Fin n → Vector p) (i : Fin n) :
    arraySum (Function.update b i 0) = arraySum b - b i := by
  classical
  unfold arraySum
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), zero_add]
  apply (eq_sub_iff_add_eq).mpr
  simpa only [Finset.sum_singleton] using Finset.sum_sdiff
    (f := b) (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))

private theorem retainedArray_remove {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (t : ℝ) (mask : Kane.Cube n) (ω : Ω) (i : Fin n) :
    arraySum (retainedArray ξ t mask ω) - retainedArray ξ t mask ω i =
      thinningScale t • maskObservationSum ξ (Function.update mask i false) ω := by
  classical
  have heq : retainedArray ξ t (Function.update mask i false) ω =
      Function.update (retainedArray ξ t mask ω) i 0 := by
    funext j
    by_cases hj : j = i
    · subst j; simp [retainedArray]
    · simp [retainedArray, Function.update_of_ne hj]
  rw [← arraySum_update_zero, ← heq, arraySum_retainedArray_eq_maskObservationSum]

private theorem integral_bernoulliArrayLaw_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (G : (Fin n → Vector p) → ℝ)
    (hG : Measurable G) {D : ℝ} (hGb : ∀ b, ‖G b‖ ≤ D) :
    (∫ b, G b ∂bernoulliArrayLaw μ ξ t) =
      ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ ω, G (retainedArray ξ t mask ω) ∂μ := by
  have hi (mask : Kane.Cube n) : Integrable G (μ.map (retainedArray ξ t mask)) := by
    letI : IsProbabilityMeasure (μ.map (retainedArray ξ t mask)) :=
      isProbabilityMeasure_map (μ := μ) (measurable_retainedArray ξ hξ t mask).aemeasurable
    exact integrable_measurable_bounded _ G hG hGb
  rw [bernoulliArrayLaw, integral_bernoulliMixtureLaw μ (retainedArray ξ t)
    (thinningProbability t) (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) G hi]
  apply Finset.sum_congr rfl
  intro mask _
  rw [integral_map (measurable_retainedArray ξ hξ t mask).aemeasurable hG.aestronglyMeasurable]

/-- Exact deletion-of-one-row transport under the full actual Bernoulli
array law. The kernel is bounded only to justify Fubini; its bound is absent
from the identity. -/
private theorem retained_leaveRow_kernel
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (K : Fin n → Vector p → Ξ → ℝ)
    (hKm : ∀ i, Measurable (fun ya : Vector p × Ξ => K i ya.1 ya.2))
    {D : ℝ} (hKb : ∀ i y a, ‖K i y a‖ ≤ D)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ b, ∑ i, ∫ a, K i (x + arraySum b - b i) a ∂ρ ∂bernoulliArrayLaw μ ξ t) =
      ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ z : Ω × Ξ, K i (x + thinningScale t •
          maskObservationSum ξ (Function.update mask i false) z.1) z.2 ∂μ.prod ρ := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  let G : Fin n → (Fin n → Vector p) → ℝ :=
    fun i b => ∫ a, K i (x + arraySum b - b i) a ∂ρ
  have hGm (i : Fin n) : Measurable (G i) := by
    change Measurable (fun b => ∫ a, K i (x + arraySum b - b i) a ∂ρ)
    exact measurable_integral_bounded ρ
      (fun ba : (Fin n → Vector p) × Ξ => K i (x + arraySum ba.1 - ba.1 i) ba.2)
      ((hKm i).comp
        (((measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).sub
          ((measurable_pi_apply i).comp measurable_fst)).prodMk measurable_snd))
  have hGb (i : Fin n) (b : Fin n → Vector p) : ‖G i b‖ ≤ D :=
    norm_integral_bounded ρ _ (hKb i _)
  have hGi (i : Fin n) : Integrable (G i) (bernoulliArrayLaw μ ξ t) :=
    integrable_measurable_bounded _ _ (hGm i) (hGb i)
  rw [integral_finset_sum Finset.univ (fun i _ => hGi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_bernoulliArrayLaw_bounded μ ξ hξ ht ht1 (G i) (hGm i) (hGb i)]
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  have hbase : Measurable (fun ω => x + thinningScale t •
      maskObservationSum ξ (Function.update mask i false) ω) :=
    measurable_const.add (measurable_const.smul
      (measurable_maskObservationSum ξ hξ _))
  have hm : Measurable (fun z : Ω × Ξ => K i
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1) z.2) :=
    (hKm i).comp ((hbase.comp measurable_fst).prodMk measurable_snd)
  have hi := integrable_measurable_bounded (μ.prod ρ) _ hm (fun z => hKb i _ _)
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by
    dsimp only [G]
    rw [show x + arraySum (retainedArray ξ t mask ω) - retainedArray ξ t mask ω i =
      x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω by
        rw [add_sub_assoc, retainedArray_remove]])


private theorem integral_fourthTensor_gaussian_split
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {p n : ℕ}
    (s : FaceSmoother p) (ν : Measure X) [IsProbabilityMeasure ν]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ)
    (B U V W Z : Fin n → X × Y → Vector p)
    (hB : ∀ i, Measurable (B i)) (hU : ∀ i, Measurable (U i))
    (hV : ∀ i, Measurable (V i)) (hW : ∀ i, Measurable (W i))
    (hZ : ∀ i, Measurable (Z i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hUb : ∀ i a, ‖U i a‖ ≤ δ) (hVb : ∀ i a, ‖V i a‖ ≤ δ)
    (hWb : ∀ i a, ‖W i a‖ ≤ δ) (hZb : ∀ i a, ‖Z i a‖ ≤ δ) :
    (∫ x, ∑ i, ∫ a, s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • A))
      (B i (x, a)) (U i (x, a)) (V i (x, a)) (W i (x, a)) (Z i (x, a)) ∂ρ ∂ν) =
    ∫ xg, ∑ i, ∫ a, s.convolutionFourthTensor (gaussianLaw (splitGaussianScale t • A))
      (B i (xg.1, a) + (splitGaussianScale t • A).mulVec xg.2)
      (U i (xg.1, a)) (V i (xg.1, a)) (W i (xg.1, a)) (Z i (xg.1, a))
        ∂ρ ∂ν.prod (standardGaussian p) := by
  let H (i : Fin n) (ba : (X × Vector p) × Y) :=
    s.convolutionFourthTensor (gaussianLaw (splitGaussianScale t • A))
      (B i (ba.1.1, ba.2) + (splitGaussianScale t • A).mulVec ba.1.2)
      (U i (ba.1.1, ba.2)) (V i (ba.1.1, ba.2))
      (W i (ba.1.1, ba.2)) (Z i (ba.1.1, ba.2))
  have hproj : Measurable (fun ba : (X × Vector p) × Y => (ba.1.1, ba.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hHm (i : Fin n) : Measurable (H i) :=
    measurable_fourthTensor_comp s _ _ _ _ _ _
      (((hB i).comp hproj).add ((measurable_mulVec _).comp
        (measurable_snd.comp measurable_fst)))
      ((hU i).comp hproj) ((hV i).comp hproj) ((hW i).comp hproj) ((hZ i).comp hproj)
  have hHb (i : Fin n) (ba : (X × Vector p) × Y) :
      ‖H i ba‖ ≤ fourthTensorDomination s δ :=
    norm_fourthTensor_le s _ _ _ _ _ _ hδ (hUb i _) (hVb i _) (hWb i _) (hZb i _)
  have hGm (i : Fin n) : Measurable (fun xg => ∫ a, H i (xg, a) ∂ρ) :=
    measurable_integral_bounded ρ (H i) (hHm i)
  have hGb (i : Fin n) (xg : X × Vector p) :
      ‖∫ a, H i (xg, a) ∂ρ‖ ≤ fourthTensorDomination s δ :=
    norm_integral_bounded ρ _ (fun a => hHb i _)
  have hsum : Integrable (fun xg => ∑ i, ∫ a, H i (xg, a) ∂ρ)
      (ν.prod (standardGaussian p)) :=
    integrable_finset_sum _ (fun i _ =>
      integrable_measurable_bounded _ _ (hGm i) (hGb i))
  change _ = ∫ xg, ∑ i, ∫ a, H i (xg, a) ∂ρ ∂ν.prod (standardGaussian p)
  rw [integral_prod _ hsum]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hsection (i : Fin n) : Integrable (fun g => ∫ a, H i ((x, g), a) ∂ρ)
      (standardGaussian p) :=
    integrable_measurable_bounded _ _
      ((hGm i).comp (measurable_const.prodMk measurable_id)) (fun g => hGb i _)
  dsimp only
  rw [integral_finset_sum _ (fun i _ => hsection i)]
  apply Finset.sum_congr rfl
  intro i _
  have hjoint : Measurable (fun ag : Y × Vector p => H i ((x, ag.2), ag.1)) :=
    (hHm i).comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
  have hi := integrable_measurable_bounded (ρ.prod (standardGaussian p)) _ hjoint
    (fun ag => hHb i _)
  calc
    _ = ∫ a, ∫ g, H i ((x, g), a) ∂standardGaussian p ∂ρ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun a => s.convolutionFourthTensor_gaussian_split A t
        (B i (x, a)) (U i (x, a)) (V i (x, a)) (W i (x, a)) (Z i (x, a)))
    _ = _ := integral_integral_swap hi


theorem splitFourthArrayExperiment_eq_restoration
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {t r : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (bY bW bShift : Bool) :
    splitFourthArrayExperiment s μ ξ A δ x t r bY bW bShift =
      splitFourthRestorationExperiment s μ ξ A δ x t r bY bW bShift := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  let B : Fin n → (Fin n → Vector p) × (Ω × Ω) → Vector p :=
    fun i ba => x + arraySum ba.1 + ((thinningScale t * r) •
      splitFourthObservable A ξ δ bShift i ba.2 - boundedRetainedObservation δ ba.1 i)
  let O : Bool → Fin n → (Fin n → Vector p) × (Ω × Ω) → Vector p :=
    fun b i ba => splitFourthObservable A ξ δ b i ba.2
  have hBm (i : Fin n) : Measurable (B i) :=
    (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
      ((((splitFourthObservable_measurable h A bShift i).comp measurable_snd).const_smul
        (thinningScale t * r)).sub
          ((boundedRetainedObservation_measurable δ i).comp measurable_fst))
  have hOm (b : Bool) (i : Fin n) : Measurable (O b i) :=
    (splitFourthObservable_measurable h A b i).comp measurable_snd
  have hOb (b : Bool) (i : Fin n) (ba : (Fin n → Vector p) × (Ω × Ω)) :
      ‖O b i ba‖ ≤ δ := splitFourthObservable_norm_le A ξ h.delta_nonneg b i _
  have hs := integral_fourthTensor_gaussian_split s (bernoulliArrayLaw μ ξ t) (μ.prod μ) A t
    B (O false) (O false) (O bY) (O bW) hBm (hOm false) (hOm false) (hOm bY) (hOm bW)
    h.delta_nonneg (hOb false) (hOb false) (hOb bY) (hOb bW)
  change splitFourthArrayExperiment s μ ξ A δ x t r bY bW bShift = _ at hs
  rw [hs]
  apply integral_congr_ae
  apply ae_of_all
  intro bg
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  apply ae_of_all
  intro a
  change s.convolutionFourthTensor _ (B i (bg.1, a) + _) _ _ _ _ =
    s.convolutionFourthTensor _ (splitBaseValue A x t bg + splitFourthShift A ξ δ t r bShift i bg a)
      _ _ _ _
  have hb : B i (bg.1, a) + (splitGaussianScale t • A).mulVec bg.2 =
      splitBaseValue A x t bg + splitFourthShift A ξ δ t r bShift i bg a := by
    dsimp only [B, splitBaseValue, splitFourthShift]
    abel
  rw [hb]
  rfl


def splitFourthMaskExperiment
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (δ : ℝ) (x : Vector p) (t r : ℝ) (bY bW bShift : Bool) : ℝ :=
  ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • A))
      (FaceSmoother.line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (splitFourthObservable A ξ δ bShift i z.2) (thinningScale t * r))
      (splitFourthObservable A ξ δ false i z.2) (splitFourthObservable A ξ δ false i z.2)
      (splitFourthObservable A ξ δ bY i z.2) (splitFourthObservable A ξ δ bW i z.2)
        ∂μ.prod (μ.prod μ)

theorem splitFourthArrayExperiment_eq_mask
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {t r : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (bY bW bShift : Bool) :
    splitFourthArrayExperiment s μ ξ A δ x t r bY bW bShift =
      splitFourthMaskExperiment s μ ξ A δ x t r bY bW bShift := by
  let K (i : Fin n) (y : Vector p) (a : Ω × Ω) :=
    s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • A))
      (y + (thinningScale t * r) • splitFourthObservable A ξ δ bShift i a)
      (splitFourthObservable A ξ δ false i a) (splitFourthObservable A ξ δ false i a)
      (splitFourthObservable A ξ δ bY i a) (splitFourthObservable A ξ δ bW i a)
  have hKm (i : Fin n) : Measurable (fun ya : Vector p × (Ω × Ω) => K i ya.1 ya.2) :=
    measurable_fourthTensor_comp s _ _ _ _ _ _
      (measurable_fst.add (((splitFourthObservable_measurable h A bShift i).comp
        measurable_snd).const_smul (thinningScale t * r)))
      ((splitFourthObservable_measurable h A false i).comp measurable_snd)
      ((splitFourthObservable_measurable h A false i).comp measurable_snd)
      ((splitFourthObservable_measurable h A bY i).comp measurable_snd)
      ((splitFourthObservable_measurable h A bW i).comp measurable_snd)
  have hKb (i : Fin n) (y : Vector p) (a : Ω × Ω) :
      ‖K i y a‖ ≤ fourthTensorDomination s δ :=
    norm_fourthTensor_le s _ _ _ _ _ _ h.delta_nonneg
      (splitFourthObservable_norm_le A ξ h.delta_nonneg false i a)
      (splitFourthObservable_norm_le A ξ h.delta_nonneg false i a)
      (splitFourthObservable_norm_le A ξ h.delta_nonneg bY i a)
      (splitFourthObservable_norm_le A ξ h.delta_nonneg bW i a)
  calc
    _ = ∫ b, ∑ i, ∫ a, K i (x + arraySum b - b i) a ∂μ.prod μ
        ∂bernoulliArrayLaw μ ξ t := by
      apply integral_congr_ae
      filter_upwards [boundedRetainedObservation_eq_ae h ht ht1] with b hb
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      apply ae_of_all
      intro a
      have hbi : boundedRetainedObservation δ b i = b i := congrFun hb i
      change s.convolutionFourthTensor _ (x + arraySum b + (_ - _)) _ _ _ _ =
        s.convolutionFourthTensor _ ((x + arraySum b - b i) + _) _ _ _ _
      rw [hbi]
      congr 1
      abel
    _ = _ := retained_leaveRow_kernel μ (μ.prod μ) ξ h.measurable K hKm hKb x ht ht1


theorem splitFourthObservable_eq_ae
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (b : Bool) (i : Fin n) :
    splitFourthObservable A ξ δ b i =ᵐ[μ.prod μ]
      (fun a => ξ i (splitFourthSample b a)) := by
  cases b
  · change (fun a : Ω × Ω => A.mulVec (boundedSupportObservation A ξ δ i a.1)) =ᵐ[μ.prod μ]
      (fun a => ξ i a.1)
    exact Measure.quasiMeasurePreserving_fst.ae (boundedSupportObservation_reconstruct h A hA i)
  · change (fun a : Ω × Ω => A.mulVec (boundedSupportObservation A ξ δ i a.2)) =ᵐ[μ.prod μ]
      (fun a => ξ i a.2)
    exact Measure.quasiMeasurePreserving_snd.ae (boundedSupportObservation_reconstruct h A hA i)

def splitFourthOriginalMaskExperiment
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (t r : ℝ) (bY bW bShift : Bool) : ℝ :=
  ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • A))
      (FaceSmoother.line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i (splitFourthSample bShift z.2)) (thinningScale t * r))
      (ξ i z.2.1) (ξ i z.2.1)
      (ξ i (splitFourthSample bY z.2)) (ξ i (splitFourthSample bW z.2))
        ∂μ.prod (μ.prod μ)

theorem splitFourthMaskExperiment_eq_original
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (t r : ℝ) (bY bW bShift : Bool) :
    splitFourthMaskExperiment s μ ξ A δ x t r bY bW bShift =
      splitFourthOriginalMaskExperiment s μ ξ A x t r bY bW bShift := by
  unfold splitFourthMaskExperiment splitFourthOriginalMaskExperiment
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro mask _
  apply congrArg (fun v : ℝ => Kane.maskWeight (thinningProbability t) mask * v)
  apply integral_congr_ae
  have hrec (b : Bool) : ∀ᵐ z : Ω × (Ω × Ω) ∂μ.prod (μ.prod μ),
      splitFourthObservable A ξ δ b i z.2 = ξ i (splitFourthSample b z.2) :=
    Measure.quasiMeasurePreserving_snd.ae (splitFourthObservable_eq_ae h A hA b i)
  filter_upwards [hrec false, hrec bY, hrec bW, hrec bShift] with z h0 hY hW hS
  change splitFourthObservable A ξ δ false i z.2 = ξ i z.2.1 at h0
  have hargs :
      (splitFourthObservable A ξ δ bShift i z.2,
        (splitFourthObservable A ξ δ false i z.2,
          (splitFourthObservable A ξ δ bY i z.2, splitFourthObservable A ξ δ bW i z.2))) =
      (ξ i (splitFourthSample bShift z.2),
        (ξ i z.2.1, (ξ i (splitFourthSample bY z.2), ξ i (splitFourthSample bW z.2)))) :=
    Prod.ext hS (Prod.ext h0 (Prod.ext hY hW))
  have heq := congrArg
    (fun v : Vector p × (Vector p × (Vector p × Vector p)) =>
      s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • A))
        (FaceSmoother.line
          (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
          v.1 (thinningScale t * r)) v.2.1 v.2.1 v.2.2.1 v.2.2.2)
    hargs
  exact heq

theorem splitFourthOriginalMaskExperiment_false_eq_A
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t r : ℝ) :
    splitFourthOriginalMaskExperiment s μ ξ A x t r false false false =
      s.fourthPathIntegrandA (gaussianLaw (Real.sqrt t • A)) μ ξ x t r := by
  unfold splitFourthOriginalMaskExperiment FaceSmoother.fourthPathIntegrandA
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  exact integral_prod_drop_fresh_copy μ (fun z : Ω × Ω =>
    s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • A))
      (FaceSmoother.line (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2) (thinningScale t * r))
      (ξ i z.2) (ξ i z.2) (ξ i z.2) (ξ i z.2))

theorem splitFourthOriginalMaskExperiment_true_eq_B
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t r : ℝ) :
    splitFourthOriginalMaskExperiment s μ ξ A x t r true true true =
      s.fourthPathIntegrandB (gaussianLaw (Real.sqrt t • A)) μ ξ x t r := rfl

theorem splitFourthOriginalMaskExperiment_mixed_eq_C
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t r : ℝ) :
    splitFourthOriginalMaskExperiment s μ ξ A x t r false true true =
      s.fourthPathIntegrandC (gaussianLaw (Real.sqrt t • A)) μ ξ x t r := rfl


theorem abs_splitFourthOriginalMaskExperiment_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t r C T : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) (bY bW bShift : Bool)
    (hmatrix : AveragedSelectorMatrixEstimate s (splitBaseLaw μ ξ t)
      (splitGaussianScale t • A) (splitBaseValue A x t) C T)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hband : 4 * restorationBandwidthConstant C * δ ≤ s.bandwidth) :
    |splitFourthOriginalMaskExperiment s μ ξ A x t r bY bW bShift| ≤
      84 * C ^ 3 * δ ^ 2 * T / (s.bandwidth ^ 2 * t) := by
  rw [← splitFourthMaskExperiment_eq_original s μ ξ h A hA x t r bY bW bShift,
    ← splitFourthArrayExperiment_eq_mask s μ ξ h A x ht.le ht1 bY bW bShift,
    splitFourthArrayExperiment_eq_restoration s μ ξ h A x ht.le ht1 bY bW bShift]
  exact abs_splitFourthRestorationExperiment_le s μ ξ h A hA x ht ht1 hr bY bW bShift
    hmatrix hC hT (by nlinarith only [hband])

end
end RectangleCLT.Companion


namespace RectangleCLT.FaceSmoother

noncomputable section
set_option autoImplicit false

/-- Actual signed fourth-order A path cap under the genuine split-base
selector matrix estimate. No covariance nonsingularity is assumed. -/
theorem abs_fourthPathIntegrandA_le_of_split_matrix_estimate
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t r C T : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hmatrix : Companion.AveragedSelectorMatrixEstimate s (Companion.splitBaseLaw μ ξ t)
      (Companion.splitGaussianScale t • A) (Companion.splitBaseValue A x t) C T)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hband : 4 * Companion.restorationBandwidthConstant C * δ ≤ s.bandwidth) :
    |s.fourthPathIntegrandA (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
      84 * C ^ 3 * δ ^ 2 * T / (s.bandwidth ^ 2 * t) := by
  rw [← Companion.splitFourthOriginalMaskExperiment_false_eq_A s μ ξ A x t r]
  exact Companion.abs_splitFourthOriginalMaskExperiment_le s μ ξ h A hA x ht ht1 hr
    false false false hmatrix hC hT hband

/-- Actual signed fourth-order B path cap under the genuine split-base
selector matrix estimate. No covariance nonsingularity is assumed. -/
theorem abs_fourthPathIntegrandB_le_of_split_matrix_estimate
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t r C T : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hmatrix : Companion.AveragedSelectorMatrixEstimate s (Companion.splitBaseLaw μ ξ t)
      (Companion.splitGaussianScale t • A) (Companion.splitBaseValue A x t) C T)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hband : 4 * Companion.restorationBandwidthConstant C * δ ≤ s.bandwidth) :
    |s.fourthPathIntegrandB (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
      84 * C ^ 3 * δ ^ 2 * T / (s.bandwidth ^ 2 * t) := by
  rw [← Companion.splitFourthOriginalMaskExperiment_true_eq_B s μ ξ A x t r]
  exact Companion.abs_splitFourthOriginalMaskExperiment_le s μ ξ h A hA x ht ht1 hr
    true true true hmatrix hC hT hband

/-- Actual signed fourth-order C path cap under the genuine split-base
selector matrix estimate. No covariance nonsingularity is assumed. -/
theorem abs_fourthPathIntegrandC_le_of_split_matrix_estimate
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {t r C T : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hmatrix : Companion.AveragedSelectorMatrixEstimate s (Companion.splitBaseLaw μ ξ t)
      (Companion.splitGaussianScale t • A) (Companion.splitBaseValue A x t) C T)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hband : 4 * Companion.restorationBandwidthConstant C * δ ≤ s.bandwidth) :
    |s.fourthPathIntegrandC (gaussianLaw (Real.sqrt t • A)) μ ξ x t r| ≤
      84 * C ^ 3 * δ ^ 2 * T / (s.bandwidth ^ 2 * t) := by
  rw [← Companion.splitFourthOriginalMaskExperiment_mixed_eq_C s μ ξ A x t r]
  exact Companion.abs_splitFourthOriginalMaskExperiment_le s μ ξ h A hA x ht ht1 hr
    false true true hmatrix hC hT hband

end
end RectangleCLT.FaceSmoother
