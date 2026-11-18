import RectangleCLTArxivV1.SupplementalIExceptional
import RectangleCLTArxivV1.SupplementalGTimeMeasurability

/-! Honest integration of the separated/exceptional decomposition through
the calibrated scalar kernels. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cap_parameter_copy_sum_measurable
    {G B C : Type*} [MeasurableSpace G] [MeasurableSpace B] [MeasurableSpace C] {n : ℕ}
    (μG : Measure G) [SFinite μG] (μB : Measure B) [SFinite μB] (μC : Measure C) [SFinite μC]
    (F : Fin n → ℝ → G → B → C → ℝ)
    (hF : ∀ i, Measurable (fun z : ((ℝ × G) × B) × C => F i z.1.1.1 z.1.1.2 z.1.2 z.2)) :
    Measurable (fun θ => ∫ g, ∫ b, ∑ i, ∫ c, F i θ g b c ∂μC ∂μB ∂μG) := by
  have hi (i : Fin n) : Measurable (fun z : (ℝ × G) × B => ∫ c, F i z.1.1 z.1.2 z.2 c ∂μC) :=
    (hF i).stronglyMeasurable.integral_prod_right'.measurable
  have hs : Measurable (fun z : (ℝ × G) × B => ∑ i, ∫ c, F i z.1.1 z.1.2 z.2 c ∂μC) :=
    Finset.measurable_sum _ (fun i _ => hi i)
  exact hs.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

theorem capSeededPairContribution_measurable_theta
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin r) ℝ)
    (s : FaceSmoother p) (x : Vector p) (ε : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f g : Face p) (freshY freshW freshShift : Bool) :
    Measurable (fun θ => capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift) := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht.1 ht.2
  let B := (Fin n → Vector p) × Vector r
  let M := (seededSplitGaussianScale ε t • A)
  let F := fun (i : Fin n) (θ : ℝ) (z : Vector r) (ω : B) (a : Ω × Ω) =>
    (capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i a)
      (capOriginalCopy ξ freshW i a)*repeatedDirectionScore z (capWhitenedCopy A ξ i a))*
      selectorTupleWeight s ![f,g] (M.mulVec z+capSeededBaseValue A x ε t ω+
        capSeededCopyShift ξ freshShift t θ i (ω,a))
  have hF (i : Fin n) : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
      F i z.1.1.1 z.1.1.2 z.1.2 z.2) := by
    have hY := (capOriginalCopy_measurable ξ hξ freshY i).comp
      (measurable_snd : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) => z.2))
    have hW := (capOriginalCopy_measurable ξ hξ freshW i).comp
      (measurable_snd : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) => z.2))
    have hC : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
        capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i z.2)
          (capOriginalCopy ξ freshW i z.2)) := by
      unfold capRectangularPairCoefficient
      exact (((continuous_normalDot f).measurable.comp hY).mul
        ((continuous_normalDot g).measurable.comp hW)).add
        (((continuous_normalDot g).measurable.comp hY).mul
          ((continuous_normalDot f).measurable.comp hW)) |>.sub
          (measurable_const.mul ((((continuous_normalDot f).measurable.comp hY).mul
            ((continuous_normalDot f).measurable.comp hW)).add
            (((continuous_normalDot g).measurable.comp hY).mul
              ((continuous_normalDot g).measurable.comp hW))))
    have hZ : Measurable (capWhitenedCopy A ξ i) := by
      unfold capWhitenedCopy whitenedObservation
      exact (continuous_const.matrix_mulVec continuous_id).measurable.comp ((hξ i).comp measurable_fst)
    have hscore : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
        repeatedDirectionScore z.1.1.2 (capWhitenedCopy A ξ i z.2)) :=
      by
        unfold repeatedDirectionScore faceDot vectorNormSq
        fun_prop
    have hshift : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
        capSeededCopyShift ξ freshShift t z.1.1.1 i (z.1.2,z.2)) := by
      unfold capSeededCopyShift
      exact (measurable_fst.fst.fst.mul_const (1+t)).smul
        ((capOriginalCopy_measurable ξ hξ freshShift i).comp measurable_snd) |>.sub
        ((measurable_pi_apply i).comp measurable_fst.snd.fst)
    have hpoint : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
        M.mulVec z.1.1.2+capSeededBaseValue A x ε t z.1.2+
          capSeededCopyShift ξ freshShift t z.1.1.1 i (z.1.2,z.2)) :=
      (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_fst.fst.snd).add
        ((capSeededBaseValue_measurable A x ε t).comp measurable_fst.snd)).add hshift
    exact (hC.mul hscore).mul (measurable_selectorTupleWeight_comp s ![f,g] _ hpoint)
  exact (cap_parameter_copy_sum_measurable (standardGaussian r)
    ((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) (μ.prod μ) F hF).const_mul _

theorem capSeededSingleContribution_measurable_theta
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin r) ℝ)
    (s : FaceSmoother p) (x : Vector p) (ε : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f : Face p) (freshY freshW freshShift : Bool) :
    Measurable (fun θ => capSeededSingleContribution s μ ξ A x ε t θ f freshY freshW freshShift) := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht.1 ht.2
  let B := (Fin n → Vector p) × Vector r
  let M := (seededSplitGaussianScale ε t • A)
  let F := fun (i : Fin n) (θ : ℝ) (z : Vector r) (ω : B) (a : Ω × Ω) =>
    ((normalDot f (capOriginalCopy ξ freshY i a)*normalDot f (capOriginalCopy ξ freshW i a))*
      capThirdHermiteScore (capRectangularFactorNormal A f) (capWhitenedCopy A ξ i a) z)*
      selectorTupleWeight s ![f] (M.mulVec z+capSeededBaseValue A x ε t ω+
        capSeededCopyShift ξ freshShift t θ i (ω,a))
  have hF (i : Fin n) : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
      F i z.1.1.1 z.1.1.2 z.1.2 z.2) := by
    have hY := (capOriginalCopy_measurable ξ hξ freshY i).comp
      (measurable_snd : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) => z.2))
    have hW := (capOriginalCopy_measurable ξ hξ freshW i).comp
      (measurable_snd : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) => z.2))
    have hC : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
        normalDot f (capOriginalCopy ξ freshY i z.2)*normalDot f (capOriginalCopy ξ freshW i z.2)) :=
      ((continuous_normalDot f).measurable.comp hY).mul ((continuous_normalDot f).measurable.comp hW)
    have hZ : Measurable (capWhitenedCopy A ξ i) := by
      unfold capWhitenedCopy whitenedObservation
      exact (continuous_const.matrix_mulVec continuous_id).measurable.comp ((hξ i).comp measurable_fst)
    have hscore : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
        capThirdHermiteScore (capRectangularFactorNormal A f) (capWhitenedCopy A ξ i z.2) z.1.1.2) :=
      by
        unfold capThirdHermiteScore repeatedDirectionScore faceDot vectorNormSq
        fun_prop
    have hshift : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
        capSeededCopyShift ξ freshShift t z.1.1.1 i (z.1.2,z.2)) := by
      unfold capSeededCopyShift
      exact (measurable_fst.fst.fst.mul_const (1+t)).smul
        ((capOriginalCopy_measurable ξ hξ freshShift i).comp measurable_snd) |>.sub
        ((measurable_pi_apply i).comp measurable_fst.snd.fst)
    have hpoint : Measurable (fun z : ((ℝ × Vector r) × B) × (Ω × Ω) =>
        M.mulVec z.1.1.2+capSeededBaseValue A x ε t z.1.2+
          capSeededCopyShift ξ freshShift t z.1.1.1 i (z.1.2,z.2)) :=
      (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_fst.fst.snd).add
        ((capSeededBaseValue_measurable A x ε t).comp measurable_fst.snd)).add hshift
    exact (hC.mul hscore).mul (measurable_selectorTupleWeight_comp s ![f] _ hpoint)
  exact (cap_parameter_copy_sum_measurable (standardGaussian r)
    ((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) (μ.prod μ) F hF).const_mul _


theorem capSeededExceptionalPattern_measurable_theta
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin r) ℝ)
    (s : FaceSmoother p) (x : Vector p) (ε c : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (freshY freshW freshShift : Bool) :
    Measurable (fun θ => capSeededExceptionalPattern s μ ξ A x ε t θ c freshY freshW freshShift) := by
  classical
  apply Finset.measurable_sum
  intro f _
  apply Finset.measurable_sum
  intro g _
  split_ifs
  · exact capSeededPairContribution_measurable_theta μ ξ hξ A s x ε ht f g freshY freshW freshShift
  · exact measurable_const

theorem capSeededSeparatedPattern_measurable_theta
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin r) ℝ)
    (s : FaceSmoother p) (x : Vector p) (ε c : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (freshY freshW freshShift : Bool) :
    Measurable (fun θ => capSeededSeparatedPattern s μ ξ A x ε t θ c freshY freshW freshShift) := by
  classical
  apply Measurable.add
  · exact Finset.measurable_sum _ (fun f _ =>
      capSeededSingleContribution_measurable_theta μ ξ hξ A s x ε ht f freshY freshW freshShift)
  · apply Finset.measurable_sum
    intro f _
    apply Finset.measurable_sum
    intro g _
    split_ifs
    · exact capSeededPairContribution_measurable_theta μ ξ hξ A s x ε ht f g freshY freshW freshShift
    · exact measurable_const

/-- A genuine measurable scalar, bounded on the whole averaging interval,
is interval-integrable. -/
theorem cap_intervalIntegrable_measurable_of_Icc_bound
    {F : ℝ → ℝ} {D : ℝ} (hF : Measurable F) (hD : ∀ θ ∈ Set.Icc (0:ℝ) 1, |F θ| ≤ D) :
    IntervalIntegrable F volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ)≤1)]
  have hi : IntegrableOn (fun _ : ℝ => D) (Set.Icc (0:ℝ) 1) volume :=
    integrableOn_const.mpr (Or.inr (by norm_num [Real.volume_Icc]))
  apply hi.mono' hF.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  simpa only [Real.norm_eq_abs] using hD θ hθ

theorem capSeededExceptionalPattern_intervalIntegrable_theta
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) (c : ℝ)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0 < t+ε)
    (freshY freshW freshShift : Bool) :
    IntervalIntegrable (fun θ => capSeededExceptionalPattern s μ ξ A x ε t θ c freshY freshW freshShift) volume 0 1 := by
  exact cap_intervalIntegrable_measurable_of_Icc_bound
    (capSeededExceptionalPattern_measurable_theta μ ξ h.measurable A s x ε c ht freshY freshW freshShift)
    (fun θ hθ => cap_seeded_exceptional_pattern_bound h A hA hunit s hband x c hε ht hθ hpos freshY freshW freshShift)


theorem capSeededFourthPattern_measurable_theta
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (x : Vector p) (ε : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    Measurable (fun θ => capSeededFourthPattern s μ ξ A x ε t θ freshY freshW freshShift) := by
  have he : (fun θ => capSeededFourthPattern s μ ξ A x ε t θ freshY freshW freshShift)=
      fun θ => (∑ f, capSeededSingleContribution s μ ξ A x ε t θ f freshY freshW freshShift)+
        ∑ f, ∑ g, capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift := by
    funext θ
    exact cap_seeded_fourth_pattern_decomposition h A hA hunit s x ht hpos freshY freshW freshShift
  rw [he]
  exact (Finset.measurable_sum _ (fun f _ => capSeededSingleContribution_measurable_theta μ ξ h.measurable A s x ε ht f freshY freshW freshShift)).add
    (Finset.measurable_sum _ (fun f _ => Finset.measurable_sum _
      (fun g _ => capSeededPairContribution_measurable_theta μ ξ h.measurable A s x ε ht f g freshY freshW freshShift)))

theorem capSeededFourthPattern_intervalIntegrable_theta
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0 < t+ε)
    (freshY freshW freshShift : Bool) :
    IntervalIntegrable (fun θ => capSeededFourthPattern s μ ξ A x ε t θ freshY freshW freshShift) volume 0 1 := by
  exact cap_intervalIntegrable_measurable_of_Icc_bound
    (capSeededFourthPattern_measurable_theta h A hA hunit s x ε ht hpos freshY freshW freshShift)
    (fun θ hθ => cap_seeded_fourth_pattern_complementary_bound h A hA hunit hr s hband x hε ht hθ hpos freshY freshW freshShift)

theorem capSeededSeparatedPattern_intervalIntegrable_theta
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) {c : ℝ} (hc : 0 < c)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0 < t+ε)
    (freshY freshW freshShift : Bool) :
    IntervalIntegrable (fun θ => capSeededSeparatedPattern s μ ξ A x ε t θ c freshY freshW freshShift) volume 0 1 := by
  have he : (fun θ => capSeededSeparatedPattern s μ ξ A x ε t θ c freshY freshW freshShift)=
      fun θ => capSeededFourthPattern s μ ξ A x ε t θ freshY freshW freshShift-
        capSeededExceptionalPattern s μ ξ A x ε t θ c freshY freshW freshShift := by
    funext θ
    have hs := cap_seeded_fourth_pattern_exceptional_split h A hA hunit s x hc ht hpos freshY freshW freshShift (θ := θ)
    linarith
  rw [he]
  exact (capSeededFourthPattern_intervalIntegrable_theta h A hA hunit hr s hband x hε ht hpos freshY freshW freshShift).sub
    (capSeededExceptionalPattern_intervalIntegrable_theta h A hA hunit s hband x c hε ht hpos freshY freshW freshShift)

def capSeededKernelCombination (t : ℝ) (F : Bool → Bool → Bool → ℝ → ℝ) : ℝ :=
  (∫ θ in (0:ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) θ*F false false false θ)+
    (1-t)/2*(∫ θ in (0:ℝ)..1, (1-θ)*F true true true θ)+
    (t*(1-t)/(3*(1+t)))*(∫ θ in (0:ℝ)..1, F false true true θ)

theorem capSeededKernelCombination_add {t : ℝ}
    (F G H : Bool → Bool → Bool → ℝ → ℝ)
    (he : ∀ a b c θ, F a b c θ=G a b c θ+H a b c θ)
    (hG : ∀ a b c, IntervalIntegrable (G a b c) volume 0 1)
    (hH : ∀ a b c, IntervalIntegrable (H a b c) volume 0 1) :
    capSeededKernelCombination t F=capSeededKernelCombination t G+capSeededKernelCombination t H := by
  have hk : Continuous (seededFourthKernel (thinningScale t) (calibratedEta t)) := by
    unfold seededFourthKernel
    fun_prop
  have hl : Continuous (fun θ : ℝ => 1-θ) := continuous_const.sub continuous_id
  unfold capSeededKernelCombination
  simp_rw [he,mul_add]
  rw [intervalIntegral.integral_add ((hG false false false).continuousOn_mul hk.continuousOn)
      ((hH false false false).continuousOn_mul hk.continuousOn),
    intervalIntegral.integral_add ((hG true true true).continuousOn_mul hl.continuousOn)
      ((hH true true true).continuousOn_mul hl.continuousOn),
    intervalIntegral.integral_add (hG false true true) (hH false true true)]
  ring

def capSeededExceptionalRemainder {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t c : ℝ) : ℝ :=
  capSeededKernelCombination t (fun a b d θ => capSeededExceptionalPattern s μ ξ A x ε t θ c a b d)

def capSeededSeparatedRemainder {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t c : ℝ) : ℝ :=
  capSeededKernelCombination t (fun a b d θ => capSeededSeparatedPattern s μ ξ A x ε t θ c a b d)

/-- The named source R4 has the exact separated/exceptional decomposition,
including the actual three scalar kernels and honest θ integrability. -/
theorem cap_seededFourthRemainder_exceptional_split
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) {c : ℝ} (hc : 0 < c)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0 < t+ε) :
    seededFourthRemainder s μ ξ C x ε t=
      capSeededSeparatedRemainder s μ ξ A x ε t c+capSeededExceptionalRemainder s μ ξ A x ε t c := by
  rw [cap_seededFourthRemainder_eq_patterns s μ ξ h A C hA hC x ht.1 ht.2 hpos]
  change capSeededKernelCombination t
      (fun a b d θ => capSeededFourthPattern s μ ξ A x ε t θ a b d)=
    capSeededKernelCombination t
      (fun a b d θ => capSeededSeparatedPattern s μ ξ A x ε t θ c a b d)+
    capSeededKernelCombination t
      (fun a b d θ => capSeededExceptionalPattern s μ ξ A x ε t θ c a b d)
  exact capSeededKernelCombination_add
    (fun a b d θ => capSeededFourthPattern s μ ξ A x ε t θ a b d)
    (fun a b d θ => capSeededSeparatedPattern s μ ξ A x ε t θ c a b d)
    (fun a b d θ => capSeededExceptionalPattern s μ ξ A x ε t θ c a b d)
    (fun a b d θ => cap_seeded_fourth_pattern_exceptional_split h A hA hunit s x hc ht hpos a b d)
    (fun a b d => capSeededSeparatedPattern_intervalIntegrable_theta h A hA hunit hr s hband x hc hε ht hpos a b d)
    (fun a b d => capSeededExceptionalPattern_intervalIntegrable_theta h A hA hunit s hband x c hε ht hpos a b d)


theorem capSeededKernelCombination_abs_le {t B : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hB : 0 ≤ B)
    (F : Bool → Bool → Bool → ℝ → ℝ)
    (hb : ∀ a b c θ, θ ∈ Set.Icc (0:ℝ) 1 → |F a b c θ| ≤ B) :
    |capSeededKernelCombination t F| ≤ 3*B := by
  have hIA : |∫ θ in (0:ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) θ*F false false false θ| ≤ B := by
    apply abs_unit_intervalIntegral_le_const
    intro θ hθ
    rw [abs_mul]
    exact (mul_le_mul (calibrated_fourth_kernel_abs_le_one ht hθ)
      (hb false false false θ hθ) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hIB : |∫ θ in (0:ℝ)..1, (1-θ)*F true true true θ| ≤ B := by
    apply abs_unit_intervalIntegral_le_const
    intro θ hθ
    rw [abs_mul]
    have hθ' : |1-θ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hθ.1,hθ.2]
    exact (mul_le_mul hθ' (hb true true true θ hθ) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hIC : |∫ θ in (0:ℝ)..1, F false true true θ| ≤ B :=
    abs_unit_intervalIntegral_le_const (fun θ hθ => hb false true true θ hθ)
  have hbc : |(1-t)/2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
  have hcc : |t*(1-t)/(3*(1+t))| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg ht.1 (by linarith [ht.2])) (by linarith [ht.1]))]
    apply (div_le_one (by linarith [ht.1] : 0 < 3*(1+t))).mpr
    nlinarith [sq_nonneg t]
  have htri (a b c : ℝ) : |a+b+c| ≤ |a|+|b|+|c| :=
    (abs_add (a+b) c).trans (add_le_add_right (abs_add a b) |c|)
  unfold capSeededKernelCombination
  calc
    _ ≤ |∫ θ in (0:ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) θ*F false false false θ|+
        |(1-t)/2| *|∫ θ in (0:ℝ)..1, (1-θ)*F true true true θ|+
        |t*(1-t)/(3*(1+t))| *|∫ θ in (0:ℝ)..1, F false true true θ| := by
      simpa only [abs_mul] using htri
        (∫ θ in (0:ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) θ*F false false false θ)
        ((1-t)/2*(∫ θ in (0:ℝ)..1, (1-θ)*F true true true θ))
        ((t*(1-t)/(3*(1+t)))*(∫ θ in (0:ℝ)..1, F false true true θ))
    _ ≤ B+1*B+1*B := add_le_add
      (add_le_add hIA (mul_le_mul hbc hIB (abs_nonneg _) zero_le_one))
      (mul_le_mul hcc hIC (abs_nonneg _) zero_le_one)
    _ = _ := by ring

/-- The actual exceptional part of the named R4 is uniformly controlled by
the original coordinate-pair budget, including every scalar copy kernel. -/
theorem cap_seeded_exceptional_remainder_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) (c : ℝ)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0 < t+ε) :
    |capSeededExceptionalRemainder s μ ξ A x ε t c| ≤
      (24*Real.sqrt 2*capSmallPairComplementaryConstant)*δ^2*
        exceptionalCorrelationBudget (A*A.transpose) c/s.bandwidth^2 := by
  let D := (8*Real.sqrt 2*capSmallPairComplementaryConstant)*δ^2*
    exceptionalCorrelationBudget (A*A.transpose) c/s.bandwidth^2
  have hD : 0 ≤ D := by
    dsimp [D,capSmallPairComplementaryConstant]
    exact div_nonneg (mul_nonneg (by positivity) (exceptionalCorrelationBudget_nonneg _ _)) (sq_nonneg _)
  have hb := capSeededKernelCombination_abs_le ht hD
    (fun a b d θ => capSeededExceptionalPattern s μ ξ A x ε t θ c a b d)
    (fun a b d θ hθ => cap_seeded_exceptional_pattern_bound h A hA hunit s hband x c hε ht hθ hpos a b d)
  exact hb.trans_eq (by dsimp [D]; ring)

end
end RectangleCLTArxivV1
