import RectangleCLTArxivV1.SupplementalGSeededBase
import RectangleCLTArxivV1.SupplementalGSingleCopies
import RectangleCLTArxivV1.SupplementalGPairCopies

/-! The three actual calibrated retained-base/copy patterns. The same
constructors allow any old/fresh slot choices and the printed Taylor shifts. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def capSeededBaseValue {p r n : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (x : Vector p) (ε t : ℝ) (z : (Fin n → Vector p) × Vector r) : Vector p :=
  x+arraySum z.1+(seededSplitGaussianScale ε t • A).mulVec z.2

def capSeededCopyShift {Ω : Type*} {p r n : ℕ} (ξ : Fin n → Ω → Vector p)
    (fresh : Bool) (t θ : ℝ) (i : Fin n)
    (z : ((Fin n → Vector p) × Vector r) × (Ω × Ω)) : Vector p :=
  (θ*(1+t)) • capOriginalCopy ξ fresh i z.2-z.1.1 i

theorem capSeededBaseValue_measurable {p r n : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (x : Vector p) (ε t : ℝ) : Measurable (capSeededBaseValue (n := n) A x ε t) :=
  (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
    ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd)

theorem capSeededCopyShift_measurable
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ} (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (fresh : Bool) (t θ : ℝ) (i : Fin n) :
    Measurable (capSeededCopyShift (r := r) ξ fresh t θ i) :=
  (measurable_const.smul ((capOriginalCopy_measurable ξ hξ fresh i).comp measurable_snd)).sub
    ((measurable_pi_apply i).comp measurable_fst.fst)

theorem capSeededCopyShift_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (fresh : Bool)
    {t θ : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    ∀ᵐ z ∂((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)).prod (μ.prod μ),
      ‖capSeededCopyShift ξ fresh t θ i z‖ ≤ 4*δ := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  have hrow : ∀ᵐ z ∂((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)).prod (μ.prod μ),
      ‖z.1.1 i‖ ≤ 2*δ :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae ((h.thinned t ht.1 ht.2).bounded i))
  have hcopy : ∀ᵐ z ∂((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)).prod (μ.prod μ),
      ‖capOriginalCopy ξ fresh i z.2‖ ≤ δ :=
    Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_bounded h fresh i)
  filter_upwards [hrow,hcopy] with z hz hc
  have ha : 0 ≤ θ*(1+t) := mul_nonneg hθ.1 (by linarith [ht.1])
  have ha2 : θ*(1+t) ≤ 2 := by nlinarith [ht.1,ht.2,hθ.1,hθ.2]
  calc
    _ ≤ ‖(θ*(1+t)) • capOriginalCopy ξ fresh i z.2‖+‖z.1.1 i‖ := norm_sub_le _ _
    _ = (θ*(1+t))*‖capOriginalCopy ξ fresh i z.2‖+‖z.1.1 i‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
    _ ≤ 4*δ := by nlinarith [mul_le_mul ha2 hc (norm_nonneg _) (by norm_num : (0:ℝ)≤2)]

theorem cap_seededScale_square_rate {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    1/(seededSplitGaussianScale ε t)^2 = 2/(t+ε) := by
  rw [seededSplitGaussianScale_sq hε ht,one_div_div]

theorem cap_seededScale_cubic_rate {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hpos : 0 < t+ε) :
    1/(seededSplitGaussianScale ε t)^3 ≤ 4/((t+ε)*Real.sqrt (t+ε)) := by
  have hb : 0 < seededSplitGaussianScale ε t := Real.sqrt_pos.mpr (half_pos hpos)
  have ha : 0 < Real.sqrt (t+ε) := Real.sqrt_pos.mpr hpos
  have hb2 := seededSplitGaussianScale_sq hε ht
  have ha2 := Real.sq_sqrt hpos.le
  have hab : Real.sqrt (t+ε) ≤ 2*seededSplitGaussianScale ε t := by
    nlinarith [sq_nonneg (Real.sqrt (t+ε)-2*seededSplitGaussianScale ε t)]
  apply (div_le_div_iff₀ (pow_pos hb 3) (mul_pos hpos ha)).mpr
  simp only [one_mul]
  calc
    _ ≤ (t+ε)*(2*seededSplitGaussianScale ε t) := mul_le_mul_of_nonneg_left hab hpos.le
    _ = _ := by
      rw [show (seededSplitGaussianScale ε t)^3 = (seededSplitGaussianScale ε t)^2*seededSplitGaussianScale ε t by ring,hb2]
      ring

/-- Every actual one-face calibrated copy pattern has the required
linear-rank σ⁻³ estimate. The base and shift premises are all discharged. -/
theorem cap_seeded_single_pattern_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) (f : Face p)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    |-(1/(s.bandwidth*(seededSplitGaussianScale ε t)^3))*(∫ g, ∫ ω, ∑ i, ∫ z,
      ((normalDot f (capOriginalCopy ξ freshY i z)*normalDot f (capOriginalCopy ξ freshW i z))*
        capThirdHermiteScore (capRectangularFactorNormal A f) (capWhitenedCopy A ξ i z) g)*
        selectorTupleWeight s ![f] ((seededSplitGaussianScale ε t • A).mulVec g+
          capSeededBaseValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,z)) ∂μ.prod μ
          ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r) ∂standardGaussian r)| ≤
      (480*Real.exp (1/2)*Real.sqrt (Real.pi/capGaussianExponent)*δ^2*(r : ℝ))/(seededSplitGaussianScale ε t)^3 := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  have hdiag : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hcov := cap_seededSplit_mixed_covariance h A hA hdiag hε ht.1 ht.2 f f
  have hvar : (1/2:ℝ) ≤ capMixedCovariance (bernoulliArrayLaw μ ξ t)
      (fun i b => capSignedProjection f f (b i))
      (seededSplitGaussianScale ε t • capSignedFactor A f f) 0 0 := by
    rw [hcov]
    change (1/2 : ℝ) ≤ 1-t/2+ε/2
    linarith [ht.2]
  have hband' : 2*δ ≤ s.bandwidth := by nlinarith [h.delta_nonneg]
  apply cap_single_face_actual_copies (cap_seeded_projection_hypotheses h t ht.1 ht.2 f f)
    (seededSplitGaussianScale ε t • capSignedFactor A f f) hvar s hband' f
    (capSeededBaseValue A x ε t) (capSeededBaseValue_measurable A x ε t) (normalDot f x)
    (fun z => cap_signed_mixed_projection_zero (fun i (b : Fin n → Vector p) => b i)
      A (seededSplitGaussianScale ε t) f f x z)
    h A hA hunit hr freshY freshW (capSeededCopyShift ξ freshShift t θ)
    (capSeededCopyShift_measurable ξ h.measurable freshShift t θ)
    (mul_nonneg (by norm_num) h.delta_nonneg) (capSeededCopyShift_bounded h freshShift ht hθ)
    (cap_seeded_shift_ratio s hband) (seededSplitGaussianScale ε t)
    (Real.sqrt_pos.mpr (by simpa only [seededSplitGaussianScale] using half_pos hpos))

/-- Every actual nonparallel pair pattern has its large-angle estimate;
all projected-base, copy-moment, and shift requirements are proved. -/
theorem cap_seeded_pair_pattern_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) (f₁ f₂ : Face p)
    (hρ : (faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂))^2 < 1)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    |(1/(s.bandwidth^2*(seededSplitGaussianScale ε t)^2))*(∫ g, ∫ ω, ∑ i, ∫ z,
      (capRectangularPairCoefficient A f₁ f₂ (capOriginalCopy ξ freshY i z)
        (capOriginalCopy ξ freshW i z)*repeatedDirectionScore g (capWhitenedCopy A ξ i z))*
        selectorTupleWeight s ![f₁,f₂] ((seededSplitGaussianScale ε t • A).mulVec g+
          capSeededBaseValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,z)) ∂μ.prod μ
          ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r) ∂standardGaussian r)| ≤
      (9216*Real.exp 1*Real.pi^3*δ^2*(r : ℝ))/
        (Real.sqrt (1-(faceDot (capRectangularFactorNormal A f₁) (capRectangularFactorNormal A f₂))^2)*
          (seededSplitGaussianScale ε t)^2) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  have hdiag : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hcov := cap_seededSplit_mixed_covariance h A hA hdiag hε ht.1 ht.2 f₁ f₂
  have hvar : (1/2 : ℝ) ≤ 1-t/2+ε/2 := by linarith [ht.2]
  have hband' : 2*(2*δ) ≤ s.bandwidth := by nlinarith [h.delta_nonneg]
  apply cap_pair_face_actual_copies (cap_seeded_projection_hypotheses h t ht.1 ht.2 f₁ f₂)
    (seededSplitGaussianScale ε t • capSignedFactor A f₁ f₂) hvar hρ hcov s hband' f₁ f₂
    (capSeededBaseValue A x ε t) (capSeededBaseValue_measurable A x ε t)
    (normalDot f₁ x) (normalDot f₂ x)
    (fun z => cap_signed_mixed_projection_zero (fun i (b : Fin n → Vector p) => b i)
      A (seededSplitGaussianScale ε t) f₁ f₂ x z)
    (fun z => cap_signed_mixed_projection_one (fun i (b : Fin n → Vector p) => b i)
      A (seededSplitGaussianScale ε t) f₁ f₂ x z)
    h A hA rfl freshY freshW (capSeededCopyShift ξ freshShift t θ)
    (capSeededCopyShift_measurable ξ h.measurable freshShift t θ)
    (mul_nonneg (by norm_num) h.delta_nonneg) (capSeededCopyShift_bounded h freshShift ht hθ)
    (cap_seeded_shift_ratio s hband) (seededSplitGaussianScale ε t)
    (Real.sqrt_pos.mpr (by simpa only [seededSplitGaussianScale] using half_pos hpos))

end
end RectangleCLTArxivV1
