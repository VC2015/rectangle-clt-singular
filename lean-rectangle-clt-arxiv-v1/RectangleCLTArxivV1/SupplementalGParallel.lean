import RectangleCLTArxivV1.SupplementalGSeededContributions

/-! Parallel and omitted faces contribute zero to the actual seeded terms. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_vectorNormSq_eq_zero {r : ℕ} {z : Vector r} (hz : vectorNormSq z = 0) : z = 0 := by
  funext j
  have hj : z j^2 ≤ ∑ k, z k^2 := Finset.single_le_sum (fun k _ => sq_nonneg (z k)) (Finset.mem_univ j)
  change (∑ k, z k^2)=0 at hz
  rw [hz] at hj
  exact sq_eq_zero_iff.mp (le_antisymm hj (sq_nonneg _))

theorem capPairCoefficient_parallel_zero {r : ℕ} (u v z w : Vector r)
    (hu : vectorNormSq u = 1) (hv : vectorNormSq v = 1) (hρ : |dotProduct u v| = 1) :
    capPairCoefficient u v z w = 0 := by
  have huu : dotProduct u u=1 := by simpa only [vectorNormSq_eq_dot_self] using hu
  have hvv : dotProduct v v=1 := by simpa only [vectorNormSq_eq_dot_self] using hv
  by_cases hp : 0 ≤ dotProduct u v
  · have hdot : dotProduct u v=1 := by simpa only [abs_of_nonneg hp] using hρ
    have hz : vectorNormSq (u-v)=0 := by
      rw [vectorNormSq_eq_dot_self,← one_smul ℝ v,dot_self_sub_smul,huu,hvv,hdot]
      norm_num
    have he : u=v := sub_eq_zero.mp (cap_vectorNormSq_eq_zero hz)
    rw [← he]
    exact capPairCoefficient_equal u z w hu
  · have hn : dotProduct u v ≤ 0 := le_of_lt (lt_of_not_ge hp)
    have hdot : dotProduct u v = -1 := by rw [abs_of_nonpos hn] at hρ; linarith
    have hz : vectorNormSq (u-(-1:ℝ) • v)=0 := by
      rw [vectorNormSq_eq_dot_self,dot_self_sub_smul,huu,hvv,hdot]
      norm_num
    have he := sub_eq_zero.mp (cap_vectorNormSq_eq_zero hz)
    have he' : v = -u := by rw [he]; simp
    rw [he']
    exact capPairCoefficient_opposite u z w hu

theorem cap_seeded_pair_parallel_zero
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (x : Vector p) (ε t θ : ℝ) (f g : Face p)
    (hρ : |faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)|=1)
    (freshY freshW freshShift : Bool) :
    capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift = 0 := by
  have hd : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hu := capRectangularFactorNormal_unit A hd f
  have hv := capRectangularFactorNormal_unit A hd g
  have hc (i : Fin n) : ∀ᵐ z ∂μ.prod μ,
      capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i z) (capOriginalCopy ξ freshW i z)=0 := by
    filter_upwards [capOriginalCopy_pair_eq_factor_ae h A hA freshY freshW f g i] with z hz
    rw [hz]
    exact capPairCoefficient_parallel_zero _ _ _ _ hu hv hρ
  unfold capSeededPairContribution
  have hi (z : Vector r) (ω : (Fin n → Vector p) × Vector r) :
      (∑ i, ∫ a, (capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i a)
        (capOriginalCopy ξ freshW i a)*repeatedDirectionScore z (capWhitenedCopy A ξ i a))*
        selectorTupleWeight s ![f,g] ((seededSplitGaussianScale ε t • A).mulVec z+
          capSeededBaseValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,a)) ∂μ.prod μ)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply integral_eq_zero_of_ae
    filter_upwards [hc i] with a ha
    simp only [ha,zero_mul,Pi.zero_apply]
  simp_rw [hi]
  simp

theorem cap_selector_single_inactive {p : ℕ} (s : FaceSmoother p) (f : Face p)
    (hf : f ∉ s.faces) (x : Vector p) : selectorTupleWeight s ![f] x=0 := by
  simp [selectorTupleWeight,FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hf]

theorem cap_selector_pair_inactive {p : ℕ} (s : FaceSmoother p) (f g : Face p)
    (hfg : f ∉ s.faces ∨ g ∉ s.faces) (x : Vector p) : selectorTupleWeight s ![f,g] x=0 := by
  rcases hfg with hf | hg
  · simp [selectorTupleWeight,FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hf]
  · simp [selectorTupleWeight,FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hg]

theorem cap_seeded_single_inactive
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t θ : ℝ) (f : Face p)
    (hf : f ∉ s.faces) (freshY freshW freshShift : Bool) :
    capSeededSingleContribution s μ ξ A x ε t θ f freshY freshW freshShift=0 := by
  unfold capSeededSingleContribution
  simp_rw [cap_selector_single_inactive s f hf]
  simp

theorem cap_seeded_pair_inactive
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t θ : ℝ) (f g : Face p)
    (hfg : f ∉ s.faces ∨ g ∉ s.faces) (freshY freshW freshShift : Bool) :
    capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift=0 := by
  unfold capSeededPairContribution
  simp_rw [cap_selector_pair_inactive s f g hfg]
  simp

end
end RectangleCLTArxivV1
