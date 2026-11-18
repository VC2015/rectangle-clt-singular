import RectangleCLTArxivV1.SupplementalIBudget
import RectangleCLTArxivV1.SupplementalGComplementary

/-! The actual exceptional seeded contribution, before time integration.
No two-face concentration or remainder estimate is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cap_seeded_pair_contribution_sine_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) (f g : Face p)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    |capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift| ≤
      capSmallPairComplementaryConstant*δ^2*
        Real.sqrt (1-(faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g))^2)/s.bandwidth^2 := by
  let ρ := faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)
  have hdiag : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hu := capRectangularFactorNormal_unit A hdiag f
  have hv := capRectangularFactorNormal_unit A hdiag g
  by_cases hρ : ρ^2 < 1
  · have hfg : f ≠ g := by
      intro he
      subst g
      have hself : faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A f)=1 := by
        simpa only [faceDot,vectorNormSq,pow_two] using hu
      change (faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A f))^2 < 1 at hρ
      rw [hself] at hρ
      norm_num at hρ
    rw [cap_seeded_pair_contribution_eq_second h A hA hunit s x f g hfg hε ht hpos freshY freshW freshShift]
    exact cap_seeded_small_angle_pattern_bound h A hA hunit s hband x f g hρ hε ht hθ freshY freshW freshShift
  · have hρle : |ρ| ≤ 1 := abs_dotProduct_unit_le_one _ _ hu hv
    have hparallel : |ρ|=1 := by nlinarith [sq_abs ρ,abs_nonneg ρ]
    rw [cap_seeded_pair_parallel_zero h A hA hunit s x ε t θ f g hparallel freshY freshW freshShift,abs_zero]
    dsimp only [capSmallPairComplementaryConstant]
    positivity

def capSeededExceptionalPattern {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t θ c : ℝ)
    (freshY freshW freshShift : Bool) : ℝ :=
  ∑ f : Face p, ∑ g : Face p,
    if 0 < correlationGap (A*A.transpose) f.1 g.1 ∧ correlationGap (A*A.transpose) f.1 g.1 < c then
      capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift else 0

theorem cap_seeded_exceptional_pattern_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) (c : ℝ)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    |capSeededExceptionalPattern s μ ξ A x ε t θ c freshY freshW freshShift| ≤
      (8*Real.sqrt 2*capSmallPairComplementaryConstant)*δ^2*
        exceptionalCorrelationBudget (A*A.transpose) c/s.bandwidth^2 := by
  classical
  let P := capSmallPairComplementaryConstant*δ^2/s.bandwidth^2
  have hP : 0 ≤ P := by dsimp [P,capSmallPairComplementaryConstant]; positivity
  have hb (f g : Face p) :
      |if 0 < correlationGap (A*A.transpose) f.1 g.1 ∧ correlationGap (A*A.transpose) f.1 g.1 < c then
        capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift else 0| ≤
      P*exceptionalFaceSine (capRectangularFactorNormal A) c f g := by
    have he := cap_signed_correlation_abs A f g
    unfold exceptionalFaceSine correlationGap
    rw [he]
    split_ifs with hg
    · have hs := cap_seeded_pair_contribution_sine_bound h A hA hunit s hband x f g hε ht hθ hpos freshY freshW freshShift
      dsimp only [P]
      exact hs.trans_eq (by ring)
    · simp
  have hdiag : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  calc
    _ ≤ ∑ f : Face p, ∑ g : Face p,
        |if 0 < correlationGap (A*A.transpose) f.1 g.1 ∧ correlationGap (A*A.transpose) f.1 g.1 < c then
          capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift else 0| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro f _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f : Face p, ∑ g : Face p,
        P*exceptionalFaceSine (capRectangularFactorNormal A) c f g :=
      Finset.sum_le_sum (fun f _ => Finset.sum_le_sum (fun g _ => hb f g))
    _ = P*(∑ f : Face p, ∑ g : Face p,
        exceptionalFaceSine (capRectangularFactorNormal A) c f g) := by simp_rw [Finset.mul_sum]
    _ ≤ P*(8*Real.sqrt 2*exceptionalCorrelationBudget (A*A.transpose) c) :=
      mul_le_mul_of_nonneg_left (exceptional_signed_face_sine_sum_le_budget A hdiag c) hP
    _ = _ := by dsimp only [P]; ring


def capSeededSeparatedPattern {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t θ c : ℝ)
    (freshY freshW freshShift : Bool) : ℝ :=
  (∑ f, capSeededSingleContribution s μ ξ A x ε t θ f freshY freshW freshShift)+
  ∑ f : Face p, ∑ g : Face p,
    if c ≤ correlationGap (A*A.transpose) f.1 g.1 then
      capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift else 0

/-- Exact actual seeded split. Parallel pairs vanish rather than entering
an inverse-gap estimate; all single faces remain in the separated part. -/
theorem cap_seeded_fourth_pattern_exceptional_split
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (x : Vector p) {c : ℝ} (hc : 0 < c)
    {ε t θ : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hpos : 0 < t+ε)
    (freshY freshW freshShift : Bool) :
    capSeededFourthPattern s μ ξ A x ε t θ freshY freshW freshShift =
      capSeededSeparatedPattern s μ ξ A x ε t θ c freshY freshW freshShift+
      capSeededExceptionalPattern s μ ξ A x ε t θ c freshY freshW freshShift := by
  classical
  let P := fun f g => capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift
  let η := fun f g : Face p => correlationGap (A*A.transpose) f.1 g.1
  have hdiag : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hp (f g : Face p) : P f g = (if c ≤ η f g then P f g else 0)+
      (if 0 < η f g ∧ η f g < c then P f g else 0) := by
    have hρle := abs_dotProduct_unit_le_one _ _
      (capRectangularFactorNormal_unit A hdiag f) (capRectangularFactorNormal_unit A hdiag g)
    change |faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)| ≤ 1 at hρle
    rw [cap_signed_correlation_abs] at hρle
    have hη : 0 ≤ η f g := by dsimp [η,correlationGap]; linarith
    by_cases hsep : c ≤ η f g
    · rw [if_pos hsep,if_neg (by intro hg; linarith [hg.2])]
      ring
    · rw [if_neg hsep]
      by_cases hηp : 0 < η f g
      · rw [if_pos ⟨hηp,lt_of_not_ge hsep⟩]
        ring
      · have hzero : η f g=0 := by linarith
        have hparallel : |faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)|=1 := by
          rw [cap_signed_correlation_abs]
          dsimp [η,correlationGap] at hzero
          linarith
        have hz : P f g=0 := cap_seeded_pair_parallel_zero h A hA hunit s x ε t θ f g hparallel freshY freshW freshShift
        rw [if_neg (by simp [hzero]),hz]
        ring
  have hs : (∑ f, ∑ g, P f g) = (∑ f, ∑ g, if c ≤ η f g then P f g else 0)+
      (∑ f, ∑ g, if 0 < η f g ∧ η f g < c then P f g else 0) := by
    calc
      _ = ∑ f, ∑ g, ((if c ≤ η f g then P f g else 0)+
          (if 0 < η f g ∧ η f g < c then P f g else 0)) := by
        apply Finset.sum_congr rfl
        intro f _
        exact Finset.sum_congr rfl (fun g _ => hp f g)
      _ = _ := by simp only [Finset.sum_add_distrib]
  rw [cap_seeded_fourth_pattern_decomposition h A hA hunit s x ht hpos freshY freshW freshShift]
  unfold capSeededSeparatedPattern capSeededExceptionalPattern
  change _+(∑ f, ∑ g, P f g)=(_+_)+_
  rw [hs]
  ring

end
end RectangleCLTArxivV1
