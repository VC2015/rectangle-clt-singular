import RectangleCLTArxivV1.ExceptionalFourthBound
import RectangleCLTArxivV1.HFourthSeededRemainder

/-! Actual bounded-array half-base and copies for the separated first-pair
cutoff. Conditional covariance and coefficient budgets are constructed from
the original array; no global coordinate correlation gap is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem exceptional_seeded_cutoff_product_bound_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (x : Vector p) {c C Q ε t θ : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hC : 1 ≤ C) (hQ : 0 ≤ Q)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hθ : θ ∈ Set.Icc (0:ℝ) 1) (hpos : 0 < t+ε)
    (hband : restorationBandwidthConstant C*(4*δ) ≤ s.bandwidth)
    (freshY freshW freshShift : Bool)
    (hcubic : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s (seededSplitGaussianScale ε t•A)
        (capRectangularFactorNormal A) (capSeededBaseValue A x ε t) γ ω)
          ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) ≤ C^(ℓ+2)*(s.bandwidth*Q))
    (hpair : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (2+ℓ) → Face p,
      if c ≤ 1-|faceDot (capRectangularFactorNormal A (γ 0)) (capRectangularFactorNormal A (γ 1))| then
        symmetricNuclearNorm (selectorGaussianScore s (seededSplitGaussianScale ε t•A)
          (capSeededBaseValue A x ε t) γ ω) else 0
            ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) ≤
      C^(ℓ+3)*(s.bandwidth^2*Q/(exceptionalCutoffDet c*seededSplitGaussianScale ε t))) :
    |exceptionalFourthCutoffExpectation s
      (((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)).prod (μ.prod μ)) A
      (fun z => capSeededBaseValue A x ε t z.1) (fun i z => capWhitenedCopy A ξ i z.2)
      (fun i z => capOriginalCopy ξ freshY i z.2) (fun i z => capOriginalCopy ξ freshW i z.2)
      (capSeededCopyShift ξ freshShift t θ) (seededSplitGaussianScale ε t)
      (fun f g => c ≤ 1-|faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)|)| ≤
      78*C^3*δ^2*Q/(exceptionalCutoffDet c*(seededSplitGaussianScale ε t)^3) := by
  classical
  have hδ := h.delta_nonneg
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  let B := (Fin n → Vector p) × Vector r
  let ρ := (bernoulliArrayLaw μ ξ t).prod (standardGaussian r)
  let V := fun z : B × (Ω × Ω) => capSeededBaseValue A x ε t z.1
  let Z := fun i (z : B × (Ω × Ω)) => capWhitenedCopy A ξ i z.2
  let Y := fun i (z : B × (Ω × Ω)) => capOriginalCopy ξ freshY i z.2
  let W := fun i (z : B × (Ω × Ω)) => capOriginalCopy ξ freshW i z.2
  let P := fun f g => c ≤ 1-|faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)|
  have hd : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hV : @Measurable (B × (Ω × Ω)) (Vector p) originalSigma inferInstance V :=
    (capSeededBaseValue_measurable A x ε t).comp (comap_measurable Prod.fst)
  have hZm (i : Fin n) : Measurable (Z i) := (capWhitenedCopy_measurable h A i).comp measurable_snd
  have hZ (i : Fin n) (j k : Fin r) : Integrable (fun z => Z i z j*Z i z k) (ρ.prod (μ.prod μ)) :=
    seededCopyWhitened_integrable_coordinate_pair ρ μ ξ h A i j k
  have hYm (i : Fin n) : Measurable (Y i) := (capOriginalCopy_measurable ξ h.measurable freshY i).comp measurable_snd
  have hWm (i : Fin n) : Measurable (W i) := (capOriginalCopy_measurable ξ h.measurable freshW i).comp measurable_snd
  have hYb (i : Fin n) : ∀ᵐ z ∂ρ.prod (μ.prod μ), ‖Y i z‖ ≤ δ :=
    Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_bounded h freshY i)
  have hWb (i : Fin n) : ∀ᵐ z ∂ρ.prod (μ.prod μ), ‖W i z‖ ≤ δ :=
    Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_bounded h freshW i)
  have hcov : ∀ᵐ z ∂ρ.prod (μ.prod μ), ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma Z (fun _ _ => 1) z) u ≤ vectorNormSq u :=
    seeded_copy_conditional_covariance_budget ρ μ ξ h A hA
  have hcub (ℓ : ℕ) : (∫ z : B × (Ω × Ω), ∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s (seededSplitGaussianScale ε t•A)
        (capRectangularFactorNormal A) V γ z) ∂ρ.prod (μ.prod μ)) ≤ C^(ℓ+2)*(s.bandwidth*Q) := by
    change (∫ z : B × (Ω × Ω), (∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s (seededSplitGaussianScale ε t•A)
        (capRectangularFactorNormal A) (capSeededBaseValue A x ε t) γ z.1)) ∂ρ.prod (μ.prod μ)) ≤ _
    have he := integral_fun_fst (μ := ρ) (ν := μ.prod μ) (fun ω : B =>
      ∑ γ : Fin (ℓ+1) → Face p,
        symmetricNuclearNorm (hFourthCubicGaussianScore s (seededSplitGaussianScale ε t•A)
          (capRectangularFactorNormal A) (capSeededBaseValue A x ε t) γ ω))
    simp only [measureReal_univ_eq_one,one_smul] at he
    exact he.trans_le (hcubic ℓ)
  have hpa (ℓ : ℕ) : (∫ z : B × (Ω × Ω), ∑ γ : Fin (2+ℓ) → Face p,
      if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s (seededSplitGaussianScale ε t•A) V γ z) else 0
        ∂ρ.prod (μ.prod μ)) ≤ C^(ℓ+3)*(s.bandwidth^2*Q/(exceptionalCutoffDet c*seededSplitGaussianScale ε t)) := by
    change (∫ z : B × (Ω × Ω), (∑ γ : Fin (2+ℓ) → Face p,
      if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s (seededSplitGaussianScale ε t•A)
        (capSeededBaseValue A x ε t) γ z.1) else 0) ∂ρ.prod (μ.prod μ)) ≤ _
    have he := integral_fun_fst (μ := ρ) (ν := μ.prod μ) (fun ω : B =>
      ∑ γ : Fin (2+ℓ) → Face p,
        if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s (seededSplitGaussianScale ε t•A)
          (capSeededBaseValue A x ε t) γ ω) else 0)
    simp only [measureReal_univ_eq_one,one_smul] at he
    exact he.trans_le (hpair ℓ)
  have hh := exceptionalFourth_cutoff_expectation_bound_of_matrix_suppliers s (ρ.prod (μ.prod μ)) originalSigma originalSigma_le
    A hd V hV Z hZm hZ Y W (capSeededCopyShift ξ freshShift t θ) hYm hWm
    (capSeededCopyShift_measurable ξ h.measurable freshShift t θ) P h.delta_nonneg
    (Real.sqrt_pos.mpr (half_pos hpos)) (by positivity : 0 ≤ 4*δ) hYb hWb
    (capSeededCopyShift_bounded h freshShift ht hθ) hcov hC hQ
    (exceptionalCutoffDet_bounds hc hc1).1 (exceptionalCutoffDet_bounds hc hc1).2.2 hband hcub hpa
  exact hh


end
end RectangleCLTArxivV1
