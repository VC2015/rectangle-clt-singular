import RectangleCLTArxivV1.HFourthSeededModel
import RectangleCLTArxivV1.SupplementalISeededKernel

/-! Actual source R4 assembly through all three calibrated copy kernels.
The two missing geometric matrix estimates are kept in an explicit
structure; no target derivative or remainder estimate is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure HFourthSeededMatrixEstimates
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t c C Q : ℝ) : Prop where
  cubic : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
    symmetricNuclearNorm (hFourthCubicGaussianScore s (seededSplitGaussianScale ε t•A)
      (capRectangularFactorNormal A) (capSeededBaseValue A x ε t) γ ω)
        ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) ≤ C^(ℓ+2)*(s.bandwidth*Q)
  pair : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (2+ℓ) → Face p,
    if c ≤ 1-|faceDot (capRectangularFactorNormal A (γ 0)) (capRectangularFactorNormal A (γ 1))| then
      symmetricNuclearNorm (selectorGaussianScore s (seededSplitGaussianScale ε t•A)
        (capSeededBaseValue A x ε t) γ ω) else 0
          ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) ≤
    C^(ℓ+3)*(s.bandwidth^2*Q/(exceptionalCutoffDet c*seededSplitGaussianScale ε t))

/-- The actual named source remainder, including every scalar kernel,
follows from the explicit two matrix suppliers on its genuine half-base. -/
theorem hFourth_seeded_remainder_bound_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (F : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ))
    (hF : F*F.transpose=covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (x : Vector p) {c C Q ε t : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ j k : Fin p, j≠k → c ≤ 1-|covariance μ (sumVector ξ) j k|)
    (hC : 1 ≤ C) (hQ : 0 ≤ Q) (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0 < t+ε)
    (hband : restorationBandwidthConstant C*(4*δ) ≤ s.bandwidth)
    (hmatrix : HFourthSeededMatrixEstimates s μ ξ A x ε t c C Q) :
    |seededFourthRemainder s μ ξ F x ε t| ≤
      234*C^3*δ^2*Q/(exceptionalCutoffDet c*(seededSplitGaussianScale ε t)^3) := by
  have hδ := h.delta_nonneg
  have hd := (exceptionalCutoffDet_bounds hc hc1).1
  have hσ : 0 < seededSplitGaussianScale ε t := Real.sqrt_pos.mpr (half_pos hpos)
  let B := 78*C^3*δ^2*Q/(exceptionalCutoffDet c*(seededSplitGaussianScale ε t)^3)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hp (a b d : Bool) (θ : ℝ) (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
      |capSeededFourthPattern s μ ξ A x ε t θ a b d| ≤ B :=
    hFourth_seeded_pattern_bound_of_matrix_suppliers h A hA hunit s x hc hc1 hgap hC hQ
      ht hθ hpos hband a b d hmatrix.cubic hmatrix.pair
  have hk := capSeededKernelCombination_abs_le ht hB
    (fun a b d θ => capSeededFourthPattern s μ ξ A x ε t θ a b d) hp
  rw [cap_seededFourthRemainder_eq_patterns s μ ξ h A F hA hF x ht.1 ht.2 hpos]
  change |capSeededKernelCombination t (fun a b d θ => capSeededFourthPattern s μ ξ A x ε t θ a b d)| ≤ _
  exact hk.trans_eq (by dsimp only [B]; ring)

/-- The printed late-time denominator is obtained from the actual
half-Gaussian variance, after all copy kernels have been integrated. -/
theorem hFourth_seeded_remainder_late_bound_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (F : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ))
    (hF : F*F.transpose=covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (x : Vector p) {c C Q ε t : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ j k : Fin p, j≠k → c ≤ 1-|covariance μ (sumVector ξ) j k|)
    (hC : 1 ≤ C) (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0 < t+ε)
    (hband : restorationBandwidthConstant C*(4*δ) ≤ s.bandwidth)
    (hmatrix : HFourthSeededMatrixEstimates s μ ξ A x ε t c C Q) :
    |seededFourthRemainder s μ ξ F x ε t| ≤
      936*C^3*δ^2*Q/(exceptionalCutoffDet c*((t+ε)*Real.sqrt (t+ε))) := by
  have hb := hFourth_seeded_remainder_bound_of_matrix_suppliers h A F hA hF hunit s x hc hc1 hgap hC hQ ht hpos hband hmatrix
  have hr := cap_seededScale_cubic_rate hε ht.1 hpos
  have hd := (exceptionalCutoffDet_bounds hc hc1).1
  have hδ := h.delta_nonneg
  have hp : 0 ≤ 234*C^3*δ^2*Q/exceptionalCutoffDet c := by positivity
  calc
    _ ≤ 234*C^3*δ^2*Q/(exceptionalCutoffDet c*(seededSplitGaussianScale ε t)^3) := hb
    _ = (234*C^3*δ^2*Q/exceptionalCutoffDet c)*(1/(seededSplitGaussianScale ε t)^3) := by ring
    _ ≤ (234*C^3*δ^2*Q/exceptionalCutoffDet c)*(4/((t+ε)*Real.sqrt (t+ε))) :=
      mul_le_mul_of_nonneg_left hr hp
    _ = _ := by field_simp [hd.ne',hpos.ne',(Real.sqrt_pos.mpr hpos).ne']; ring

end
end RectangleCLTArxivV1
