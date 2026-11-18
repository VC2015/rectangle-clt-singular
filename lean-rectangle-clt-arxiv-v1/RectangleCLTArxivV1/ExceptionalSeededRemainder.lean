import RectangleCLTArxivV1.ExceptionalSeededModel
import RectangleCLTArxivV1.ExceptionalSeededTensor
import RectangleCLTArxivV1.ExceptionalMatrixSuppliers

/-! The actual separated and exceptional source remainders, through all
three calibrated copy kernels. No global correlation-gap hypothesis is
used; perfectly parallel pairs vanish in the proved exact source split. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem exceptional_seeded_separated_pattern_bound_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (x : Vector p) {c C Q ε t θ : ℝ}
    (hc : 0<c) (hc1 : c≤1) (hC : 1≤C) (hQ : 0≤Q)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hθ : θ ∈ Set.Icc (0:ℝ) 1) (hpos : 0<t+ε)
    (hband : restorationBandwidthConstant C*(4*δ)≤s.bandwidth)
    (freshY freshW freshShift : Bool)
    (hmatrix : HFourthSeededMatrixEstimates s μ ξ A x ε t c C Q) :
    |capSeededSeparatedPattern s μ ξ A x ε t θ c freshY freshW freshShift|≤
      78*C^3*δ^2*Q/(exceptionalCutoffDet c*(seededSplitGaussianScale ε t)^3) := by
  rw [exceptional_seeded_separated_eq_cutoff_product h A hA hunit s x ε t θ c ht freshY freshW freshShift]
  exact exceptional_seeded_cutoff_product_bound_of_matrix_suppliers h A hA hunit s x hc hc1 hC hQ
    ht hθ hpos hband freshY freshW freshShift hmatrix.cubic hmatrix.pair

theorem exceptional_seeded_separated_remainder_bound_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (x : Vector p) {c C Q ε t : ℝ}
    (hc : 0<c) (hc1 : c≤1) (hC : 1≤C) (hQ : 0≤Q)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0<t+ε)
    (hband : restorationBandwidthConstant C*(4*δ)≤s.bandwidth)
    (hmatrix : HFourthSeededMatrixEstimates s μ ξ A x ε t c C Q) :
    |capSeededSeparatedRemainder s μ ξ A x ε t c|≤
      234*C^3*δ^2*Q/(exceptionalCutoffDet c*(seededSplitGaussianScale ε t)^3) := by
  have hδ := h.delta_nonneg
  have hd := (exceptionalCutoffDet_bounds hc hc1).1
  have hσ : 0<seededSplitGaussianScale ε t := Real.sqrt_pos.mpr (half_pos hpos)
  let B := 78*C^3*δ^2*Q/(exceptionalCutoffDet c*(seededSplitGaussianScale ε t)^3)
  have hB : 0≤B := by dsimp only [B]; positivity
  have hp (a b d : Bool) (θ : ℝ) (hθ : θ ∈ Set.Icc (0:ℝ) 1) :
      |capSeededSeparatedPattern s μ ξ A x ε t θ c a b d|≤B :=
    exceptional_seeded_separated_pattern_bound_of_matrix_suppliers h A hA hunit s x hc hc1 hC hQ
      ht hθ hpos hband a b d hmatrix
  exact (capSeededKernelCombination_abs_le ht hB
    (fun a b d θ => capSeededSeparatedPattern s μ ξ A x ε t θ c a b d) hp).trans_eq (by dsimp [B]; ring)

theorem exceptional_seeded_separated_remainder_late_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (s : FaceSmoother p) (x : Vector p) {c C Q ε t : ℝ}
    (hc : 0<c) (hc1 : c≤1) (hC : 1≤C) (hQ : 0≤Q) (hε : 0≤ε)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0<t+ε)
    (hband : restorationBandwidthConstant C*(4*δ)≤s.bandwidth)
    (hmatrix : HFourthSeededMatrixEstimates s μ ξ A x ε t c C Q) :
    |capSeededSeparatedRemainder s μ ξ A x ε t c|≤
      936*C^3*δ^2*Q/(exceptionalCutoffDet c*((t+ε)*Real.sqrt (t+ε))) := by
  have hb := exceptional_seeded_separated_remainder_bound_of_matrix_suppliers h A hA hunit s x hc hc1
    hC hQ ht hpos hband hmatrix
  have hr := cap_seededScale_cubic_rate hε ht.1 hpos
  have hd := (exceptionalCutoffDet_bounds hc hc1).1
  have hδ := h.delta_nonneg
  have hp : 0≤234*C^3*δ^2*Q/exceptionalCutoffDet c := by positivity
  calc
    _≤234*C^3*δ^2*Q/(exceptionalCutoffDet c*(seededSplitGaussianScale ε t)^3) := hb
    _=(234*C^3*δ^2*Q/exceptionalCutoffDet c)*(1/(seededSplitGaussianScale ε t)^3) := by ring
    _≤(234*C^3*δ^2*Q/exceptionalCutoffDet c)*(4/((t+ε)*Real.sqrt (t+ε))) :=
      mul_le_mul_of_nonneg_left hr hp
    _=_ := by field_simp [hd.ne',hpos.ne',(Real.sqrt_pos.mpr hpos).ne']; ring

/-- All geometric suppliers have been consumed except the two actual
matrix sums. The exceptional term is the proved original coordinate
budget, with no inverse correlation gap and no time singularity. -/
theorem exceptional_seeded_remainder_late_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (F : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ))
    (hF : F*F.transpose=covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1) (hr : 1≤r)
    (s : FaceSmoother p) (x : Vector p) {c C Q ε t : ℝ}
    (hc : 0<c) (hc1 : c≤1) (hC : 1≤C) (hQ : 0≤Q) (hε : 0≤ε)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0<t+ε)
    (hband : restorationBandwidthConstant C*(4*δ)≤s.bandwidth)
    (hsmallband : 16*δ≤s.bandwidth)
    (hmatrix : HFourthSeededMatrixEstimates s μ ξ A x ε t c C Q) :
    |seededFourthRemainder s μ ξ F x ε t|≤
      936*C^3*δ^2*Q/(exceptionalCutoffDet c*((t+ε)*Real.sqrt (t+ε)))+
      (24*Real.sqrt 2*capSmallPairComplementaryConstant)*δ^2*
        exceptionalCorrelationBudget (A*A.transpose) c/s.bandwidth^2 := by
  rw [cap_seededFourthRemainder_exceptional_split h A F hA hF hunit hr s hsmallband x hc hε ht hpos]
  exact (abs_add _ _).trans (add_le_add
    (exceptional_seeded_separated_remainder_late_of_matrix_suppliers h A hA hunit s x hc hc1 hC hQ
      hε ht hpos hband hmatrix)
    (cap_seeded_exceptional_remainder_bound h A hA hunit s hsmallband x c hε ht hpos))

end
end RectangleCLTArxivV1
