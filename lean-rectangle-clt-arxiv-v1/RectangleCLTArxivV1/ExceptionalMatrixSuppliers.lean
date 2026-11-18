import RectangleCLTArxivV1.HFourthSeededRemainder
import RectangleCLTArxivV1.HFourthPairIndexTransport

/-! The remaining geometric suppliers for Corollary 5, on the genuine
half-Gaussian base: actual cubic and full angle-weighted pair nuclear
sums at every restoration length. No derivative or remainder is a field. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

structure ExceptionalSeededAngleMatrixEstimates
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (ε t C Q : ℝ) : Prop where
  cubic : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
    symmetricNuclearNorm (hFourthCubicGaussianScore s (seededSplitGaussianScale ε t•A)
      (capRectangularFactorNormal A) (capSeededBaseValue A x ε t) γ ω)
        ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) ≤ C^(ℓ+2)*(s.bandwidth*Q)
  pair : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+2) → Face p,
    correlationAngleWeight (faceDot (capRectangularFactorNormal A (γ 0))
      (capRectangularFactorNormal A (γ 1)))*
      symmetricNuclearNorm (selectorGaussianScore s (seededSplitGaussianScale ε t•A)
        (capSeededBaseValue A x ε t) γ ω)
          ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) ≤
    C^(ℓ+3)*(s.bandwidth^2*Q/seededSplitGaussianScale ε t)

/-- Full angle control restricts only the first pair. All appended tuple
labels and the actual smoother/base law are preserved. -/
theorem exceptional_seeded_matrix_estimates_of_angle
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) {ε t c C Q : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hc : 0<c) (hc1 : c≤1)
    (hmatrix : ExceptionalSeededAngleMatrixEstimates s μ ξ A x ε t C Q) :
    HFourthSeededMatrixEstimates s μ ξ A x ε t c C Q := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  refine ⟨hmatrix.cubic,?_⟩
  have hp := hFourth_pair_supplier_of_angle_weighted_front
    ((bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) s
    (seededSplitGaussianScale ε t•A) (capRectangularFactorNormal A)
    (capSeededBaseValue A x ε t) (capSeededBaseValue_measurable A x ε t) hc hc1 hmatrix.pair
  intro ℓ
  exact (hp ℓ).trans_eq (by ring)

/-- Normalization changes the physical smoother, while the H3 normal
remains the unit row of A. The supplier is independent of the cutoff. -/
def ExceptionalNormalizedMatrixEstimates
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (hp : 1≤p)
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (C κ t : ℝ) : Prop :=
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  let hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
  ExceptionalSeededAngleMatrixEstimates (seededRescaledSmoother s ε hε)
    μ ξ A 0 ε t C (κ*L*Real.sqrt L)

end
end RectangleCLTArxivV1
