import RectangleCLTArxivV1.PolyhedralIntrinsicBounded
import RectangleCLTArxivV1.PolyhedralIntrinsicPolynomial
import RectangleCLTArxivV1.PolyhedralIntrinsicSubexponentialAllFaces

/-! Corollary 3 and Appendix D.2 of the frozen arXiv v1 source. All rates
use the actual projected Gaussian width, the number of retained positive
variance faces, and the exact substituted moment parameters. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
universe u

def PolyhedralBoundedIntrinsicBound (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p m n : ℕ) (ξ : Fin n → Ω → Vector p) (δ s₄ : ℝ),
    BoundedIndependentHypotheses μ ξ δ → RelativeFourthBudgets μ ξ s₄ →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose=covariance μ (sumVector ξ) →
  ∀ (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ), 1 ≤ J → PolyhedralNormalBound A ν J →
    let k := positivePolyhedralFaceCount A ν
    let gP := polyhedralIntrinsicWidth A ν
    (polyhedralDistance μ (sumVector ξ) A ν ≤ C*
      min 1 (intrinsicRelativeRate gP (J*δ) (J^2*s₄) (dimensionLog k))) ∧
    (polyhedralDistance μ (sumVector ξ) A ν ≤ C*
      min 1 ((J*δ)*gP*dimensionLog k*Real.sqrt (D_L (J*δ) (dimensionLog k))))

/-- The simpler bounded rate has no supplied relative-fourth premise. -/
def PolyhedralEnvelopeIntrinsicBound (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p m n : ℕ) (ξ : Fin n → Ω → Vector p) (δ : ℝ),
    BoundedIndependentHypotheses μ ξ δ →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose=covariance μ (sumVector ξ) →
  ∀ (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ), 1 ≤ J → PolyhedralNormalBound A ν J →
    polyhedralDistance μ (sumVector ξ) A ν ≤ C*
      min 1 ((J*δ)*polyhedralIntrinsicWidth A ν*dimensionLog (positivePolyhedralFaceCount A ν)*
        Real.sqrt (D_L (J*δ) (dimensionLog (positivePolyhedralFaceCount A ν))))

def PolyhedralOrliczIntrinsicBound (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p m n : ℕ), 1 ≤ n →
  ∀ (X : Fin n → Ω → Vector p) (K : ℝ), Psi1IndependentHypotheses μ X K →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose=covariance μ (normalizedObservationSum X) →
  ∀ (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ), 1 ≤ J → PolyhedralNormalBound A ν J →
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤ C*min 1
      (subexponentialWidthRate n (positivePolyhedralFaceCount A ν) (J*K)
        (polyhedralIntrinsicWidth A ν))

private theorem dimensionLog_nonneg_all (k : ℕ) : 0 ≤ dimensionLog k := by
  by_cases hk : k=0
  · simp [hk,dimensionLog]
  · exact zero_le_one.trans (log_exp_mul_nat_ge_one (by omega))

/-- Corollary 3 in the bounded and sub-exponential classes. The coefficient
is fixed before every probability model, dimension, face family and scale. -/
theorem corollary_3_bounded_orlicz_intrinsic :
    ∃ C : ℝ, 0 < C ∧ PolyhedralBoundedIntrinsicBound.{u} C ∧
      PolyhedralEnvelopeIntrinsicBound.{u} C ∧ PolyhedralOrliczIntrinsicBound.{u} C := by
  refine ⟨subexponentialWidthConstant,zero_lt_one.trans_le one_le_subexponentialWidthConstant,?_,?_,?_⟩
  · intro Ω mΩ μ hprob p m n ξ δ s₄ h hr A hA ν J hJ hν
    obtain ⟨hf,he,_⟩ := boundedPolyhedralCLT_all_faces_intrinsic μ ξ h hr A hA ν J hJ hν
    have hC : intrinsicUniversalConstant≤subexponentialWidthConstant := by
      have hi := intrinsicUniversalConstant_pos
      have hm : 1 ≤ max 1 (1/Real.sqrt (2/Real.pi)) := le_max_left _ _
      unfold subexponentialWidthConstant
      nlinarith
    have hg : 0 ≤ polyhedralIntrinsicWidth A ν := integral_nonneg (fun _ => norm_nonneg _)
    have hL := dimensionLog_nonneg_all (positivePolyhedralFaceCount A ν)
    have hδ : 0 ≤ J*δ := mul_nonneg (zero_le_one.trans hJ) h.delta_nonneg
    refine ⟨hf.trans (mul_le_mul_of_nonneg_right hC
      (le_min zero_le_one (intrinsicRelativeRate_nonneg hg hδ hL))),?_⟩
    exact he.trans (mul_le_mul_of_nonneg_right hC (le_min zero_le_one
      (mul_nonneg (mul_nonneg (mul_nonneg hδ hg) hL) (Real.sqrt_nonneg _))))
  · intro Ω mΩ μ hprob p m n ξ δ h A hA ν J hJ hν
    have he := boundedPolyhedralEnvelopeCLT_all_faces_intrinsic μ ξ h A hA ν J hJ hν
    have hC : intrinsicUniversalConstant≤subexponentialWidthConstant := by
      have hi := intrinsicUniversalConstant_pos
      have hm : 1 ≤ max 1 (1/Real.sqrt (2/Real.pi)) := le_max_left _ _
      unfold subexponentialWidthConstant
      nlinarith
    have hg : 0 ≤ polyhedralIntrinsicWidth A ν := integral_nonneg (fun _ => norm_nonneg _)
    have hL := dimensionLog_nonneg_all (positivePolyhedralFaceCount A ν)
    have hδ : 0 ≤ J*δ := mul_nonneg (zero_le_one.trans hJ) h.delta_nonneg
    exact he.trans (mul_le_mul_of_nonneg_right hC (le_min zero_le_one
      (mul_nonneg (mul_nonneg (mul_nonneg hδ hg) hL) (Real.sqrt_nonneg _))))
  · intro Ω mΩ μ hprob p m n hn X K h A hA ν J hJ hν
    exact orliczPolyhedralCLT_intrinsic_all_faces μ hn X K h A hA ν J hJ hν

/-- The complete polyhedral transfer: universal bounded/Orlicz constants
and q-dependent polynomial constants precede all models. The polynomial
branches retain the distinct exact substitutions `JB` and `J²B`. -/
theorem corollary_3_intrinsic :
    (∃ C : ℝ, 0 < C ∧ PolyhedralBoundedIntrinsicBound.{u} C ∧
      PolyhedralEnvelopeIntrinsicBound.{u} C ∧ PolyhedralOrliczIntrinsicBound.{u} C) ∧
    (∀ q : ℝ, 2 < q → ∃ C : ℝ, 0 < C ∧ PolyhedralAllFacesEnvelopeBound.{u} q C ∧
      PolyhedralAllFacesFourthBound.{u} q C ∧ PolyhedralAllFacesCombinedBound.{u} q C) :=
  ⟨corollary_3_bounded_orlicz_intrinsic,polynomialPolyhedralCLT_all_faces_intrinsic⟩

end
end RectangleCLTArxivV1
