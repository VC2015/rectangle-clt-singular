import RectangleCLTArxivV1.SupplementalHFamilyKernelBounds
import RectangleCLTArxivV1.SupplementalHProjectionMoments
import RectangleCLTArxivV1.SupplementalHWeightedReference
import RectangleCLTArxivV1.SupplementalHQuantitativeEntropy

/-! Actual finite-family mass, projected-moment, and reference budgets
for every tuple length, with the base average included. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def supplementalHCubicTupleMoment {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (U : Face p → Vector r) (q : ℕ) (α : Fin (K+1) → Face p) (ω : Ω) : ℝ :=
  ∫ g, (supplementalHPositiveDirection (U (α 0)) g*|faceDot (U (α 0)) g|^q)*
    selectorWeight s α (V ω+M.mulVec g) ∂standardGaussian r

def supplementalHCubicReferenceMass {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (U : Face p → Vector r) (α : Fin (K+1) → Face p) (ω : Ω) : ℝ :=
  ∫ g, supplementalHPositiveDirection (U (α 0)) g*
    oneFaceReference s (α 0) (V ω+M.mulVec g) ∂standardGaussian r

/-- For q=0 this is the actual signed-half mass; q=2 is its projected
second moment. The common projection maximum costs one or three powers
of sqrt L, independently of the number of appended selector factors. -/
theorem intrinsicRectangleConcentration_cubicTupleMoment
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (U : Face p → Vector r) (hU : ∀ f, vectorNormSq (U f)=1) (q : ℕ) :
    (∀ α : Fin (K+1) → Face p,
      Measurable (supplementalHCubicTupleMoment s M V U q α) ∧
      Integrable (supplementalHCubicTupleMoment s M V U q α) μ) ∧
    (∫ ω, ∑ α : Fin (K+1) → Face p, supplementalHCubicTupleMoment s M V U q α ω ∂μ) ≤
      (4*C₀*s.bandwidth*κ)*((Real.sqrt (dimensionLog p))^(q+1)*
        Real.exp (8+((q+2:ℝ))^2/2)) := by
  let B := fun g : Vector r => (supplementalHProjectionRadius U g)^(q+1)
  let c := fun (α : Fin (K+1) → Face p) (g : Vector r) =>
    supplementalHPositiveDirection (U (α 0)) g*|faceDot (U (α 0)) g|^q
  have hcm (α) : Measurable (c α) := by unfold c supplementalHPositiveDirection faceDot; fun_prop
  have hc0 (α) (g) : 0 ≤ c α g := by
    exact mul_nonneg (supplementalHPositiveDirection_nonneg _ _) (pow_nonneg (abs_nonneg _) _)
  have hdom (α) (g : Vector r) : c α g ≤ B g := by
    have ha := abs_faceDot_le_supplementalHProjectionRadius U (α 0) g
    have hpos : supplementalHPositiveDirection (U (α 0)) g ≤ supplementalHProjectionRadius U g :=
      (max_le (le_abs_self _) (abs_nonneg _)).trans ha
    have hp := mul_le_mul hpos (pow_le_pow_left₀ (abs_nonneg _) ha q)
      (pow_nonneg (abs_nonneg _) q) (zero_le_one.trans (supplementalHProjectionRadius_ge_one U g))
    simpa only [c,B,pow_succ,mul_comm] using hp
  have hB := supplementalHProjectionRadius_moment_le hp U hU (q+1)
  have hbound := intrinsicRectangleConcentration_selectorFamilyKernel μ V hV s M hC₀ hκ hδh hc
    c hcm hc0 B ((measurable_supplementalHProjectionRadius U).pow_const (q+1))
    (fun g => pow_nonneg (zero_le_one.trans (supplementalHProjectionRadius_ge_one U g)) _) hB.1 hdom
  refine ⟨hbound.1,?_⟩
  have hB' : (∫ g, B g ∂standardGaussian r) ≤
      (Real.sqrt (dimensionLog p))^(q+1)*Real.exp (8+((q+2:ℝ))^2/2) := by
    simpa only [B,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hB.2
  exact hbound.2.trans (mul_le_mul_of_nonneg_left hB'
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀) s.bandwidth_pos.le) hκ))

/-- The reference is the actual one-face kernel, with an unbounded
positive Gaussian coordinate. Its outer integrability is proved. -/
theorem supplementalHCubicReferenceMass_properties
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ)
    (U : Face p → Vector r) (α : Fin (K+1) → Face p) :
    Measurable (supplementalHCubicReferenceMass s M V U α) ∧
      Integrable (supplementalHCubicReferenceMass s M V U α) μ := by
  let B := supplementalHPositiveDirection (U (α 0))
  let W := fun z : Ω × Vector r => B z.2*oneFaceReference s (α 0) (V z.1+M.mulVec z.2)
  have hBm : Measurable B := by unfold B supplementalHPositiveDirection faceDot; fun_prop
  have hM : Measurable (fun g : Vector r => M.mulVec g) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hm : Measurable (oneFaceReference s (α 0)) := by
    unfold oneFaceReference FaceSmoother.faceScore FaceSmoother.normalDot
    cases hf : (α 0).2 <;> simp [hf] <;> fun_prop
  have hWm : Measurable W := (hBm.comp measurable_snd).mul
    (hm.comp ((hV.comp measurable_fst).add (hM.comp measurable_snd)))
  have hprop := supplementalH_dominated_kernel_mass_properties μ (standardGaussian r) W hWm
    (fun z => mul_nonneg (supplementalHPositiveDirection_nonneg _ _) (oneFaceReference_bounds s (α 0) _).1)
    B hBm (supplementalH_integrable_positiveDirection _) (fun z =>
      mul_le_of_le_one_right (supplementalHPositiveDirection_nonneg _ _) (oneFaceReference_bounds s (α 0) _).2)
  exact ⟨hprop.1,hprop.2.1⟩

/-- Counting all original tuples is needed only for the reference
mass. The actual mass was bounded after summing selector factors. -/
theorem intrinsicRectangleConcentration_cubicReferenceFamily
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (U : Face p → Vector r) (hU : ∀ f, vectorNormSq (U f)=1) :
    (∫ ω, ∑ α : Fin (K+1) → Face p, supplementalHCubicReferenceMass s M V U α ω ∂μ) ≤
      (4*C₀*s.bandwidth*κ)*(Fintype.card (Face p):ℝ)^(K+1) := by
  classical
  rw [integral_finset_sum _ (fun α _ => (supplementalHCubicReferenceMass_properties μ V hV s M U α).2)]
  calc
    _ ≤ ∑ _α : Fin (K+1) → Face p, 4*C₀*s.bandwidth*κ := by
      apply Finset.sum_le_sum
      intro α _
      exact intrinsicRectangleConcentration_positiveOneFaceMass μ V hV s M hC₀ hκ hδh hc
        (U (α 0)) (hU (α 0)) (α 0)
    _ = _ := by simp [Fintype.card_fun,mul_comm]

end
end RectangleCLTArxivV1
