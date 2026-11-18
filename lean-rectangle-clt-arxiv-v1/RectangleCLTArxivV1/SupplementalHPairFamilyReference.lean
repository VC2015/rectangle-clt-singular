import RectangleCLTArxivV1.SupplementalHPairSelectorReference
import RectangleCLTArxivV1.SupplementalHPairReferenceTransport
import RectangleCLTArxivV1.SupplementalHKernelMass
import RectangleCLTArxivV1.SupplementalIRestriction

/-! Actual angle-weighted reference masses for every pair tuple. The
original base law is integrated before the finite reference count. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def supplementalHPairTupleAngle {p r K : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (α : Fin (K+2) → Face p) : ℝ :=
  correlationAngleWeight (faceDot (selectorFaceNormal A (α 0)) (selectorFaceNormal A (α 1)))

def supplementalHPairTupleMass {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (α : Fin (K+2) → Face p) (ω : Ω) : ℝ :=
  ∫ g, selectorWeight s α (M.mulVec g+V ω) ∂standardGaussian r

def supplementalHPairTupleReferenceMass {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (α : Fin (K+2) → Face p) (ω : Ω) : ℝ :=
  ∫ g, supplementalHPairReference s (α 0) (α 1) (M.mulVec g+V ω) ∂standardGaussian r

theorem supplementalHPairTupleReferenceMass_properties
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (α : Fin (K+2) → Face p) :
    Measurable (supplementalHPairTupleReferenceMass s M V α) ∧
      Integrable (supplementalHPairTupleReferenceMass s M V α) μ := by
  let W := fun z : Ω × Vector r => supplementalHPairReference s (α 0) (α 1) (M.mulVec z.2+V z.1)
  have hM : Measurable (fun g : Vector r => M.mulVec g) := by unfold Matrix.mulVec dotProduct; fun_prop
  have hm : Measurable W := (measurable_supplementalHPairReference s _ _).comp
    ((hM.comp measurable_snd).add (hV.comp measurable_fst))
  have hp := supplementalH_dominated_kernel_mass_properties μ (standardGaussian r) W hm
    (fun _ => (supplementalHPairReference_bounds s _ _ _).1) (fun _ => 1) measurable_const
    (integrable_const _) (fun _ => (supplementalHPairReference_bounds s _ _ _).2)
  exact ⟨hp.1,hp.2.1⟩

theorem supplementalHPairTupleMass_properties
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (α : Fin (K+2) → Face p) :
    Measurable (supplementalHPairTupleMass s M V α) ∧
      Integrable (supplementalHPairTupleMass s M V α) μ := by
  let W := fun z : Ω × Vector r => selectorWeight s α (M.mulVec z.2+V z.1)
  have hM : Measurable (fun g : Vector r => M.mulVec g) := by unfold Matrix.mulVec dotProduct; fun_prop
  have hm : Measurable W := (continuous_selectorWeight s α).measurable.comp
    ((hM.comp measurable_snd).add (hV.comp measurable_fst))
  have hp := supplementalH_dominated_kernel_mass_properties μ (standardGaussian r) W hm
    (fun _ => selectorWeight_nonneg s α _) (fun _ => 1) measurable_const
    (integrable_const _) (fun _ => selectorWeight_le_one s α _)
  exact ⟨hp.1,hp.2.1⟩

theorem intrinsicRectangleConcentration_pairTupleReference
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ σ : ℝ} (hC₀ : 0≤C₀) (hκ : 0≤κ) (hσ : 0<σ) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (α : Fin (K+2) → Face p) :
    (∫ ω, supplementalHPairTupleAngle A α*supplementalHPairTupleReferenceMass s (σ • A) V α ω ∂μ) ≤
      2*Real.pi*C₀*s.bandwidth^2*κ/σ := by
  let u := selectorFaceNormal A (α 0)
  let v := selectorFaceNormal A (α 1)
  let ρ := faceDot u v
  by_cases hρ : ρ^2<1
  · let W := fun z : Ω × Vector r => supplementalHPairReference s (α 0) (α 1) ((σ • A).mulVec z.2+V z.1)
    have hM : Measurable (fun g : Vector r => (σ • A).mulVec g) := by unfold Matrix.mulVec dotProduct; fun_prop
    have hWm : Measurable W := (measurable_supplementalHPairReference s _ _).comp
      ((hM.comp measurable_snd).add (hV.comp measurable_fst))
    have hWi : Integrable W (μ.prod (standardGaussian r)) := by
      apply (integrable_const (1:ℝ)).mono' hWm.aestronglyMeasurable
      exact ae_of_all _ (fun _ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (supplementalHPairReference_bounds s _ _ _).1]
        exact (supplementalHPairReference_bounds s _ _ _).2)
    rw [integral_const_mul]
    change correlationAngleWeight ρ*(∫ ω, ∫ g, W (ω,g) ∂standardGaussian r ∂μ)≤_
    rw [←integral_prod _ hWi]
    have he (z : Ω × Vector r) : W z=hReferencePair
        ((FaceSmoother.normalDot (α 0) (V z.1)+σ*faceDot u z.2-s.offsets (α 0))/s.bandwidth,
         (FaceSmoother.normalDot (α 1) (V z.1)+σ*faceDot v z.2-s.offsets (α 1))/s.bandwidth) := by
      dsimp only [W,supplementalHPairReference,FaceSmoother.faceScore]
      rw [Matrix.smul_mulVec_assoc,normalDot_affine,normalDot_affine]
      congr 2 <;> dsimp only [u,v] <;> ring
    rw [integral_congr_ae (ae_of_all _ he)]
    exact intrinsicRectangleConcentration_pair_projected_angular_reference_mass μ V hV hC₀ hκ
      s.bandwidth_pos hσ hδh hc u v (selectorFaceNormal_normSq A hunit _)
      (selectorFaceNormal_normSq A hunit _) hρ _ _ _ _
  · have hz : supplementalHPairTupleAngle A α=0 := by
      have hs : Real.sqrt (1-ρ^2)=0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
      change Real.arccos ρ*Real.sqrt (1-ρ^2)=0
      rw [hs,mul_zero]
    simp only [hz,zero_mul,integral_zero]
    have hh := s.bandwidth_pos
    positivity

/-- Only the reference family is counted by all tuples. Every original
first pair and every later selector label remains in the index type. -/
theorem intrinsicRectangleConcentration_pairReferenceFamily
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ σ : ℝ} (hC₀ : 0≤C₀) (hκ : 0≤κ) (hσ : 0<σ) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hunit : ∀ j,vectorNormSq (A j)=1) :
    (∫ ω, ∑ α : Fin (K+2) → Face p,
      supplementalHPairTupleAngle A α*supplementalHPairTupleReferenceMass s (σ • A) V α ω ∂μ) ≤
      (2*Real.pi*C₀*s.bandwidth^2*κ/σ)*(Fintype.card (Face p):ℝ)^(K+2) := by
  classical
  rw [integral_finset_sum _ (fun α _ =>
    (supplementalHPairTupleReferenceMass_properties μ V hV s (σ • A) α).2.const_mul _)]
  calc
    _ ≤ ∑ _α : Fin (K+2) → Face p, 2*Real.pi*C₀*s.bandwidth^2*κ/σ := Finset.sum_le_sum
      (fun α _ => intrinsicRectangleConcentration_pairTupleReference μ V hV s A hC₀ hκ hσ hδh hc hunit α)
    _ = _ := by simp [Fintype.card_fun,mul_comm]

end
end RectangleCLTArxivV1
