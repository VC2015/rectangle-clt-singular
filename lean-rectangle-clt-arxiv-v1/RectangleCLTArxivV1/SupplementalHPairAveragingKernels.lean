import RectangleCLTArxivV1.SupplementalHPairFamilyEntropy

/-! Genuine outer measurability and integrability for the pair projection,
logarithmic reference, and signed radial kernels. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem supplementalH_dominated_signed_kernel_properties
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (W : Ω × Γ → ℝ) (hW : Measurable W)
    (B : Γ → ℝ) (hB : Measurable B) (hBi : Integrable B ν)
    (hdom : ∀ z, ‖W z‖≤B z.2) :
    Measurable (fun ω => ∫ g, W (ω,g) ∂ν) ∧
      Integrable (fun ω => ∫ g, W (ω,g) ∂ν) μ ∧
      (∀ ω, Integrable (fun g => W (ω,g)) ν) := by
  have hBprod : Integrable (fun z : Ω × Γ => B z.2) (μ.prod ν) := by
    apply (integrable_prod_iff (hB.comp measurable_snd).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun _ => hBi),?_⟩
    change Integrable (fun _ : Ω => ∫ g, ‖B g‖ ∂ν) μ
    exact integrable_const _
  have hWi : Integrable W (μ.prod ν) := hBprod.mono' hW.aestronglyMeasurable (ae_of_all _ hdom)
  refine ⟨hW.stronglyMeasurable.integral_prod_right'.measurable,hWi.integral_prod_left,?_⟩
  intro ω
  exact hBi.mono' (hW.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (ae_of_all _ (fun g => hdom (ω,g)))

def supplementalHPairTupleProjection {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (M A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (α : Fin (K+2) → Face p) (ω : Ω) : ℝ :=
  supplementalHPairTupleAngle A α*(∫ g, selectorWeight s α (M.mulVec g+V ω)*
    vectorNormSq ((supplementalHPairPlane (selectorFaceNormal A (α 0))
      (selectorFaceNormal A (α 1))).mulVec g) ∂standardGaussian r)

def supplementalHPairTupleRadialTrace {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (M A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (α : Fin (K+2) → Face p) (ω : Ω) : ℝ :=
  supplementalHPairTupleAngle A α*(∫ g, (vectorNormSq g-(r:ℝ))*
    selectorWeight s α (M.mulVec g+V ω) ∂standardGaussian r)

def supplementalHPairTupleEntropy {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (M A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (α : Fin (K+2) → Face p) (ω : Ω) : ℝ :=
  (supplementalHPairTupleAngle A α*supplementalHPairTupleMass s M V α ω)*
    Real.log ((supplementalHPairTupleAngle A α*supplementalHPairTupleReferenceMass s M V α ω)/
      (supplementalHPairTupleAngle A α*supplementalHPairTupleMass s M V α ω))

theorem supplementalHPairTupleProjection_properties
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M A : Matrix (Fin p) (Fin r) ℝ) (α : Fin (K+2) → Face p) :
    Measurable (supplementalHPairTupleProjection s M A V α) ∧
      Integrable (supplementalHPairTupleProjection s M A V α) μ := by
  let P := supplementalHPairPlane (selectorFaceNormal A (α 0)) (selectorFaceNormal A (α 1))
  let B := fun g : Vector r => vectorNormSq (P.mulVec g)
  let W := fun z : Ω × Vector r => selectorWeight s α (M.mulVec z.2+V z.1)*B z.2
  have hBm : Measurable B := by unfold B vectorNormSq Matrix.mulVec dotProduct; fun_prop
  have hBi : Integrable B (standardGaussian r) := by
    have ht := integrable_finset_sum Finset.univ (fun j (_ : j∈Finset.univ) =>
      SignedSurface.standardGaussian_integrable_faceDot_sq (P j))
    simpa only [B,vectorNormSq,faceDot,Matrix.mulVec,dotProduct] using ht
  have hM : Measurable (fun g : Vector r => M.mulVec g) := by unfold Matrix.mulVec dotProduct; fun_prop
  have hWm : Measurable W := ((continuous_selectorWeight s α).measurable.comp
    ((hM.comp measurable_snd).add (hV.comp measurable_fst))).mul (hBm.comp measurable_snd)
  have hdom (z : Ω × Vector r) : ‖W z‖≤B z.2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (selectorWeight_nonneg s α _) (vectorNormSq_nonneg _))]
    exact mul_le_of_le_one_left (vectorNormSq_nonneg _) (selectorWeight_le_one s α _)
  have hp := supplementalH_dominated_signed_kernel_properties μ (standardGaussian r) W hWm B hBm hBi hdom
  exact ⟨hp.1.const_mul _,hp.2.1.const_mul _⟩

theorem supplementalHPairTupleRadialTrace_properties
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M A : Matrix (Fin p) (Fin r) ℝ) (α : Fin (K+2) → Face p) :
    Measurable (supplementalHPairTupleRadialTrace s M A V α) ∧
      Integrable (supplementalHPairTupleRadialTrace s M A V α) μ := by
  let B := fun g : Vector r => |vectorNormSq g-(r:ℝ)|
  let W := fun z : Ω × Vector r => (vectorNormSq z.2-(r:ℝ))*selectorWeight s α (M.mulVec z.2+V z.1)
  have hBm : Measurable B := by unfold B vectorNormSq; fun_prop
  have hBi : Integrable B (standardGaussian r) :=
    ((SignedSurface.standardGaussian_integrable_vectorNormSq r).sub (integrable_const _)).abs
  have hM : Measurable (fun g : Vector r => M.mulVec g) := by unfold Matrix.mulVec dotProduct; fun_prop
  have hWm : Measurable W := (by unfold vectorNormSq; fun_prop : Measurable (fun z : Ω × Vector r => vectorNormSq z.2-(r:ℝ))).mul
    ((continuous_selectorWeight s α).measurable.comp ((hM.comp measurable_snd).add (hV.comp measurable_fst)))
  have hdom (z : Ω × Vector r) : ‖W z‖≤B z.2 := by
    change |(vectorNormSq z.2-(r:ℝ))*selectorWeight s α (M.mulVec z.2+V z.1)|≤_
    rw [abs_mul,abs_of_nonneg (selectorWeight_nonneg s α _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (selectorWeight_le_one s α _)
  have hp := supplementalH_dominated_signed_kernel_properties μ (standardGaussian r) W hWm B hBm hBi hdom
  exact ⟨hp.1.const_mul _,hp.2.1.const_mul _⟩

theorem supplementalH_angle_weighted_pair_selector_reduction {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (σ : ℝ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (α : Fin (K+2) → Face p) :
    supplementalHPairTupleAngle A α*symmetricNuclearNorm (weightedScore (standardGaussian r) id
      (fun g => selectorWeight s α ((σ • A).mulVec g+v))) ≤
      2*supplementalHPairTupleProjection s (σ • A) A (fun _ : Unit => v) α ()+
      4*supplementalHPairTupleEntropy s (σ • A) A (fun _ : Unit => v) α ()-
      supplementalHPairTupleRadialTrace s (σ • A) A (fun _ : Unit => v) α () := by
  let c := supplementalHPairTupleAngle A α
  let ρ := faceDot (selectorFaceNormal A (α 0)) (selectorFaceNormal A (α 1))
  have hc : 0≤c := correlationAngleWeight_nonneg _
  by_cases hρ : ρ^2<1
  · have ht := mul_le_mul_of_nonneg_left (supplementalH_pair_selector_projected_reduction s A v σ α hunit hρ) hc
    have he := entropy_term_common_factor
      (p := supplementalHPairTupleMass s (σ • A) (fun _ : Unit => v) α ())
      (b := supplementalHPairTupleReferenceMass s (σ • A) (fun _ : Unit => v) α ()) hc
    dsimp only [supplementalHPairTupleProjection,supplementalHPairTupleEntropy,supplementalHPairTupleRadialTrace]
    rw [he]
    exact ht.trans_eq (by
      dsimp only [supplementalHSelectorProjection,supplementalHSelectorMass,supplementalHSelectorRadialTrace,
        supplementalHPairTupleMass,supplementalHPairTupleReferenceMass,weightMass,c]
      ring)
  · have hz : c=0 := by
      change Real.arccos ρ*Real.sqrt (1-ρ^2)=0
      rw [Real.sqrt_eq_zero_of_nonpos (by linarith),mul_zero]
    change c*_≤_
    simp only [show supplementalHPairTupleAngle A α=c from rfl,hz,zero_mul,
      supplementalHPairTupleProjection,supplementalHPairTupleEntropy,supplementalHPairTupleRadialTrace,
      zero_div,Real.log_zero,mul_zero,add_zero,sub_zero,le_refl]

end
end RectangleCLTArxivV1
