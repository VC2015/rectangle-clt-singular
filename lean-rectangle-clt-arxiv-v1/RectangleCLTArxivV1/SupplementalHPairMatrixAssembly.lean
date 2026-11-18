import RectangleCLTArxivV1.SupplementalHPairExtraFactors

/-! The pair matrix assembly from the actual ordinary positive kernels
and actual signed coarea trace. This is an intermediate theorem; the
geometric suppliers are discharged in the physical endpoint separately. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem supplementalH_integrable_angle_weighted_pair_nuclear_sum
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M A : Matrix (Fin p) (Fin r) ℝ) :
    Integrable (fun ω => ∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
      symmetricNuclearNorm (selectorGaussianScore s M V α ω)) μ := by
  classical
  have hsum := integrable_selector_nuclear_sum (k := K+2) μ s M V hV
  have hi (α : Fin (K+2) → Face p) :
      Integrable (fun ω => symmetricNuclearNorm (selectorGaussianScore s M V α ω)) μ := by
    apply hsum.mono' (measurable_selectorGaussianScore_nuclear s M V hV α).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (symmetricNuclearNorm_nonneg _)]
      exact Finset.single_le_sum
        (f := fun β : Fin (K+2) → Face p => symmetricNuclearNorm (selectorGaussianScore s M V β ω))
        (fun _ _ => symmetricNuclearNorm_nonneg _) (Finset.mem_univ α))
  exact integrable_finset_sum _ (fun α _ => (hi α).const_mul _)

theorem intrinsicRectangleConcentration_pairMatrix_of_mass_projection_trace
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ} (hp : 1≤p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ σ D₀ D₁ D₂ : ℝ} (hC₀ : 0≤C₀) (hκ : 0≤κ) (hσ : 0<σ)
    (hD₀ : 0≤D₀) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hunit : ∀ j,vectorNormSq (A j)=1)
    (hMass : (∫ ω, ∑ α : Fin (K+2) → Face p,
      supplementalHPairTupleAngle A α*supplementalHPairTupleMass s (σ • A) V α ω ∂μ) ≤
        (D₀*s.bandwidth^2*κ/σ)*Real.sqrt (dimensionLog p))
    (hProjection : (∫ ω, ∑ α : Fin (K+2) → Face p,
      supplementalHPairTupleProjection s (σ • A) A V α ω ∂μ) ≤
        D₁*s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p))
    (hTrace : -(∫ ω, ∑ α : Fin (K+2) → Face p,
      supplementalHPairTupleRadialTrace s (σ • A) A V α ω ∂μ) ≤
        2^K*D₂*s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p)) :
    (∫ ω, ∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
      symmetricNuclearNorm (selectorGaussianScore s (σ • A) V α ω) ∂μ) ≤
      (2*D₁+4*(D₀+2*Real.pi*C₀)*((K:ℝ)+3)+2^K*D₂)*
        s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p) := by
  classical
  let N := fun ω => ∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
    symmetricNuclearNorm (selectorGaussianScore s (σ • A) V α ω)
  let P := fun ω => ∑ α : Fin (K+2) → Face p, supplementalHPairTupleProjection s (σ • A) A V α ω
  let E := fun ω => ∑ α : Fin (K+2) → Face p, supplementalHPairTupleEntropy s (σ • A) A V α ω
  let T := fun ω => ∑ α : Fin (K+2) → Face p, supplementalHPairTupleRadialTrace s (σ • A) A V α ω
  have hNi := supplementalH_integrable_angle_weighted_pair_nuclear_sum (K := K) μ V hV s (σ • A) A
  have hPi : Integrable P μ := integrable_finset_sum _ (fun α _ =>
    (supplementalHPairTupleProjection_properties μ V hV s (σ • A) A α).2)
  have hTi : Integrable T μ := integrable_finset_sum _ (fun α _ =>
    (supplementalHPairTupleRadialTrace_properties μ V hV s (σ • A) A α).2)
  have hEnt := intrinsicRectangleConcentration_pairFamilyEntropy_of_mass (K := K) hp μ V hV s A hC₀ hκ hσ hD₀ hδh hc hunit hMass
  have hEi : Integrable E μ := hEnt.1
  have hpoint (ω : Ω) : N ω≤2*P ω+4*E ω-T ω := by
    have h := Finset.sum_le_sum (fun (α : Fin (K+2) → Face p) (_ : α∈Finset.univ) =>
      supplementalH_angle_weighted_pair_selector_reduction s A (V ω) σ hunit α)
    simpa only [N,P,E,T,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum] using h
  have hm := integral_mono hNi (((hPi.const_mul 2).add (hEi.const_mul 4)).sub hTi) hpoint
  have heI : (∫ ω,2*P ω+4*E ω-T ω ∂μ)=
      2*(∫ ω,P ω ∂μ)+4*(∫ ω,E ω ∂μ)-(∫ ω,T ω ∂μ) := by
    calc
      _ = (∫ ω,2*P ω+4*E ω ∂μ)-(∫ ω,T ω ∂μ) :=
        integral_sub ((hPi.const_mul 2).add (hEi.const_mul 4)) hTi
      _ = _ := by rw [integral_add (hPi.const_mul 2) (hEi.const_mul 4),integral_const_mul,integral_const_mul]
  change (∫ ω,N ω ∂μ)≤(∫ ω,2*P ω+4*E ω-T ω ∂μ) at hm
  rw [heI] at hm
  calc
    _ ≤ 2*(∫ ω,P ω ∂μ)+4*(∫ ω,E ω ∂μ)+
        2^K*D₂*s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p) := by
      linarith only [hm,hTrace]
    _ ≤ 2*(D₁*s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p))+
        4*(((D₀+2*Real.pi*C₀)*s.bandwidth^2*κ/σ)*((K:ℝ)+3)*dimensionLog p*Real.sqrt (dimensionLog p))+
        2^K*D₂*s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p) :=
      add_le_add_right (add_le_add (mul_le_mul_of_nonneg_left hProjection (by norm_num))
        (mul_le_mul_of_nonneg_left hEnt.2 (by norm_num))) _
    _ = _ := by ring

end
end RectangleCLTArxivV1
