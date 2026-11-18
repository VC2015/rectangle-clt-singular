import RectangleCLTArxivV1.SupplementalHPairFamilyReference
import RectangleCLTArxivV1.SupplementalHCubicFamilyEntropy

/-! The outer log-sum step for actual angle-weighted pair tuple masses.
Only the ordinary positive mass budget is supplied to this intermediate
lemma; the entropy's measurability and integrability are conclusions. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem supplementalH_weighted_pair_mass_le_reference {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (v : Vector p)
    (hunit : ∀ j,vectorNormSq (A j)=1) (α : Fin (K+2) → Face p) :
    supplementalHPairTupleAngle A α*supplementalHPairTupleMass s (σ • A) (fun _ : Unit => v) α () ≤
      supplementalHPairTupleAngle A α*supplementalHPairTupleReferenceMass s (σ • A) (fun _ : Unit => v) α () := by
  let ρ := faceDot (selectorFaceNormal A (α 0)) (selectorFaceNormal A (α 1))
  by_cases hρ : ρ^2<1
  · have hfg : α 0≠α 1 := by
      intro he
      have hd : ρ=1 := by
        dsimp only [ρ]
        rw [he]
        simpa only [faceDot,vectorNormSq,pow_two] using selectorFaceNormal_normSq A hunit (α 1)
      rw [hd] at hρ
      norm_num at hρ
    have hMi : Integrable (fun g : Vector r => supplementalHPairReference s (α 0) (α 1) ((σ • A).mulVec g+v))
        (standardGaussian r) := by
      have hX : Measurable (fun g : Vector r => (σ • A).mulVec g+v) := by
        unfold Matrix.mulVec dotProduct
        fun_prop
      have hm := (measurable_supplementalHPairReference s (α 0) (α 1)).comp hX
      apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
      exact ae_of_all _ (fun g => by
        dsimp only [Function.comp_apply]
        rw [Real.norm_eq_abs,abs_of_nonneg (supplementalHPairReference_bounds s _ _ _).1]
        exact (supplementalHPairReference_bounds s _ _ _).2)
    exact mul_le_mul_of_nonneg_left (integral_mono
      (selectorWeight_affine_moments s α (σ • A) v).1 hMi
      (fun g => selectorWeight_le_supplementalHPairReference s α hfg _)) (correlationAngleWeight_nonneg ρ)
  · have hz : supplementalHPairTupleAngle A α=0 := by
      change Real.arccos ρ*Real.sqrt (1-ρ^2)=0
      rw [Real.sqrt_eq_zero_of_nonpos (by linarith),mul_zero]
    simp [hz]

theorem intrinsicRectangleConcentration_pairFamilyEntropy_of_mass
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ} (hp : 1≤p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ σ D : ℝ} (hC₀ : 0≤C₀) (hκ : 0≤κ) (hσ : 0<σ) (hD : 0≤D) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hunit : ∀ j,vectorNormSq (A j)=1)
    (hMass : (∫ ω, ∑ α : Fin (K+2) → Face p,
      supplementalHPairTupleAngle A α*supplementalHPairTupleMass s (σ • A) V α ω ∂μ) ≤
        (D*s.bandwidth^2*κ/σ)*Real.sqrt (dimensionLog p)) :
    Integrable (fun ω => ∑ α : Fin (K+2) → Face p,
      (supplementalHPairTupleAngle A α*supplementalHPairTupleMass s (σ • A) V α ω)*
        Real.log ((supplementalHPairTupleAngle A α*supplementalHPairTupleReferenceMass s (σ • A) V α ω)/
          (supplementalHPairTupleAngle A α*supplementalHPairTupleMass s (σ • A) V α ω))) μ ∧
    (∫ ω, ∑ α : Fin (K+2) → Face p,
      (supplementalHPairTupleAngle A α*supplementalHPairTupleMass s (σ • A) V α ω)*
        Real.log ((supplementalHPairTupleAngle A α*supplementalHPairTupleReferenceMass s (σ • A) V α ω)/
          (supplementalHPairTupleAngle A α*supplementalHPairTupleMass s (σ • A) V α ω)) ∂μ) ≤
      ((D+2*Real.pi*C₀)*s.bandwidth^2*κ/σ)*((K:ℝ)+3)*dimensionLog p*Real.sqrt (dimensionLog p) := by
  classical
  let P := fun (α : Fin (K+2) → Face p) ω => supplementalHPairTupleAngle A α*supplementalHPairTupleMass s (σ • A) V α ω
  let B := fun (α : Fin (K+2) → Face p) ω => supplementalHPairTupleAngle A α*supplementalHPairTupleReferenceMass s (σ • A) V α ω
  let T := (D+2*Real.pi*C₀)*s.bandwidth^2*κ/σ
  have hP (α : Fin (K+2) → Face p) := supplementalHPairTupleMass_properties μ V hV s (σ • A) α
  have hB (α : Fin (K+2) → Face p) := supplementalHPairTupleReferenceMass_properties μ V hV s (σ • A) α
  have hPm (α) : Measurable (P α) := (hP α).1.const_mul _
  have hBm (α) : Measurable (B α) := (hB α).1.const_mul _
  have hPi (α) : Integrable (P α) μ := (hP α).2.const_mul _
  have hBi (α) : Integrable (B α) μ := (hB α).2.const_mul _
  have hP0 (α) (ω) : 0≤P α ω := mul_nonneg (correlationAngleWeight_nonneg _)
    (integral_nonneg (fun g => selectorWeight_nonneg s α _))
  have hPB (α) (ω : Ω) : P α ω≤B α ω := supplementalH_weighted_pair_mass_le_reference s A σ (V ω) hunit α
  have hT : 0≤T := by dsimp [T]; positivity
  have hL := log_exp_mul_nat_ge_one hp
  have hR : 1≤Real.sqrt (dimensionLog p) := Real.one_le_sqrt.mpr hL
  have hcoefM : D*s.bandwidth^2*κ/σ≤T := by
    have ht := mul_le_mul_of_nonneg_right (show D≤D+2*Real.pi*C₀ from le_add_of_nonneg_right (by positivity))
      (show 0≤s.bandwidth^2*κ/σ by positivity)
    simpa only [T,mul_div_assoc,mul_assoc] using ht
  have hM : (∫ ω, ∑ α : Fin (K+2) → Face p, P α ω ∂μ)≤T*Real.sqrt (dimensionLog p) :=
    hMass.trans (mul_le_mul_of_nonneg_right hcoefM (Real.sqrt_nonneg _))
  have hcoefB : 2*Real.pi*C₀*s.bandwidth^2*κ/σ≤T := by
    have ht := mul_le_mul_of_nonneg_right (show 2*Real.pi*C₀≤D+2*Real.pi*C₀ by linarith)
      (show 0≤s.bandwidth^2*κ/σ by positivity)
    simpa only [T,mul_div_assoc,mul_assoc] using ht
  have hRef := intrinsicRectangleConcentration_pairReferenceFamily (K := K) μ V hV s A hC₀ hκ hσ hδh hc hunit
  have hRefs : (∫ ω, ∑ α : Fin (K+2) → Face p,B α ω ∂μ)≤T*(Fintype.card (Face p):ℝ)^(K+2) :=
    hRef.trans (mul_le_mul_of_nonneg_right hcoefB (pow_nonneg (Nat.cast_nonneg _) _))
  refine ⟨integrable_finset_sum _ (fun α _ => integrable_entropy_term μ (P α) (B α)
    (hPm α) (hBm α) (hP0 α) (hPB α) (hPi α) (hBi α)),?_⟩
  have ht := supplementalH_integral_entropy_cardinality_bound μ P B hPm hBm hP0 hPB hPi hBi
    hT hL hR (supplementalH_log_face_card_le hp).1 (supplementalH_log_face_card_le hp).2 (K+2) hM hRefs
  simpa only [T,P,B,dimensionLog,Nat.cast_add,Nat.cast_ofNat,
    show ((2:ℝ)+1)=3 by norm_num,add_assoc,mul_assoc] using ht

end
end RectangleCLTArxivV1
