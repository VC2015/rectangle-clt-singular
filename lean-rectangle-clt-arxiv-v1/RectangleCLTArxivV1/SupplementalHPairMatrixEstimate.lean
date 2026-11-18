import RectangleCLTArxivV1.SupplementalHPairPhysicalMoments
import RectangleCLTArxivV1.SupplementalHPairMatrixAssembly
import RectangleCLTArxivV1.SupplementalHPairConstant

/-! Complete actual angle-weighted pair matrix estimate. Every positive
mass, plane moment, entropy and signed trace supplier is discharged. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def supplementalHPairPhysicalMatrixConstant (C₀ : ℝ) : ℝ :=
  supplementalHPairMatrixConstant C₀ (supplementalHPairMassConstant C₀)
    (supplementalHPairProjectionConstant C₀) (supplementalHPairTraceConstant C₀)

theorem supplementalHPairPhysicalMatrixConstant_ge_four {C₀ : ℝ} (hC₀ : 0≤C₀) :
    4≤supplementalHPairPhysicalMatrixConstant C₀ :=
  supplementalHPairMatrixConstant_ge_four hC₀ (supplementalHPairMassConstant_nonneg hC₀)
    (supplementalHPairProjectionConstant_nonneg hC₀) (supplementalHPairTraceConstant_nonneg hC₀)

/-- The full original angle-weighted pair matrix proposition, with all
additional tuple factors retained and no first-pair gap hypothesis. -/
theorem proposition_H2_pair_matrix {p n K : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin (n+1)) ℝ) {C₀ δ κ σ : ℝ}
    (hC₀ : 0≤C₀) (hδ : 0≤δ) (hκ : 0≤κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    (∫ x, ∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
      symmetricNuclearNorm (selectorGaussianScore s (σ • A) (fun x => A.mulVec x) α x) ∂ν) ≤
      supplementalHPairPhysicalMatrixConstant C₀^(K+3)*s.bandwidth^2*κ/σ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  let V := fun x : Vector (n+1) => A.mulVec x
  have hV : Measurable V := by unfold V Matrix.mulVec dotProduct; fun_prop
  have hMass := intrinsicRectangleConcentration_pairPhysicalMass (K := K) hp ν s A hC₀ hδ hκ hσ hunit hc hδσ
  have hProj := intrinsicRectangleConcentration_pairPhysicalProjection (K := K) hp ν s A hC₀ hδ hκ hσ hunit hc hδσ
  have hTrace := intrinsicRectangleConcentration_pairPhysicalTrace hp ν s A hC₀ hδ hκ hσ hunit hc hδσ K
  let T := fun x => ∑ α : Fin (K+2) → Face p, supplementalHPairTupleRadialTrace s (σ • A) A V α x
  have hTi : Integrable T ν := hTrace.1
  have hNeg : -(∫ x,T x ∂ν)≤(2:ℝ)^K*supplementalHPairTraceConstant C₀*s.bandwidth^2*κ/σ*
      dimensionLog p*Real.sqrt (dimensionLog p) := by
    have ht := integral_mono hTi.neg hTi.abs (fun x => neg_le_abs (T x))
    change (∫ x,-T x ∂ν)≤(∫ x,|T x| ∂ν) at ht
    rw [integral_neg] at ht
    exact ht.trans hTrace.2
  have hRaw := intrinsicRectangleConcentration_pairMatrix_of_mass_projection_trace (K := K) hp ν V hV s A
    hC₀ hκ hσ (supplementalHPairMassConstant_nonneg hC₀) hδh hc hunit hMass hProj hNeg
  have hb := supplementalH_pair_matrix_bracket_le_power hC₀ (supplementalHPairMassConstant_nonneg hC₀)
    (supplementalHPairProjectionConstant_nonneg hC₀) (supplementalHPairTraceConstant_nonneg hC₀) K
  let Z := s.bandwidth^2*κ/σ*dimensionLog p*Real.sqrt (dimensionLog p)
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hZ : 0≤Z := by dsimp [Z]; positivity
  have hBound := mul_le_mul_of_nonneg_right hb hZ
  exact hRaw.trans (by
    simpa only [supplementalHPairPhysicalMatrixConstant,Z,mul_assoc,div_eq_mul_inv] using hBound)

end
end RectangleCLTArxivV1
