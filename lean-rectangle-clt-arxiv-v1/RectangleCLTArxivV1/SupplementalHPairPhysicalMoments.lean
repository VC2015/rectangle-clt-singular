import RectangleCLTArxivV1.SupplementalHPairPositiveCoordinates
import RectangleCLTArxivV1.PositiveGammaMeans

/-! The two sharp actual positive budgets for every original pair tuple.
The physical concentration, positive coarea and all extra factors are
proved inputs; no averaged positive moment is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def supplementalHPairMassConstant (C₀ : ℝ) : ℝ := positiveSoftPairMassConstant*C₀
def supplementalHPairProjectionConstant (C₀ : ℝ) : ℝ := positiveSoftPairProjectionConstant*C₀

theorem supplementalHPairMassConstant_nonneg {C₀ : ℝ} (hC₀ : 0≤C₀) :
    0≤supplementalHPairMassConstant C₀ := mul_nonneg positiveSoftPairMassConstant_pos.le hC₀

theorem supplementalHPairProjectionConstant_nonneg {C₀ : ℝ} (hC₀ : 0≤C₀) :
    0≤supplementalHPairProjectionConstant C₀ := mul_nonneg positiveSoftPairProjectionConstant_pos.le hC₀

theorem intrinsicRectangleConcentration_pairPhysicalMass {p n K : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin (n+1)) ℝ) {C₀ δ κ σ : ℝ}
    (hC₀ : 0≤C₀) (hδ : 0≤δ) (hκ : 0≤κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    (∫ x, ∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
      supplementalHPairTupleMass s (σ • A) (fun x => A.mulVec x) α x ∂ν) ≤
      (supplementalHPairMassConstant C₀*s.bandwidth^2*κ/σ)*Real.sqrt (dimensionLog p) := by
  let V := fun x : Vector (n+1) => A.mulVec x
  have hV : Measurable V := by unfold V Matrix.mulVec dotProduct; fun_prop
  have hu (j : Fin s.faces.card) : vectorNormSq (selectorFaceNormal A (activeFaceIndex s j))=1 :=
    selectorFaceNormal_normSq A hunit _
  have hNormal (f : Face p) : capRectangularFactorNormal A f=selectorFaceNormal A f := by
    ext j
    unfold capRectangularFactorNormal selectorFaceNormal
    split_ifs <;> rfl
  have hb (b : Vector s.faces.card) (t : ℝ) (ht : 0<t) :
      ν.real (faceLayer (fun j => selectorFaceNormal A (activeFaceIndex s j)) b t)≤(C₀*κ)*(t+δ) := by
    simpa only [hNormal] using intrinsicRectangleConcentration_physical_layer ν A hc (activeFaceIndex s) b ht
  have h := positiveGammaSoftOrderedPairMass_concentrated_base hp ν (selectorFaceNormal A) (activeFaceIndex s)
    (activeFaceOffsets s) (mul_nonneg hC₀ hκ) hδ hσ s.bandwidth_pos hu hb hδσ
  have heU : (fun j => selectorFaceNormal A (activeFaceIndex s j))=activeFaceNormals s A := by
    funext j
    exact (activeFaceNormals_eq_selectorFaceNormal s A j).symm
  rw [heU] at h
  have hKi : Integrable (fun x => ∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
      supplementalHPairTupleMass s (σ • A) V α x) ν := integrable_finset_sum _ (fun α _ =>
    (supplementalHPairTupleMass_properties ν V hV s (σ • A) α).2.const_mul _)
  have hbound := integral_mono hKi h.1 (fun x =>
    (supplementalHPairTupleMass_extra_factors (K := K) s (σ • A) A (A.mulVec x)).trans_eq
      (supplementalHPairMass_baseline_eq_native s A σ x))
  exact (hbound.trans h.2).trans_eq (by unfold supplementalHPairMassConstant;ring)

theorem intrinsicRectangleConcentration_pairPhysicalProjection {p n K : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin (n+1)) ℝ) {C₀ δ κ σ : ℝ}
    (hC₀ : 0≤C₀) (hδ : 0≤δ) (hκ : 0≤κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    (∫ x, ∑ α : Fin (K+2) → Face p,
      supplementalHPairTupleProjection s (σ • A) A (fun x => A.mulVec x) α x ∂ν) ≤
      supplementalHPairProjectionConstant C₀*s.bandwidth^2*κ/σ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  let V := fun x : Vector (n+1) => A.mulVec x
  have hV : Measurable V := by unfold V Matrix.mulVec dotProduct; fun_prop
  have hu (j : Fin s.faces.card) : vectorNormSq (selectorFaceNormal A (activeFaceIndex s j))=1 :=
    selectorFaceNormal_normSq A hunit _
  have hNormal (f : Face p) : capRectangularFactorNormal A f=selectorFaceNormal A f := by
    ext j
    unfold capRectangularFactorNormal selectorFaceNormal
    split_ifs <;> rfl
  have hb (b : Vector s.faces.card) (t : ℝ) (ht : 0<t) :
      ν.real (faceLayer (fun j => selectorFaceNormal A (activeFaceIndex s j)) b t)≤(C₀*κ)*(t+δ) := by
    simpa only [hNormal] using intrinsicRectangleConcentration_physical_layer ν A hc (activeFaceIndex s) b ht
  have h := positiveGammaSoftOrderedPairProjection_concentrated_base hp ν (selectorFaceNormal A) (activeFaceIndex s)
    (activeFaceOffsets s) (mul_nonneg hC₀ hκ) hδ hσ s.bandwidth_pos hu hb hδσ
  have heU : (fun j => selectorFaceNormal A (activeFaceIndex s j))=activeFaceNormals s A := by
    funext j
    exact (activeFaceNormals_eq_selectorFaceNormal s A j).symm
  rw [heU] at h
  have hKi : Integrable (fun x => ∑ α : Fin (K+2) → Face p, supplementalHPairTupleProjection s (σ • A) A V α x) ν :=
    integrable_finset_sum _ (fun α _ => (supplementalHPairTupleProjection_properties ν V hV s (σ • A) A α).2)
  have hbound := integral_mono hKi h.1 (fun x =>
    (supplementalHPairTupleProjection_extra_factors (K := K) s (σ • A) A (A.mulVec x)).trans_eq
      (supplementalHPairProjection_baseline_eq_native s A σ x))
  exact (hbound.trans h.2).trans_eq (by unfold supplementalHPairProjectionConstant;ring)

end
end RectangleCLTArxivV1
