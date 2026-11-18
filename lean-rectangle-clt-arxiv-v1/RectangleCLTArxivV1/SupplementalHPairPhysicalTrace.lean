import RectangleCLTArxivV1.SupplementalHPairTraceRestoration
import RectangleCLTArxivV1.SupplementalHPairAveragingKernels
import RectangleCLTArxivV1.SupplementalHActiveFaceReindex
import RectangleCLTArxivV1.SupplementalHPhysicalConcentration

/-! The complete actual angle-weighted pair radial trace on the physical
base. Every active and inactive original face and every extra selector
label is transported exactly, before the aggregate absolute value. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem sum_activeFace_pair_weight_physical {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (y : Vector r) (c : Face p → Face p → ℝ) (K : ℕ) :
    (∑ f : Face p,∑ g : Face p,c f g*s.F (A.mulVec y)*s.pi (A.mulVec y) f*
      s.pi (A.mulVec y) g*s.theta (A.mulVec y)^K)=
    ∑ j : Fin s.faces.card,∑ l : Fin s.faces.card,c (activeFaceIndex s j) (activeFaceIndex s l)*
      logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y*
      logisticFaceWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y j*
      logisticFaceWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y l*
      (1-logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y)^K := by
  rw [sum_activeFace_values s _ (fun f hf => by
    simp [FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hf])]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_activeFace_values s _ (fun f hf => by
    simp [FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hf])]
  simp_rw [activeFace_nullWeight,activeFace_piWeight,activeFace_thetaWeight]

def supplementalHPairPhysicalTrace {p r : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (K : ℕ) (x : Vector r) : ℝ :=
  ∑ α : Fin (K+2) → Face p,supplementalHPairTupleRadialTrace s (σ•A) A
    (fun x => A.mulVec x) α x

theorem integrable_gaussian_pair_radial_selector_physical {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (x : Vector r)
    (α : Fin (K+2) → Face p) :
    Integrable (fun g => (vectorNormSq g-(r:ℝ))*
      selectorWeight s α ((σ•A).mulVec g+A.mulVec x)) (standardGaussian r) := by
  have hm : Measurable (fun g : Vector r => (vectorNormSq g-(r:ℝ))*
      selectorWeight s α ((σ•A).mulVec g+A.mulVec x)) := by
    apply Measurable.mul _ (continuous_selectorWeight_affine s α (σ•A) (A.mulVec x)).measurable
    unfold vectorNormSq
    fun_prop
  apply ((SignedSurface.standardGaussian_integrable_vectorNormSq r).sub (integrable_const _)).norm.mono'
    hm.aestronglyMeasurable
  exact ae_of_all _ (fun g => by
    change |(vectorNormSq g-(r:ℝ))*selectorWeight s α ((σ•A).mulVec g+A.mulVec x)|≤|vectorNormSq g-(r:ℝ)|
    rw [abs_mul,abs_of_nonneg (selectorWeight_nonneg s α _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (selectorWeight_le_one s α _))

theorem supplementalHPairPhysicalTrace_eq_softTrace {p r : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (K : ℕ) (x : Vector r) :
    supplementalHPairPhysicalTrace s A σ K x=
      supplementalHSoftPairTrace (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth σ K x := by
  classical
  unfold supplementalHPairPhysicalTrace supplementalHPairTupleRadialTrace
  simp_rw [←integral_const_mul]
  rw [←integral_finset_sum _ (fun α _ =>
    (integrable_gaussian_pair_radial_selector_physical s A σ x α).const_mul _)]
  unfold supplementalHSoftPairTrace
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have he : (σ•A).mulVec g+A.mulVec x=A.mulVec (x+σ • g) := by
      rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.smul_mulVec_assoc]
      exact add_comm _ _
    dsimp only
    rw [he]
    calc
      _=(vectorNormSq g-(r:ℝ))*(∑ α : Fin (K+2) → Face p,
        correlationAngleWeight (faceDot (selectorFaceNormal A (α 0)) (selectorFaceNormal A (α 1)))*
          selectorWeight s α (A.mulVec (x+σ • g))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by unfold supplementalHPairTupleAngle;ring)
      _=(vectorNormSq g-(r:ℝ))*(∑ f : Face p,∑ l : Face p,
        correlationAngleWeight (faceDot (selectorFaceNormal A f) (selectorFaceNormal A l))*
          s.F (A.mulVec (x+σ • g))*s.pi (A.mulVec (x+σ • g)) f*
            s.pi (A.mulVec (x+σ • g)) l*s.theta (A.mulVec (x+σ • g))^K) := by
        rw [sum_selector_first_pair_weight (K := K) s _
          (fun f l => correlationAngleWeight (faceDot (selectorFaceNormal A f) (selectorFaceNormal A l)))]
      _=(vectorNormSq g-(r:ℝ))*(∑ j : Fin s.faces.card,∑ l : Fin s.faces.card,
        correlationAngleWeight (faceDot (selectorFaceNormal A (activeFaceIndex s j))
          (selectorFaceNormal A (activeFaceIndex s l)))*
          logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g)*
          logisticFaceWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g) j*
          logisticFaceWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g) l*
          (1-logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g))^K) := by
        rw [sum_activeFace_pair_weight_physical]
      _=_ := by
        simp only [Fintype.sum_prod_type]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        rw [activeFaceNormals_eq_selectorFaceNormal s A j,activeFaceNormals_eq_selectorFaceNormal s A l]
        ring)

/-- The actual aggregate signed pair trace with every tuple retained.
No hard-surface, trace, or matrix estimate is assumed. -/
theorem intrinsicRectangleConcentration_pairPhysicalTrace {p n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin (n+1)) ℝ) {C₀ δ κ σ : ℝ}
    (hC₀ : 0≤C₀) (hδ : 0≤δ) (hκ : 0≤κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (K : ℕ) :
    Integrable (fun x => ∑ α : Fin (K+2) → Face p,
      supplementalHPairTupleRadialTrace s (σ•A) A (fun x => A.mulVec x) α x) ν ∧
    (∫ x,|∑ α : Fin (K+2) → Face p,
      supplementalHPairTupleRadialTrace s (σ•A) A (fun x => A.mulVec x) α x| ∂ν)≤
      (2:ℝ)^K*supplementalHPairTraceConstant C₀*s.bandwidth^2*κ/σ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  have hu (j : Fin s.faces.card) : vectorNormSq (selectorFaceNormal A (activeFaceIndex s j))=1 :=
    selectorFaceNormal_normSq A hunit _
  have hNormal (f : Face p) : capRectangularFactorNormal A f=selectorFaceNormal A f := by
    ext j
    unfold capRectangularFactorNormal selectorFaceNormal
    split_ifs <;> rfl
  have hb (b : Vector s.faces.card) (t : ℝ) (ht : 0<t) :
      ν.real (faceLayer (fun j => selectorFaceNormal A (activeFaceIndex s j)) b t)≤(C₀*κ)*(t+δ) := by
    simpa only [hNormal] using
      intrinsicRectangleConcentration_physical_layer ν A hc (activeFaceIndex s) b ht
  have h := supplementalH_softPairTrace_concentrated_base hp ν (selectorFaceNormal A) (activeFaceIndex s)
    (activeFaceOffsets s) (mul_nonneg hC₀ hκ) hδ hσ s.bandwidth_pos hu hb hδσ K
  have heU : (fun j => selectorFaceNormal A (activeFaceIndex s j))=activeFaceNormals s A := by
    funext j
    exact (activeFaceNormals_eq_selectorFaceNormal s A j).symm
  rw [heU] at h
  have he : supplementalHPairPhysicalTrace s A σ K=
      supplementalHSoftPairTrace (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth σ K :=
    funext (supplementalHPairPhysicalTrace_eq_softTrace s A σ K)
  change Integrable (supplementalHPairPhysicalTrace s A σ K) ν ∧
    (∫ x,|supplementalHPairPhysicalTrace s A σ K x| ∂ν)≤_
  rw [he]
  refine ⟨h.1,?_⟩
  exact h.2.trans_eq (by unfold supplementalHPairTraceConstant;ring)

end
end RectangleCLTArxivV1
