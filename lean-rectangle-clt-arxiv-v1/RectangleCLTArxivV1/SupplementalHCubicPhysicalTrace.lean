import RectangleCLTArxivV1.SupplementalHCubicTraceRestoration
import RectangleCLTArxivV1.SupplementalHActiveFaceReindex
import RectangleCLTArxivV1.SupplementalHPhysicalConcentration

/-! The actual signed radial tuple trace for an arbitrary rectangle
smoother, with inactive faces and all extra factors retained. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def supplementalHCubicPhysicalTrace {p r : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (K : ℕ) (x : Vector r) : ℝ :=
  ∑ α : Fin (K+1) → Face p, ∫ g, (vectorNormSq g-(r:ℝ))*|faceDot (selectorFaceNormal A (α 0)) g| *
    selectorWeight s α (A.mulVec (x+σ • g)) ∂standardGaussian r

theorem integrable_gaussianAbsoluteFace_selector_physical {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (x : Vector r)
    (α : Fin (K+1) → Face p) :
    Integrable (fun g => (vectorNormSq g-(r:ℝ))*|faceDot (selectorFaceNormal A (α 0)) g| *
      selectorWeight s α (A.mulVec (x+σ • g))) (standardGaussian r) := by
  have hX : Measurable (fun g : Vector r => A.mulVec (x+σ • g)) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hP : Measurable (fun g : Vector r => (vectorNormSq g-(r:ℝ))*|faceDot (selectorFaceNormal A (α 0)) g|) := by
    unfold vectorNormSq faceDot
    fun_prop
  apply (integrable_gaussianAbsoluteFaceScore (selectorFaceNormal A (α 0))).norm.mono'
    (hP.mul ((continuous_selectorWeight s α).measurable.comp hX)).aestronglyMeasurable
  exact ae_of_all _ (fun g => by
    change |((vectorNormSq g-(r:ℝ))*|faceDot (selectorFaceNormal A (α 0)) g|)*
      selectorWeight s α (A.mulVec (x+σ • g))|≤
      |(vectorNormSq g-(r:ℝ))*(|faceDot (selectorFaceNormal A (α 0)) g|)|
    rw [abs_mul,abs_of_nonneg (selectorWeight_nonneg s α _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (selectorWeight_le_one s α _))

/-- Exact active-face transport of the complete signed tuple trace. -/
theorem supplementalHCubicPhysicalTrace_eq_softTrace {p r : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (K : ℕ) (x : Vector r) :
    supplementalHCubicPhysicalTrace s A σ K x=
      supplementalHSoftCubicTrace (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth σ K x := by
  classical
  unfold supplementalHCubicPhysicalTrace supplementalHSoftCubicTrace
  rw [←integral_finset_sum _ (fun α _ => integrable_gaussianAbsoluteFace_selector_physical s A σ x α)]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    calc
      _ = (vectorNormSq g-(r:ℝ))*(∑ α : Fin (K+1) → Face p,
          |faceDot (selectorFaceNormal A (α 0)) g| *selectorWeight s α (A.mulVec (x+σ • g))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = (vectorNormSq g-(r:ℝ))*(∑ f : Face p, |faceDot (selectorFaceNormal A f) g| *
          s.F (A.mulVec (x+σ • g))*s.pi (A.mulVec (x+σ • g)) f*s.theta (A.mulVec (x+σ • g))^K) := by
        rw [sum_selector_first_weight (K := K) s _ (fun f => |faceDot (selectorFaceNormal A f) g|)]
      _ = (vectorNormSq g-(r:ℝ))*(∑ j : Fin s.faces.card,
          |faceDot (selectorFaceNormal A (activeFaceIndex s j)) g| *
          logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g)*
          logisticFaceWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g) j*
          (1-logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g))^K) := by
        rw [sum_activeFace_first_weight_physical]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [activeFaceNormals_eq_selectorFaceNormal]
        ring)

/-- Actual arbitrary-smoother cubic signed trace, derived from physical
concentration and the proved hard geometry/Gamma coarea estimates. -/
theorem intrinsicRectangleConcentration_cubicPhysicalTrace {p n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin (n+1)) ℝ) {C₀ δ κ σ : ℝ}
    (hC₀ : 0≤C₀) (hδ : 0≤δ) (hκ : 0≤κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (K : ℕ) :
    Integrable (supplementalHCubicPhysicalTrace s A σ K) ν ∧
    (∫ x, |supplementalHCubicPhysicalTrace s A σ K x| ∂ν) ≤
      (2:ℝ)^K*((32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C₀*κ*s.bandwidth*
        dimensionLog p*Real.sqrt (dimensionLog p)) := by
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
  have h := supplementalH_softCubicTrace_concentrated_base hp ν (selectorFaceNormal A) (activeFaceIndex s)
    (activeFaceOffsets s) (mul_nonneg hC₀ hκ) hδ hσ s.bandwidth_pos hu hb hδσ K
  have heU : (fun j => selectorFaceNormal A (activeFaceIndex s j))=activeFaceNormals s A := by
    funext j
    exact (activeFaceNormals_eq_selectorFaceNormal s A j).symm
  rw [heU] at h
  have he : supplementalHCubicPhysicalTrace s A σ K=
      supplementalHSoftCubicTrace (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth σ K := by
    funext x
    exact supplementalHCubicPhysicalTrace_eq_softTrace s A σ K x
  rw [he]
  refine ⟨h.1,?_⟩
  exact h.2.trans_eq (by ring)

end
end RectangleCLTArxivV1
