import RectangleCLTArxivV1.PositiveGammaPairSum
import RectangleCLTArxivV1.SupplementalHPairPhysicalTrace
import RectangleCLTArxivV1.SupplementalHPairExtraFactors

/-! Exact original-smoother active-face coordinates for the positive
pair baselines. The additional tuple factors were reduced separately. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem supplementalHPairMass_baseline_eq_native {p r : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (x : Vector r) :
    (∑ α : Fin 2 → Face p, supplementalHPairTupleAngle A α*
      supplementalHPairTupleMass s (σ • A) (fun x => A.mulVec x) α x)=
    positiveGammaSoftOrderedPairMass (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth σ x := by
  classical
  unfold supplementalHPairTupleMass
  simp_rw [←integral_const_mul]
  rw [←integral_finset_sum _ (fun α _ =>
    (selectorWeight_affine_moments s α (σ • A) (A.mulVec x)).1.const_mul _)]
  unfold positiveGammaSoftOrderedPairMass
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have he : (σ • A).mulVec g+A.mulVec x=A.mulVec (x+σ • g) := by
      rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.smul_mulVec_assoc]
      exact add_comm _ _
    dsimp only
    rw [he]
    have hsum := sum_selector_first_pair_weight (K := 0) s (A.mulVec (x+σ • g))
      (fun f l => correlationAngleWeight (faceDot (selectorFaceNormal A f) (selectorFaceNormal A l)))
    simp only [Nat.zero_add,pow_zero,mul_one] at hsum
    change (∑ α : Fin 2 → Face p, correlationAngleWeight
      (faceDot (selectorFaceNormal A (α 0)) (selectorFaceNormal A (α 1)))*
        selectorWeight s α (A.mulVec (x+σ • g)))=_
    rw [hsum]
    have ha := sum_activeFace_pair_weight_physical s A (x+σ • g)
      (fun f l => correlationAngleWeight (faceDot (selectorFaceNormal A f) (selectorFaceNormal A l))) 0
    simp only [pow_zero,mul_one] at ha
    rw [ha]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    rw [activeFaceNormals_eq_selectorFaceNormal s A j,activeFaceNormals_eq_selectorFaceNormal s A l]
    ring)

theorem integrable_gaussian_pair_projection_selector {p r K : ℕ}
    (s : FaceSmoother p) (M A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : Fin (K+2) → Face p) :
    Integrable (fun g => selectorWeight s α (M.mulVec g+v)*
      vectorNormSq ((supplementalHPairPlane (selectorFaceNormal A (α 0))
        (selectorFaceNormal A (α 1))).mulVec g)) (standardGaussian r) := by
  let P := supplementalHPairPlane (selectorFaceNormal A (α 0)) (selectorFaceNormal A (α 1))
  have hm : Measurable (fun g : Vector r => vectorNormSq (P.mulVec g)) := by
    unfold vectorNormSq Matrix.mulVec dotProduct
    fun_prop
  apply (supplementalH_gaussian_projection_normSq_integrable P).mono'
    ((continuous_selectorWeight_affine s α M v).measurable.mul hm).aestronglyMeasurable
  exact ae_of_all _ (fun g => by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (selectorWeight_nonneg s α _) (vectorNormSq_nonneg _))]
    exact mul_le_of_le_one_left (vectorNormSq_nonneg _) (selectorWeight_le_one s α _))

theorem supplementalHPairProjection_baseline_eq_native {p r : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (x : Vector r) :
    (∑ α : Fin 2 → Face p, supplementalHPairTupleProjection s (σ • A) A (fun x => A.mulVec x) α x)=
    positiveGammaSoftOrderedPairProjection (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth σ x := by
  classical
  unfold supplementalHPairTupleProjection
  simp_rw [←integral_const_mul]
  rw [←integral_finset_sum _ (fun α _ =>
    (integrable_gaussian_pair_projection_selector s (σ • A) A (A.mulVec x) α).const_mul _)]
  unfold positiveGammaSoftOrderedPairProjection
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have he : (σ • A).mulVec g+A.mulVec x=A.mulVec (x+σ • g) := by
      rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.smul_mulVec_assoc]
      exact add_comm _ _
    dsimp only
    rw [he]
    let c := fun f l => correlationAngleWeight (faceDot (selectorFaceNormal A f) (selectorFaceNormal A l))*
      vectorNormSq ((supplementalHPairPlane (selectorFaceNormal A f) (selectorFaceNormal A l)).mulVec g)
    calc
      _ = ∑ α : Fin 2 → Face p, c (α 0) (α 1)*selectorWeight s α (A.mulVec (x+σ • g)) := by
        apply Finset.sum_congr rfl
        intro α _
        dsimp only [c,supplementalHPairTupleAngle]
        ring
      _ = ∑ f : Face p, ∑ l : Face p, c f l*s.F (A.mulVec (x+σ • g))*s.pi (A.mulVec (x+σ • g)) f*
          s.pi (A.mulVec (x+σ • g)) l := by
        simpa only [Nat.zero_add,pow_zero,mul_one] using sum_selector_first_pair_weight (K := 0) s _ c
      _ = ∑ j : Fin s.faces.card, ∑ l : Fin s.faces.card, c (activeFaceIndex s j) (activeFaceIndex s l)*
          logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g)*
          logisticFaceWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g) j*
          logisticFaceWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth (x+σ • g) l := by
        simpa only [pow_zero,mul_one] using sum_activeFace_pair_weight_physical s A (x+σ • g) c 0
      _ = _ := by
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        rw [activeFaceNormals_eq_selectorFaceNormal s A j,activeFaceNormals_eq_selectorFaceNormal s A l]
        dsimp only [c]
        ring)

end
end RectangleCLTArxivV1
