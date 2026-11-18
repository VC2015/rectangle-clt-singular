import RectangleCLTArxivV1.SupplementalHPairAveragingKernels

/-! Extra pair-selector labels cost no positive mass or projected moment.
Only the first two original labels are distinguished. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem supplementalH_pair_kernel_extra_factors {p r K : ℕ}
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (c : Face p → Face p → Vector r → ℝ)
    (hcm : ∀ f g, Measurable (c f g)) (hc0 : ∀ f g z,0≤c f g z)
    (hci : ∀ f g,Integrable (c f g) (standardGaussian r)) :
    (∫ z, ∑ α : Fin (K+2) → Face p, c (α 0) (α 1) z*selectorWeight s α (M.mulVec z+v)
      ∂standardGaussian r) ≤
    ∫ z, ∑ α : Fin 2 → Face p, c (α 0) (α 1) z*selectorWeight s α (M.mulVec z+v)
      ∂standardGaussian r := by
  classical
  have hi (q : ℕ) (α : Fin (q+2) → Face p) : Integrable
      (fun z => c (α 0) (α 1) z*selectorWeight s α (M.mulVec z+v)) (standardGaussian r) := by
    apply (hci (α 0) (α 1)).mono' ((hcm _ _).mul (continuous_selectorWeight_affine s α M v).measurable).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hc0 _ _ _) (selectorWeight_nonneg s α _))]
      exact mul_le_of_le_one_right (hc0 _ _ _) (selectorWeight_le_one s α _))
  apply integral_mono (integrable_finset_sum _ (fun α _ => hi K α))
    (integrable_finset_sum _ (fun α _ => hi 0 α))
  intro z
  have hz := sum_selector_first_pair_weight_le (K := K) s (M.mulVec z+v) (fun f g => c f g z) (fun f g => hc0 f g z)
  have he := sum_selector_first_pair_weight (K := 0) s (M.mulVec z+v) (fun f g => c f g z)
  simp only [Nat.zero_add,pow_zero,mul_one] at he
  exact hz.trans_eq he.symm

theorem supplementalH_gaussian_projection_normSq_integrable {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) : Integrable (fun g => vectorNormSq (P.mulVec g)) (standardGaussian r) := by
  have ht := integrable_finset_sum Finset.univ (fun j (_ : j∈Finset.univ) =>
    SignedSurface.standardGaussian_integrable_faceDot_sq (P j))
  simpa only [vectorNormSq,faceDot,Matrix.mulVec,dotProduct] using ht

theorem supplementalHPairTupleMass_extra_factors {p r K : ℕ}
    (s : FaceSmoother p) (M A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    (∑ α : Fin (K+2) → Face p, supplementalHPairTupleAngle A α*
      supplementalHPairTupleMass s M (fun _ : Unit => v) α ()) ≤
    ∑ α : Fin 2 → Face p, supplementalHPairTupleAngle A α*
      supplementalHPairTupleMass s M (fun _ : Unit => v) α () := by
  classical
  let c := fun f g (_ : Vector r) => correlationAngleWeight (faceDot (selectorFaceNormal A f) (selectorFaceNormal A g))
  have hc := supplementalH_pair_kernel_extra_factors (K := K) s M v c
    (fun _ _ => measurable_const) (fun _ _ _ => correlationAngleWeight_nonneg _) (fun _ _ => integrable_const _)
  have he (q : ℕ) : (∑ α : Fin (q+2) → Face p, supplementalHPairTupleAngle A α*
      supplementalHPairTupleMass s M (fun _ : Unit => v) α ()) =
      ∫ z, ∑ α : Fin (q+2) → Face p, c (α 0) (α 1) z*selectorWeight s α (M.mulVec z+v)
        ∂standardGaussian r := by
    rw [integral_finset_sum _ (fun α _ => (selectorWeight_affine_moments s α M v).1.const_mul _)]
    exact Finset.sum_congr rfl (fun α _ => (integral_const_mul _ _).symm)
  rw [he K,he 0]
  exact hc

theorem supplementalHPairTupleProjection_extra_factors {p r K : ℕ}
    (s : FaceSmoother p) (M A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    (∑ α : Fin (K+2) → Face p, supplementalHPairTupleProjection s M A (fun _ : Unit => v) α ()) ≤
    ∑ α : Fin 2 → Face p, supplementalHPairTupleProjection s M A (fun _ : Unit => v) α () := by
  classical
  let P := fun f g => supplementalHPairPlane (selectorFaceNormal A f) (selectorFaceNormal A g)
  let a := fun f g => correlationAngleWeight (faceDot (selectorFaceNormal A f) (selectorFaceNormal A g))
  let c := fun f g (z : Vector r) => a f g*vectorNormSq ((P f g).mulVec z)
  have hcm (f g) : Measurable (c f g) := by unfold c vectorNormSq Matrix.mulVec dotProduct; fun_prop
  have hc0 (f g) (z) : 0≤c f g z := mul_nonneg (correlationAngleWeight_nonneg _) (vectorNormSq_nonneg _)
  have hci (f g) : Integrable (c f g) (standardGaussian r) :=
    (supplementalH_gaussian_projection_normSq_integrable (P f g)).const_mul _
  have hi (q : ℕ) (α : Fin (q+2) → Face p) : Integrable
      (fun z => c (α 0) (α 1) z*selectorWeight s α (M.mulVec z+v)) (standardGaussian r) := by
    apply (hci (α 0) (α 1)).mono' ((hcm _ _).mul (continuous_selectorWeight_affine s α M v).measurable).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hc0 _ _ _) (selectorWeight_nonneg s α _))]
      exact mul_le_of_le_one_right (hc0 _ _ _) (selectorWeight_le_one s α _))
  have he (q : ℕ) : (∑ α : Fin (q+2) → Face p, supplementalHPairTupleProjection s M A (fun _ : Unit => v) α ()) =
      ∫ z, ∑ α : Fin (q+2) → Face p, c (α 0) (α 1) z*selectorWeight s α (M.mulVec z+v)
        ∂standardGaussian r := by
    rw [integral_finset_sum _ (fun α _ => hi q α)]
    apply Finset.sum_congr rfl
    intro α _
    dsimp only [supplementalHPairTupleProjection]
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by dsimp only [c,a,P,supplementalHPairTupleAngle]; ring)
  rw [he K,he 0]
  exact supplementalH_pair_kernel_extra_factors (K := K) s M v c hcm hc0 hci

end
end RectangleCLTArxivV1
