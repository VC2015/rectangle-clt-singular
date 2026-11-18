import RectangleCLTArxivV1.SupplementalGArrayDecomposition
import RectangleCLTArxivV1.HFourthCubicTrace

/-! The exact single/pair fourth-tensor identity in the product-integral
order used by Appendix H's conditional restoration bounds. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem hFourth_sum_pair_tuples {p : ℕ} (F : (Fin 2 → Face p) → ℝ) :
    (∑ α, F α)=∑ f : Face p, ∑ g : Face p, F ![f,g] := by
  rw [sum_face_tuples_cons]
  simp_rw [hFourth_sum_singleton_tuples]
  rfl

theorem hFourth_gaussian_outer_sum_eq_product
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Fin n → ι → Ω × Vector r → ℝ)
    (hF : ∀ i a, Integrable (F i a) (μ.prod (standardGaussian r))) :
    (∑ a, ∫ g, ∫ ω, ∑ i, F i a (ω,g) ∂μ ∂standardGaussian r)=
      ∫ z : Ω × Vector r, ∑ i, ∑ a, F i a z ∂μ.prod (standardGaussian r) := by
  classical
  have he (z : Ω × Vector r) : (∑ i, ∑ a, F i a z)=∑ a, ∑ i, F i a z := Finset.sum_comm
  simp_rw [he]
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun i _ => hF i a))]
  exact Finset.sum_congr rfl (fun a _ => (integral_prod_symm _ (integrable_finset_sum _ (fun i _ => hF i a))).symm)

/-- Two actual Stein integrations and the cancellation-preserving Hessian
decomposition, with every Gaussian/Fubini exchange justified by moments. -/
theorem hFourth_expectation_eq_single_pair_products
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ j, (A*A.transpose) j j=1)
    (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (Y W v : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i))
    (hW : ∀ i, Measurable (W i)) (hv : ∀ i, Measurable (v i))
    {δ σ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hσ : σ ≠ 0) :
    restorationFourthExpectation s μ A V Z Y W v σ=
      -(1/(s.bandwidth*σ^3))*(∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
        ((normalDot f (Y i z.1)*normalDot f (W i z.1))*
          capThirdHermiteScore (capRectangularFactorNormal A f) (Z i z.1) z.2)*
            selectorTupleWeight s ![f] ((σ•A).mulVec z.2+V z.1+v i z.1) ∂μ.prod (standardGaussian r))+
      (1/(s.bandwidth^2*σ^2))*(∫ z : Ω × Vector r, ∑ i, ∑ α : Fin 2 → Face p,
        (capRectangularPairCoefficient A (α 0) (α 1) (Y i z.1) (W i z.1)*
          repeatedDirectionScore z.2 (Z i z.1))*
            selectorTupleWeight s α ((σ•A).mulVec z.2+V z.1+v i z.1) ∂μ.prod (standardGaussian r)) := by
  classical
  let P := fun i (f : Face p) (z : Ω × Vector r) =>
    ((normalDot f (Y i z.1)*normalDot f (W i z.1))*
      capThirdHermiteScore (capRectangularFactorNormal A f) (Z i z.1) z.2)*
        selectorTupleWeight s ![f] ((σ•A).mulVec z.2+V z.1+v i z.1)
  let Q := fun i (α : Fin 2 → Face p) (z : Ω × Vector r) =>
    (capRectangularPairCoefficient A (α 0) (α 1) (Y i z.1) (W i z.1)*
      repeatedDirectionScore z.2 (Z i z.1))*
        selectorTupleWeight s α ((σ•A).mulVec z.2+V z.1+v i z.1)
  have hpoint (i : Fin n) : Measurable (fun z : Ω × Vector r => (σ•A).mulVec z.2+V z.1+v i z.1) :=
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst)).add ((hv i).comp measurable_fst)
  have hCm (i : Fin n) (f : Face p) : Measurable (fun ω => normalDot f (Y i ω)*normalDot f (W i ω)) :=
    ((continuous_normalDot f).measurable.comp (hY i)).mul ((continuous_normalDot f).measurable.comp (hW i))
  have hCb (i : Fin n) (f : Face p) : ∀ᵐ ω ∂μ, |normalDot f (Y i ω)*normalDot f (W i ω)| ≤ δ^2 := by
    filter_upwards [hYb i,hWb i] with ω hy hw
    rw [abs_mul]
    exact (mul_le_mul (abs_normalDot_le_of_norm_le f hy) (abs_normalDot_le_of_norm_le f hw)
      (abs_nonneg _) hδ).trans_eq (by ring)
  have hBm (i : Fin n) (α : Fin 2 → Face p) :
      Measurable (fun ω => capRectangularPairCoefficient A (α 0) (α 1) (Y i ω) (W i ω)) := by
    unfold capRectangularPairCoefficient normalDot
    split <;> split <;> fun_prop
  have hBb (i : Fin n) (α : Fin 2 → Face p) : ∀ᵐ ω ∂μ,
      |capRectangularPairCoefficient A (α 0) (α 1) (Y i ω) (W i ω)| ≤ 4*δ^2 := by
    filter_upwards [hYb i,hWb i] with ω hy hw
    exact cap_original_pair_coefficient_abs_le A hdiag _ _ _ _ hδ hy hw
  have hPi (i : Fin n) (f : Face p) : Integrable (P i f) (μ.prod (standardGaussian r)) := by
    simpa only [P,mul_assoc] using cap_integrable_bounded_coefficient_score μ (standardGaussian r) _ _
      (integrable_random_capThirdHermiteScore μ _ (Z i) (hZ i))
      (measurable_selectorTupleWeight_comp s ![f] _ (hpoint i))
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _)
      _ (hCm i f) (hCb i f)
  have hQi (i : Fin n) (α : Fin 2 → Face p) : Integrable (Q i α) (μ.prod (standardGaussian r)) := by
    simpa only [Q,mul_assoc] using cap_integrable_bounded_coefficient_score μ (standardGaussian r) _ _
      (integrable_random_repeatedDirectionScore μ (Z i) (hZ i))
      (measurable_selectorTupleWeight_comp s α _ (hpoint i))
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _)
      _ (hBm i α) (hBb i α)
  rw [cap_array_fourth_expectation_single_pair s μ A hdiag V hV Z hZm hZ Y W v hY hW hv hδ hYb hWb hσ]
  have hp := hFourth_gaussian_outer_sum_eq_product μ P hPi
  have hq := hFourth_gaussian_outer_sum_eq_product μ Q hQi
  rw [hFourth_sum_pair_tuples] at hq
  simpa only [P,Q,Matrix.cons_val_zero,Matrix.cons_val_one] using congrArg₂
    (fun a b : ℝ => -(1/(s.bandwidth*σ^3))*a+(1/(s.bandwidth^2*σ^2))*b) hp hq

end
end RectangleCLTArxivV1
