import RectangleCLTCompanion.FourthIdentityPath

/-! Product-law formulations of the two fresh rows in the exact fourth-order
identity. These identify the moment contractions with actual independent
copies, not with a formal tensor whose probabilistic realization is assumed. -/

open MeasureTheory
open scoped BigOperators Interval

set_option maxHeartbeats 1000000

namespace RectangleCLT.Companion

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] {p : ℕ}

theorem integral_fresh_pair_tensor2
    (f g : Ω → Fin p → Fin p → ℝ)
    (hf : ∀ j k, Integrable (fun ω => f ω j k) μ)
    (hg : ∀ j k, Integrable (fun ω => g ω j k) μ) :
    (∑ j, ∑ k, (∫ ω, f ω j k ∂μ) * (∫ ω, g ω j k ∂μ)) =
      ∫ z, ∑ j, ∑ k, f z.1 j k * g z.2 j k ∂μ.prod μ := by
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _
    (fun k _ => (hf j k).mul_prod (hg j k)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum _ (fun k _ => (hf j k).mul_prod (hg j k))]
  apply Finset.sum_congr rfl
  intro k _
  exact (integral_prod_mul (fun ω => f ω j k) (fun ω => g ω j k)).symm

theorem integral_fresh_pair_tensor3
    (f g : Ω → Fin p → Fin p → Fin p → ℝ)
    (hf : ∀ j k l, Integrable (fun ω => f ω j k l) μ)
    (hg : ∀ j k l, Integrable (fun ω => g ω j k l) μ) :
    (∑ j, ∑ k, ∑ l, (∫ ω, f ω j k l ∂μ) * (∫ ω, g ω j k l ∂μ)) =
      ∫ z, ∑ j, ∑ k, ∑ l, f z.1 j k l * g z.2 j k l ∂μ.prod μ := by
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _
    (fun k _ => integrable_finset_sum _ (fun l _ => (hf j k l).mul_prod (hg j k l))))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _
    (fun l _ => (hf j k l).mul_prod (hg j k l)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finset_sum _ (fun l _ => (hf j k l).mul_prod (hg j k l))]
  apply Finset.sum_congr rfl
  intro l _
  exact (integral_prod_mul (fun ω => f ω j k l) (fun ω => g ω j k l)).symm

end
end RectangleCLT.Companion

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

/-- The multilinear contraction of the actual fourth convolution derivative. -/
def convolutionFourthTensor (x u v w z : Vector p) : ℝ :=
  ∑ j, ∑ k, ∑ l, ∑ m,
    s.convolutionFourthDerivative ν x j k l m * u j * v k * w l * z m

theorem integrable_secondFourthKernel
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) {a : ℝ} (ha : a ≠ 0)
    (j k : Fin p) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..1, (1 - r) *
      (∑ l, ∑ m, s.convolutionFourthDerivative ν
        (line x (ξ ω) (a * r)) j k l m * ξ ω l * ξ ω m)) μ := by
  let K := fun ω => ∫ r in (0 : ℝ)..1, (1 - r) *
    (∑ l, ∑ m, s.convolutionFourthDerivative ν
      (line x (ξ ω) (a * r)) j k l m * ξ ω l * ξ ω m)
  have hline : Measurable (fun ω => x + a • ξ ω) :=
    measurable_const.add (measurable_const.smul hξ)
  have hiA := integrable_bounded_test_comp μ _ hline _
    (s.continuous_convolutionSecondDerivative ν j k) _
    (fun z => s.norm_convolutionSecondDerivative_le ν z j k)
  have hiξ (l : Fin p) : Integrable (fun ω => ξ ω l) μ := by
    simpa only [Fin.prod_univ_one] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (fun _ : Fin 1 => l)
  have hiL : Integrable (fun ω => a * ∑ l, s.convolutionThirdDerivative ν x j k l * ξ ω l) μ :=
    (integrable_finset_sum _ (fun l _ => (hiξ l).const_mul _)).const_mul a
  have hiAK : Integrable (fun ω => a ^ 2 * K ω) μ := by
    convert hiA.sub ((integrable_const (s.convolutionSecondDerivative ν x j k)).add hiL) using 1
    ext ω
    dsimp only [Pi.sub_apply, Pi.add_apply]
    rw [s.convolutionSecondDerivative_integral_remainder,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp [K]
    ring
  convert hiAK.const_mul ((a ^ 2)⁻¹) using 1
  ext ω
  dsimp only
  field_simp [ha]
  rfl

theorem integrable_thirdFourthKernel
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) (x : Vector p) {a : ℝ} (ha : a ≠ 0)
    (j k l : Fin p) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..1,
      (∑ m, s.convolutionFourthDerivative ν
        (line x (ξ ω) (a * r)) j k l m * ξ ω m)) μ := by
  let K := fun ω => ∫ r in (0 : ℝ)..1,
    (∑ m, s.convolutionFourthDerivative ν
      (line x (ξ ω) (a * r)) j k l m * ξ ω m)
  have hline : Measurable (fun ω => x + a • ξ ω) :=
    measurable_const.add (measurable_const.smul hξ)
  have hiA := integrable_bounded_test_comp μ _ hline _
    (s.continuous_convolutionThirdDerivative_commonPoint ν j k l) _
    (fun z => s.norm_convolutionThirdDerivative_le ν z j k l)
  have hiAK : Integrable (fun ω => a * K ω) μ := by
    convert hiA.sub (integrable_const (s.convolutionThirdDerivative ν x j k l)) using 1
    ext ω
    dsimp only [Pi.sub_apply]
    rw [s.convolutionThirdDerivative_integral_increment,
      intervalIntegral.integral_const_mul]
  convert hiAK.const_mul a⁻¹ using 1
  ext ω
  dsimp only
  field_simp [ha]
  rfl

end
end RectangleCLT.FaceSmoother
