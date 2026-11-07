import RectangleCLTCompanion.SplitV4.ModerateInverseTilt
import RectangleCLTCompanion.SplitV4.GenericProductTilt

/-! Exact bridges between the nonidentical marginal cumulants and their product model. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section
variable {n : ℕ}

theorem moderateProduct_coordinate_identDistrib (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (i : Fin n) :
    IdentDistrib (fun z : Fin n → ℝ => z i) id (Measure.pi ν) (ν i) :=
  ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
    by rw [lowerScalarPi_map_eval ν i, Measure.map_id]⟩

theorem moderateProduct_coordinate_bound (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (i : Fin n) :
    ∀ᵐ z ∂Measure.pi ν, |z i| ≤ δ := by
  have hh := hbound i
  rw [← lowerScalarPi_map_eval ν i] at hh
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (measurableSet_le measurable_id.abs measurable_const)).mp hh

theorem moderateProduct_coordinate_integral (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ z : Fin n → ℝ, f (z i) ∂Measure.pi ν) = ∫ x, f x ∂ν i := by
  simpa only [Function.comp_apply, id_eq] using
    ((moderateProduct_coordinate_identDistrib ν i).comp hf).integral_eq

theorem moderateProduct_coordinate_cgf (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (i : Fin n) :
    cgf (fun z : Fin n → ℝ => z i) (Measure.pi ν) = cgf id (ν i) := by
  funext t
  unfold cgf
  congr 1
  exact congrFun (mgf_congr_identDistrib (moderateProduct_coordinate_identDistrib ν i)) t

theorem moderateProduct_mean_eq (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) :
    moderateArrayMean (Measure.pi ν) (fun i z => z i) t = ∑ i, genericTiltMean (ν i) t := by
  apply Finset.sum_congr rfl
  intro i _
  rw [moderateTiltMean_eq_deriv (measurable_pi_apply i) (moderateProduct_coordinate_bound ν hbound i),
    moderateProduct_coordinate_cgf]
  rfl

theorem moderateProduct_variance_eq (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) :
    moderateArrayVariance (Measure.pi ν) (fun i z => z i) t = genericTiltTotalVariance ν t := by
  apply Finset.sum_congr rfl
  intro i _
  rw [moderateTiltVariance_eq_iteratedDeriv (measurable_pi_apply i) (moderateProduct_coordinate_bound ν hbound i),
    moderateProduct_coordinate_cgf]
  rfl

theorem moderateProduct_cgf_eq (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (t : ℝ) :
    moderateArrayCGF (Measure.pi ν) (fun i z => z i) t = ∑ i, cgf id (ν i) t := by
  simp only [moderateArrayCGF, moderateProduct_coordinate_cgf]

end
end RectangleCLT.Companion.SplitV4
