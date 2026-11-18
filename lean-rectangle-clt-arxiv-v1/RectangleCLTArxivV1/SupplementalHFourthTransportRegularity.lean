import RectangleCLTArxivV1.SupplementalHFourthTransportThreeFace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Generic threshold lists remain regular for almost every arbitrary
sampled base after the actual invertible affine standardization. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem residualThresholdRegularity_isOpen {m r : ℕ}
    (u : Fin m → Vector r) (j : Fin m) : IsOpen {b | ResidualThresholdRegularity u b j} := by
  exact (localFiniteThresholdRegularity_isOpen (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l))).preimage (by fun_prop)

theorem measurableSet_all_residualThresholdRegularity {m r : ℕ} (u : Fin m → Vector r) :
    MeasurableSet {b | ∀ j,ResidualThresholdRegularity u b j} := by
  simp only [setOf_forall]
  exact MeasurableSet.iInter (fun j => (residualThresholdRegularity_isOpen u j).measurableSet)

theorem ae_affine_residualThresholdRegularity {m r : ℕ} (u : Fin m → Vector r)
    (x : Vector r) {σ : ℝ} (hσ : σ≠0) :
    ∀ᵐ a : Vector m ∂volume,∀ j,ResidualThresholdRegularity u
      (fun k => (a k-faceDot (u k) x)/σ) j := by
  have hs : Measure.QuasiMeasurePreserving (fun a : Vector m => σ⁻¹ • a) volume volume :=
    Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hσ)
  have ht : Measure.QuasiMeasurePreserving (fun a : Vector m => a+ -(fun k => faceDot (u k) x)) volume volume :=
    MeasureTheory.quasiMeasurePreserving_add_right volume _
  have hh := (hs.comp ht).ae (ae_residualThresholdRegularity u)
  filter_upwards [hh] with a ha
  have he : (fun k => (a k-faceDot (u k) x)/σ)=σ⁻¹ • (a+ -(fun k => faceDot (u k) x)) := by
    funext k
    simp only [Pi.smul_apply,Pi.add_apply,Pi.neg_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  rw [he]
  exact ha

/-- No absolute continuity is needed for the base law. The exceptional
threshold set is null before and after averaging that arbitrary base. -/
theorem ae_threshold_ae_base_residualThresholdRegularity {m r : ℕ}
    (ν : Measure (Vector r)) [SFinite ν] (u : Fin m → Vector r) {σ : ℝ} (hσ : σ≠0) :
    ∀ᵐ a : Vector m ∂volume,∀ᵐ x ∂ν,∀ j,ResidualThresholdRegularity u
      (fun k => (a k-faceDot (u k) x)/σ) j := by
  have hc : Continuous (fun z : Vector m × Vector r => fun k => (z.1 k-faceDot (u k) z.2)/σ) := by
    apply continuous_pi
    intro k
    have hfst : Continuous (fun z : Vector m × Vector r => z.1 k) :=
      (continuous_apply k).comp continuous_fst
    have hsnd : Continuous (fun z : Vector m × Vector r => faceDot (u k) z.2) :=
      (continuous_faceDot_left (u k)).comp continuous_snd
    exact (hfst.sub hsnd).div_const σ
  have hm := (measurableSet_all_residualThresholdRegularity u).preimage hc.measurable
  have hm' : MeasurableSet {z : Vector m × Vector r | ∀ j,ResidualThresholdRegularity u
      (fun k => (z.1 k-faceDot (u k) z.2)/σ) j} := hm
  exact (Measure.ae_ae_comm hm').mpr (ae_of_all _ (fun x => ae_affine_residualThresholdRegularity u x hσ))

end
end RectangleCLTArxivV1
