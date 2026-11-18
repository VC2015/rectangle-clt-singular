import RectangleCLTArxivV1.SupplementalHRidgeValueContinuity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Sequences

/-! Genuine extension of a parameter-AE uniform absolute expectation
bound to every point of almost-sure parameter continuity, by density and
Fatou. The sampled law is arbitrary and may be singular. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter Set RectangleCLT
open scoped Topology
noncomputable section

theorem integrable_abs_bound_of_ae_parameter_continuity {m : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (ν : Measure Ω) (J : Vector m → Ω → ℝ) (a : Vector m) {B : ℝ}
    (hgood : ∀ᵐ b : Vector m ∂volume, Integrable (J b) ν ∧ (∫ x,|J b x| ∂ν)≤B)
    (hcont : ∀ᵐ x ∂ν,ContinuousAt (fun b => J b x) a)
    (hJm : AEStronglyMeasurable (J a) ν) :
    Integrable (J a) ν ∧ (∫ x,|J a x| ∂ν)≤B := by
  have hd : Dense {b | Integrable (J b) ν ∧ (∫ x,|J b x| ∂ν)≤B} := volume.dense_of_ae hgood
  obtain ⟨b,hb,hlim⟩ := (mem_closure_iff_seq_limit.mp (hd a))
  have hB : 0≤B := (integral_nonneg (fun x => abs_nonneg (J (b 0) x))).trans (hb 0).2
  let F := fun k x => ENNReal.ofReal |J (b k) x|
  have hm (k : ℕ) : AEMeasurable (F k) ν := (hb k).1.abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have he : (fun x => ENNReal.ofReal |J a x|)=ᵐ[ν] fun x => liminf (fun k => F k x) atTop := by
    filter_upwards [hcont] with x hx
    have hh := (ENNReal.continuous_ofReal.tendsto |J a x|).comp ((hx.tendsto.comp hlim).abs)
    exact hh.liminf_eq.symm
  have hbound (k : ℕ) : (∫⁻ x,F k x ∂ν)≤ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hb k).1.abs (ae_of_all _ (fun x => abs_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hb k).2
  have hf : (∫⁻ x,ENNReal.ofReal |J a x| ∂ν)≤ENNReal.ofReal B :=
    (le_of_eq (lintegral_congr_ae he)).trans ((lintegral_liminf_le' hm).trans
      (liminf_le_of_frequently_le' (Frequently.of_forall hbound)))
  have hfi : HasFiniteIntegral (J a) ν := (hasFiniteIntegral_iff_norm _).mpr (by
    simpa only [Real.norm_eq_abs] using hf.trans_lt ENNReal.ofReal_lt_top)
  have hJi : Integrable (J a) ν := ⟨hJm,hfi⟩
  refine ⟨hJi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hJi.abs (ae_of_all _ (fun x => abs_nonneg _))] at hf
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hf

end
end RectangleCLTArxivV1
