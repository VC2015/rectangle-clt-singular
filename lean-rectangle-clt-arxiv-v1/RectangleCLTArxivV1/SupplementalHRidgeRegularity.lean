import RectangleCLTArxivV1.SupplementalHGenericPairGreen
import RectangleCLTArxivV1.SupplementalHTripleIncidenceMass
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Generic ridge regularity after arbitrary singular concentrated bases.
Exceptional affine thresholds are removed by genuine product Fubini. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def AllPairResidualThresholdRegularity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : Prop :=
  ∀ j l, LocalFiniteThresholdRegularity ((Finset.univ.erase j).erase l)
    (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
    (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l))

theorem allPairResidualThresholdRegularity_isOpen {m r : ℕ} (u : Fin m → Vector r) :
    IsOpen {b | AllPairResidualThresholdRegularity u b} := by
  simp only [AllPairResidualThresholdRegularity,Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro l
  apply (localFiniteThresholdRegularity_isOpen _ _).preimage
  unfold hardPairResidualLevels thresholdPairFirstLevel thresholdPairSecondLevel
  fun_prop

/-- Any volume-almost-every threshold property stays true after actual
invertible affine standardization and arbitrary independent base Fubini. -/
theorem ae_threshold_ae_base_affine_property {m r : ℕ}
    (ν : Measure (Vector r)) [SFinite ν] (u : Fin m → Vector r) {σ : ℝ} (hσ : σ≠0)
    (P : Vector m → Prop) (hP : MeasurableSet {b | P b}) (ha : ∀ᵐ b : Vector m ∂volume, P b) :
    ∀ᵐ a : Vector m ∂volume, ∀ᵐ x ∂ν, P (fun k => (a k-faceDot (u k) x)/σ) := by
  have hfixed (x : Vector r) : ∀ᵐ a : Vector m ∂volume, P (fun k => (a k-faceDot (u k) x)/σ) := by
    have hs : Measure.QuasiMeasurePreserving (fun a : Vector m => σ⁻¹ • a) volume volume :=
      Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hσ)
    have ht : Measure.QuasiMeasurePreserving (fun a : Vector m => a+ -(fun k => faceDot (u k) x)) volume volume :=
      MeasureTheory.quasiMeasurePreserving_add_right volume _
    have hh := (hs.comp ht).ae ha
    filter_upwards [hh] with a h
    have he : (fun k => (a k-faceDot (u k) x)/σ)=σ⁻¹ • (a+ -(fun k => faceDot (u k) x)) := by
      funext k
      simp only [Pi.smul_apply,Pi.add_apply,Pi.neg_apply,smul_eq_mul,div_eq_mul_inv]
      ring
    rwa [he]
  have hc : Continuous (fun z : Vector m × Vector r => fun k => (z.1 k-faceDot (u k) z.2)/σ) := by
    apply continuous_pi
    intro k
    have hfst : Continuous (fun z : Vector m × Vector r => z.1 k) :=
      (continuous_apply k).comp continuous_fst
    have hsnd : Continuous (fun z : Vector m × Vector r => faceDot (u k) z.2) :=
      (continuous_faceDot_left (u k)).comp continuous_snd
    exact (hfst.sub hsnd).div_const σ
  have hm := hP.preimage hc.measurable
  have hm' : MeasurableSet {z : Vector m × Vector r | P (fun k => (z.1 k-faceDot (u k) z.2)/σ)} := hm
  exact (Measure.ae_ae_comm hm').mpr (ae_of_all _ hfixed)

/-- The actual double-residual ridge condition holds for almost every
threshold and almost every arbitrary sampled base, with no base density. -/
theorem ae_threshold_ae_base_pairResidualThresholdRegularity {m r : ℕ}
    (ν : Measure (Vector r)) [SFinite ν] (u : Fin m → Vector r) {σ : ℝ} (hσ : σ≠0) :
    ∀ᵐ a : Vector m ∂volume, ∀ᵐ x ∂ν,
      AllPairResidualThresholdRegularity u (fun k => (a k-faceDot (u k) x)/σ) :=
  ae_threshold_ae_base_affine_property ν u hσ _ (allPairResidualThresholdRegularity_isOpen u).measurableSet
    (ae_pairResidualThresholdRegularity u)

theorem AllPairResidualThresholdRegularity.triple {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} (h : AllPairResidualThresholdRegularity u b)
    (F : Fin 3 → Fin m) : TripleIncidenceRegularity u b F := by
  intro i
  exact h (tripleIncidenceLeft F i) (tripleIncidenceRight F i)

end
end RectangleCLTArxivV1
