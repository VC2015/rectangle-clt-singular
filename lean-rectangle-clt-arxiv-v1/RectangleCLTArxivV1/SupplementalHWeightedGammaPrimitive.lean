import RectangleCLTArxivV1.SupplementalHMixedCoareaIntegral
import RectangleCLTArxivV1.SupplementalHGammaSignedFace

/-! Actual Gamma hard-threshold representation for any genuine
integrable Gaussian test, used by the positive pair moment estimates. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section

theorem measurable_gaussianFiniteWeightedThreshold {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (P : Vector r → ℝ) (hP : Measurable P) :
    Measurable (fun b => gaussianFiniteWeightedThreshold s u b P) := by
  let E := {z : Vector m × Vector r | ∀ j∈s,faceDot (u j) z.2≤z.1 j}
  have hE : MeasurableSet E := by
    unfold E
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le ((continuous_faceDot_left _).measurable.comp measurable_snd)
      ((measurable_pi_apply j).comp measurable_fst)
  exact (((hP.comp measurable_snd).indicator hE).stronglyMeasurable.integral_prod_right').measurable

theorem abs_gaussianFiniteWeightedThreshold_le {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (P : Vector r → ℝ)
    (hP : Integrable P (standardGaussian r)) :
    |gaussianFiniteWeightedThreshold s u b P|≤∫ g,|P g| ∂standardGaussian r := by
  have hi := hP.indicator (measurableSet_gaussianFiniteThresholdEvent s u b)
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono_ae hi.abs hP.abs
  exact ae_of_all _ (fun g => by
    by_cases hg : g∈gaussianFiniteThresholdEvent s u b <;> simp [hg])

/-- The actual integrable test is retained through genuine Gamma/Gaussian
Fubini; the auxiliary threshold law and every original inequality are
those of the existing logistic mixture. -/
theorem weighted_logistic_power_eq_gamma_weighted_threshold {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector r) (q : ℕ) (P : Vector r → ℝ) (hP : Integrable P (standardGaussian r)) :
    (∫ g,P g*logisticNullWeight u a h (x+σ • g)^(q+1) ∂standardGaussian r)=
      ∫ e,gaussianFiniteWeightedThreshold Finset.univ u
        (fun j => (gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ) P ∂gammaRectangleLaw m q := by
  have hg := gammaMixture_integral_signed_test (standardGaussian r)
    (fun g => Matrix.mulVec u (x+σ • g)) (by fun_prop) P hP (upperFaceSmoother a h hh) q
  simp_rw [upperFaceSmoother_F] at hg
  rw [hg]
  apply integral_congr_ae
  exact ae_of_all _ (fun e => by
    dsimp only
    unfold gaussianFiniteWeightedThreshold
    have he : {g | ((upperFaceSmoother a h hh).randomRectangle e).Inside
        (Matrix.mulVec u (x+σ • g))}=gaussianFiniteThresholdEvent Finset.univ u
          (fun j => (gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ) := by
      ext g
      rw [mem_setOf_eq,upper_randomRectangle_inside_iff]
      constructor
      · intro h j hj
        have hh := h j
        rw [threshold_faceDot_add_right,threshold_faceDot_smul_right] at hh
        exact (le_div_iff₀ hσ).mpr (by nlinarith)
      · intro h j
        have hh := (le_div_iff₀ hσ).mp (h j (Finset.mem_univ _))
        rw [threshold_faceDot_add_right,threshold_faceDot_smul_right]
        nlinarith
    rw [he])

end
end RectangleCLTArxivV1
