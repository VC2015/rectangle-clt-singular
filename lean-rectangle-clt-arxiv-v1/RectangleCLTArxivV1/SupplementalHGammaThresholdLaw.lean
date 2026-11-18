import RectangleCLTCompanion.SplitV4.LogisticGammaTrace
import Mathlib.MeasureTheory.Function.Jacobian

/-! Absolute continuity of the actual random threshold vector. The
base law itself may be singular; only auxiliary clocks are transported. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

theorem supplementalH_unitExponential_absolutelyContinuous : unitExponential ≪ volume := by
  unfold unitExponential expMeasure gammaMeasure
  exact withDensity_absolutelyContinuous _ _

theorem supplementalH_logExponential_absolutelyContinuous (o : ℝ) {h t : ℝ}
    (hh : 0<h) (ht : 0<t) :
    unitExponential.map (fun x : ℝ => o+h*Real.log (x/t)) ≪ volume := by
  let T := fun x : ℝ => o+h*Real.log (x/t)
  let S := fun y : ℝ => t*Real.exp ((y-o)/h)
  have hT : Measurable T := by unfold T; fun_prop
  have hS : Differentiable ℝ S := by unfold S; fun_prop
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hA0
  rw [Measure.map_apply hT hA]
  have himg : volume (S '' A)=0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hS.differentiableOn hA0
  have he : T ⁻¹' A =ᵐ[unitExponential] S '' A := by
    filter_upwards [unitExponential_ae_pos] with x hx
    change (T x∈A)=(x∈S '' A)
    apply propext
    constructor
    · intro hxA
      refine ⟨T x,hxA,?_⟩
      dsimp only [S,T]
      have hq : (o+h*Real.log (x/t)-o)/h=Real.log (x/t) := by field_simp
      rw [hq,Real.exp_log (div_pos hx ht)]
      field_simp
    · rintro ⟨y,hy,hxy⟩
      rw [←hxy]
      dsimp only [S,T]
      rw [mul_div_cancel_left₀ _ ht.ne',Real.log_exp]
      have hq : o+h*((y-o)/h)=y := by field_simp
      rwa [hq]
  rw [measure_congr he]
  exact supplementalH_unitExponential_absolutelyContinuous himg

/-- A finite product of absolutely continuous probability laws is
absolutely continuous for the actual Euclidean threshold volume. -/
theorem supplementalH_pi_absolutelyContinuous {m : ℕ}
    (μ : Fin m → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (hμ : ∀ j, μ j ≪ volume) : Measure.pi μ ≪ (volume : Measure (Vector m)) := by
  induction m with
  | zero =>
      rw [Measure.pi_of_empty,Measure.volume_pi_eq_dirac]
  | succ m ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
      have h1 := measurePreserving_piFinSuccAbove μ (0 : Fin (m+1))
      have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) (0 : Fin (m+1))
      have hp := (hμ 0).prod (ih (fun j => μ (Fin.succAbove 0 j)) (fun j => hμ _))
      have hb := hp.map e.symm.measurable
      have hb1 := (MeasurePreserving.symm e h1).map_eq
      have hb2 := (MeasurePreserving.symm e h2).map_eq
      rw [hb1,←Measure.volume_eq_prod,hb2] at hb
      exact hb

theorem supplementalH_faceExponential_true_projection (m : ℕ) :
    (faceExponentialLaw m).map (fun e : Face m → ℝ => fun j : Fin m => e (j,true)) =
      Measure.pi (fun _ : Fin m => unitExponential) := by
  classical
  have hm : Measurable (fun e : Face m → ℝ => fun j : Fin m => e (j,true)) := by fun_prop
  apply (Measure.pi_eq (fun S hS => ?_)).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hS)]
  have he : (fun e : Face m → ℝ => fun j : Fin m => e (j,true)) ⁻¹' (Set.univ.pi S) =
      Set.univ.pi (fun f : Face m => if f.2 then S f.1 else Set.univ) := by
    ext e
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies]
    constructor
    · intro h
      rintro ⟨j,c⟩
      cases c <;> simp [h]
    · intro h j
      exact h (j,true)
  rw [he,faceExponentialLaw,Measure.pi_pi]
  simp [Fintype.prod_prod_type]

/-- Conditional on each positive Gamma clock, the original actual
threshold vector has an absolutely continuous law in threshold space. -/
theorem supplementalH_conditionalGammaThreshold_absolutelyContinuous {m : ℕ}
    (a : Vector m) {h t : ℝ} (hh : 0<h) (ht : 0<t) :
    (faceExponentialLaw m).map (fun e => gammaAdjustedThreshold a h (t,e)) ≪ volume := by
  let T := fun (x : Vector m) j => a j+h*Real.log (x j/t)
  have hT : Measurable T := by unfold T; fun_prop
  have hproj : Measurable (fun e : Face m → ℝ => fun j : Fin m => e (j,true)) := by fun_prop
  have he : (fun e => gammaAdjustedThreshold a h (t,e))=
      T ∘ (fun e : Face m → ℝ => fun j : Fin m => e (j,true)) := rfl
  rw [he,←Measure.map_map hT hproj,supplementalH_faceExponential_true_projection]
  let η := fun j : Fin m => unitExponential.map (fun x : ℝ => a j+h*Real.log (x/t))
  have hm (j : Fin m) : Measurable (fun x : ℝ => a j+h*Real.log (x/t)) := by fun_prop
  letI (j : Fin m) : IsProbabilityMeasure (η j) := isProbabilityMeasure_map (hm j).aemeasurable
  have heq : (Measure.pi (fun _ : Fin m => unitExponential)).map T=Measure.pi η :=
    (measurePreserving_pi (fun _ => unitExponential) η (fun j => ⟨hm j,rfl⟩)).map_eq
  rw [heq]
  exact supplementalH_pi_absolutelyContinuous η (fun j =>
    supplementalH_logExponential_absolutelyContinuous (a j) hh ht)

/-- The auxiliary random thresholds are absolutely continuous even
though a separate physical base law need not be. -/
theorem supplementalH_gammaThreshold_absolutelyContinuous {m : ℕ}
    (a : Vector m) {h : ℝ} (hh : 0<h) (q : ℕ) :
    (gammaRectangleLaw m q).map (gammaAdjustedThreshold a h) ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hA0
  rw [Measure.map_apply (measurable_gammaAdjustedThreshold a h) hA,gammaRectangleLaw,
    Measure.prod_apply ((measurable_gammaAdjustedThreshold a h) hA)]
  apply (lintegral_congr_ae (g := fun _ : ℝ => (0 : ℝ≥0∞)) ?_).trans (by simp)
  filter_upwards [gammaClock_ae_pos q] with t ht
  have hc := supplementalH_conditionalGammaThreshold_absolutelyContinuous a hh ht
  change (faceExponentialLaw m) ((fun e => gammaAdjustedThreshold a h (t,e)) ⁻¹' A)=0
  rw [←Measure.map_apply (by fun_prop : Measurable (fun e => gammaAdjustedThreshold a h (t,e))) hA]
  exact hc hA0

end
end RectangleCLTArxivV1
