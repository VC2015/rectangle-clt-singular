import RectangleCLTCompanion.SplitV4.Smoothing
import RectangleCLTCompanion.SplitV4.ClockCutoff
import RectangleCLTCompanion.SubexponentialTransfer
import RectangleCLT.ExponentialMixture

/-!
# Gaussian-endpoint smoothing for an arbitrary observation law

The exact exponential mixture represents each logistic expectation as an
average of sharp rectangle probabilities. On a clock cutoff event, enlarged
and contracted thresholds sandwich the original box. Gaussian concentration
controls the probability change there; the full rectangle distance controls
the complement and is absorbed only after integration. No moment or boundedness
condition is imposed on the observation law.
-/

open MeasureTheory Set

namespace RectangleCLT.Companion.SplitV4

noncomputable section

private theorem full_face_inside_eq_box {p : ℕ} (s : FaceSmoother p)
    (hs : s.faces = Finset.univ) :
    {x | s.Inside x} = (Rect.closedBox (fun j => -s.offsets (j, false))
      (fun j => s.offsets (j, true))).carrier := by
  ext x
  simp only [FaceSmoother.Inside, FaceSmoother.faceScore, hs, Finset.mem_univ,
    forall_true_left, Rect.closedBox, Rect.carrier, mem_pi, mem_univ, mem_Icc]
  constructor
  · intro hx j
    have hl := hx (j, false)
    have hu := hx (j, true)
    simp only [FaceSmoother.normalDot, Bool.false_eq_true, ↓reduceIte] at hl hu
    constructor <;> linarith
  · intro hx f
    rcases f with ⟨j, b⟩
    have hj := hx j
    cases b <;> simp only [FaceSmoother.normalDot, Bool.false_eq_true, ↓reduceIte] <;>
      linarith [hj.1, hj.2]

private def randomBoxGap {p : ℕ} (ν : Measure (Vector p))
    (A : Matrix (Fin p) (Fin p) ℝ) (s : FaceSmoother p)
    (e : ℝ × (Face p → ℝ)) : ℝ :=
  ν.real {x | (s.randomRectangle e).Inside x} -
    (gaussianLaw A).real {x | (s.randomRectangle e).Inside x}

private theorem integrable_randomBoxGap {p : ℕ} (ν : Measure (Vector p))
    [IsProbabilityMeasure ν] (A : Matrix (Fin p) (Fin p) ℝ) (s : FaceSmoother p) :
    Integrable (randomBoxGap ν A s) (exponentialRectangleLaw p) :=
  (s.integrable_randomRectangle_probability ν).sub
    (s.integrable_randomRectangle_probability (gaussianLaw A))

private theorem integral_randomBoxGap {p : ℕ} (ν : Measure (Vector p))
    [IsProbabilityMeasure ν] (A : Matrix (Fin p) (Fin p) ℝ) (s : FaceSmoother p) :
    (∫ e, randomBoxGap ν A s e ∂exponentialRectangleLaw p) =
      (∫ x, s.F x ∂ν) - (∫ x, s.F x ∂gaussianLaw A) := by
  unfold randomBoxGap
  rw [integral_sub (s.integrable_randomRectangle_probability ν)
    (s.integrable_randomRectangle_probability (gaussianLaw A)),
    ← s.integral_F_eq_randomRectangle_average ν,
    ← s.integral_F_eq_randomRectangle_average (gaussianLaw A)]

private theorem randomBoxGap_abs_le_distance {p : ℕ} (ν : Measure (Vector p))
    [IsProbabilityMeasure ν] (A : Matrix (Fin p) (Fin p) ℝ)
    (s : FaceSmoother p) (hs : s.faces = Finset.univ) (e : ℝ × (Face p → ℝ)) :
    |randomBoxGap ν A s e| ≤ rectangleDistance ν id A := by
  let t := s.randomRectangle e
  have ht : t.faces = Finset.univ := hs
  have hi := full_face_inside_eq_box t ht
  unfold randomBoxGap
  change |ν.real {x | t.Inside x} - (gaussianLaw A).real {x | t.Inside x}| ≤ _
  rw [hi]
  simpa only [rectangleError, Set.preimage_id] using
    rectangleError_le_rectangleDistance ν id A
      (Rect.closedBox (fun j => -t.offsets (j, false)) (fun j => t.offsets (j, true)))

private def shiftedSmoother {p : ℕ} (lo hi : Vector p) (t h : ℝ) (hh : 0 < h) :
    FaceSmoother p :=
  FaceSmoother.closedBox (fun j => lo j - t) (fun j => hi j + t) h hh

private theorem random_shifted_inside_iff {p : ℕ} (lo hi : Vector p)
    (t h : ℝ) (hh : 0 < h) (e : ℝ × (Face p → ℝ)) (x : Vector p) :
    ((shiftedSmoother lo hi t h hh).randomRectangle e).Inside x ↔
      ∀ j, lo j - t - h * Real.log (e.2 (j, false) / e.1) ≤ x j ∧
        x j ≤ hi j + t + h * Real.log (e.2 (j, true) / e.1) := by
  simp only [FaceSmoother.Inside, FaceSmoother.faceScore, FaceSmoother.randomRectangle,
    shiftedSmoother, FaceSmoother.closedBox, Finset.mem_univ, forall_true_left]
  constructor
  · intro hx j
    have hl := hx (j, false)
    have hu := hx (j, true)
    simp only [FaceSmoother.normalDot, Bool.false_eq_true, ↓reduceIte] at hl hu
    constructor <;> linarith
  · intro hx f
    rcases f with ⟨j, b⟩
    have hj := hx j
    cases b <;> simp only [FaceSmoother.normalDot, Bool.false_eq_true, ↓reduceIte] <;>
      linarith [hj.1, hj.2]

private theorem random_shifted_sandwich {p : ℕ} (lo hi : Vector p)
    (t h : ℝ) (hh : 0 < h) (d : ℝ) (e : ℝ × (Face p → ℝ))
    (he : ∀ f, |h * Real.log (e.2 f / e.1)| ≤ d) :
    (shiftedBox lo hi (t - d)).carrier ⊆
        {x | ((shiftedSmoother lo hi t h hh).randomRectangle e).Inside x} ∧
      {x | ((shiftedSmoother lo hi t h hh).randomRectangle e).Inside x} ⊆
        (shiftedBox lo hi (t + d)).carrier := by
  constructor
  · intro x hx
    apply (random_shifted_inside_iff lo hi t h hh e x).mpr
    intro j
    have hj := (mem_shiftedBox lo hi (t - d) x).mp hx j
    have hl := abs_le.mp (he (j, false))
    have hu := abs_le.mp (he (j, true))
    constructor <;> linarith [hj.1, hj.2, hl.1, hl.2, hu.1, hu.2]
  · intro x hx
    apply (mem_shiftedBox lo hi (t + d) x).mpr
    intro j
    have hj := (random_shifted_inside_iff lo hi t h hh e x).mp hx j
    have hl := abs_le.mp (he (j, false))
    have hu := abs_le.mp (he (j, true))
    constructor <;> linarith [hj.1, hj.2, hl.1, hl.2, hu.1, hu.2]

/-- A cutoff costs its actual probability times the global discrepancy.
This elementary integration step is used in both threshold directions. -/
private theorem integrate_good_event_bound
    {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (good : Set E) (hgood : MeasurableSet good)
    (f : E → ℝ) (hf : Integrable f ν) (a rho err : ℝ)
    (ha : |a| ≤ rho) (hfall : ∀ e, |f e| ≤ rho) (herr : 0 ≤ err)
    (hpoint : ∀ e ∈ good, a ≤ f e + err) :
    a ≤ (∫ e, f e ∂ν) + err + 2 * rho * ν.real goodᶜ := by
  have hI : Integrable (goodᶜ.indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_const _).indicator hgood.compl
  have h : ∀ e, a ≤ f e + err +
      2 * rho * goodᶜ.indicator (fun _ => (1 : ℝ)) e := by
    intro e
    by_cases he : e ∈ good
    · simp only [Set.indicator_of_not_mem (show e ∉ goodᶜ from not_not.mpr he), mul_zero, add_zero]
      exact hpoint e he
    · rw [Set.indicator_of_mem (show e ∈ goodᶜ from he), mul_one]
      linarith [(abs_le.mp ha).2, (abs_le.mp (hfall e)).1]
  have hi := integral_mono (integrable_const a)
    ((hf.add (integrable_const err)).add (hI.const_mul (2 * rho))) h
  simp only [Pi.add_apply] at hi
  rw [integral_add (f := fun e => f e + err)
      (g := fun e => 2 * rho * goodᶜ.indicator (fun _ => (1 : ℝ)) e)
      (hf.add (integrable_const err)) (hI.const_mul (2 * rho)),
    integral_add (f := f) (g := fun _ => err) hf (integrable_const err), integral_const_mul,
    integral_indicator_const (1 : ℝ) hgood.compl] at hi
  simpa using hi

private theorem gaussian_endpoint_cutoff_smoothing {p : ℕ} (hp : 1 ≤ p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (h : ℝ) (hh : 0 < h) (d : ℝ) (hd : 0 < d)
    (good : Set (ℝ × (Face p → ℝ))) (hgood : MeasurableSet good)
    (hshift : ∀ e ∈ good, ∀ f, |h * Real.log (e.2 f / e.1)| ≤ d)
    (hbad : (exponentialRectangleLaw p).real goodᶜ ≤ 1 / 4) :
    rectangleDistance ν id A ≤
      2 * smoothingDiscrepancy ν id A h hh +
        4 * (12 * Real.exp (3 / 2 : ℝ)) * d * Real.sqrt (dimensionLog p) := by
  let rho := rectangleDistance ν id A
  let M := smoothingDiscrepancy ν id A h hh
  let err := (12 * Real.exp (3 / 2 : ℝ)) * (2 * d) * Real.sqrt (dimensionLog p)
  have hrho : 0 ≤ rho := rectangleDistance_nonneg ν id A
  have herr : 0 ≤ err := by dsimp [err]; positivity
  have hbadcost : 2 * rho * (exponentialRectangleLaw p).real goodᶜ ≤ rho / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hbad (show 0 ≤ 2 * rho by positivity)]
  have hboxes (lo hi : Vector p) :
      rectangleError ν id A (Rect.closedBox lo hi) ≤ M + err + rho / 2 := by
    let base := ν.real (Rect.closedBox lo hi).carrier -
      (gaussianLaw A).real (Rect.closedBox lo hi).carrier
    let sp := shiftedSmoother lo hi d h hh
    let sm := shiftedSmoother lo hi (-d) h hh
    have hbase : |base| ≤ rho := by
      simpa only [base, rho, rectangleError, Set.preimage_id] using
        rectangleError_le_rectangleDistance ν id A (Rect.closedBox lo hi)
    have hplus : ∀ e, |randomBoxGap ν A sp e| ≤ rho :=
      randomBoxGap_abs_le_distance ν A sp rfl
    have hminus : ∀ e, |-randomBoxGap ν A sm e| ≤ rho := by
      intro e
      simpa only [abs_neg] using randomBoxGap_abs_le_distance ν A sm rfl e
    have hplusgood : ∀ e ∈ good, base ≤ randomBoxGap ν A sp e + err := by
      intro e he
      have hs := random_shifted_sandwich lo hi d h hh d e (hshift e he)
      have hμ : ν.real (Rect.closedBox lo hi).carrier ≤
          ν.real {x | (sp.randomRectangle e).Inside x} := by
        exact measureReal_mono (by simpa only [sub_self, shiftedBox_zero] using hs.1)
      have hG : (gaussianLaw A).real {x | (sp.randomRectangle e).Inside x} ≤
          (gaussianLaw A).real (shiftedBox lo hi (2 * d)).carrier := by
        exact measureReal_mono (by convert hs.2 using 1 <;> ring)
      have hconc := gaussian_probability_shiftedBox_le hp A hdiag lo hi
        (show 0 < 2 * d by positivity)
      change base ≤ randomBoxGap ν A sp e + err
      dsimp only [base, randomBoxGap, err]
      linarith
    have hminusgood : ∀ e ∈ good, -base ≤ -randomBoxGap ν A sm e + err := by
      intro e he
      have hs := random_shifted_sandwich lo hi (-d) h hh d e (hshift e he)
      have hμ : ν.real {x | (sm.randomRectangle e).Inside x} ≤
          ν.real (Rect.closedBox lo hi).carrier := by
        exact measureReal_mono (by simpa only [neg_add_cancel, shiftedBox_zero] using hs.2)
      have hG : (gaussianLaw A).real (shiftedBox lo hi (-(2 * d))).carrier ≤
          (gaussianLaw A).real {x | (sm.randomRectangle e).Inside x} := by
        exact measureReal_mono (by convert hs.1 using 1 <;> ring)
      have hconc := gaussian_probability_le_contractedBox_add hp A hdiag lo hi
        (show 0 < 2 * d by positivity)
      dsimp only [base, randomBoxGap, err]
      linarith
    have hmeanplus : |∫ e, randomBoxGap ν A sp e ∂exponentialRectangleLaw p| ≤ M := by
      rw [integral_randomBoxGap]
      exact closedBoxSmoothingGap_le_smoothingDiscrepancy ν id measurable_id A h hh
        ((fun j => lo j - d), (fun j => hi j + d))
    have hmeanminus : |∫ e, -randomBoxGap ν A sm e ∂exponentialRectangleLaw p| ≤ M := by
      rw [integral_neg, abs_neg, integral_randomBoxGap]
      exact closedBoxSmoothingGap_le_smoothingDiscrepancy ν id measurable_id A h hh
        ((fun j => lo j - -d), (fun j => hi j + -d))
    have hpbound := integrate_good_event_bound (exponentialRectangleLaw p) good hgood
      (randomBoxGap ν A sp) (integrable_randomBoxGap ν A sp) base rho err
      hbase hplus herr hplusgood
    have hmbound := integrate_good_event_bound (exponentialRectangleLaw p) good hgood
      (fun e => -randomBoxGap ν A sm e) (integrable_randomBoxGap ν A sm).neg (-base) rho err
      (by simpa only [abs_neg] using hbase) hminus herr hminusgood
    have hp' : base ≤ M + err + rho / 2 :=
      hpbound.trans (add_le_add
        (add_le_add_right ((le_abs_self _).trans hmeanplus) err) hbadcost)
    have hm' : -base ≤ M + err + rho / 2 :=
      hmbound.trans (add_le_add
        (add_le_add_right ((le_abs_self _).trans hmeanminus) err) hbadcost)
    change |base| ≤ _
    exact abs_le.mpr ⟨by linarith only [hm'], hp'⟩
  have hall (R : Rect p) : rectangleError ν id A R ≤ M + err + rho / 2 :=
    rectangleError_le_of_closedBox hp ν id measurable_id A hboxes R
  have hsup := rectangleDistance_le ν id A hall
  change rho ≤ _ at hsup
  dsimp only [rho, M, err] at hsup ⊢
  linarith

/-- A single numerical constant works for all dimensions, all observation
laws, all positive bandwidths, and all singular Gaussian factors. -/
def gaussianSmoothingConstant : ℝ := 2 + 576 * Real.exp (3 / 2 : ℝ)

theorem gaussianSmoothingConstant_ge_two : 2 ≤ gaussianSmoothingConstant := by
  unfold gaussianSmoothingConstant
  linarith [Real.exp_pos (3 / 2 : ℝ)]

private theorem gaussianEndpointSmoothing_law {p : ℕ} (hp : 1 ≤ p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (h : ℝ) (hh : 0 < h) :
    rectangleDistance ν id A ≤ gaussianSmoothingConstant *
      (smoothingDiscrepancy ν id A h hh + h * Real.sqrt (dimensionLog p) * dimensionLog p) := by
  have hc := gaussian_endpoint_cutoff_smoothing hp ν A hdiag h hh
    (clockRadius p h) (clockRadius_pos hh) (clockGood p) (measurableSet_clockGood p)
    (fun e he f => clockGood_shift_abs_le hh he f) (clockGood_compl_probability_le p)
  have hM := smoothingDiscrepancy_nonneg ν id measurable_id A h hh
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hrate : 0 ≤ h * Real.sqrt (dimensionLog p) * dimensionLog p := by positivity
  have hcoeff : 0 ≤ 4 * (12 * Real.exp (3 / 2 : ℝ)) * Real.sqrt (dimensionLog p) :=
    by positivity
  have hbudget := mul_le_mul_of_nonneg_left (clockRadius_le hp hh) hcoeff
  have herr : 4 * (12 * Real.exp (3 / 2 : ℝ)) * clockRadius p h * Real.sqrt (dimensionLog p) ≤
      (576 * Real.exp (3 / 2 : ℝ)) * (h * Real.sqrt (dimensionLog p) * dimensionLog p) := by
    convert hbudget using 1 <;> ring
  have hfirst := mul_le_mul_of_nonneg_right gaussianSmoothingConstant_ge_two hM
  have hsecond : (576 * Real.exp (3 / 2 : ℝ)) *
      (h * Real.sqrt (dimensionLog p) * dimensionLog p) ≤
        gaussianSmoothingConstant * (h * Real.sqrt (dimensionLog p) * dimensionLog p) := by
    apply mul_le_mul_of_nonneg_right _ hrate
    unfold gaussianSmoothingConstant
    linarith
  calc
    _ ≤ 2 * smoothingDiscrepancy ν id A h hh +
        (576 * Real.exp (3 / 2 : ℝ)) *
          (h * Real.sqrt (dimensionLog p) * dimensionLog p) := hc.trans (add_le_add_left herr _)
    _ ≤ gaussianSmoothingConstant * smoothingDiscrepancy ν id A h hh +
        gaussianSmoothingConstant * (h * Real.sqrt (dimensionLog p) * dimensionLog p) :=
      add_le_add hfirst hsecond
    _ = _ := by ring

/-- Lemma G.2 for any measurable random vector. The smooth discrepancy and
rectangle distance are their actual suprema. Only the Gaussian endpoint has
unit marginal variance; no covariance rank or observation moment hypothesis
is imposed. -/
theorem gaussianEndpointSmoothing
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (h : ℝ) (hh : 0 < h) :
    rectangleDistance μ V A ≤ gaussianSmoothingConstant *
      (smoothingDiscrepancy μ V A h hh + h * Real.sqrt (dimensionLog p) * dimensionLog p) := by
  let ν := μ.map V
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hV.aemeasurable
  have herr (R : Rect p) : rectangleError ν id A R = rectangleError μ V A R := by
    simp only [rectangleError, ν, Set.preimage_id, Measure.real,
      Measure.map_apply hV R.measurableSet_carrier]
  have hrho : rectangleDistance ν id A = rectangleDistance μ V A := by
    have hf : rectangleError ν id A = rectangleError μ V A := funext herr
    unfold rectangleDistance
    rw [hf]
  have hgap : closedBoxSmoothingGap ν id A h hh = closedBoxSmoothingGap μ V A h hh := by
    funext bounds
    let s := FaceSmoother.closedBox bounds.1 bounds.2 h hh
    change |(∫ x, s.F x ∂ν) - (∫ x, s.F x ∂gaussianLaw A)| =
      |(∫ ω, s.F (V ω) ∂μ) - (∫ x, s.F x ∂gaussianLaw A)|
    rw [show (∫ x, s.F x ∂ν) = ∫ ω, s.F (V ω) ∂μ from
      integral_map hV.aemeasurable s.continuous_F.aestronglyMeasurable]
  have hM : smoothingDiscrepancy ν id A h hh = smoothingDiscrepancy μ V A h hh := by
    unfold smoothingDiscrepancy
    rw [hgap]
  simpa only [hrho, hM] using gaussianEndpointSmoothing_law hp ν A hdiag h hh

/-- The pointwise full-rectangle consequence of the same Gaussian-endpoint
smoothing theorem, including atomic and mixed rectangle boundaries. -/
theorem rectangleError_le_gaussianEndpointSmoothing
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (h : ℝ) (hh : 0 < h) (R : Rect p) :
    rectangleError μ V A R ≤ gaussianSmoothingConstant *
      (smoothingDiscrepancy μ V A h hh + h * Real.sqrt (dimensionLog p) * dimensionLog p) :=
  (rectangleError_le_rectangleDistance μ V A R).trans
    (gaussianEndpointSmoothing hp μ V hV A hdiag h hh)

end
end RectangleCLT.Companion.SplitV4
