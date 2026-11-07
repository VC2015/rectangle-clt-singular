import RectangleCLTCompanion.SplitV4.Printed.EndpointLemma2
import RectangleCLTCompanion.SplitV4.Printed.ClockMarkov
import RectangleCLTCompanion.SubexponentialTransfer

/-! The printed Gaussian-endpoint route: Markov on the actual expected
clock width, variable d+R error, average, and absorb the global distance. -/
open MeasureTheory Set
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem full_face_inside_eq_box {p : ℕ} (s : FaceSmoother p)
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

def randomBoxGap {p : ℕ} (ν : Measure (Vector p))
    (A : Matrix (Fin p) (Fin p) ℝ) (s : FaceSmoother p)
    (e : ℝ × (Face p → ℝ)) : ℝ :=
  ν.real {x | (s.randomRectangle e).Inside x} -
    (gaussianLaw A).real {x | (s.randomRectangle e).Inside x}

theorem integrable_randomBoxGap {p : ℕ} (ν : Measure (Vector p))
    [IsProbabilityMeasure ν] (A : Matrix (Fin p) (Fin p) ℝ) (s : FaceSmoother p) :
    Integrable (randomBoxGap ν A s) (exponentialRectangleLaw p) :=
  (s.integrable_randomRectangle_probability ν).sub
    (s.integrable_randomRectangle_probability (gaussianLaw A))

theorem integral_randomBoxGap {p : ℕ} (ν : Measure (Vector p))
    [IsProbabilityMeasure ν] (A : Matrix (Fin p) (Fin p) ℝ) (s : FaceSmoother p) :
    (∫ e, randomBoxGap ν A s e ∂exponentialRectangleLaw p) =
      (∫ x, s.F x ∂ν) - (∫ x, s.F x ∂gaussianLaw A) := by
  unfold randomBoxGap
  rw [integral_sub (s.integrable_randomRectangle_probability ν)
    (s.integrable_randomRectangle_probability (gaussianLaw A)),
    ← s.integral_F_eq_randomRectangle_average ν,
    ← s.integral_F_eq_randomRectangle_average (gaussianLaw A)]

theorem randomBoxGap_abs_le_distance {p : ℕ} (ν : Measure (Vector p))
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

def shiftedSmoother {p : ℕ} (lo hi : Vector p) (t h : ℝ) (hh : 0 < h) :
    FaceSmoother p :=
  FaceSmoother.closedBox (fun j => lo j - t) (fun j => hi j + t) h hh

theorem random_shifted_inside_iff {p : ℕ} (lo hi : Vector p)
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

theorem random_shifted_sandwich {p : ℕ} (lo hi : Vector p)
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


/-- The Gaussian part of the actual Lemma 1 controls expansions and
contractions at their exact deterministic radius. -/
theorem gaussian_shifted_probability_bounds {p : ℕ} (hp : 1≤p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀j,(A*A.transpose) j j=1)
    (lo hi : Vector p) {r : ℝ} (hr : 0≤r) :
    (gaussianLaw A).real (shiftedBox lo hi r).carrier ≤
      (gaussianLaw A).real (Rect.closedBox lo hi).carrier+512*r*Real.sqrt (dimensionLog p) ∧
    (gaussianLaw A).real (Rect.closedBox lo hi).carrier ≤
      (gaussianLaw A).real (shiftedBox lo hi (-r)).carrier+512*r*Real.sqrt (dimensionLog p) := by
  let s := FaceSmoother.closedBox lo hi 1 (by norm_num)
  have hs : {x | s.Inside x}=(Rect.closedBox lo hi).carrier := by
    ext x; exact FaceSmoother.closedBox_Inside lo hi 1 (by norm_num) x
  have ho : (shiftedBox lo hi r).carrier=s.outerSet r := shiftedBox_eq_outerSet lo hi r
  have hn : (shiftedBox lo hi (-r)).carrier=s.outerSet (-r) := shiftedBox_eq_outerSet lo hi (-r)
  have hc := gaussian_boundary_layer_le hp A hdiag s rfl hr
  have hleft : s.outerSet r ⊆ {x | s.Inside x} ∪ s.boundaryLayer r := by
    intro x hx
    by_cases hi : s.Inside x
    · exact Or.inl hi
    · exact Or.inr ⟨hx,fun hh => hi (inner_subset_inside s hr hh)⟩
  have hright : {x | s.Inside x} ⊆ s.outerSet (-r) ∪ s.boundaryLayer r := by
    intro x hx
    by_cases hi : x∈s.outerSet (-r)
    · exact Or.inl hi
    · exact Or.inr ⟨inside_subset_outer s hr hx,hi⟩
  constructor
  · rw [ho,←hs]
    exact ((measureReal_mono (μ:=gaussianLaw A) hleft).trans (measureReal_union_le _ _)).trans (add_le_add_left hc _)
  · rw [hn,←hs]
    exact ((measureReal_mono (μ:=gaussianLaw A) hright).trans (measureReal_union_le _ _)).trans (add_le_add_left hc _)

/-- Variable-error averaging retains the expected random width. -/
theorem integrate_good_event_variable_bound
    {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (good : Set E) (hgood : MeasurableSet good)
    (f err : E→ℝ) (hf : Integrable f ν) (he : Integrable err ν) (a rho : ℝ)
    (ha : |a|≤rho) (hfall : ∀e,|f e|≤rho) (herr : ∀e,0≤err e)
    (hpoint : ∀e∈good,a≤f e+err e) :
    a≤(∫e,f e ∂ν)+(∫e,err e ∂ν)+2*rho*ν.real goodᶜ := by
  have hI : Integrable (goodᶜ.indicator (fun _ => (1:ℝ))) ν := (integrable_const _).indicator hgood.compl
  have h (e) : a≤f e+err e+2*rho*goodᶜ.indicator (fun _ => (1:ℝ)) e := by
    by_cases hx : e∈good
    · simpa only [Set.indicator_of_not_mem (show e∉goodᶜ from not_not.mpr hx),mul_zero,add_zero] using hpoint e hx
    · rw [Set.indicator_of_mem (show e∈goodᶜ from hx),mul_one]
      linarith [(abs_le.mp ha).2,(abs_le.mp (hfall e)).1,herr e]
  have hi := integral_mono (integrable_const a) ((hf.add he).add (hI.const_mul (2*rho))) h
  simp only [Pi.add_apply] at hi
  rw [integral_add (f:=fun e => f e+err e)
      (g:=fun e => 2*rho*goodᶜ.indicator (fun _ => (1:ℝ)) e)
      (hf.add he) (hI.const_mul (2*rho)),integral_add hf he,integral_const_mul,
    integral_indicator_const (1:ℝ) hgood.compl] at hi
  simpa using hi

/-- G.2 with the actual expected clock width still visible. The good event
is defined by that width, and its quarter-probability bound is Markov. -/
theorem gaussian_endpoint_expected_width {p : ℕ} (hp : 1≤p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀j,(A*A.transpose) j j=1)
    (h : ℝ) (hh : 0<h) :
    rectangleDistance ν id A ≤ 2*smoothingDiscrepancy ν id A h hh+
      1024*(expectedClockCutoff p h+
        ∫e,randomThresholdRadius p h e ∂exponentialRectangleLaw p)*Real.sqrt (dimensionLog p) := by
  let rho := rectangleDistance ν id A
  let D := smoothingDiscrepancy ν id A h hh
  let d := expectedClockCutoff p h
  let good := {e | randomThresholdRadius p h e≤d}
  let err := fun e => 512*(d+randomThresholdRadius p h e)*Real.sqrt (dimensionLog p)
  have hd : 0<d := expectedClockCutoff_pos hp hh
  have hg : MeasurableSet good := measurableSet_le (measurable_randomThresholdRadius p h) measurable_const
  have hrho : 0≤rho := rectangleDistance_nonneg ν id A
  have hbad : (exponentialRectangleLaw p).real goodᶜ≤1/4 := by
    have he : goodᶜ={e | d<randomThresholdRadius p h e} := by ext e; simp only [good,mem_compl_iff,mem_setOf_eq,not_le]
    rw [he]; exact expectedClockCutoff_bad_le hp hh
  have hbadcost : 2*rho*(exponentialRectangleLaw p).real goodᶜ≤rho/2 := by
    nlinarith [mul_le_mul_of_nonneg_left hbad (show 0≤2*rho by positivity)]
  have hR := integrable_randomThresholdRadius hp h
  have herrI : Integrable err (exponentialRectangleLaw p) :=
    (((integrable_const d).add hR).const_mul 512).mul_const _
  have herr (e) : 0≤err e := by
    have hRn := randomThresholdRadius_nonneg hh.le e
    dsimp only [err]; positivity
  have hmeanerr : (∫e,err e ∂exponentialRectangleLaw p)=
      512*(d+∫e,randomThresholdRadius p h e ∂exponentialRectangleLaw p)*Real.sqrt (dimensionLog p) := by
    change (∫e,512*(d+randomThresholdRadius p h e)*Real.sqrt (dimensionLog p) ∂exponentialRectangleLaw p)=_
    rw [integral_mul_const,integral_const_mul,integral_add (integrable_const d) hR]
    simp
  have hboxes (lo hi : Vector p) : rectangleError ν id A (Rect.closedBox lo hi)≤
      D+(∫e,err e ∂exponentialRectangleLaw p)+rho/2 := by
    let base := ν.real (Rect.closedBox lo hi).carrier-(gaussianLaw A).real (Rect.closedBox lo hi).carrier
    let sp := shiftedSmoother lo hi d h hh
    let sm := shiftedSmoother lo hi (-d) h hh
    have hb : |base|≤rho := by
      simpa only [base,rho,rectangleError,Set.preimage_id] using rectangleError_le_rectangleDistance ν id A (Rect.closedBox lo hi)
    have hfplus : ∀e,|randomBoxGap ν A sp e|≤rho := randomBoxGap_abs_le_distance ν A sp rfl
    have hfminus : ∀e,|-randomBoxGap ν A sm e|≤rho := by
      intro e; simpa only [abs_neg] using randomBoxGap_abs_le_distance ν A sm rfl e
    have hpGood : ∀e∈good,base≤randomBoxGap ν A sp e+err e := by
      intro e he
      have hRe : randomThresholdRadius p h e≤d := he
      have hRn : 0≤randomThresholdRadius p h e := randomThresholdRadius_nonneg hh.le e
      have hs := random_shifted_sandwich lo hi d h hh (randomThresholdRadius p h e) e
        (fun f => randomThresholdRadius_shift_le hh.le e f)
      have hsub : (Rect.closedBox lo hi).carrier ⊆ {x | (sp.randomRectangle e).Inside x} := by
        have hm := shiftedBox_mono lo hi (show 0≤d-randomThresholdRadius p h e by linarith)
        have hm' : (Rect.closedBox lo hi).carrier ⊆ (shiftedBox lo hi (d-randomThresholdRadius p h e)).carrier := by
          simpa only [shiftedBox_zero] using hm
        exact hm'.trans hs.1
      have hμ := measureReal_mono (μ:=ν) hsub
      have hG := measureReal_mono (μ:=gaussianLaw A) hs.2
      have hc := (gaussian_shifted_probability_bounds hp A hdiag lo hi (add_nonneg hd.le hRn)).1
      dsimp only [base,randomBoxGap,err]
      linarith
    have hmGood : ∀e∈good,-base≤-randomBoxGap ν A sm e+err e := by
      intro e he
      have hRe : randomThresholdRadius p h e≤d := he
      have hRn : 0≤randomThresholdRadius p h e := randomThresholdRadius_nonneg hh.le e
      have hs := random_shifted_sandwich lo hi (-d) h hh (randomThresholdRadius p h e) e
        (fun f => randomThresholdRadius_shift_le hh.le e f)
      have hsub : {x | (sm.randomRectangle e).Inside x} ⊆ (Rect.closedBox lo hi).carrier := by
        have hm := shiftedBox_mono lo hi (show -d+randomThresholdRadius p h e≤0 by linarith)
        exact hs.2.trans (by simpa only [shiftedBox_zero] using hm)
      have hμ := measureReal_mono (μ:=ν) hsub
      have hG : (gaussianLaw A).real (shiftedBox lo hi (-(d+randomThresholdRadius p h e))).carrier≤
          (gaussianLaw A).real {x | (sm.randomRectangle e).Inside x} := by
        have hh' : -(d+randomThresholdRadius p h e) = -d-randomThresholdRadius p h e := by ring
        rw [hh']
        exact measureReal_mono hs.1
      have hc := (gaussian_shifted_probability_bounds hp A hdiag lo hi (add_nonneg hd.le hRn)).2
      dsimp only [base,randomBoxGap,err]
      linarith
    have hpMean : |∫e,randomBoxGap ν A sp e ∂exponentialRectangleLaw p|≤D := by
      rw [integral_randomBoxGap]
      exact closedBoxSmoothingGap_le_smoothingDiscrepancy ν id measurable_id A h hh
        ((fun j => lo j-d),(fun j => hi j+d))
    have hmMean : |∫e,-randomBoxGap ν A sm e ∂exponentialRectangleLaw p|≤D := by
      rw [integral_neg,abs_neg,integral_randomBoxGap]
      exact closedBoxSmoothingGap_le_smoothingDiscrepancy ν id measurable_id A h hh
        ((fun j => lo j- -d),(fun j => hi j+ -d))
    have hpInt := integrate_good_event_variable_bound (exponentialRectangleLaw p) good hg
      (randomBoxGap ν A sp) err (integrable_randomBoxGap ν A sp) herrI base rho hb hfplus herr hpGood
    have hmInt := integrate_good_event_variable_bound (exponentialRectangleLaw p) good hg
      (fun e => -randomBoxGap ν A sm e) err (integrable_randomBoxGap ν A sm).neg herrI (-base) rho
      (by simpa only [abs_neg] using hb) hfminus herr hmGood
    have hp' : base≤D+(∫e,err e ∂exponentialRectangleLaw p)+rho/2 :=
      hpInt.trans (add_le_add
        (add_le_add_right ((le_abs_self _).trans hpMean) _) hbadcost)
    have hm' : -base≤D+(∫e,err e ∂exponentialRectangleLaw p)+rho/2 :=
      hmInt.trans (add_le_add
        (add_le_add_right ((le_abs_self _).trans hmMean) _) hbadcost)
    change |base|≤_
    apply abs_le.mpr
    constructor
    · linarith only [hm']
    · exact hp'
  have hall (R : Rect p) : rectangleError ν id A R≤D+(∫e,err e ∂exponentialRectangleLaw p)+rho/2 :=
    rectangleError_le_of_closedBox hp ν id measurable_id A hboxes R
  have hsup := rectangleDistance_le ν id A hall
  change rho≤_ at hsup
  rw [hmeanerr] at hsup
  change rho≤2*D+1024*(d+∫e,randomThresholdRadius p h e ∂exponentialRectangleLaw p)*Real.sqrt (dimensionLog p)
  linarith

/-- The literal G.2 route, after applying the already-proved expected-width
bound to its final averaged error. -/
theorem gaussianEndpointSmoothing_printed_law {p : ℕ} (hp : 1≤p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀j,(A*A.transpose) j j=1)
    (h : ℝ) (hh : 0<h) :
    rectangleDistance ν id A ≤ 2*smoothingDiscrepancy ν id A h hh+
      20480*h*Real.sqrt (dimensionLog p)*dimensionLog p := by
  have he := gaussian_endpoint_expected_width hp ν A hdiag h hh
  have hw := mul_le_mul_of_nonneg_right (expectedClockCutoff_add_mean_le hp hh.le)
    (Real.sqrt_nonneg (dimensionLog p))
  nlinarith

/-- The full printed G.2 conclusion for any measurable observation vector. -/
theorem gaussianEndpointSmoothing_printed
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (h : ℝ) (hh : 0 < h) :
    rectangleDistance μ V A ≤ 2*smoothingDiscrepancy μ V A h hh+
      20480*h*Real.sqrt (dimensionLog p)*dimensionLog p := by
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
  simpa only [hrho, hM] using gaussianEndpointSmoothing_printed_law hp ν A hdiag h hh


end
end RectangleCLT.Companion.SplitV4.Printed
