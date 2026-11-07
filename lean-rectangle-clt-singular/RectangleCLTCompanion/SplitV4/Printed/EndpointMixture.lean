import RectangleCLTCompanion.SplitV4.Printed.ClockMean
import RectangleCLTCompanion.SplitV4.Smoothing
import RectangleCLT.ExponentialMixture

/-! The literal random-threshold sandwich, indicator bound and Jensen
transition in the printed proof of Lemma 2. The concentration bound used
here is an explicit intermediate input, instantiated from Lemma 1 later. -/
open MeasureTheory Set
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem random_rectangle_sandwich {p : ℕ} (s : FaceSmoother p)
    (e : ℝ × (Face p → ℝ)) :
    s.outerSet (-randomThresholdRadius p s.bandwidth e) ⊆
        {x | (s.randomRectangle e).Inside x} ∧
      {x | (s.randomRectangle e).Inside x} ⊆
        s.outerSet (randomThresholdRadius p s.bandwidth e) := by
  constructor
  · intro x hx f hf
    have hxf := hx f hf
    have hs := abs_le.mp (randomThresholdRadius_shift_le s.bandwidth_pos.le e f)
    change FaceSmoother.normalDot f x-(s.offsets f+s.bandwidth*Real.log (e.2 f/e.1)) ≤ 0
    linarith [hs.1]
  · intro x hx f hf
    have hxf := hx f hf
    have hs := abs_le.mp (randomThresholdRadius_shift_le s.bandwidth_pos.le e f)
    change FaceSmoother.normalDot f x-(s.offsets f+s.bandwidth*Real.log (e.2 f/e.1)) ≤ 0 at hxf
    change FaceSmoother.normalDot f x ≤ s.offsets f+randomThresholdRadius p s.bandwidth e
    linarith [hs.2]

theorem inside_subset_outer {p : ℕ} (s : FaceSmoother p) {r : ℝ} (hr : 0 ≤ r) :
    {x | s.Inside x} ⊆ s.outerSet r := by
  intro x hx f hf
  have hh := hx f hf
  change FaceSmoother.normalDot f x-s.offsets f ≤ 0 at hh
  change FaceSmoother.normalDot f x ≤ s.offsets f+r
  linarith

theorem inner_subset_inside {p : ℕ} (s : FaceSmoother p) {r : ℝ} (hr : 0 ≤ r) :
    s.outerSet (-r) ⊆ {x | s.Inside x} := by
  intro x hx f hf
  have hh := hx f hf
  change FaceSmoother.normalDot f x ≤ s.offsets f+-r at hh
  change FaceSmoother.normalDot f x-s.offsets f ≤ 0
  linarith

theorem endpoint_symmDiff_subset_boundary {p : ℕ} (s : FaceSmoother p)
    (e : ℝ × (Face p → ℝ)) :
    {x | (s.Inside x ∧ ¬(s.randomRectangle e).Inside x) ∨
      ((s.randomRectangle e).Inside x ∧ ¬s.Inside x)} ⊆
        s.boundaryLayer (randomThresholdRadius p s.bandwidth e) := by
  intro x hx
  have hr : 0 ≤ randomThresholdRadius p s.bandwidth e :=
    mul_nonneg s.bandwidth_pos.le (clockLogMaximum_nonneg p e)
  rcases hx with hx | hx
  · exact ⟨inside_subset_outer s hr hx.1, fun hi => hx.2 ((random_rectangle_sandwich s e).1 hi)⟩
  · exact ⟨(random_rectangle_sandwich s e).2 hx.1, fun hi => hx.2 (inner_subset_inside s hr hi)⟩

theorem endpoint_indicator_bound {p : ℕ} (s : FaceSmoother p)
    (e : ℝ × (Face p → ℝ)) (x : Vector p) :
    |({y | s.Inside y}.indicator (fun _ => (1 : ℝ))) x-
      ({y | (s.randomRectangle e).Inside y}.indicator (fun _ => (1 : ℝ))) x| ≤
      (s.boundaryLayer (randomThresholdRadius p s.bandwidth e)).indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hS : s.Inside x <;> by_cases hR : (s.randomRectangle e).Inside x
  · simp [hS,hR,Set.indicator_nonneg (fun _ _ => zero_le_one) x]
  · have hb := endpoint_symmDiff_subset_boundary s e (Or.inl ⟨hS,hR⟩)
    simp [hS,hR,hb]
  · have hb := endpoint_symmDiff_subset_boundary s e (Or.inr ⟨hR,hS⟩)
    simp [hS,hR,hb]
  · simp [hS,hR,Set.indicator_nonneg (fun _ _ => zero_le_one) x]

theorem endpoint_probability_bound {p : ℕ} (s : FaceSmoother p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (e : ℝ × (Face p → ℝ)) :
    |ν.real {x | s.Inside x}-ν.real {x | (s.randomRectangle e).Inside x}| ≤
      ν.real (s.boundaryLayer (randomThresholdRadius p s.bandwidth e)) := by
  have hleft : {x | s.Inside x} ⊆ {x | (s.randomRectangle e).Inside x} ∪
      s.boundaryLayer (randomThresholdRadius p s.bandwidth e) := by
    intro x hx
    by_cases hR : (s.randomRectangle e).Inside x
    · exact Or.inl hR
    · exact Or.inr (endpoint_symmDiff_subset_boundary s e (Or.inl ⟨hx,hR⟩))
  have hright : {x | (s.randomRectangle e).Inside x} ⊆ {x | s.Inside x} ∪
      s.boundaryLayer (randomThresholdRadius p s.bandwidth e) := by
    intro x hx
    by_cases hS : s.Inside x
    · exact Or.inl hS
    · exact Or.inr (endpoint_symmDiff_subset_boundary s e (Or.inr ⟨hx,hS⟩))
  have hl := (measureReal_mono (μ := ν) hleft).trans (measureReal_union_le _ _)
  have hr := (measureReal_mono (μ := ν) hright).trans (measureReal_union_le _ _)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The printed Jensen/averaging transition: genuine concentration at every
deterministic radius is integrated at the actual random radius. -/
theorem endpoint_error_le_average_radius {p : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (C δ L : ℝ)
    (hLayer : ∀ r, 0 ≤ r → ν.real (s.boundaryLayer r) ≤ C*(r+δ)*Real.sqrt L) :
    |ν.real {x | s.Inside x}-(∫ x, s.F x ∂ν)| ≤
      C*((∫ e, randomThresholdRadius p s.bandwidth e ∂exponentialRectangleLaw p)+δ)*Real.sqrt L := by
  let a := ν.real {x | s.Inside x}
  let g := fun e => ν.real {x | (s.randomRectangle e).Inside x}
  have hg : Integrable g (exponentialRectangleLaw p) := s.integrable_randomRectangle_probability ν
  have hi : Integrable (fun e => a-g e) (exponentialRectangleLaw p) := (integrable_const a).sub hg
  have hmean : a-(∫ x, s.F x ∂ν) = ∫ e, a-g e ∂exponentialRectangleLaw p := by
    rw [integral_sub (integrable_const a) hg]
    simp only [integral_const,measureReal_univ_eq_one,one_smul]
    rw [s.integral_F_eq_randomRectangle_average ν]
  have hR := integrable_randomThresholdRadius hp s.bandwidth
  have hM : Integrable (fun e => C*(randomThresholdRadius p s.bandwidth e+δ)*Real.sqrt L)
      (exponentialRectangleLaw p) := ((hR.add (integrable_const δ)).const_mul C).mul_const _
  have hpoint (e : ℝ × (Face p → ℝ)) :
      |a-g e| ≤ C*(randomThresholdRadius p s.bandwidth e+δ)*Real.sqrt L :=
    (endpoint_probability_bound s ν e).trans (hLayer _ (mul_nonneg s.bandwidth_pos.le (clockLogMaximum_nonneg p e)))
  have hJ := norm_integral_le_integral_norm (μ := exponentialRectangleLaw p) (fun e => a-g e)
  simp only [Real.norm_eq_abs] at hJ
  change |a-(∫ x, s.F x ∂ν)| ≤ _
  rw [hmean]
  apply hJ.trans
  apply (integral_mono hi.abs hM hpoint).trans_eq
  rw [integral_mul_const,integral_const_mul,integral_add hR (integrable_const δ)]
  simp

end
end RectangleCLT.Companion.SplitV4.Printed
