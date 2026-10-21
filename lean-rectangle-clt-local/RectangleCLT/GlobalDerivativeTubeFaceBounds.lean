import RectangleCLT.GlobalDerivativeTubeDomination
import RectangleCLT.WeightedConditioning

/-! Weighted full-dual tube unions in one common probability space.
Disjointness and physical-coordinate boundary containment are proved
geometrically; actual boundary estimates for the independent base vector
can therefore be inserted without changing the Gaussian score weight. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

def liftedDualImageEvent {Ω : Type*} {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p)
    (width : ℝ) : Set (CommonSamples p × Ω) :=
  {z | z.1 ∈ dualImageEvent S s A (V z.2) width}

theorem measurableSet_liftedDualImageEvent {Ω : Type*} [MeasurableSpace Ω]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (width : ℝ) (hd : IsUnit (A * A.transpose).det) :
    MeasurableSet (liftedDualImageEvent S s A V width) :=
  (measurableSet_dualImageEvent_joint S s A width hd).preimage
    ((hV.comp measurable_snd).prodMk measurable_fst)

theorem sum_weighted_dual_image_indicators_le
    {Ω ι : Type*} {p q : ℕ} (I : Finset ι) (S : ι → CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (A * A.transpose).det) (V : Ω → Vector p)
    (hactive : ∀ i ∈ I, ∀ j, (S i).face j ∈ s.faces)
    (hq : 0 < q) {width : ℝ} (hwidth : 0 ≤ width)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, activeFaces (S i) = activeFaces (S j) → i = j)
    (w : CommonSamples p → ℝ) (hw0 : ∀ e, 0 ≤ w e) (z : CommonSamples p × Ω) :
    (∑ i ∈ I, w z.1 *
      (liftedDualImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) ≤
      w z.1 * (annulusEvent s A V ((q : ℝ) * width)).indicator
        (fun _ => (1 : ℝ)) z := by
  classical
  by_cases hex : ∃ i ∈ I, z ∈ liftedDualImageEvent (S i) s A V width
  · obtain ⟨i, hi, hzi⟩ := hex
    have hza : z ∈ annulusEvent s A V ((q : ℝ) * width) :=
      dualImageEvent_mem_boundaryLayer (S i) s A hd (V z.2)
        (hactive i hi) hq hwidth hzi
    rw [Set.indicator_of_mem hza, Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem hzi]
    · intro j hj hji
      have hne : activeFaces (S j) ≠ activeFaces (S i) := fun hh => hji (hinj j hj i hi hh)
      have hdis := dualImageEvent_disjoint (S j) (S i) s A hd (V z.2)
        (hactive j hj) (hactive i hi) width hne
      have hzj : z ∉ liftedDualImageEvent (S j) s A V width :=
        fun hh => Set.disjoint_left.mp hdis hh hzi
      rw [Set.indicator_of_not_mem hzj, mul_zero]
    · exact fun hn => False.elim (hn hi)
  · have hsum : (∑ i ∈ I, w z.1 *
        (liftedDualImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_not_mem (fun hz => hex ⟨i, hi, hz⟩), mul_zero]
    rw [hsum]
    apply mul_nonneg (hw0 _)
    by_cases hz : z ∈ annulusEvent s A V ((q : ℝ) * width) <;> simp [hz]

/-- A general conditioning bridge. The base-vector concentration premise
is a probability estimate, and the score weight lives in the independent
Gaussian/exponential experiment. In the applications this premise is
supplied by a proved bounded or Gaussian boundary theorem. -/
theorem integral_sum_weighted_dual_image_indicators_le
    {Ω ι : Type*} [MeasurableSpace Ω] {p q : ℕ}
    (I : Finset ι) (S : ι → CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (A * A.transpose).det)
    (hactive : ∀ i ∈ I, ∀ j, (S i).face j ∈ s.faces)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, activeFaces (S i) = activeFaces (S j) → i = j)
    (hq : 0 < q) {width : ℝ} (hwidth : 0 ≤ width)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (γ : Measure (CommonSamples p)) [IsProbabilityMeasure γ]
    (w : CommonSamples p → ℝ) (hw : Integrable w γ) (hw0 : ∀ e, 0 ≤ w e)
    (B : ℝ)
    (hboundary : ∀ (t : FaceSmoother p) (r : Vector p),
      μ.real {ω | V ω + r ∈ t.boundaryLayer ((q : ℝ) * width)} ≤ B) :
    (∑ i ∈ I, ∫ z, w z.1 *
      (liftedDualImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z
        ∂γ.prod μ) ≤ B * (∫ e, w e ∂γ) := by
  classical
  have hwp : Integrable (fun z : CommonSamples p × Ω => w z.1) (γ.prod μ) := by
    simpa only [mul_one] using hw.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have hwi (i : ι) (hi : i ∈ I) : Integrable (fun z : CommonSamples p × Ω => w z.1 *
      (liftedDualImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z)
        (γ.prod μ) := by
    have heq : (fun z : CommonSamples p × Ω => w z.1 *
        (liftedDualImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) =
        (liftedDualImageEvent (S i) s A V width).indicator (fun z => w z.1) := by
      funext z
      by_cases hz : z ∈ liftedDualImageEvent (S i) s A V width <;> simp [hz]
    rw [heq]
    exact hwp.indicator (measurableSet_liftedDualImageEvent (S i) s A V hV width hd)
  have hAnn := measurableSet_annulusEvent s A V hV ((q : ℝ) * width)
  have hwa : Integrable (fun z : CommonSamples p × Ω => w z.1 *
      (annulusEvent s A V ((q : ℝ) * width)).indicator (fun _ => (1 : ℝ)) z)
        (γ.prod μ) := by
    have heq : (fun z : CommonSamples p × Ω => w z.1 *
        (annulusEvent s A V ((q : ℝ) * width)).indicator (fun _ => (1 : ℝ)) z) =
        (annulusEvent s A V ((q : ℝ) * width)).indicator (fun z => w z.1) := by
      funext z
      by_cases hz : z ∈ annulusEvent s A V ((q : ℝ) * width) <;> simp [hz]
    rw [heq]
    exact hwp.indicator hAnn
  have hsections (e : CommonSamples p) :
      μ.real {ω | (e, ω) ∈ annulusEvent s A V ((q : ℝ) * width)} ≤ B := by
    simpa only [annulusEvent, Set.mem_setOf_eq, add_comm] using
      hboundary (s.randomRectangle e.2) (A.mulVec e.1)
  rw [← integral_finset_sum I (fun i hi => hwi i hi)]
  calc
    _ ≤ ∫ z, w z.1 * (annulusEvent s A V ((q : ℝ) * width)).indicator
        (fun _ => (1 : ℝ)) z ∂γ.prod μ :=
      integral_mono (integrable_finset_sum I (fun i hi => hwi i hi)) hwa
        (sum_weighted_dual_image_indicators_le I S s A hd V
          hactive hq hwidth hinj w hw0)
    _ ≤ _ := integral_weighted_indicator_le hAnn hw hw0 hsections

/-- The actual bounded-base specialization, with physical-coordinate tube
width and no covariance determinant in its coefficient. -/
theorem integral_sum_weighted_dual_image_indicators_bounded_le
    {Ω ι : Type*} [MeasurableSpace Ω] {p n q : ℕ}
    (I : Finset ι) (S : ι → CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (A * A.transpose).det)
    (hactive : ∀ i ∈ I, ∀ j, (S i).face j ∈ s.faces)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, activeFaces (S i) = activeFaces (S j) → i = j)
    (hq : 0 < q) {width : ℝ} (hwidth : 0 < width)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (γ : Measure (CommonSamples p)) [IsProbabilityMeasure γ]
    (w : CommonSamples p → ℝ) (hw : Integrable w γ) (hw0 : ∀ e, 0 ≤ w e) :
    (∑ i ∈ I, ∫ z, w z.1 *
      (liftedDualImageEvent (S i) s A (sumVector ξ) width).indicator (fun _ => (1 : ℝ)) z
        ∂γ.prod μ) ≤
      (1073741824 * ((q : ℝ) * width + η) * Real.sqrt (dimensionLog p / v)) *
        (∫ e, w e ∂γ) := by
  apply integral_sum_weighted_dual_image_indicators_le I S s A hd hactive hinj hq
    hwidth.le μ (sumVector ξ) h.measurable_sum γ w hw hw0
  intro t r
  exact h.boundary_probability_le hp hv hdiag t r
    (mul_pos (by exact_mod_cast hq) hwidth)

end

end RectangleCLT.GaussianTube
