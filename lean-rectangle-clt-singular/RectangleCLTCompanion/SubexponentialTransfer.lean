import RectangleCLTCompanion.GaussianConcentration
import RectangleCLT.RectangleSmoothing

/-!
# Rectangle comparison under two probabilistic perturbations

The two couplings may each contain dependent components.  Closed boxes are
expanded and contracted before compact approximation extends the estimate
to all measurable coordinate rectangles, including atomic endpoints.
-/

open MeasureTheory Set

namespace RectangleCLT.Companion

noncomputable section

def shiftedBox {p : ℕ} (lo hi : Vector p) (t : ℝ) : Rect p :=
  Rect.closedBox (fun j => lo j - t) (fun j => hi j + t)

@[simp] theorem shiftedBox_zero {p : ℕ} (lo hi : Vector p) :
    shiftedBox lo hi 0 = Rect.closedBox lo hi := by
  simp only [shiftedBox, sub_zero, add_zero]

theorem mem_shiftedBox {p : ℕ} (lo hi : Vector p) (t : ℝ) (x : Vector p) :
    x ∈ (shiftedBox lo hi t).carrier ↔
      ∀ j, lo j - t ≤ x j ∧ x j ≤ hi j + t := by
  simp only [shiftedBox, Rect.closedBox, Rect.carrier, mem_pi, mem_univ,
    forall_true_left, mem_Icc]

theorem shiftedBox_mono {p : ℕ} (lo hi : Vector p) {t u : ℝ} (htu : t ≤ u) :
    (shiftedBox lo hi t).carrier ⊆ (shiftedBox lo hi u).carrier := by
  intro x hx
  apply (mem_shiftedBox lo hi u x).mpr
  intro j
  have hj := (mem_shiftedBox lo hi t x).mp hx j
  constructor <;> linarith

theorem shiftedBox_eq_outerSet {p : ℕ} (lo hi : Vector p) (t : ℝ) :
    (shiftedBox lo hi t).carrier =
      (FaceSmoother.closedBox lo hi 1 (by norm_num)).outerSet t := by
  ext x
  rw [mem_shiftedBox]
  simp only [FaceSmoother.outerSet, FaceSmoother.closedBox, Finset.mem_univ,
    forall_true_left, mem_setOf_eq]
  constructor
  · intro hx f
    rcases f with ⟨j, b⟩
    have hj := hx j
    cases b <;> simp only [FaceSmoother.normalDot, Bool.false_eq_true, ↓reduceIte] <;> linarith
  · intro hx j
    have hl := hx (j, false)
    have hh := hx (j, true)
    simp only [FaceSmoother.normalDot, Bool.false_eq_true, ↓reduceIte] at hl hh
    constructor <;> linarith

/-- Deterministic maximum-norm control expands every face by the same
amount. The shift `t` may be negative, so this also handles contractions. -/
theorem mem_shiftedBox_of_norm_sub_le {p : ℕ} (lo hi : Vector p)
    (x y : Vector p) (t r : ℝ)
    (hx : x ∈ (shiftedBox lo hi t).carrier) (hxy : ‖x - y‖ ≤ r) :
    y ∈ (shiftedBox lo hi (t + r)).carrier := by
  apply (mem_shiftedBox lo hi (t + r) y).mpr
  intro j
  have hj := (mem_shiftedBox lo hi t x).mp hx j
  have hab : |x j - y j| ≤ r := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      (norm_le_pi_norm (x - y) j).trans hxy
  have ha := abs_le.mp hab
  constructor <;> linarith

/-- A coupling tail estimate gives a one-sided comparison on every shifted
box. No independence is needed between the two variables in the coupling. -/
theorem probability_shiftedBox_le_add_bad
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U V : Ω → Vector p) (lo hi : Vector p) (t r ε : ℝ)
    (hbad : μ.real {ω | r < ‖U ω - V ω‖} ≤ ε) :
    μ.real (U ⁻¹' (shiftedBox lo hi t).carrier) ≤
      μ.real (V ⁻¹' (shiftedBox lo hi (t + r)).carrier) + ε := by
  have hs : U ⁻¹' (shiftedBox lo hi t).carrier ⊆
      (V ⁻¹' (shiftedBox lo hi (t + r)).carrier) ∪ {ω | r < ‖U ω - V ω‖} := by
    intro ω hω
    by_cases hb : r < ‖U ω - V ω‖
    · exact Or.inr hb
    · exact Or.inl (mem_shiftedBox_of_norm_sub_le lo hi (U ω) (V ω) t r hω
        (le_of_not_gt hb))
  exact (measureReal_mono hs).trans
    ((measureReal_union_le _ _).trans (add_le_add_left hbad _))

theorem gaussian_probability_shiftedBox_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (lo hi : Vector p) {r : ℝ} (hr : 0 < r) :
    (gaussianLaw A).real (shiftedBox lo hi r).carrier ≤
      (gaussianLaw A).real (Rect.closedBox lo hi).carrier +
        12 * Real.exp (3 / 2 : ℝ) * r * Real.sqrt (dimensionLog p) := by
  let s := FaceSmoother.closedBox lo hi 1 (by norm_num)
  have hshell : (gaussianLaw A).real (s.boundaryLayer r) ≤
      12 * Real.exp (3 / 2 : ℝ) * r * Real.sqrt (dimensionLog p) := by
    simpa only [add_zero, div_one, setOf_mem_eq] using
      s.gaussian_boundary_probability_le hp A (by norm_num : (0 : ℝ) < 1) hdiag 0 hr
  have hin : (shiftedBox lo hi (-r)).carrier ⊆ (Rect.closedBox lo hi).carrier := by
    simpa only [shiftedBox_zero] using shiftedBox_mono lo hi (by linarith : -r ≤ 0)
  have hsub : (shiftedBox lo hi r).carrier ⊆
      (Rect.closedBox lo hi).carrier ∪ s.boundaryLayer r := by
    intro x hx
    by_cases hbase : x ∈ (Rect.closedBox lo hi).carrier
    · exact Or.inl hbase
    · right
      change x ∈ s.outerSet r ∧ x ∉ s.outerSet (-r)
      constructor
      · exact (Set.ext_iff.mp (shiftedBox_eq_outerSet lo hi r) x).mp hx
      · intro hxinner
        apply hbase
        apply hin
        exact (Set.ext_iff.mp (shiftedBox_eq_outerSet lo hi (-r)) x).mpr hxinner
  exact (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add_left hshell _))

theorem gaussian_probability_le_contractedBox_add {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (lo hi : Vector p) {r : ℝ} (hr : 0 < r) :
    (gaussianLaw A).real (Rect.closedBox lo hi).carrier ≤
      (gaussianLaw A).real (shiftedBox lo hi (-r)).carrier +
        12 * Real.exp (3 / 2 : ℝ) * r * Real.sqrt (dimensionLog p) := by
  let s := FaceSmoother.closedBox lo hi 1 (by norm_num)
  have hshell : (gaussianLaw A).real (s.boundaryLayer r) ≤
      12 * Real.exp (3 / 2 : ℝ) * r * Real.sqrt (dimensionLog p) := by
    simpa only [add_zero, div_one, setOf_mem_eq] using
      s.gaussian_boundary_probability_le hp A (by norm_num : (0 : ℝ) < 1) hdiag 0 hr
  have hout : (Rect.closedBox lo hi).carrier ⊆ (shiftedBox lo hi r).carrier := by
    simpa only [shiftedBox_zero] using shiftedBox_mono lo hi hr.le
  have hsub : (Rect.closedBox lo hi).carrier ⊆
      (shiftedBox lo hi (-r)).carrier ∪ s.boundaryLayer r := by
    intro x hx
    by_cases hinner : x ∈ (shiftedBox lo hi (-r)).carrier
    · exact Or.inl hinner
    · right
      change x ∈ s.outerSet r ∧ x ∉ s.outerSet (-r)
      constructor
      · exact (Set.ext_iff.mp (shiftedBox_eq_outerSet lo hi r) x).mp (hout hx)
      · intro hxinner
        exact hinner ((Set.ext_iff.mp (shiftedBox_eq_outerSet lo hi (-r)) x).mpr hxinner)
  exact (measureReal_mono hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add_left hshell _))

theorem probability_eq_gaussian_of_map_eq
    {E : Type*} [MeasurableSpace E] {p : ℕ}
    (ν : Measure E) (Z : E → Vector p) (hZ : Measurable Z)
    (A : Matrix (Fin p) (Fin p) ℝ) (hlaw : ν.map Z = gaussianLaw A) (R : Rect p) :
    ν.real (Z ⁻¹' R.carrier) = (gaussianLaw A).real R.carrier := by
  rw [← hlaw]
  simp only [Measure.real, Measure.map_apply hZ R.measurableSet_carrier]

/-- Transfer through two genuine couplings, with the actual Gaussian
rectangle concentration bound. Neither coupling needs independent parts. -/
theorem rectangleError_le_of_two_couplings
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p : ℕ}
    (hp : 1 ≤ p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (W WT : Ω → Vector p) (Z ZT : E → Vector p)
    (hW : Measurable W) (hZ : Measurable Z)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hZlaw : ν.map Z = gaussianLaw A)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {B r₁ r₂ ε₁ ε₂ : ℝ} (hr : 0 < r₁ + r₂)
    (hcompare : ∀ R : Rect p,
      |μ.real (WT ⁻¹' R.carrier) - ν.real (ZT ⁻¹' R.carrier)| ≤ B)
    (hbadW : μ.real {ω | r₁ < ‖W ω - WT ω‖} ≤ ε₁)
    (hbadZ : ν.real {z | r₂ < ‖ZT z - Z z‖} ≤ ε₂)
    (R : Rect p) :
    rectangleError μ W A R ≤ B +
      12 * Real.exp (3 / 2 : ℝ) * (r₁ + r₂) * Real.sqrt (dimensionLog p) + ε₁ + ε₂ := by
  apply rectangleError_le_of_closedBox hp μ W hW A _ R
  intro lo hi
  let d := r₁ + r₂
  have hpZ (t : ℝ) := probability_eq_gaussian_of_map_eq ν Z hZ A hZlaw (shiftedBox lo hi t)
  have huW := probability_shiftedBox_le_add_bad μ W WT lo hi 0 r₁ ε₁ hbadW
  have huZ := probability_shiftedBox_le_add_bad ν ZT Z lo hi r₁ r₂ ε₂ hbadZ
  have huC := (abs_le.mp (hcompare (shiftedBox lo hi r₁))).2
  have huG := gaussian_probability_shiftedBox_le hp A hdiag lo hi hr
  have hlW := probability_shiftedBox_le_add_bad μ WT W lo hi (-r₁) r₁ ε₁
    (by simpa only [norm_sub_rev] using hbadW)
  have hlZ := probability_shiftedBox_le_add_bad ν Z ZT lo hi (-d) r₂ ε₂
    (by simpa only [norm_sub_rev] using hbadZ)
  have hlC := (abs_le.mp (hcompare (shiftedBox lo hi (-r₁)))).1
  have hlG := gaussian_probability_le_contractedBox_add hp A hdiag lo hi hr
  have hneg : -d + r₂ = -r₁ := by dsimp only [d]; ring
  simp only [zero_add, shiftedBox_zero] at huW
  rw [hpZ (r₁ + r₂)] at huZ
  rw [neg_add_cancel, shiftedBox_zero] at hlW
  rw [hneg] at hlZ
  rw [hpZ (-d)] at hlZ
  dsimp only [d] at hlZ
  change |μ.real (W ⁻¹' (Rect.closedBox lo hi).carrier) -
    (gaussianLaw A).real (Rect.closedBox lo hi).carrier| ≤ _
  apply abs_le.mpr
  constructor <;> linarith

end

end RectangleCLT.Companion
