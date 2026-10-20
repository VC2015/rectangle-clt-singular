import RectangleCLT.Statement
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Order.Compact

/-! A uniform probability bound for finite closed boxes extends to every
coordinate interval convention, by compact approximation from within. No
assumption that the two laws give zero mass to rectangle boundaries is used. -/

open MeasureTheory Set

namespace RectangleCLT

theorem Rect.compact_subset_closedBox {p : ℕ} (R : Rect p) (hp : 1 ≤ p)
    {K : Set (Vector p)} (hK : IsCompact K) (hKR : K ⊆ R.carrier) :
    ∃ lo hi : Vector p, K ⊆ (Rect.closedBox lo hi).carrier ∧
      (Rect.closedBox lo hi).carrier ⊆ R.carrier := by
  classical
  by_cases hne : K.Nonempty
  · have hmin (j : Fin p) : ∃ a : ℝ, IsLeast ((fun x : Vector p => x j) '' K) a :=
      (hK.image (continuous_apply j)).exists_isLeast (hne.image _)
    have hmax (j : Fin p) : ∃ a : ℝ, IsGreatest ((fun x : Vector p => x j) '' K) a :=
      (hK.image (continuous_apply j)).exists_isGreatest (hne.image _)
    choose lo hlo using hmin
    choose hi hhi using hmax
    refine ⟨lo, hi, ?_, ?_⟩
    · intro x hx j _
      exact ⟨(hlo j).2 ⟨x, hx, rfl⟩, (hhi j).2 ⟨x, hx, rfl⟩⟩
    · intro x hx j _
      have hlom : lo j ∈ R.interval j := by
        rcases (hlo j).1 with ⟨y, hy, hyeq⟩
        simpa only [← hyeq] using hKR hy j (mem_univ j)
      have hhim : hi j ∈ R.interval j := by
        rcases (hhi j).1 with ⟨y, hy, hyeq⟩
        simpa only [← hyeq] using hKR hy j (mem_univ j)
      exact (R.ordConnected j).out hlom hhim (hx j (mem_univ j))
  · refine ⟨fun _ => 1, fun _ => 0, ?_, ?_⟩
    · simp only [not_nonempty_iff_eq_empty.mp hne, empty_subset]
    · intro x hx
      have hh := hx ⟨0, by omega⟩ (mem_univ _)
      change (1 : ℝ) ≤ x ⟨0, by omega⟩ ∧ x ⟨0, by omega⟩ ≤ 0 at hh
      exact False.elim (by linarith)

/-- A closed-box bound extends to every measurable rectangle with connected
coordinate intervals. The constant stays unchanged. -/
theorem rectangle_probability_le_of_closedBox
    {p : ℕ} (hp : 1 ≤ p) (μ ν : Measure (Vector p))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ}
    (hboxes : ∀ lo hi : Vector p,
      μ.real (Rect.closedBox lo hi).carrier ≤ ν.real (Rect.closedBox lo hi).carrier + B)
    (R : Rect p) : μ.real R.carrier ≤ ν.real R.carrier + B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨K, hKR, hK, hμK⟩ := R.measurableSet_carrier.exists_isCompact_lt_add
    (measure_ne_top μ R.carrier) (ENNReal.ofReal_ne_zero_iff.mpr hε)
  obtain ⟨lo, hi, hKB, hBR⟩ := R.compact_subset_closedBox hp hK hKR
  have hlt : μ.real R.carrier < μ.real K + ε := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ R.carrier)
      (by finiteness : μ K + ENNReal.ofReal ε ≠ ⊤)).mpr hμK
    simpa only [← measureReal_def, ENNReal.toReal_add (measure_ne_top μ K)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le] using hh
  have hμ := measureReal_mono (μ := μ) hKB
  have hν := measureReal_mono (μ := ν) hBR
  linarith [hboxes lo hi]

theorem rectangle_abs_probability_le_of_closedBox
    {p : ℕ} (hp : 1 ≤ p) (μ ν : Measure (Vector p))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {B : ℝ}
    (hboxes : ∀ lo hi : Vector p,
      |μ.real (Rect.closedBox lo hi).carrier - ν.real (Rect.closedBox lo hi).carrier| ≤ B)
    (R : Rect p) : |μ.real R.carrier - ν.real R.carrier| ≤ B := by
  apply abs_le.mpr
  constructor
  · have hh := rectangle_probability_le_of_closedBox hp ν μ
      (fun lo hi => by linarith [(abs_le.mp (hboxes lo hi)).1]) R
    linarith
  · have hh := rectangle_probability_le_of_closedBox hp μ ν
      (fun lo hi => by linarith [(abs_le.mp (hboxes lo hi)).2]) R
    linarith

theorem rectangleError_le_of_closedBox
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (hp : 1 ≤ p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) {B : ℝ}
    (hboxes : ∀ lo hi : Vector p, rectangleError μ W A (Rect.closedBox lo hi) ≤ B)
    (R : Rect p) : rectangleError μ W A R ≤ B := by
  letI : IsProbabilityMeasure (μ.map W) := isProbabilityMeasure_map hW.aemeasurable
  have hmap (T : Rect p) : (μ.map W).real T.carrier = μ.real (W ⁻¹' T.carrier) := by
    simp only [Measure.real, Measure.map_apply hW T.measurableSet_carrier]
  have hh := rectangle_abs_probability_le_of_closedBox hp (μ.map W) (gaussianLaw A)
    (fun lo hi => by simpa only [hmap, rectangleError] using hboxes lo hi) R
  simpa only [hmap, rectangleError] using hh

end RectangleCLT
