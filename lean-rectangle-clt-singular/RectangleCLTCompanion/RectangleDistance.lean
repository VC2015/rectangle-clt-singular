import RectangleCLTCompanion.Statement

/-! The actual rectangle distance is the supremum of the actual
probability discrepancies. These elementary order facts connect individual
detecting rectangles and uniform CLT bounds to the same distance. -/

open MeasureTheory Set

namespace RectangleCLT.Companion

noncomputable section

def rectangleDistance {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  sSup (Set.range (rectangleError μ W A))

theorem rectangleErrors_bddAbove {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) : BddAbove (Set.range (rectangleError μ W A)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨R, rfl⟩
  exact rectangleError_le_one μ W A R

theorem rectangleErrors_nonempty {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) :
    (Set.range (rectangleError μ W A)).Nonempty :=
  ⟨_, ⟨Rect.closedBox 0 0, rfl⟩⟩

theorem rectangleError_le_rectangleDistance
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) :
    rectangleError μ W A R ≤ rectangleDistance μ W A :=
  le_csSup (rectangleErrors_bddAbove μ W A) ⟨R, rfl⟩

theorem rectangleDistance_le {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    {C : ℝ} (h : ∀ R : Rect p, rectangleError μ W A R ≤ C) :
    rectangleDistance μ W A ≤ C := by
  apply csSup_le (rectangleErrors_nonempty μ W A)
  rintro x ⟨R, rfl⟩
  exact h R

theorem rectangleDistance_nonneg {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) : 0 ≤ rectangleDistance μ W A :=
  (abs_nonneg _).trans (rectangleError_le_rectangleDistance μ W A (Rect.closedBox 0 0))

theorem rectangleDistance_le_one {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) : rectangleDistance μ W A ≤ 1 :=
  rectangleDistance_le μ W A (rectangleError_le_one μ W A)

end

end RectangleCLT.Companion
