import RectangleCLTArxivV1.SignedCoordinates

/-! # Fixed face projections and common threshold shifts -/

namespace RectangleCLTArxivV1

open MeasureTheory
open scoped BigOperators

/-- The vector of projections onto the fixed face directions. -/
def faceProjection {r m : ℕ} (U : Fin m → Fin r → ℝ) (x : Fin r → ℝ) : Fin m → ℝ :=
  fun j => dotProduct (U j) x

/-- The maximum absolute face projection used in Lemma 1. -/
def faceNorm {r m : ℕ} (U : Fin m → Fin r → ℝ) (x : Fin r → ℝ) : ℝ :=
  ‖faceProjection U x‖

/-- All face thresholds are shifted by the same scalar; this is not set dilation. -/
def facePolyhedron {r m : ℕ} (U : Fin m → Fin r → ℝ) (a : Fin m → ℝ) (s : ℝ) :
    Set (Fin r → ℝ) := {x | ∀ j, dotProduct (U j) x ≤ a j + s}

/-- The outer polyhedron with the inner polyhedron removed. -/
def faceLayer {r m : ℕ} (U : Fin m → Fin r → ℝ) (a : Fin m → ℝ) (s : ℝ) :
    Set (Fin r → ℝ) := facePolyhedron U a s \ facePolyhedron U a (-s)

@[simp] theorem faceProjection_eq_mulVec {r m : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (x : Fin r → ℝ) : faceProjection U x = U.mulVec x := rfl

@[simp] theorem faceProjection_add {r m : ℕ} (U : Fin m → Fin r → ℝ) (x y : Fin r → ℝ) :
    faceProjection U (x + y) = faceProjection U x + faceProjection U y := by
  ext j
  exact dotProduct_add _ _ _

@[simp] theorem faceProjection_zero {r m : ℕ} (U : Fin m → Fin r → ℝ) :
    faceProjection U 0 = 0 := by ext j; simp [faceProjection]

theorem faceProjection_sum {r m : ℕ} {I : Type*} (S : Finset I)
    (U : Fin m → Fin r → ℝ) (x : I → Fin r → ℝ) :
    faceProjection U (∑ i ∈ S, x i) = ∑ i ∈ S, faceProjection U (x i) := by
  ext j
  simp only [faceProjection, dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem continuous_faceProjection {r m : ℕ} (U : Fin m → Fin r → ℝ) :
    Continuous (faceProjection U) := by
  apply continuous_pi
  intro j
  change Continuous (fun x : Fin r → ℝ => ∑ k, U j k * x k)
  apply continuous_finset_sum
  intro k hk
  exact continuous_const.mul (continuous_apply k)

theorem measurable_faceProjection {r m : ℕ} (U : Fin m → Fin r → ℝ) :
    Measurable (faceProjection U) := (continuous_faceProjection U).measurable

theorem measurableSet_faceLayer {r m : ℕ} (U : Fin m → Fin r → ℝ)
    (a : Fin m → ℝ) (s : ℝ) : MeasurableSet (faceLayer U a s) := by
  apply MeasurableSet.diff
  all_goals
    unfold facePolyhedron
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le
      ((measurable_pi_apply j).comp (measurable_faceProjection U)) measurable_const)

theorem faceNorm_nonneg {r m : ℕ} (U : Fin m → Fin r → ℝ) (x : Fin r → ℝ) :
    0 ≤ faceNorm U x := norm_nonneg _

/-- The expected face norm is the expected largest absolute projection. -/
theorem faceNorm_eq_signedMaximum {r m : ℕ} (U : Fin m → Fin r → ℝ) (x : Fin r → ℝ) :
    faceNorm U x = ⨆ t : SignedIndex m, signedCoordinate t (faceProjection U x) :=
  (signedMaximum_eq_norm _).symm

end RectangleCLTArxivV1
