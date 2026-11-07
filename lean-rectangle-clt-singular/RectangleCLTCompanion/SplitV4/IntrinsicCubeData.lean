import Kane.Cube
import Mathlib.Data.Finset.Lattice.Fold

/-! Actual finite sign-cube data and the intrinsic positive maximum in
Lemma C.1. `Kane.avg` is the uniform average over every sign vector. -/

open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def cubeSign {n : ℕ} (x : Kane.Cube n) (i : Fin n) : ℝ := if x i then 1 else -1

def cubeLinear {n : ℕ} (b : Fin n → ℝ) (x : Kane.Cube n) : ℝ :=
  ∑ i, b i * cubeSign x i

/-- Include a zero branch explicitly, so this maximum exists even if the
original face family is empty. -/
def positiveLinearMaximum {m n : ℕ} (b : Fin m → Fin n → ℝ) (x : Kane.Cube n) : ℝ :=
  (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty
    (Fin.cases 0 (fun α => cubeLinear (b α) x))

def intrinsicCubeMean {m n : ℕ} (b : Fin m → Fin n → ℝ) : ℝ :=
  Kane.avg (positiveLinearMaximum b)

theorem positiveLinearMaximum_nonneg {m n : ℕ} (b : Fin m → Fin n → ℝ) (x : Kane.Cube n) :
    0 ≤ positiveLinearMaximum b x := by
  have hh := Finset.le_sup' (s := (Finset.univ : Finset (Fin (m + 1))))
    (f := Fin.cases (0 : ℝ) (fun α => cubeLinear (b α) x)) (Finset.mem_univ 0)
  simpa only [Fin.cases_zero] using hh

theorem cubeLinear_le_positiveMaximum {m n : ℕ} (b : Fin m → Fin n → ℝ)
    (x : Kane.Cube n) (α : Fin m) : cubeLinear (b α) x ≤ positiveLinearMaximum b x := by
  have hh := Finset.le_sup' (s := (Finset.univ : Finset (Fin (m + 1))))
    (f := Fin.cases (0 : ℝ) (fun α => cubeLinear (b α) x)) (Finset.mem_univ α.succ)
  simpa only [Fin.cases_succ] using hh

theorem intrinsicCubeMean_nonneg {m n : ℕ} (b : Fin m → Fin n → ℝ) :
    0 ≤ intrinsicCubeMean b := Kane.avg_nonneg (positiveLinearMaximum_nonneg b)

end

end RectangleCLT.Companion.SplitV4
