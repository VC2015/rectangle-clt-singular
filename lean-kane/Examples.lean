import Kane
import Mathlib.Algebra.BigOperators.Fin

/-!
Semantic checks for the sensitivity normalization, independent coordinate-flip
noise, the `{-1, 1}` encoding, and concrete lower-bound witnesses.
Run separately from the library with `lake env lean Examples.lean`.
-/

open scoped BigOperators

namespace Kane.SemanticExamples

example (n : ℕ) : averageSensitivity (fun _ : Cube n => false) = 0 := by
  simp [averageSensitivity, avg]

example (n : ℕ) : averageSensitivity (fun _ : Cube n => true) = 0 := by
  simp [averageSensitivity, avg]

example (f : Cube 0 → Bool) : averageSensitivity f = 0 := by
  simp [averageSensitivity, avg]

/-- A single sensitive edge contributes one, rather than one half or two. -/
theorem projection_averageSensitivity_one :
    averageSensitivity (fun x : Cube 1 => x 0) = 1 := by
  unfold averageSensitivity
  have hpoint (x : Cube 1) :
      (∑ i : Fin 1, if x 0 = (flip x i) 0 then (0 : ℝ) else 1) = 1 := by
    rw [Fin.sum_univ_one]
    cases hx : x 0 <;> simp [flip, hx]
  calc
    _ = avg (fun _ : Cube 1 => (1 : ℝ)) := avg_congr hpoint
    _ = 1 := avg_const 1

/-- A coordinate is changed with probability `θ`. In particular, the model
uses bit flips; replacing a bit by a fresh uniform bit would give `θ/2`. This
calculation expands the finite mask law directly. -/
theorem projection_noiseSensitivity (θ : ℝ) :
    noiseSensitivity (fun x : Cube 1 => x 0) θ = θ := by
  have hterm (x mask : Cube 1) :
      maskWeight θ mask *
        (if x 0 = maskedFlip mask x 0 then (0 : ℝ) else 1) =
          if mask 0 then θ else 0 := by
    cases hm : mask 0 <;> cases hx : x 0 <;>
      simp [maskWeight, Fin.prod_univ_one, maskedFlip, hm, hx]
  have hsum : (∑ mask : Cube 1, if mask 0 then θ else 0) = θ := by
    have h := (Equiv.funUnique (Fin 1) Bool).sum_comp
      (fun b : Bool => if b then θ else 0)
    simpa using h
  unfold noiseSensitivity
  calc
    _ = avg (fun _ : Cube 1 => θ) := by
      apply avg_congr
      intro x
      simp_rw [hterm x]
      exact hsum
    _ = θ := avg_const θ

example : noiseSensitivity (fun x : Cube 1 => x 0) 1 = 1 :=
  projection_noiseSensitivity 1

example (n : ℕ) (b : Bool) (θ : ℝ) :
    noiseSensitivity (fun _ : Cube n => b) θ = 0 := by
  simp [noiseSensitivity]

example {n : ℕ} (f : Cube n → Bool) : noiseSensitivity f 0 = 0 :=
  noiseSensitivity_zero f

example (n : ℕ) (θ : ℝ) : noiseSensitivity (intersection ([] : List (Halfspace n))) θ = 0 := by
  simp [intersection, noiseSensitivity]

def positiveCoordinate : Halfspace 1 where
  weights := fun _ => 1
  threshold := 0

example : positiveCoordinate.score (fun _ => false) = -1 := by
  norm_num [positiveCoordinate, Halfspace.score, Fin.sum_univ_one]

example : positiveCoordinate.score (fun _ => true) = 1 := by
  norm_num [positiveCoordinate, Halfspace.score, Fin.sum_univ_one]

theorem positiveCoordinate_indicator (x : Cube 1) :
    positiveCoordinate.indicator x = x 0 := by
  classical
  cases hx : x 0 <;>
    norm_num [positiveCoordinate, Halfspace.indicator, Halfspace.score,
      Fin.sum_univ_one, hx]

example : averageSensitivity (intersection [positiveCoordinate]) = 1 := by
  have heq : intersection [positiveCoordinate] = (fun x : Cube 1 => x 0) := by
    funext x
    simp [intersection, positiveCoordinate_indicator]
  rw [heq]
  exact projection_averageSensitivity_one

/-- A point whose score equals the threshold belongs to the closed halfspace. -/
example :
    (Halfspace.mk (fun _ : Fin 1 => (1 : ℝ)) 1).indicator (fun _ => true) = true := by
  classical
  norm_num [Halfspace.indicator, Halfspace.score, Fin.sum_univ_one]

/-- XOR changes on every edge of the square, so its sensitivity is two. -/
def twoBitParity (x : Cube 2) : Bool := x 0 ^^ x 1

private theorem twoBitParity_flip (x : Cube 2) (i : Fin 2) :
    twoBitParity (flip x i) = !twoBitParity x := by
  fin_cases i <;> cases hzero : x 0 <;> cases hone : x 1 <;>
    simp [twoBitParity, flip, hzero, hone]

theorem twoBitParity_averageSensitivity : averageSensitivity twoBitParity = 2 := by
  have hpoint (x : Cube 2) :
      (∑ i : Fin 2, if twoBitParity x = twoBitParity (flip x i) then (0 : ℝ) else 1) = 2 := by
    simp_rw [twoBitParity_flip]
    cases twoBitParity x <;> norm_num
  unfold averageSensitivity
  calc
    _ = avg (fun _ : Cube 2 => (2 : ℝ)) := avg_congr hpoint
    _ = 2 := avg_const 2

/-- Removing the two constant vertices realizes XOR by two genuine halfspaces. -/
def twoBitParityHalfspaces : List (Halfspace 2) :=
  [Lower.excludeVertex (fun _ => false), Lower.excludeVertex (fun _ => true)]

theorem twoBitParityHalfspaces_indicator :
    intersection twoBitParityHalfspaces = twoBitParity := by
  classical
  funext x
  cases hzero : x 0 <;> cases hone : x 1 <;>
    simp [twoBitParityHalfspaces, intersection, Lower.excludeVertex_indicator,
      funext_iff, Fin.forall_fin_succ, twoBitParity, hzero, hone]

example : twoBitParityHalfspaces.length = 2 ∧
    averageSensitivity (intersection twoBitParityHalfspaces) = 2 := by
  constructor
  · rfl
  · rw [twoBitParityHalfspaces_indicator]
    exact twoBitParity_averageSensitivity

/-- Complementing a closed halfspace excludes its original boundary point.
Negating the weights and the old threshold would incorrectly keep that point. -/
example :
    let h : Halfspace 1 := ⟨fun _ => 1, 1⟩
    h.indicator (fun _ => true) = true ∧
      h.cubeComplement.indicator (fun _ => true) = false ∧
      h.cubeComplement.indicator (fun _ => false) = true := by
  classical
  dsimp only
  simp only [Halfspace.cubeComplement_indicator]
  norm_num [Halfspace.indicator, Halfspace.score, Fin.sum_univ_one]

/-- The exported theorem includes the unique zero-dimensional family budget. -/
example : ∃ hs : List (Halfspace 0), hs.length ≤ 1 ∧
    lowerBoundConstant * Real.sqrt ((0 : ℝ) * Real.log 1) ≤
      averageSensitivity (intersection hs) := by
  simpa using halfspaces_averageSensitivity_lower_bound_explicit 0 1 (by decide) (by decide)

/-- The `k = 1` endpoint has zero logarithmic target in every dimension. -/
example (n : ℕ) : ∃ hs : List (Halfspace n), hs.length ≤ 1 ∧
    0 ≤ averageSensitivity (intersection hs) := by
  simpa using halfspaces_averageSensitivity_lower_bound_explicit n 1
    (by decide) (Nat.one_le_pow n 2 (by decide))

end Kane.SemanticExamples
