import Kane.UpperBound

/-! Restricting an intersection of halfspaces to randomly signed blocks keeps
it an intersection of the same number of halfspaces. The one-block sensitivity
bound below is the deterministic part of Kane's noise-sensitivity argument. -/

open scoped BigOperators

namespace Kane

/-- Substitute `signs i * b (assignment i)` in coordinate `i`, where Boolean
`true` represents `+1` and Boolean `false` represents `-1`. -/
def blockRestriction {n m : ℕ} (assignment : Fin n → Fin m) (signs : Cube n)
    (b : Cube m) : Cube n :=
  fun i => signs i == b (assignment i)

namespace Halfspace

/-- Collect weights belonging to the same block, after applying fixed signs. -/
def blockPullback {n m : ℕ} (h : Halfspace n)
    (assignment : Fin n → Fin m) (signs : Cube n) : Halfspace m where
  weights j := ∑ i, if assignment i = j then
    h.weights i * (if signs i then (1 : ℝ) else -1) else 0
  threshold := h.threshold

@[simp] theorem blockPullback_threshold {n m : ℕ} (h : Halfspace n)
    (assignment : Fin n → Fin m) (signs : Cube n) :
    (h.blockPullback assignment signs).threshold = h.threshold := rfl

/-- Grouping coefficients by block gives the same affine score. -/
theorem blockPullback_score {n m : ℕ} (h : Halfspace n)
    (assignment : Fin n → Fin m) (signs : Cube n) (b : Cube m) :
    (h.blockPullback assignment signs).score b =
      h.score (blockRestriction assignment signs b) := by
  classical
  simp only [score, blockPullback, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul]
  cases hs : signs i <;> cases hb : b (assignment i) <;>
    simp [blockRestriction, hs, hb]

/-- The halfspace indicator commutes with a block substitution, including its
boundary. -/
theorem blockPullback_indicator {n m : ℕ} (h : Halfspace n)
    (assignment : Fin n → Fin m) (signs : Cube n) (b : Cube m) :
    (h.blockPullback assignment signs).indicator b =
      h.indicator (blockRestriction assignment signs b) := by
  simp only [indicator, blockPullback_threshold, blockPullback_score]

end Halfspace

/-- A block restriction preserves an intersection and its number of halfspaces. -/
theorem intersection_blockPullback {n m : ℕ} (hs : List (Halfspace n))
    (assignment : Fin n → Fin m) (signs : Cube n) :
    intersection (hs.map fun h => h.blockPullback assignment signs) =
      fun b => intersection hs (blockRestriction assignment signs b) := by
  funext b
  induction hs with
  | nil => rfl
  | cons h hs ih =>
      simp only [List.map_cons, intersection, Halfspace.blockPullback_indicator, ih]

/-- Every fixed signed-block restriction obeys the sensitivity bound in the
number of blocks, independently of the original dimension. -/
theorem blockRestriction_averageSensitivity_le {n m : ℕ}
    (hs : List (Halfspace n)) (assignment : Fin n → Fin m) (signs : Cube n) :
    averageSensitivity (fun b => intersection hs (blockRestriction assignment signs b)) ≤
      2 * Real.sqrt (2 * (m : ℝ) * Real.log ((hs.length : ℝ) + 1)) := by
  rw [← intersection_blockPullback]
  simpa only [List.length_map] using
    halfspaces_averageSensitivity_le (hs.map fun h => h.blockPullback assignment signs)

/-- Uniformly choose an input and then one block, and test whether flipping
that block changes the output. For zero blocks this finite average is zero. -/
noncomputable def uniformOneBlockDisagreement {m : ℕ} (f : Cube m → Bool) : ℝ :=
  avg fun b => avg fun j : Fin m => if f b = f (flip b j) then (0 : ℝ) else 1

/-- Uniform one-block disagreement is average sensitivity divided by the
number of blocks. The convention also gives equality when there are no blocks. -/
theorem uniformOneBlockDisagreement_eq {m : ℕ} (f : Cube m → Bool) :
    uniformOneBlockDisagreement f = averageSensitivity f / (m : ℝ) := by
  unfold uniformOneBlockDisagreement averageSensitivity avg
  simp only [Fintype.card_fin]
  rw [← Finset.mul_sum]
  ring

private theorem sqrt_normalize_blocks (m : ℕ) (hm : 0 < m) (L : ℝ) :
    (2 * Real.sqrt (2 * (m : ℝ) * L)) / (m : ℝ) =
      2 * Real.sqrt (2 * L / (m : ℝ)) := by
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmreal
  have hs : Real.sqrt (2 * (m : ℝ) * L) =
      (m : ℝ) * Real.sqrt (2 * L / (m : ℝ)) := by
    calc
      _ = Real.sqrt ((m : ℝ) ^ 2 * (2 * L / (m : ℝ))) := by
        congr 1
        field_simp
        ring
      _ = Real.sqrt ((m : ℝ) ^ 2) * Real.sqrt (2 * L / (m : ℝ)) :=
        Real.sqrt_mul (sq_nonneg _) _
      _ = _ := by rw [Real.sqrt_sq hmreal.le]
  rw [hs]
  field_simp
  ring

/-- The deterministic signed-block bound, normalized as a probability of
disagreement after one uniformly selected block flip. -/
theorem blockRestriction_uniformOneBlockDisagreement_le {n m : ℕ}
    (hs : List (Halfspace n)) (assignment : Fin n → Fin m) (signs : Cube n)
    (hm : 0 < m) :
    uniformOneBlockDisagreement
        (fun b => intersection hs (blockRestriction assignment signs b)) ≤
      2 * Real.sqrt (2 * Real.log ((hs.length : ℝ) + 1) / (m : ℝ)) := by
  rw [uniformOneBlockDisagreement_eq]
  calc
    _ ≤ (2 * Real.sqrt (2 * (m : ℝ) * Real.log ((hs.length : ℝ) + 1))) /
        (m : ℝ) :=
      div_le_div_of_nonneg_right
        (blockRestriction_averageSensitivity_le hs assignment signs) (Nat.cast_nonneg _)
    _ = _ := sqrt_normalize_blocks m hm _

end Kane
