import Kane.UpperBound

/-! The literal `sqrt (n * log k)` form of Kane's upper bound for `k ≥ 2`. -/

namespace Kane

/-- For at least two functions, the endpoint-safe logarithm costs at most a
factor of two. -/
theorem log_add_one_le_two_log {k : ℕ} (hk : 2 ≤ k) :
    Real.log ((k : ℝ) + 1) ≤ 2 * Real.log (k : ℝ) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsq : (k : ℝ) + 1 ≤ (k : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((k : ℝ) - 1)]
  calc
    Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hsq
    _ = 2 * Real.log (k : ℝ) := by rw [Real.log_pow]; norm_num

private theorem sqrt_log_add_one_bound (n k : ℕ) (hk : 2 ≤ k) :
    2 * Real.sqrt (2 * (n : ℝ) * Real.log ((k : ℝ) + 1)) ≤
      4 * Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) := by
  have hlog := log_add_one_le_two_log hk
  have hinside : 2 * (n : ℝ) * Real.log ((k : ℝ) + 1) ≤
      4 * ((n : ℝ) * Real.log (k : ℝ)) := by
    calc
      _ ≤ 2 * (n : ℝ) * (2 * Real.log (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 2 * Real.sqrt (4 * ((n : ℝ) * Real.log (k : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinside) (by norm_num)
    _ = 4 * Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) := by
      have hfour : Real.sqrt (4 : ℝ) = 2 := by
        have h := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
        norm_num at h
        exact h
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hfour]
      ring

/-- Proposition 3 with an explicit universal constant: a union of `k ≥ 2`
unate functions has average sensitivity at most `4 * sqrt (n * log k)`. -/
theorem unate_union_averageSensitivity_le_log {n : ℕ}
    (fs : List (UnateFunction n)) (hk : 2 ≤ fs.length) :
    averageSensitivity (union fs) ≤
      4 * Real.sqrt ((n : ℝ) * Real.log (fs.length : ℝ)) :=
  (unate_union_averageSensitivity_le fs).trans (sqrt_log_add_one_bound n fs.length hk)

/-- Theorem 1 in its stated asymptotic form, with the explicit universal
constant `4`: intersections of `k ≥ 2` affine halfspaces have sensitivity at
most `4 * sqrt (n * log k)`. -/
theorem halfspaces_averageSensitivity_le_log {n : ℕ}
    (hs : List (Halfspace n)) (hk : 2 ≤ hs.length) :
    averageSensitivity (intersection hs) ≤
      4 * Real.sqrt ((n : ℝ) * Real.log (hs.length : ℝ)) :=
  (halfspaces_averageSensitivity_le hs).trans (sqrt_log_add_one_bound n hs.length hk)

end Kane
