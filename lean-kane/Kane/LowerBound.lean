import Kane.Lower.Construction
import Kane.Lower.Tail
import Kane.Lower.Parity

/-! Kane's matching average-sensitivity lower bound. The constant is independent
of both dimension and family size. All estimates, including the halfspace tail
and the random-sign amplification, are proved in the imported finite modules. -/

namespace Kane

/-- One explicit universal constant for the matching lower bound. -/
noncomputable def lowerBoundConstant : ℝ :=
  min (1 / 512) (Real.exp (-2) * Real.log (9 / 8 : ℝ) / 64)

theorem lowerBoundConstant_pos : 0 < lowerBoundConstant := by
  have hlog := Lower.log_nine_eighths_pos
  unfold lowerBoundConstant
  exact lt_min (by norm_num) (by positivity)

private theorem log_count_le_dimension {n k : ℕ} (hk : 1 ≤ k) (hkmax : k ≤ 2 ^ n) :
    Real.log (k : ℝ) ≤ (n : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt hk
  have hcast : (k : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hkmax
  have hlog : Real.log (k : ℝ) ≤ (n : ℝ) * Real.log 2 := by
    calc
      _ ≤ Real.log ((2 : ℝ) ^ n) := Real.log_le_log hkpos hcast
      _ = _ := Real.log_pow _ _
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  nlinarith [mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The matching lower bound with an explicit fixed positive constant. The
range includes `k = 1`, `n = 0`, and `k = 2^n`. -/
theorem halfspaces_averageSensitivity_lower_bound_explicit (n k : ℕ)
    (hk : 1 ≤ k) (hkmax : k ≤ 2 ^ n) :
    ∃ hs : List (Halfspace n), hs.length ≤ k ∧
      lowerBoundConstant * Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) ≤
        averageSensitivity (intersection hs) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨[], by simp, ?_⟩
    simp [averageSensitivity, avg]
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  have hL : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  by_cases hsmall : Real.log (k : ℝ) ≤ 64
  · obtain ⟨a, ha, hp⟩ := Lower.small_halfspace_witness hn
    let h := Lower.uniformHalfspace n a
    have hlogpos := Lower.log_nine_eighths_pos
    have ha0 : 0 ≤ Real.log (9 / 8 : ℝ) * Real.sqrt (n : ℝ) := by
      positivity
    have hp0 : 0 ≤ Real.exp (-2) / 16 := by positivity
    have hbound := Lower.uniformHalfspace_averageSensitivity_ge n a
    have hprod :
        2 * (Real.log (9 / 8 : ℝ) * Real.sqrt (n : ℝ)) * (Real.exp (-2) / 16) ≤
          averageSensitivity h.indicator := by
      exact (mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hp hp0
        (by linarith : 0 ≤ 2 * a)).trans hbound
    have hroot : Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) ≤ 8 * Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n)]
      have hlogroot : Real.sqrt (Real.log (k : ℝ)) ≤ 8 :=
        Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
      nlinarith [mul_le_mul_of_nonneg_left hlogroot (Real.sqrt_nonneg (n : ℝ))]
    refine ⟨[h], by simpa using hk, ?_⟩
    simp only [intersection, Bool.and_true]
    calc
      _ ≤ (Real.exp (-2) * Real.log (9 / 8 : ℝ) / 64) *
          Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
      _ ≤ (Real.exp (-2) * Real.log (9 / 8 : ℝ) / 64) *
          (8 * Real.sqrt (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hroot
        positivity
      _ = 2 * (Real.log (9 / 8 : ℝ) * Real.sqrt (n : ℝ)) *
          (Real.exp (-2) / 16) := by ring
      _ ≤ _ := hprod
  · have hlarge : 64 ≤ Real.log (k : ℝ) := le_of_lt (lt_of_not_ge hsmall)
    obtain ⟨a, ha, hp⟩ := Lower.large_halfspace_witness hn hlarge
      (log_count_le_dimension hk hkmax)
    have ha0 : 0 ≤ a := (div_nonneg (Real.sqrt_nonneg _) (by norm_num)).trans ha
    have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt hk
    have hexp : Real.exp (-Real.log (k : ℝ)) = 1 / (k : ℝ) := by
      rw [Real.exp_neg, Real.exp_log hkpos, one_div]
    rw [hexp] at hp
    obtain ⟨hs, hlen, hbound⟩ := Lower.exists_intersection_of_mass_and_sensitivity
      (Lower.uniformHalfspace n a) a hk ha0 hp
      (Lower.uniformHalfspace_averageSensitivity_ge n a)
    refine ⟨hs, hlen, ?_⟩
    calc
      _ ≤ (1 / 512 : ℝ) * Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
      _ = (Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) / 64) / 8 := by ring
      _ ≤ a / 8 := div_le_div_of_nonneg_right ha (by norm_num)
      _ ≤ _ := hbound

/-- Kane's Theorem 2: one absolute positive constant works for every dimension
and every family budget in `1 ≤ k ≤ 2^n`. No tail lemma is assumed. -/
theorem halfspaces_averageSensitivity_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ 2 ^ n →
      ∃ hs : List (Halfspace n), hs.length ≤ k ∧
        c * Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) ≤
          averageSensitivity (intersection hs) :=
  ⟨lowerBoundConstant, lowerBoundConstant_pos,
    halfspaces_averageSensitivity_lower_bound_explicit⟩

end Kane
