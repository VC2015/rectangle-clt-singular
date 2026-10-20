import Kane.NoiseSensitivity
import Kane.LogBound

/-! General noise rates via weighted assignment to active blocks and one
additional block that is never selected for a flip. -/

open scoped BigOperators

namespace Kane

/-- Every active block has mass `θ`; the last block receives the remaining
mass. It is not selected when testing disagreement. -/
def blockAssignmentWeight (m : ℕ) (θ : ℝ) (a : Fin (m + 1)) : ℝ :=
  if a = Fin.last m then 1 - (m : ℝ) * θ else θ

theorem blockAssignmentWeight_sum (m : ℕ) (θ : ℝ) :
    (∑ a : Fin (m + 1), blockAssignmentWeight m θ a) = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [blockAssignmentWeight]

theorem blockAssignmentWeight_nonneg {m : ℕ} {θ : ℝ}
    (hθ : 0 ≤ θ) (hmθ : (m : ℝ) * θ ≤ 1) (a : Fin (m + 1)) :
    0 ≤ blockAssignmentWeight m θ a := by
  unfold blockAssignmentWeight
  split_ifs
  · linarith
  · exact hθ

private theorem blockAssignment_mass (m : ℕ) (θ : ℝ) (j : Fin m) (b : Bool) :
    (∑ a : Fin (m + 1), if decide (a = j.castSucc) = b then
      blockAssignmentWeight m θ a else 0) = if b then θ else 1 - θ := by
  have hj : blockAssignmentWeight m θ j.castSucc = θ := by
    simp [blockAssignmentWeight]
  cases b with
  | true => simpa using hj
  | false =>
      have hh (a : Fin (m + 1)) :
          (if decide (a = j.castSucc) = false then blockAssignmentWeight m θ a else 0) =
            blockAssignmentWeight m θ a -
              if a = j.castSucc then blockAssignmentWeight m θ a else 0 := by
        by_cases ha : a = j.castSucc <;> simp [ha]
      simp_rw [hh]
      simp [Finset.sum_sub_distrib, blockAssignmentWeight_sum, hj]

/-- The weighted assignment gives independent coordinate noise of rate `θ`
for every fixed selected active block. -/
theorem weighted_blockMask {n m : ℕ} (θ : ℝ) (j : Fin m) (H : Cube n → ℝ) :
    (∑ assignment : Fin n → Fin (m + 1),
      (∏ i, blockAssignmentWeight m θ (assignment i)) *
        H (blockMask assignment j.castSucc)) =
      ∑ mask : Cube n, maskWeight θ mask * H mask := by
  have hp := product_pushforward (n := n)
    (fun a : Fin (m + 1) => decide (a = j.castSucc)) (blockAssignmentWeight m θ) H
  simp_rw [blockAssignment_mass m θ j] at hp
  exact hp

private theorem weighted_sum_avg {α β : Type*} [Fintype α] [Fintype β]
    (w : α → ℝ) (H : α → β → ℝ) :
    (∑ a, w a * avg (H a)) = avg (fun b => ∑ a, w a * H a b) := by
  rw [avg_sum]
  simp_rw [avg_const_mul]

private theorem blockAssignment_product_sum (n m : ℕ) (θ : ℝ) :
    (∑ assignment : Fin n → Fin (m + 1),
      ∏ i, blockAssignmentWeight m θ (assignment i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp only [blockAssignmentWeight_sum, Finset.prod_const_one]

/-- Average disagreement when choosing uniformly among the first `m` of the
`m+1` block bits. -/
noncomputable def activeBlockDisagreement {m : ℕ} (f : Cube (m + 1) → Bool) : ℝ :=
  avg fun b => avg fun j : Fin m =>
    if f b = f (flip b j.castSucc) then (0 : ℝ) else 1

private theorem avg_signs_activeBlockDisagreement {n m : ℕ} (f : Cube n → Bool)
    (assignment : Fin n → Fin (m + 1)) :
    avg (fun signs => activeBlockDisagreement
      (fun b => f (blockRestriction assignment signs b))) =
    avg (fun j : Fin m => avg (fun x =>
      if f x = f (maskedFlip (blockMask assignment j.castSucc) x) then (0 : ℝ) else 1)) := by
  unfold activeBlockDisagreement
  calc
    _ = avg (fun b : Cube (m + 1) => avg (fun j : Fin m => avg (fun signs =>
        if f (blockRestriction assignment signs b) =
            f (blockRestriction assignment signs (flip b j.castSucc)) then (0 : ℝ) else 1))) := by
      rw [avg_commute]
      apply avg_congr
      intro b
      exact avg_commute _
    _ = avg (fun _ : Cube (m + 1) => avg (fun j : Fin m => avg (fun x =>
        if f x = f (maskedFlip (blockMask assignment j.castSucc) x) then (0 : ℝ) else 1))) := by
      apply avg_congr
      intro b
      apply avg_congr
      intro j
      simp_rw [blockRestriction_flip]
      exact avg_blockRestriction_signs assignment b
        (fun x => if f x = f (maskedFlip (blockMask assignment j.castSucc) x) then (0 : ℝ) else 1)
    _ = _ := avg_const _

/-- The active-block construction realizes independent noise at any real rate;
nonnegative normalized weights are used separately when bounding it. -/
theorem weightedBlockConstruction_eq_noiseSensitivity {n m : ℕ} (hm : 0 < m)
    (f : Cube n → Bool) (θ : ℝ) :
    (∑ assignment : Fin n → Fin (m + 1),
      (∏ i, blockAssignmentWeight m θ (assignment i)) *
        avg (fun signs => activeBlockDisagreement
          (fun b => f (blockRestriction assignment signs b)))) = noiseSensitivity f θ := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  simp_rw [avg_signs_activeBlockDisagreement]
  rw [weighted_sum_avg]
  calc
    _ = avg (fun j : Fin m => avg (fun x : Cube n =>
        ∑ assignment : Fin n → Fin (m + 1),
          (∏ i, blockAssignmentWeight m θ (assignment i)) *
            if f x = f (maskedFlip (blockMask assignment j.castSucc) x) then (0 : ℝ) else 1)) := by
      apply avg_congr
      intro j
      exact weighted_sum_avg _ _
    _ = avg (fun _ : Fin m => noiseSensitivity f θ) := by
      apply avg_congr
      intro j
      unfold noiseSensitivity
      apply avg_congr
      intro x
      exact weighted_blockMask θ j
        (fun mask => if f x = f (maskedFlip mask x) then (0 : ℝ) else 1)
    _ = _ := avg_const _

theorem activeBlockDisagreement_le {m : ℕ} (f : Cube (m + 1) → Bool) :
    activeBlockDisagreement f ≤ averageSensitivity f / (m : ℝ) := by
  have hsum (b : Cube (m + 1)) :
      (∑ j : Fin m, if f b = f (flip b j.castSucc) then (0 : ℝ) else 1) ≤
        ∑ j : Fin (m + 1), if f b = f (flip b j) then (0 : ℝ) else 1 := by
    rw [Fin.sum_univ_castSucc]
    have hnonneg : (0 : ℝ) ≤ if f b = f (flip b (Fin.last m)) then 0 else 1 := by
      split_ifs <;> norm_num
    linarith
  have havg := avg_mono hsum
  have hscale := mul_le_mul_of_nonneg_left havg (inv_nonneg.mpr (Nat.cast_nonneg m))
  simpa only [activeBlockDisagreement, avg, Fintype.card_fin, ← Finset.mul_sum,
    averageSensitivity, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using hscale

/-- A weighted signed-block restriction bounds noise sensitivity by the
sensitivity in `m+1` dimensions, divided by the number of active blocks. -/
theorem halfspaces_noiseSensitivity_blocks_le {n m : ℕ} (hm : 0 < m)
    (hs : List (Halfspace n)) (θ : ℝ) (hθ : 0 ≤ θ) (hmθ : (m : ℝ) * θ ≤ 1) :
    noiseSensitivity (intersection hs) θ ≤
      (2 * Real.sqrt (2 * ((m : ℝ) + 1) * Real.log ((hs.length : ℝ) + 1))) / (m : ℝ) := by
  let C := (2 * Real.sqrt (2 * ((m : ℝ) + 1) * Real.log ((hs.length : ℝ) + 1))) / (m : ℝ)
  rw [← weightedBlockConstruction_eq_noiseSensitivity hm]
  calc
    _ ≤ ∑ assignment : Fin n → Fin (m + 1),
        (∏ i, blockAssignmentWeight m θ (assignment i)) * C := by
      apply Finset.sum_le_sum
      intro assignment _
      apply mul_le_mul_of_nonneg_left _
        (Finset.prod_nonneg fun i _ => blockAssignmentWeight_nonneg hθ hmθ (assignment i))
      calc
        _ ≤ avg (fun _ : Cube n => C) := by
          apply avg_mono
          intro signs
          calc
            _ ≤ averageSensitivity
                (fun b => intersection hs (blockRestriction assignment signs b)) / (m : ℝ) :=
              activeBlockDisagreement_le _
            _ ≤ C := by
              apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
              simpa only [Nat.cast_add, Nat.cast_one] using
                blockRestriction_averageSensitivity_le hs assignment signs
        _ = C := avg_const C
    _ = C := by
      rw [← Finset.sum_mul, blockAssignment_product_sum]
      ring

private theorem blocks_to_noise_bound (m : ℕ) (hm : 0 < m) (θ L : ℝ)
    (hθ : 0 ≤ θ) (hL : 0 ≤ L) (hinv : 1 ≤ 2 * θ * (m : ℝ)) :
    (2 * Real.sqrt (2 * ((m : ℝ) + 1) * L)) / (m : ℝ) ≤
      4 * Real.sqrt (2 * θ * L) := by
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdim : (m : ℝ) + 1 ≤ 2 * m := by linarith
  have hscale : 2 * (m : ℝ) ≤ 4 * θ * (m : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 2 * m)
    nlinarith
  have hinside : 2 * ((m : ℝ) + 1) * L ≤
      (2 * (m : ℝ)) ^ 2 * (2 * θ * L) := by
    have hh := mul_le_mul_of_nonneg_right (hdim.trans hscale)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)
    nlinarith
  calc
    _ ≤ (2 * Real.sqrt ((2 * (m : ℝ)) ^ 2 * (2 * θ * L))) / (m : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinside) (by norm_num)) hmreal.le
    _ = 4 * Real.sqrt (2 * θ * L) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * m)]
      field_simp
      ring

/-- Corollary 4 for every independent coordinate-flip rate `0 < θ ≤ 1`,
with a universal explicit constant and an endpoint-safe logarithm.
Weighted assignment to an extra inactive block avoids a monotonicity argument. -/
theorem halfspaces_noiseSensitivity_le {n : ℕ} (hs : List (Halfspace n))
    (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    noiseSensitivity (intersection hs) θ ≤
      4 * Real.sqrt (2 * θ * Real.log ((hs.length : ℝ) + 1)) := by
  let m := Nat.floor θ⁻¹
  have ht : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).mpr hθone
  have hmone : 1 ≤ m := Nat.le_floor (by simpa using ht)
  have hm : 0 < m := Nat.zero_lt_of_lt hmone
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hmone
  have hmle : (m : ℝ) ≤ θ⁻¹ := Nat.floor_le (inv_nonneg.mpr hθ.le)
  have hmθ : (m : ℝ) * θ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hmle hθ.le
    simpa [ne_of_gt hθ] using hh
  have hfloor : θ⁻¹ < (m : ℝ) + 1 := Nat.lt_floor_add_one θ⁻¹
  have hinv : 1 ≤ 2 * θ * (m : ℝ) := by
    have hh := mul_lt_mul_of_pos_right hfloor hθ
    have hcancel : θ⁻¹ * θ = 1 := inv_mul_cancel₀ (ne_of_gt hθ)
    rw [hcancel] at hh
    nlinarith
  have hL : 0 ≤ Real.log ((hs.length : ℝ) + 1) :=
    Real.log_nonneg (by have hh : (0 : ℝ) ≤ hs.length := Nat.cast_nonneg _; linarith)
  exact (halfspaces_noiseSensitivity_blocks_le hm hs θ hθ.le hmθ).trans
    (blocks_to_noise_bound m hm θ _ hθ.le hL hinv)

/-- Corollary 4 in its literal logarithmic form for at least two halfspaces. -/
theorem halfspaces_noiseSensitivity_le_log {n : ℕ} (hs : List (Halfspace n))
    (hk : 2 ≤ hs.length) (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    noiseSensitivity (intersection hs) θ ≤
      8 * Real.sqrt (θ * Real.log (hs.length : ℝ)) := by
  have hinside : 2 * θ * Real.log ((hs.length : ℝ) + 1) ≤
      4 * (θ * Real.log (hs.length : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left (log_add_one_le_two_log hk)
      (by positivity : 0 ≤ 2 * θ)
    nlinarith
  have hfour : Real.sqrt (4 : ℝ) = 2 := by
    have hh := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at hh
    exact hh
  calc
    _ ≤ 4 * Real.sqrt (2 * θ * Real.log ((hs.length : ℝ) + 1)) :=
      halfspaces_noiseSensitivity_le hs θ hθ hθone
    _ ≤ 4 * Real.sqrt (4 * (θ * Real.log (hs.length : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinside) (by norm_num)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hfour]
      ring

end Kane
