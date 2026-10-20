import Kane.BlockRestriction
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! The finite probability law in the signed-block noise construction. -/

open scoped BigOperators

namespace Kane

/-- Flip exactly the coordinates selected by a Boolean mask. -/
def maskedFlip {n : ℕ} (mask x : Cube n) : Cube n :=
  fun i => if mask i then !(x i) else x i

/-- The independent Bernoulli weight of a coordinate-flip mask. -/
def maskWeight {n : ℕ} (θ : ℝ) (mask : Cube n) : ℝ :=
  ∏ i, if mask i then θ else 1 - θ

/-- Noise sensitivity under independent coordinate flips with probability `θ`.
This finite weighted sum is meaningful for every real `θ`, and is a probability
when `0 ≤ θ ≤ 1`. -/
noncomputable def noiseSensitivity {n : ℕ} (f : Cube n → Bool) (θ : ℝ) : ℝ :=
  avg fun x => ∑ mask : Cube n, maskWeight θ mask *
    (if f x = f (maskedFlip mask x) then (0 : ℝ) else 1)

/-- The independent mask weights have total mass one. -/
theorem maskWeight_sum {n : ℕ} (θ : ℝ) :
    (∑ mask : Cube n, maskWeight θ mask) = 1 := by
  calc
    _ = ∏ _ : Fin n, ∑ b : Bool, if b then θ else 1 - θ :=
      (Fintype.prod_sum (fun _ : Fin n => fun b : Bool => if b then θ else 1 - θ)).symm
    _ = 1 := by simp

/-- Each independent mask has nonnegative weight at every probability rate. -/
theorem maskWeight_nonneg {n : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (mask : Cube n) : 0 ≤ maskWeight θ mask := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact hθ
  · linarith

/-- Noise sensitivity is a nonnegative probability. -/
theorem noiseSensitivity_nonneg {n : ℕ} (f : Cube n → Bool) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) : 0 ≤ noiseSensitivity f θ := by
  apply avg_nonneg
  intro x
  apply Finset.sum_nonneg
  intro mask _
  apply mul_nonneg (maskWeight_nonneg hθ hθone mask)
  split_ifs <;> norm_num

/-- A disagreement probability is at most one. -/
theorem noiseSensitivity_le_one {n : ℕ} (f : Cube n → Bool) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθone : θ ≤ 1) : noiseSensitivity f θ ≤ 1 := by
  calc
    _ ≤ avg (fun _ : Cube n => ∑ mask : Cube n, maskWeight θ mask) := by
      apply avg_mono
      intro x
      apply Finset.sum_le_sum
      intro mask _
      exact mul_le_of_le_one_right (maskWeight_nonneg hθ hθone mask)
        (by split_ifs <;> norm_num)
    _ = 1 := by simp [maskWeight_sum]

/-- At noise rate zero only the empty flip mask has positive mass. -/
theorem maskWeight_zero {n : ℕ} (mask : Cube n) :
    maskWeight 0 mask = if mask = (fun _ => false) then 1 else 0 := by
  unfold maskWeight
  have hcoord (i : Fin n) :
      (if mask i then (0 : ℝ) else 1 - 0) = if mask i = false then 1 else 0 := by
    cases mask i <;> norm_num
  simp_rw [hcoord]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one]
  congr 1
  exact propext funext_iff.symm

@[simp] theorem noiseSensitivity_zero {n : ℕ} (f : Cube n → Bool) :
    noiseSensitivity f 0 = 0 := by
  unfold noiseSensitivity
  simp only [maskWeight_zero, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hmask (x : Cube n) : maskedFlip (fun _ => false) x = x := rfl
  simp only [hmask, ite_true, avg_zero]

@[simp] theorem noiseSensitivity_const {n : ℕ} (b : Bool) (θ : ℝ) :
    noiseSensitivity (fun _ : Cube n => b) θ = 0 := by
  simp [noiseSensitivity]

/-- A coordinate belongs to the selected block exactly when its assignment
equals that block's index. -/
def blockMask {n m : ℕ} (assignment : Fin n → Fin m) (j : Fin m) : Cube n :=
  fun i => decide (assignment i = j)

theorem product_pushforward {n : ℕ} {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → β) (w : α → ℝ) (H : (Fin n → β) → ℝ) :
    (∑ a : Fin n → α, (∏ i, w (a i)) * H (fun i => p (a i))) =
      ∑ b : Fin n → β, (∏ i, ∑ a : α, if p a = b i then w a else 0) * H b := by
  classical
  have hdelta (a : Fin n → α) (b : Fin n → β) :
      (∏ i, if p (a i) = b i then w (a i) else 0) =
        if (fun i => p (a i)) = b then ∏ i, w (a i) else 0 := by
    rw [Fintype.prod_ite_zero]
    congr 1
    exact propext funext_iff.symm
  calc
    _ = ∑ a : Fin n → α, ∑ b : Fin n → β,
        (∏ i, if p (a i) = b i then w (a i) else 0) * H b := by
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [hdelta]
      simp only [ite_mul, zero_mul]
      simp
    _ = ∑ b : Fin n → β,
        (∑ a : Fin n → α, ∏ i, if p (a i) = b i then w (a i) else 0) * H b := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      exact (Fintype.prod_sum (fun i a => if p a = b i then w a else (0 : ℝ))).symm

private theorem uniform_block_mass {m : ℕ} (hm : 0 < m) (j : Fin m) (b : Bool) :
    (∑ a : Fin m, if decide (a = j) = b then (m : ℝ)⁻¹ else 0) =
      if b then (m : ℝ)⁻¹ else 1 - (m : ℝ)⁻¹ := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  cases b with
  | true => simp
  | false =>
      have hh (a : Fin m) :
          (if decide (a = j) = false then (m : ℝ)⁻¹ else 0) =
            (m : ℝ)⁻¹ - if a = j then (m : ℝ)⁻¹ else 0 := by
        by_cases ha : a = j <;> simp [ha]
      simp_rw [hh]
      simp [Finset.sum_sub_distrib, hmne]

/-- Independent uniform assignment of each coordinate to a block produces an
independent Bernoulli `1/m` mask for every fixed selected block. -/
theorem avg_blockMask {n m : ℕ} (hm : 0 < m) (j : Fin m) (H : Cube n → ℝ) :
    avg (fun assignment : Fin n → Fin m => H (blockMask assignment j)) =
      ∑ mask : Cube n, maskWeight ((m : ℝ)⁻¹) mask * H mask := by
  have hp := product_pushforward (n := n) (fun a : Fin m => decide (a = j))
    (fun _ => (m : ℝ)⁻¹) H
  simp_rw [uniform_block_mass hm j] at hp
  simpa only [avg, blockMask, maskWeight, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, inv_pow, Finset.prod_const, Finset.card_univ, Finset.mul_sum] using hp

theorem avg_commute {α β : Type*} [Fintype α] [Fintype β]
    (H : α → β → ℝ) :
    avg (fun a => avg (H a)) = avg (fun b => avg (fun a => H a b)) := by
  unfold avg
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

private theorem blockRestriction_signs_involutive {n m : ℕ}
    (assignment : Fin n → Fin m) (b : Cube m) :
    Function.Involutive (fun signs => blockRestriction assignment signs b) := by
  intro signs
  funext i
  cases hs : signs i <;> cases hb : b (assignment i) <;>
    simp [blockRestriction, hs, hb]

theorem avg_blockRestriction_signs {n m : ℕ}
    (assignment : Fin n → Fin m) (b : Cube m) (H : Cube n → ℝ) :
    avg (fun signs => H (blockRestriction assignment signs b)) = avg H := by
  let e : Cube n ≃ Cube n :=
    { toFun := fun signs => blockRestriction assignment signs b
      invFun := fun signs => blockRestriction assignment signs b
      left_inv := blockRestriction_signs_involutive assignment b
      right_inv := blockRestriction_signs_involutive assignment b }
  unfold avg
  congr 1
  exact e.sum_comp H

/-- Flipping one block bit flips exactly the coordinates assigned to that block. -/
theorem blockRestriction_flip {n m : ℕ} (assignment : Fin n → Fin m)
    (signs : Cube n) (b : Cube m) (j : Fin m) :
    blockRestriction assignment signs (flip b j) =
      maskedFlip (blockMask assignment j) (blockRestriction assignment signs b) := by
  funext i
  by_cases hi : assignment i = j
  · cases hs : signs i <;> cases hb : b j <;>
      simp [blockRestriction, blockMask, maskedFlip, flip, hi, hs, hb] <;>
      rw [hi] <;> simp
  · simp [blockRestriction, blockMask, maskedFlip, flip, hi]

private theorem avg_signs_oneBlockDisagreement {n m : ℕ} (f : Cube n → Bool)
    (assignment : Fin n → Fin m) :
    avg (fun signs => uniformOneBlockDisagreement
      (fun b => f (blockRestriction assignment signs b))) =
    avg (fun j : Fin m => avg (fun x =>
      if f x = f (maskedFlip (blockMask assignment j) x) then (0 : ℝ) else 1)) := by
  unfold uniformOneBlockDisagreement
  calc
    _ = avg (fun b : Cube m => avg (fun j : Fin m => avg (fun signs =>
        if f (blockRestriction assignment signs b) =
            f (blockRestriction assignment signs (flip b j)) then (0 : ℝ) else 1))) := by
      rw [avg_commute]
      apply avg_congr
      intro b
      exact avg_commute _
    _ = avg (fun _ : Cube m => avg (fun j : Fin m => avg (fun x =>
        if f x = f (maskedFlip (blockMask assignment j) x) then (0 : ℝ) else 1))) := by
      apply avg_congr
      intro b
      apply avg_congr
      intro j
      simp_rw [blockRestriction_flip]
      exact avg_blockRestriction_signs assignment b
        (fun x => if f x = f (maskedFlip (blockMask assignment j) x) then (0 : ℝ) else 1)
    _ = _ := avg_const _

/-- The signed-block construction produces exactly the same law as independent
coordinate noise of rate `1/m`, without a distributional assumption. -/
theorem blockNoiseConstruction_eq_noiseSensitivity {n m : ℕ} (hm : 0 < m)
    (f : Cube n → Bool) :
    avg (fun assignment : Fin n → Fin m => avg (fun signs : Cube n =>
      uniformOneBlockDisagreement (fun b => f (blockRestriction assignment signs b)))) =
        noiseSensitivity f ((m : ℝ)⁻¹) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  simp_rw [avg_signs_oneBlockDisagreement]
  rw [avg_commute]
  calc
    _ = avg (fun j : Fin m => avg (fun x : Cube n =>
        avg (fun assignment : Fin n → Fin m =>
          if f x = f (maskedFlip (blockMask assignment j) x) then (0 : ℝ) else 1))) := by
      apply avg_congr
      intro j
      exact avg_commute _
    _ = avg (fun _ : Fin m => noiseSensitivity f ((m : ℝ)⁻¹)) := by
      apply avg_congr
      intro j
      unfold noiseSensitivity
      apply avg_congr
      intro x
      exact avg_blockMask (n := n) hm j
        (fun mask => if f x = f (maskedFlip mask x) then (0 : ℝ) else 1)
    _ = _ := avg_const _

/-- Corollary 4 at reciprocal integer noise rates, with an explicit constant.
The identity above links this bound to independent coordinate flips. -/
theorem halfspaces_noiseSensitivity_reciprocal_le {n m : ℕ} (hm : 0 < m)
    (hs : List (Halfspace n)) :
    noiseSensitivity (intersection hs) ((m : ℝ)⁻¹) ≤
      2 * Real.sqrt (2 * Real.log ((hs.length : ℝ) + 1) / (m : ℝ)) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [← blockNoiseConstruction_eq_noiseSensitivity hm]
  calc
    _ ≤ avg (fun _ : Fin n → Fin m => avg (fun _ : Cube n =>
        2 * Real.sqrt (2 * Real.log ((hs.length : ℝ) + 1) / (m : ℝ)))) := by
      apply avg_mono
      intro assignment
      apply avg_mono
      intro signs
      exact blockRestriction_uniformOneBlockDisagreement_le hs assignment signs hm
    _ = _ := by simp

end Kane
