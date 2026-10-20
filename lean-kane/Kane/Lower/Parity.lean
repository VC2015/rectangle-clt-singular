import Kane.Halfspace
import Mathlib.Data.Finset.Fold

/-!
Concrete parity witnesses for the large-family endpoint of Kane's lower bound.
Every excluded vertex is removed by one closed affine halfspace.
-/

open scoped BigOperators

namespace Kane.Lower

noncomputable section

/-- A closed halfspace containing every cube vertex except `v`. -/
def excludeVertex {n : ℕ} (v : Cube n) : Halfspace n where
  weights i := if v i then -1 else 1
  threshold := 1 - (n : ℝ)

theorem excludeVertex_score {n : ℕ} (v x : Cube n) :
    (excludeVertex v).score x = ∑ i, if x i = v i then (-1 : ℝ) else 1 := by
  apply Finset.sum_congr rfl
  intro i _
  cases hv : v i <;> cases hx : x i <;> norm_num [excludeVertex, Halfspace.score, hv, hx]

theorem excludeVertex_indicator {n : ℕ} (v x : Cube n) :
    (excludeVertex v).indicator x = decide (x ≠ v) := by
  classical
  by_cases h : x = v
  · subst x
    have hs : (excludeVertex v).score v = -(n : ℝ) := by
      rw [excludeVertex_score]
      simp
    have hn : ¬ (1 - (n : ℝ) ≤ -(n : ℝ)) := by linarith
    rw [show decide (v ≠ v) = false by simp]
    change decide (1 - (n : ℝ) ≤ (excludeVertex v).score v) = false
    rw [hs]
    simp [hn]
  · obtain ⟨i, hi⟩ := not_forall.mp
      (show ¬ ∀ i, x i = v i from fun hh => h (funext hh))
    let t : Fin n → ℝ := fun j => if x j = v j then -1 else 1
    have hrest : -((Finset.univ.erase i).card : ℝ) ≤
        ∑ j ∈ Finset.univ.erase i, t j := by
      calc
        _ = ∑ _j ∈ Finset.univ.erase i, (-1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun j _ => by
          dsimp [t]
          split_ifs <;> norm_num
    have hcard : ((Finset.univ.erase i).card : ℝ) + 1 = (n : ℝ) := by
      have hh : (Finset.univ.erase i).card + 1 = n := by
        simpa using Finset.card_erase_add_one (Finset.mem_univ i)
      exact_mod_cast hh
    have hsum : (∑ j ∈ Finset.univ.erase i, t j) + t i = ∑ j, t j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have hti : t i = 1 := by simp [t, hi]
    have hs : (excludeVertex v).threshold ≤ (excludeVertex v).score x := by
      rw [excludeVertex_score]
      change 1 - (n : ℝ) ≤ ∑ j, t j
      linarith
    simp [Halfspace.indicator, hs, h]

/-- The vertex exclusions represent an arbitrary Boolean truth table exactly. -/
def vertexExclusionHalfspaces {n : ℕ} (f : Cube n → Bool) : List (Halfspace n) := by
  classical
  exact ((Finset.univ.filter fun v => f v = false).toList.map excludeVertex)

private theorem intersection_eq_true_iff {n : ℕ} (hs : List (Halfspace n))
    (x : Cube n) : intersection hs x = true ↔ ∀ h ∈ hs, h.indicator x = true := by
  induction hs with
  | nil => simp [intersection]
  | cons h hs ih => simp [intersection, ih]

theorem intersection_vertexExclusionHalfspaces {n : ℕ} (f : Cube n → Bool) :
    intersection (vertexExclusionHalfspaces f) = f := by
  classical
  funext x
  have hiff : intersection (vertexExclusionHalfspaces f) x = true ↔ f x = true := by
    rw [intersection_eq_true_iff]
    constructor
    · intro hall
      cases hf : f x with
      | false =>
          have hm : excludeVertex x ∈ vertexExclusionHalfspaces f := by
            unfold vertexExclusionHalfspaces
            exact List.mem_map.mpr ⟨x, by simp [hf], rfl⟩
          have hh := hall (excludeVertex x) hm
          simp [excludeVertex_indicator] at hh
      | true => rfl
    · intro hfx h hh
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hh
      have hvf : f v = false := by
        exact (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
      have hxv : x ≠ v := by
        intro heq
        subst v
        simp_all
      simp [excludeVertex_indicator, hxv]
  cases hi : intersection (vertexExclusionHalfspaces f) x <;>
    cases hf : f x <;> simp_all

theorem vertexExclusionHalfspaces_length {n : ℕ} (f : Cube n → Bool) :
    (vertexExclusionHalfspaces f).length =
      (Finset.univ.filter fun v : Cube n => f v = false).card := by
  classical
  simp [vertexExclusionHalfspaces]

theorem vertexExclusionHalfspaces_length_le {n : ℕ} (f : Cube n → Bool) :
    (vertexExclusionHalfspaces f).length ≤ 2 ^ n := by
  classical
  rw [vertexExclusionHalfspaces_length]
  calc
    _ ≤ Fintype.card (Cube n) := Finset.card_filter_le _ _
    _ = 2 ^ n := by simp [Cube, Fintype.card_fun]

local instance : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩
local instance : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩

/-- Boolean parity, false at the all-false vertex. -/
def parity {n : ℕ} (x : Cube n) : Bool := Finset.univ.fold Bool.xor false x

theorem parity_flip {n : ℕ} (x : Cube n) (i : Fin n) :
    parity (flip x i) = !parity x := by
  classical
  have hu : insert i (Finset.univ.erase i) = (Finset.univ : Finset (Fin n)) :=
    Finset.insert_erase (Finset.mem_univ i)
  have hfold : (Finset.univ.erase i).fold Bool.xor false (flip x i) =
      (Finset.univ.erase i).fold Bool.xor false x := by
    apply Finset.fold_congr
    intro j hj
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  unfold parity
  rw [← hu, Finset.fold_insert (Finset.not_mem_erase i _),
    Finset.fold_insert (Finset.not_mem_erase i _), hfold]
  simp only [flip, Function.update_self]
  cases x i <;> cases (Finset.univ.erase i).fold Bool.xor false x <;> rfl

theorem parity_averageSensitivity (n : ℕ) :
    averageSensitivity (parity : Cube n → Bool) = (n : ℝ) := by
  have hp (x : Cube n) :
      (∑ i : Fin n, if parity x = parity (flip x i) then (0 : ℝ) else 1) = n := by
    simp_rw [parity_flip]
    cases parity x <;> simp
  unfold averageSensitivity
  calc
    _ = avg (fun _ : Cube n => (n : ℝ)) := avg_congr hp
    _ = n := avg_const _

theorem parity_false_card_eq_true {n : ℕ} (i : Fin n) :
    (Finset.univ.filter fun x : Cube n => parity x = false).card =
      (Finset.univ.filter fun x : Cube n => parity x = true).card := by
  classical
  let e : Cube n ≃ Cube n :=
    { toFun := fun x => flip x i
      invFun := fun x => flip x i
      left_inv := fun x => flip_flip x i
      right_inv := fun x => flip_flip x i }
  apply Finset.card_equiv e
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change parity x = false ↔ parity (flip x i) = true
  rw [parity_flip]
  cases parity x <;> simp

theorem parity_twice_false_card {n : ℕ} (i : Fin n) :
    2 * (Finset.univ.filter fun x : Cube n => parity x = false).card = 2 ^ n := by
  classical
  have heq := parity_false_card_eq_true i
  have hp := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Cube n))) (fun x => parity x = true)
  simp only [Bool.not_eq_true] at hp
  rw [← heq] at hp
  simpa [two_mul, Cube, Fintype.card_fun] using hp

theorem parity_false_card {n : ℕ} (hn : 0 < n) :
    (Finset.univ.filter fun x : Cube n => parity x = false).card = 2 ^ (n - 1) := by
  classical
  have hp := parity_twice_false_card (⟨0, hn⟩ : Fin n)
  have he : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]
      _ = 2 * 2 ^ (n - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [he] at hp
  exact Nat.eq_of_mul_eq_mul_left (by decide) hp

/-- In positive dimension, parity uses exactly half of the cube vertices. -/
theorem parity_halfspaces_length {n : ℕ} (hn : 0 < n) :
    (vertexExclusionHalfspaces (parity : Cube n → Bool)).length = 2 ^ (n - 1) := by
  rw [vertexExclusionHalfspaces_length, parity_false_card hn]

/-- A sensitivity-`n` witness using exactly `2^(n-1)` halfspaces. -/
theorem exists_parity_intersection {n : ℕ} (hn : 0 < n) :
    ∃ hs : List (Halfspace n), hs.length = 2 ^ (n - 1) ∧
      averageSensitivity (intersection hs) = (n : ℝ) := by
  refine ⟨vertexExclusionHalfspaces parity, parity_halfspaces_length hn, ?_⟩
  rw [intersection_vertexExclusionHalfspaces, parity_averageSensitivity]

/-- On the range in Kane's lower-bound theorem the requested scale is at most `n`. -/
theorem sqrt_dimension_log_le_dimension {n k : ℕ} (hk : 1 ≤ k) (hkmax : k ≤ 2 ^ n) :
    Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) ≤ (n : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.zero_lt_of_lt hk
  have hcast : (k : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hkmax
  have hlog : Real.log (k : ℝ) ≤ (n : ℝ) * Real.log 2 := by
    calc
      Real.log (k : ℝ) ≤ Real.log ((2 : ℝ) ^ n) := Real.log_le_log hkpos hcast
      _ = (n : ℝ) * Real.log 2 := Real.log_pow _ _
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hln : Real.log (k : ℝ) ≤ (n : ℝ) := by nlinarith
  exact Real.sqrt_le_iff.mpr ⟨hn, by nlinarith⟩

/-- The complete lower-bound conclusion in the upper half of the allowed
family-size range, with the explicit constant one. -/
theorem exists_lowerBound_of_large_family {n k : ℕ} (hn : 0 < n)
    (hlarge : 2 ^ (n - 1) ≤ k) (hkmax : k ≤ 2 ^ n) :
    ∃ hs : List (Halfspace n), hs.length ≤ k ∧
      Real.sqrt ((n : ℝ) * Real.log (k : ℝ)) ≤ averageSensitivity (intersection hs) := by
  obtain ⟨hs, hlen, hAS⟩ := exists_parity_intersection hn
  refine ⟨hs, hlen ▸ hlarge, ?_⟩
  rw [hAS]
  have hkpos : 0 < k := lt_of_lt_of_le (by positivity : 0 < 2 ^ (n - 1)) hlarge
  exact sqrt_dimension_log_le_dimension (Nat.succ_le_of_lt hkpos) hkmax

/-- A concrete endpoint witness, using at most one halfspace per cube vertex. -/
theorem exists_intersection_sensitivity_eq_dimension (n : ℕ) :
    ∃ hs : List (Halfspace n), hs.length ≤ 2 ^ n ∧
      averageSensitivity (intersection hs) = (n : ℝ) := by
  refine ⟨vertexExclusionHalfspaces parity, vertexExclusionHalfspaces_length_le _, ?_⟩
  rw [intersection_vertexExclusionHalfspaces, parity_averageSensitivity]

end

end Kane.Lower
