import Kane.Analytic
import Kane.Combinatorial
import Kane.Halfspace
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Kane's upper bound, with explicit constants and the endpoint-safe `log (k+1)`. -/

open scoped BigOperators

namespace Kane

private theorem avg_list_sum {α β : Type*} [Fintype α]
    (fs : List β) (h : β → α → ℝ) :
    avg (fun x => (fs.map fun f => h f x).sum) =
      (fs.map fun f => avg (h f)).sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [avg_add, ih]

private theorem exp_selected_le {n : ℕ} (fs : List (UnateFunction n))
    (G : Cube n → ℝ)
    (hG : ∀ x, G x = 0 ∨ ∃ f ∈ fs, G x = signedSum f.direction x)
    (t : ℝ) (x : Cube n) :
    Real.exp (t * G x) ≤
      1 + (fs.map fun f => Real.exp (t * signedSum f.direction x)).sum := by
  have hnonneg : 0 ≤ (fs.map fun f => Real.exp (t * signedSum f.direction x)).sum := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp ha
    exact (Real.exp_pos _).le
  rcases hG x with hz | ⟨f, hf, heq⟩
  · rw [hz]
    simpa using hnonneg
  · rw [heq]
    have hsingle : Real.exp (t * signedSum f.direction x) ≤
        (fs.map fun g => Real.exp (t * signedSum g.direction x)).sum := by
      apply List.single_le_sum ?_ _ (List.mem_map.mpr ⟨f, hf, rfl⟩)
      intro a ha
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp ha
      exact (Real.exp_pos _).le
    linarith

private theorem selected_exp_moment {n : ℕ} (fs : List (UnateFunction n))
    (G : Cube n → ℝ)
    (hG : ∀ x, G x = 0 ∨ ∃ f ∈ fs, G x = signedSum f.direction x)
    (t : ℝ) :
    avg (fun x => Real.exp (t * G x)) ≤
      ((fs.length : ℝ) + 1) * Real.exp ((n : ℝ) * t ^ 2 / 2) := by
  let C := Real.exp ((n : ℝ) * t ^ 2 / 2)
  have hsum : (fs.map fun f => avg (fun x => Real.exp (t * signedSum f.direction x))).sum ≤
      (fs.length : ℝ) * C := by
    have hh := List.sum_le_card_nsmul
      (fs.map fun f => avg (fun x => Real.exp (t * signedSum f.direction x))) C
      (by
        intro a ha
        obtain ⟨f, _, rfl⟩ := List.mem_map.mp ha
        exact avg_exp_signedSum_le f.direction t)
    simpa only [List.length_map, nsmul_eq_mul] using hh
  have hC : 1 ≤ C := by
    change 1 ≤ Real.exp _
    exact Real.one_le_exp (by positivity)
  calc
    _ ≤ avg (fun x => 1 + (fs.map fun f => Real.exp (t * signedSum f.direction x)).sum) :=
      avg_mono (exp_selected_le fs G hG t)
    _ = 1 + (fs.map fun f => avg (fun x => Real.exp (t * signedSum f.direction x))).sum := by
      rw [avg_add, avg_const, avg_list_sum]
    _ ≤ ((fs.length : ℝ) + 1) * C := by nlinarith

/-- Proposition 3: the average sensitivity of a union of `k` unate functions in
`n` variables is at most `2 * sqrt (2 * n * log (k+1))`. The formula includes
the empty union and the one-function case. -/
theorem unate_union_averageSensitivity_le {n : ℕ} (fs : List (UnateFunction n)) :
    averageSensitivity (union fs) ≤
      2 * Real.sqrt (2 * (n : ℝ) * Real.log ((fs.length : ℝ) + 1)) := by
  by_cases hn : n = 0
  · subst n
    simp [averageSensitivity, avg]
  by_cases hk : fs.length = 0
  · have hfs : fs = [] := List.length_eq_zero_iff.mp hk
    subst fs
    simp [averageSensitivity, union, avg]
  obtain ⟨G, hb, hG⟩ := union_sensitivity_charge fs
  have hmean := avg_le_sqrt_of_exp_moment G n fs.length
    (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hk)
    (fun t _ => selected_exp_moment fs G hG t)
  linarith

/-- Theorem 1: the sensitivity upper bound for an intersection of real affine
halfspaces, with a universal explicit constant. -/
theorem halfspaces_averageSensitivity_le {n : ℕ} (hs : List (Halfspace n)) :
    averageSensitivity (intersection hs) ≤
      2 * Real.sqrt (2 * (n : ℝ) * Real.log ((hs.length : ℝ) + 1)) := by
  rw [intersection_averageSensitivity_eq]
  simpa only [List.length_map] using
    unate_union_averageSensitivity_le (hs.map fun h => h.toUnate.complement)

end Kane
