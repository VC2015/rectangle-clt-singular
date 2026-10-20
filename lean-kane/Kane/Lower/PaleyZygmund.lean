import Kane.Cube

/-! A finite Paley--Zygmund inequality for uniform real averages. -/

open scoped BigOperators

namespace Kane.Lower

theorem avg_mul_sq_le {α : Type*} [Fintype α] (f g : α → ℝ) :
    (avg (fun x => f x * g x)) ^ 2 ≤
      avg (fun x => f x ^ 2) * avg (fun x => g x ^ 2) := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hc : 0 ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 := sq_nonneg _
  unfold avg
  calc
    _ = ((Fintype.card α : ℝ)⁻¹) ^ 2 * (∑ x, f x * g x) ^ 2 := by ring
    _ ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 *
        ((∑ x, f x ^ 2) * (∑ x, g x ^ 2)) := mul_le_mul_of_nonneg_left hs hc
    _ = _ := by ring

/-- The nonnegative-variable Paley--Zygmund estimate, expressed entirely
as finite uniform averages. -/
theorem paley_zygmund {α : Type*} [Fintype α] [Nonempty α]
    (Y : α → ℝ) (hY : ∀ x, 0 ≤ Y x)
    (hmean : 0 < avg Y) (hsecond : 0 < avg (fun x => Y x ^ 2))
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    (1 - η) ^ 2 * (avg Y) ^ 2 / avg (fun x => Y x ^ 2) ≤
      avg (fun x => if η * avg Y ≤ Y x then (1 : ℝ) else 0) := by
  classical
  let I : α → ℝ := fun x => if η * avg Y ≤ Y x then 1 else 0
  have hI0 (x : α) : 0 ≤ I x := by unfold I; split_ifs <;> norm_num
  have hI2 : (fun x => I x ^ 2) = I := by
    funext x
    unfold I
    split_ifs <;> norm_num
  have hsplit : avg Y = avg (fun x => Y x * I x) +
      avg (fun x => Y x * (1 - I x)) := by
    rw [← avg_add]
    apply avg_congr
    intro x
    ring
  have hsmall : avg (fun x => Y x * (1 - I x)) ≤ η * avg Y := by
    calc
      _ ≤ avg (fun _ : α => η * avg Y) := by
        apply avg_mono
        intro x
        unfold I
        split_ifs with hx
        · simpa only [sub_self, mul_zero] using mul_nonneg hη hmean.le
        · simpa only [sub_zero, mul_one] using (le_of_not_ge hx)
      _ = _ := avg_const _
  have hlarge : (1 - η) * avg Y ≤ avg (fun x => Y x * I x) := by
    linarith
  have hnonneg : 0 ≤ (1 - η) * avg Y := mul_nonneg (sub_nonneg.mpr hη1) hmean.le
  have hsq : (1 - η) ^ 2 * (avg Y) ^ 2 ≤
      (avg (fun x => Y x * I x)) ^ 2 := by
    have hpos : 0 ≤ avg (fun x => Y x * I x) := avg_nonneg (fun x => mul_nonneg (hY x) (hI0 x))
    nlinarith
  have hcs := avg_mul_sq_le Y I
  rw [hI2] at hcs
  apply (div_le_iff₀ hsecond).mpr
  exact hsq.trans (by simpa only [mul_comm] using hcs)

end Kane.Lower
