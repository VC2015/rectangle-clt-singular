import Kane.Base

/-! The finite exponential-moment argument used for the sensitivity bound. -/

open scoped BigOperators

namespace Kane

/-- Jensen's inequality for the exponential and a uniform finite average. -/
theorem exp_avg_le_avg_exp {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (G : Ω → ℝ) (t : ℝ) :
    Real.exp (t * avg G) ≤ avg (fun x => Real.exp (t * G x)) := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hweights : ∑ _x : Ω, (Fintype.card Ω : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard
  have hj := convexOn_exp.map_sum_le
    (t := Finset.univ) (w := fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹)
    (p := fun x => t * G x)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hweights
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have hsum : (∑ x, (Fintype.card Ω : ℝ)⁻¹ * (t * G x)) = t * avg G := by
    simp only [avg, ← Finset.mul_sum]
    ring
  rw [hsum] at hj
  simpa only [avg, Finset.mul_sum] using hj

/-- Optimizing the exponential-moment bound for a finite selection of signed sums.
The extra `1` includes the possibility of selecting no sum. -/
theorem avg_le_sqrt_of_exp_moment {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (G : Ω → ℝ) (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hmgf : ∀ t : ℝ, 0 < t →
      avg (fun x => Real.exp (t * G x)) ≤
        ((k : ℝ) + 1) * Real.exp ((n : ℝ) * t ^ 2 / 2)) :
    avg G ≤ Real.sqrt (2 * (n : ℝ) * Real.log ((k : ℝ) + 1)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos (by linarith)
  let s := Real.sqrt (2 * (n : ℝ) * Real.log ((k : ℝ) + 1))
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = 2 * (n : ℝ) * Real.log ((k : ℝ) + 1) :=
    Real.sq_sqrt (by positivity)
  have ht : 0 < s / (n : ℝ) := div_pos hs hn'
  have hb := (exp_avg_le_avg_exp G (s / (n : ℝ))).trans (hmgf _ ht)
  have hfactor : ((k : ℝ) + 1) * Real.exp ((n : ℝ) * (s / (n : ℝ)) ^ 2 / 2) =
      Real.exp (Real.log ((k : ℝ) + 1) + (n : ℝ) * (s / (n : ℝ)) ^ 2 / 2) := by
    rw [Real.exp_add, Real.exp_log (by positivity)]
  rw [hfactor, Real.exp_le_exp] at hb
  have hL_eq : Real.log ((k : ℝ) + 1) = s ^ 2 / (2 * (n : ℝ)) := by
    apply (eq_div_iff (by positivity : (2 : ℝ) * (n : ℝ) ≠ 0)).2
    nlinarith [hs2]
  have heq : Real.log ((k : ℝ) + 1) + (n : ℝ) * (s / (n : ℝ)) ^ 2 / 2 =
      (s / (n : ℝ)) * s := by
    rw [hL_eq]
    field_simp [ne_of_gt hn']
    ring
  rw [heq] at hb
  exact (mul_le_mul_left ht).mp hb

end Kane
