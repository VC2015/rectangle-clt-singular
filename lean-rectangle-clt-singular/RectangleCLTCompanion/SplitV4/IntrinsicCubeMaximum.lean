import RectangleCLTCompanion.SplitV4.IntrinsicCubeData
import Kane.Analytic

/-! The logarithmic specialization of the intrinsic sign-cube maximum.
Weights are arbitrary and may be dependent between faces. The independent
sign coordinates give an actual finite-cube exponential moment. -/

open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem avg_exp_cubeLinear {n : ℕ} (b : Fin n → ℝ) (t : ℝ) :
    Kane.avg (fun x : Kane.Cube n => Real.exp (t * cubeLinear b x)) =
      ∏ i : Fin n, Real.cosh (t * b i) := by
  have hfactor : (∑ x : Kane.Cube n, Real.exp (t * cubeLinear b x)) =
      ∏ i : Fin n, ∑ e : Bool, Real.exp (t * b i * (if e then 1 else -1)) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [cubeLinear, cubeSign, Finset.mul_sum, Real.exp_sum, mul_assoc]
  have hcoord (i : Fin n) : (∑ e : Bool, Real.exp (t * b i * (if e then 1 else -1))) =
      2 * Real.cosh (t * b i) := by
    rw [Fintype.sum_bool, Real.cosh_eq]
    simp only [Bool.false_eq_true, ↓reduceIte, mul_neg, mul_one]
    ring
  simp_rw [hcoord] at hfactor
  have hcard : Fintype.card (Kane.Cube n) = 2^n := by simp [Kane.Cube, Fintype.card_fun]
  unfold Kane.avg
  rw [hfactor, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcard,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ)^n ≠ 0), one_mul]

theorem avg_exp_cubeLinear_le {n : ℕ} (b : Fin n → ℝ) (t : ℝ) :
    Kane.avg (fun x : Kane.Cube n => Real.exp (t * cubeLinear b x)) ≤
      Real.exp (t^2 * (∑ i, b i ^ 2) / 2) := by
  rw [avg_exp_cubeLinear]
  calc
    _ ≤ ∏ i : Fin n, Real.exp ((t * b i)^2 / 2) :=
      Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le)
        (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [mul_pow, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]

theorem avg_exp_selected_cubeLinear_le {m n : ℕ} (b : Fin m → Fin n → ℝ)
    (hrow : ∀ α, (∑ i, b α i ^ 2) ≤ 1) (G : Kane.Cube n → ℝ)
    (hG : ∀ x, G x = 0 ∨ ∃ α, G x = cubeLinear (b α) x) (t : ℝ) :
    Kane.avg (fun x => Real.exp (t * G x)) ≤
      ((m : ℝ) + 1) * Real.exp (t^2 / 2) := by
  have hpoint (x : Kane.Cube n) : Real.exp (t * G x) ≤
      1 + ∑ α : Fin m, Real.exp (t * cubeLinear (b α) x) := by
    rcases hG x with hz | ⟨α, hα⟩
    · rw [hz, mul_zero, Real.exp_zero]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
    · have hs := Finset.single_le_sum (fun β _ => (Real.exp_pos
        (t * cubeLinear (b β) x)).le) (Finset.mem_univ α)
      rw [hα]
      linarith
  have hsum : (∑ α : Fin m, Kane.avg (fun x => Real.exp (t * cubeLinear (b α) x))) ≤
      (m : ℝ) * Real.exp (t^2 / 2) := by
    calc
      _ ≤ ∑ _α : Fin m, Real.exp (t^2 / 2) := by
        apply Finset.sum_le_sum
        intro α _
        apply (avg_exp_cubeLinear_le (b α) t).trans
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ (by norm_num)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hrow α) (sq_nonneg t)
      _ = _ := by simp
  have hC : 1 ≤ Real.exp (t^2 / 2) := Real.one_le_exp (by positivity)
  calc
    _ ≤ Kane.avg (fun x => 1 + ∑ α : Fin m, Real.exp (t * cubeLinear (b α) x)) :=
      Kane.avg_mono hpoint
    _ = 1 + ∑ α : Fin m, Kane.avg (fun x => Real.exp (t * cubeLinear (b α) x)) := by
      rw [Kane.avg_add, Kane.avg_const, Kane.avg_sum]
    _ ≤ _ := by nlinarith

theorem avg_selected_cubeLinear_le_sqrt {m n : ℕ} (b : Fin m → Fin n → ℝ)
    (hrow : ∀ α, (∑ i, b α i ^ 2) ≤ 1) (G : Kane.Cube n → ℝ)
    (hG : ∀ x, G x = 0 ∨ ∃ α, G x = cubeLinear (b α) x) :
    Kane.avg G ≤ Real.sqrt (2 * Real.log ((m : ℝ) + 1)) := by
  by_cases hm : m = 0
  · subst m
    have hzero : G = (fun _ => 0) := by
      funext x
      rcases hG x with hz | ⟨α, _⟩
      · exact hz
      · exact Fin.elim0 α
    simp [hzero]
  have hbound := Kane.avg_le_sqrt_of_exp_moment G 1 m (by decide) (by omega)
    (fun t _ => by simpa using avg_exp_selected_cubeLinear_le b hrow G hG t)
  simpa using hbound

theorem positiveLinearMaximum_selected {m n : ℕ}
    (b : Fin m → Fin n → ℝ) (x : Kane.Cube n) :
    positiveLinearMaximum b x = 0 ∨ ∃ α, positiveLinearMaximum b x = cubeLinear (b α) x := by
  obtain ⟨α, _, heq⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Fin (m+1)))) Finset.univ_nonempty
    (Fin.cases (0 : ℝ) (fun α => cubeLinear (b α) x))
  cases α using Fin.cases with
  | zero => exact Or.inl (by simpa only [positiveLinearMaximum, Fin.cases_zero] using heq)
  | succ α => exact Or.inr ⟨α, by simpa only [positiveLinearMaximum, Fin.cases_succ] using heq⟩

/-- The exact final assertion of Lemma C.1, including a zero face family.
The expectation is the uniform average over the entire sign cube. -/
theorem intrinsicCubeMean_le_sqrt_log {m n : ℕ} (b : Fin m → Fin n → ℝ)
    (hrow : ∀ α, (∑ i, b α i ^ 2) ≤ 1) :
    intrinsicCubeMean b ≤ Real.sqrt (2 * Real.log ((m : ℝ) + 1)) :=
  avg_selected_cubeLinear_le_sqrt b hrow (positiveLinearMaximum b)
    (positiveLinearMaximum_selected b)

end
end RectangleCLT.Companion.SplitV4
