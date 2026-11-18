import RectangleCLTArxivV1.SupplementalHOuterEntropy

/-! Arbitrary extra face factors in the H cubic and angle-weighted pair
matrix sums. The first one or two labels remain distinguished throughout. -/
namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- Split off one label without restricting any of the later labels. -/
theorem sum_face_tuples_cons {p K : ℕ} (f : (Fin (K+1) → Face p) → ℝ) :
    (∑ α, f α) = ∑ j : Face p, ∑ β : Fin K → Face p, f (Fin.cons j β) := by
  classical
  have h := (Fin.consEquiv (fun _ : Fin (K+1) => Face p)).sum_comp f
  rw [Fintype.sum_prod_type] at h
  exact h.symm

theorem sum_face_probability_products {p K : ℕ} (s : FaceSmoother p) (x : Vector p) :
    (∑ β : Fin K → Face p, ∏ i, s.pi x (β i)) = s.theta x ^ K := by
  classical
  rw [← Fintype.prod_sum]
  simp only [FaceSmoother.pi, FaceSmoother.theta, FaceWeights.sum_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Extra factors sum to theta^K, with the first label retained. -/
theorem sum_selector_first_weight {p K : ℕ} (s : FaceSmoother p)
    (x : Vector p) (c : Face p → ℝ) :
    (∑ α : Fin (K+1) → Face p, c (α 0)*selectorWeight s α x) =
      ∑ j : Face p, c j*s.F x*s.pi x j*s.theta x^K := by
  classical
  rw [sum_face_tuples_cons]
  apply Finset.sum_congr rfl
  intro j _
  simp only [selectorWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  calc
    _ = (c j*s.F x*s.pi x j)*(∑ β : Fin K → Face p, ∏ i, s.pi x (β i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      ring
    _ = _ := by rw [sum_face_probability_products]

/-- Extra factors sum to theta^K, with both original pair labels retained. -/
theorem sum_selector_first_pair_weight {p K : ℕ} (s : FaceSmoother p)
    (x : Vector p) (c : Face p → Face p → ℝ) :
    (∑ α : Fin (K+2) → Face p, c (α 0) (α 1)*selectorWeight s α x) =
      ∑ j : Face p, ∑ l : Face p, c j l*s.F x*s.pi x j*s.pi x l*s.theta x^K := by
  classical
  rw [sum_face_tuples_cons]
  apply Finset.sum_congr rfl
  intro j _
  rw [sum_face_tuples_cons]
  apply Finset.sum_congr rfl
  intro l _
  simp only [selectorWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  change (∑ β : Fin K → Face p,
    c j l*(s.F x*(s.pi x j*(s.pi x l*∏ i, s.pi x (β i))))) = _
  calc
    _ = (c j l*s.F x*s.pi x j*s.pi x l)*
        (∑ β : Fin K → Face p, ∏ i, s.pi x (β i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      ring
    _ = _ := by rw [sum_face_probability_products]

/-- Nonnegative mass and projected-moment bounds for the first face
remain valid after any number of restoration factors are appended. -/
theorem sum_selector_first_weight_le {p K : ℕ} (s : FaceSmoother p)
    (x : Vector p) (c : Face p → ℝ) (hc : ∀ j, 0 ≤ c j) :
    (∑ α : Fin (K+1) → Face p, c (α 0)*selectorWeight s α x) ≤
      ∑ j : Face p, c j*s.F x*s.pi x j := by
  rw [sum_selector_first_weight]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_of_le_one_right
    (mul_nonneg (mul_nonneg (hc j) (s.F_pos x).le) ((s.weights x).pi_nonneg j))
    (pow_le_one₀ (s.weights x).theta_nonneg (s.weights x).theta_lt_one.le)

/-- In particular, this applies with c(j,l) equal to the angle factor
or that factor times the actual two-face projected squared length. -/
theorem sum_selector_first_pair_weight_le {p K : ℕ} (s : FaceSmoother p)
    (x : Vector p) (c : Face p → Face p → ℝ) (hc : ∀ j l, 0 ≤ c j l) :
    (∑ α : Fin (K+2) → Face p, c (α 0) (α 1)*selectorWeight s α x) ≤
      ∑ j : Face p, ∑ l : Face p, c j l*s.F x*s.pi x j*s.pi x l := by
  rw [sum_selector_first_pair_weight]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_of_le_one_right
    (mul_nonneg (mul_nonneg (mul_nonneg (hc j l) (s.F_pos x).le)
      ((s.weights x).pi_nonneg j)) ((s.weights x).pi_nonneg l))
    (pow_le_one₀ (s.weights x).theta_nonneg (s.weights x).theta_lt_one.le)

/-- Exact signed binomial expansion used before taking the Gaussian
trace. It retains cancellation for every number of additional factors. -/
theorem selector_extra_factors_binomial {p : ℕ} (s : FaceSmoother p)
    (x : Vector p) (w : ℝ) (K : ℕ) :
    w*s.theta x^K = ∑ q ∈ Finset.range (K+1),
      (-1:ℝ)^q*(K.choose q:ℝ)*(w*s.F x^q) := by
  have hbin : s.theta x ^ K = ∑ q ∈ Finset.range (K+1),
      (-1:ℝ)^q*s.F x^q*(K.choose q:ℝ) := by
    calc
      _ = (-s.F x+1)^K := by
        congr 1
        change 1-s.F x = -s.F x+1
        ring
      _ = _ := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro q _
        rw [one_pow,mul_one,neg_pow]
  rw [hbin,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

end
end RectangleCLTArxivV1
