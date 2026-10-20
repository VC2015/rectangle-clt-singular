import RectangleCLT.SmootherSecondDerivatives
import RectangleCLT.SmootherStability

/-!
# Actual higher mixed coordinate derivatives of the rational smoother

The mixed derivatives in this file are iterated ordinary derivatives along
coordinate lines. Nonnegative entrywise majorants are uniform over shifts
of maximum norm at most the bandwidth, and their sums retain `F * (1 - F)`.
No averaged probabilistic estimate is asserted.
-/

open scoped BigOperators

namespace RectangleCLT
namespace FaceWeights

variable {p : ℕ} (w : FaceWeights p)

noncomputable def thirdDiagonalMass (j k l : Fin p) : ℝ :=
  if j = k ∧ j = l then w.v j else 0

noncomputable def thirdFactor (j k l : Fin p) : ℝ :=
  -6 * w.v j * w.v k * w.v l +
    2 * (w.diagonalMass j k * w.v l + w.diagonalMass j l * w.v k +
      w.diagonalMass k l * w.v j) - w.thirdDiagonalMass j k l

noncomputable def fourthDiagonalMass (j k l m : Fin p) : ℝ :=
  if j = k ∧ j = l ∧ j = m then w.coordinateMass j else 0

noncomputable def fourthFactor (j k l m : Fin p) : ℝ :=
  24 * w.v j * w.v k * w.v l * w.v m -
    6 * (w.diagonalMass j k * w.v l * w.v m +
      w.diagonalMass j l * w.v k * w.v m +
      w.diagonalMass j m * w.v k * w.v l +
      w.diagonalMass k l * w.v j * w.v m +
      w.diagonalMass k m * w.v j * w.v l +
      w.diagonalMass l m * w.v j * w.v k) +
    2 * (w.diagonalMass j k * w.diagonalMass l m +
      w.diagonalMass j l * w.diagonalMass k m +
      w.diagonalMass j m * w.diagonalMass k l) +
    2 * (w.thirdDiagonalMass j k l * w.v m +
      w.thirdDiagonalMass j k m * w.v l +
      w.thirdDiagonalMass j l m * w.v k +
      w.thirdDiagonalMass k l m * w.v j) - w.fourthDiagonalMass j k l m

theorem sum_abs_thirdDiagonalMass :
    (∑ j, ∑ k, ∑ l, |w.thirdDiagonalMass j k l|) = ∑ j, |w.v j| := by
  simp_rw [thirdDiagonalMass, apply_ite abs, abs_zero, ite_and]
  simp

theorem sum_abs_third_factor_le :
    (∑ j, ∑ k, ∑ l, |w.thirdFactor j k l|) ≤ 13 * w.theta := by
  have hpoint (j k l : Fin p) :
      |w.thirdFactor j k l| ≤
        6 * |w.v j| * |w.v k| * |w.v l| +
          2 * (w.diagonalMass j k * |w.v l| +
            w.diagonalMass j l * |w.v k| + w.diagonalMass k l * |w.v j|) +
            |w.thirdDiagonalMass j k l| := by
    have hA := abs_add (w.diagonalMass j k * w.v l + w.diagonalMass j l * w.v k)
      (w.diagonalMass k l * w.v j)
    have hB := abs_add (w.diagonalMass j k * w.v l) (w.diagonalMass j l * w.v k)
    have hC := abs_add (-6 * w.v j * w.v k * w.v l)
      (2 * (w.diagonalMass j k * w.v l + w.diagonalMass j l * w.v k +
        w.diagonalMass k l * w.v j))
    have hD : |w.thirdFactor j k l| ≤
        |-6 * w.v j * w.v k * w.v l +
          2 * (w.diagonalMass j k * w.v l + w.diagonalMass j l * w.v k +
            w.diagonalMass k l * w.v j)| + |w.thirdDiagonalMass j k l| := by
      simpa [thirdFactor] using abs_sub_le
        (-6 * w.v j * w.v k * w.v l +
          2 * (w.diagonalMass j k * w.v l + w.diagonalMass j l * w.v k +
            w.diagonalMass k l * w.v j)) (0 : ℝ) (w.thirdDiagonalMass j k l)
    simp only [abs_mul, abs_of_nonneg (w.diagonalMass_nonneg j k),
      abs_of_nonneg (w.diagonalMass_nonneg j l),
      abs_of_nonneg (w.diagonalMass_nonneg k l)] at hA hB hC
    norm_num at hC hD
    linarith
  have hprod : (∑ j, ∑ k, ∑ l, 6 * |w.v j| * |w.v k| * |w.v l|) =
      6 * (∑ j, |w.v j|) ^ 3 := by
    rw [pow_succ, pow_two]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have h1 : (∑ j, ∑ k, ∑ l, w.diagonalMass j k * |w.v l|) =
      w.theta * (∑ j, |w.v j|) := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    rw [w.sum_diagonalMass]
  have h2 : (∑ j, ∑ k, ∑ l, w.diagonalMass j l * |w.v k|) =
      w.theta * (∑ j, |w.v j|) := by
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    rw [w.sum_diagonalMass]
  have h3 : (∑ j, ∑ k, ∑ l, w.diagonalMass k l * |w.v j|) =
      w.theta * (∑ j, |w.v j|) := by
    simp only [← Finset.sum_mul]
    rw [w.sum_diagonalMass]
    rw [← Finset.mul_sum]
  have hA : 0 ≤ ∑ j, |w.v j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hAle := w.sum_abs_v_le_one
  have hAtheta := w.sum_abs_v_le_theta
  have hA2 : (∑ j, |w.v j|) ^ 2 ≤ ∑ j, |w.v j| := by
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hAle)]
  have hA3 : (∑ j, |w.v j|) ^ 3 ≤ w.theta := by
    have hh := mul_le_mul_of_nonneg_left hA2 hA
    nlinarith
  have hmix : w.theta * (∑ j, |w.v j|) ≤ w.theta := by
    simpa using mul_le_mul_of_nonneg_left hAle w.theta_nonneg
  calc
    _ ≤ ∑ j, ∑ k, ∑ l,
        (6 * |w.v j| * |w.v k| * |w.v l| +
          2 * (w.diagonalMass j k * |w.v l| +
            w.diagonalMass j l * |w.v k| + w.diagonalMass k l * |w.v j|) +
            |w.thirdDiagonalMass j k l|) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact Finset.sum_le_sum fun l _ => hpoint j k l
    _ = 6 * (∑ j, |w.v j|) ^ 3 + 6 * (w.theta * (∑ j, |w.v j|)) +
        (∑ j, |w.v j|) := by
      have hc (f : Fin p → Fin p → Fin p → ℝ) :
          (∑ j, ∑ k, ∑ l, 2 * f j k l) = 2 * (∑ j, ∑ k, ∑ l, f j k l) := by
        simp only [Finset.mul_sum]
      simp_rw [Finset.sum_add_distrib]
      rw [hprod, hc]
      simp_rw [Finset.sum_add_distrib]
      rw [h1, h2, h3, w.sum_abs_thirdDiagonalMass]
      ring
    _ ≤ 13 * w.theta := by linarith

theorem fourthDiagonalMass_nonneg (j k l m : Fin p) :
    0 ≤ w.fourthDiagonalMass j k l m := by
  unfold fourthDiagonalMass
  split_ifs
  · exact w.coordinateMass_nonneg j
  · rfl

theorem sum_fourthDiagonalMass :
    (∑ j, ∑ k, ∑ l, ∑ m, w.fourthDiagonalMass j k l m) = w.theta := by
  simp only [fourthDiagonalMass, ite_and]
  simpa using w.sum_coordinateMass

set_option maxHeartbeats 1000000 in
theorem sum_abs_fourth_factor_le :
    (∑ j, ∑ k, ∑ l, ∑ m, |w.fourthFactor j k l m|) ≤ 75 * w.theta := by
  have hpoint (j k l m : Fin p) : |w.fourthFactor j k l m| ≤
      24 * (|w.v j| * |w.v k| * |w.v l| * |w.v m|) +
          6 * (w.diagonalMass j k * |w.v l| * |w.v m|) +
          6 * (w.diagonalMass j l * |w.v k| * |w.v m|) +
          6 * (w.diagonalMass j m * |w.v k| * |w.v l|) +
          6 * (w.diagonalMass k l * |w.v j| * |w.v m|) +
          6 * (w.diagonalMass k m * |w.v j| * |w.v l|) +
          6 * (w.diagonalMass l m * |w.v j| * |w.v k|) +
          2 * (w.diagonalMass j k * w.diagonalMass l m) +
          2 * (w.diagonalMass j l * w.diagonalMass k m) +
          2 * (w.diagonalMass j m * w.diagonalMass k l) +
          2 * (|w.thirdDiagonalMass j k l| * |w.v m|) +
          2 * (|w.thirdDiagonalMass j k m| * |w.v l|) +
          2 * (|w.thirdDiagonalMass j l m| * |w.v k|) +
          2 * (|w.thirdDiagonalMass k l m| * |w.v j|) +
          1 * (w.fourthDiagonalMass j k l m) := by
    let terms : Fin 15 → ℝ := ![24 * w.v j * w.v k * w.v l * w.v m,
      -6 * w.diagonalMass j k * w.v l * w.v m,
      -6 * w.diagonalMass j l * w.v k * w.v m,
      -6 * w.diagonalMass j m * w.v k * w.v l,
      -6 * w.diagonalMass k l * w.v j * w.v m,
      -6 * w.diagonalMass k m * w.v j * w.v l,
      -6 * w.diagonalMass l m * w.v j * w.v k,
      2 * w.diagonalMass j k * w.diagonalMass l m,
      2 * w.diagonalMass j l * w.diagonalMass k m,
      2 * w.diagonalMass j m * w.diagonalMass k l,
      2 * w.thirdDiagonalMass j k l * w.v m,
      2 * w.thirdDiagonalMass j k m * w.v l,
      2 * w.thirdDiagonalMass j l m * w.v k,
      2 * w.thirdDiagonalMass k l m * w.v j,
      -w.fourthDiagonalMass j k l m]
    have ht := Finset.abs_sum_le_sum_abs terms Finset.univ
    have heq : (∑ i, terms i) = w.fourthFactor j k l m := by
      simp [terms, fourthFactor, Fin.sum_univ_succ]
      ring
    rw [heq] at ht
    simpa only [terms, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, add_assoc, mul_assoc, abs_mul, abs_neg,
      abs_of_nonneg (w.diagonalMass_nonneg j k), abs_of_nonneg (w.diagonalMass_nonneg j l),
      abs_of_nonneg (w.diagonalMass_nonneg j m), abs_of_nonneg (w.diagonalMass_nonneg k l),
      abs_of_nonneg (w.diagonalMass_nonneg k m), abs_of_nonneg (w.diagonalMass_nonneg l m),
      abs_of_nonneg (w.fourthDiagonalMass_nonneg j k l m), show |(24 : ℝ)| = 24 by norm_num,
      show |(2 : ℝ)| = 2 by norm_num, show |(-6 : ℝ)| = 6 by norm_num, one_mul] using ht
  have hif (P : Prop) [Decidable P] (f : Fin p → ℝ) :
      (∑ i, if P then f i else 0) = if P then ∑ i, f i else 0 := by
    by_cases h : P <;> simp [h]
  have h1 : (∑ j, ∑ k, ∑ l, ∑ m, |w.v j| * |w.v k| * |w.v l| * |w.v m|) = (∑ j, |w.v j|) ^ 4 := by
    rw [show (∑ j, |w.v j|) ^ 4 = (∑ j, |w.v j|) * (∑ j, |w.v j|) * (∑ j, |w.v j|) * (∑ j, |w.v j|) by ring]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    ring
  have h2 : (∑ j, ∑ k, ∑ l, ∑ m, w.diagonalMass j k * |w.v l| * |w.v m|) = w.theta * (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h3 : (∑ j, ∑ k, ∑ l, ∑ m, w.diagonalMass j l * |w.v k| * |w.v m|) = w.theta * (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h4 : (∑ j, ∑ k, ∑ l, ∑ m, w.diagonalMass j m * |w.v k| * |w.v l|) = w.theta * (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h5 : (∑ j, ∑ k, ∑ l, ∑ m, w.diagonalMass k l * |w.v j| * |w.v m|) = w.theta * (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h6 : (∑ j, ∑ k, ∑ l, ∑ m, w.diagonalMass k m * |w.v j| * |w.v l|) = w.theta * (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h7 : (∑ j, ∑ k, ∑ l, ∑ m, w.diagonalMass l m * |w.v j| * |w.v k|) = w.theta * (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h8 : (∑ j, ∑ k, ∑ l, ∑ m, w.diagonalMass j k * w.diagonalMass l m) = w.theta ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h9 : (∑ j, ∑ k, ∑ l, ∑ m, w.diagonalMass j l * w.diagonalMass k m) = w.theta ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h10 : (∑ j, ∑ k, ∑ l, ∑ m, w.diagonalMass j m * w.diagonalMass k l) = w.theta ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h11 : (∑ j, ∑ k, ∑ l, ∑ m, |w.thirdDiagonalMass j k l| * |w.v m|) = (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h12 : (∑ j, ∑ k, ∑ l, ∑ m, |w.thirdDiagonalMass j k m| * |w.v l|) = (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h13 : (∑ j, ∑ k, ∑ l, ∑ m, |w.thirdDiagonalMass j l m| * |w.v k|) = (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h14 : (∑ j, ∑ k, ∑ l, ∑ m, |w.thirdDiagonalMass k l m| * |w.v j|) = (∑ j, |w.v j|) ^ 2 := by
    simp only [diagonalMass, thirdDiagonalMass, apply_ite abs, abs_zero, ite_and, ite_mul, mul_ite, zero_mul, mul_zero]
    simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    try simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
    ring
  have h15 : (∑ j, ∑ k, ∑ l, ∑ m, w.fourthDiagonalMass j k l m) = w.theta := by
    exact w.sum_fourthDiagonalMass
  have hc (c : ℝ) (f : Fin p → Fin p → Fin p → Fin p → ℝ) :
      (∑ j, ∑ k, ∑ l, ∑ m, c * f j k l m) = c * (∑ j, ∑ k, ∑ l, ∑ m, f j k l m) := by
    simp only [Finset.mul_sum]
  have hc1 : (∑ j, ∑ k, ∑ l, ∑ m, 24 * (|w.v j| * |w.v k| * |w.v l| * |w.v m|)) = 24 * ((∑ j, |w.v j|) ^ 4) := by
    rw [hc, h1]
  have hc2 : (∑ j, ∑ k, ∑ l, ∑ m, 6 * (w.diagonalMass j k * |w.v l| * |w.v m|)) = 6 * (w.theta * (∑ j, |w.v j|) ^ 2) := by
    rw [hc, h2]
  have hc3 : (∑ j, ∑ k, ∑ l, ∑ m, 6 * (w.diagonalMass j l * |w.v k| * |w.v m|)) = 6 * (w.theta * (∑ j, |w.v j|) ^ 2) := by
    rw [hc, h3]
  have hc4 : (∑ j, ∑ k, ∑ l, ∑ m, 6 * (w.diagonalMass j m * |w.v k| * |w.v l|)) = 6 * (w.theta * (∑ j, |w.v j|) ^ 2) := by
    rw [hc, h4]
  have hc5 : (∑ j, ∑ k, ∑ l, ∑ m, 6 * (w.diagonalMass k l * |w.v j| * |w.v m|)) = 6 * (w.theta * (∑ j, |w.v j|) ^ 2) := by
    rw [hc, h5]
  have hc6 : (∑ j, ∑ k, ∑ l, ∑ m, 6 * (w.diagonalMass k m * |w.v j| * |w.v l|)) = 6 * (w.theta * (∑ j, |w.v j|) ^ 2) := by
    rw [hc, h6]
  have hc7 : (∑ j, ∑ k, ∑ l, ∑ m, 6 * (w.diagonalMass l m * |w.v j| * |w.v k|)) = 6 * (w.theta * (∑ j, |w.v j|) ^ 2) := by
    rw [hc, h7]
  have hc8 : (∑ j, ∑ k, ∑ l, ∑ m, 2 * (w.diagonalMass j k * w.diagonalMass l m)) = 2 * (w.theta ^ 2) := by
    rw [hc, h8]
  have hc9 : (∑ j, ∑ k, ∑ l, ∑ m, 2 * (w.diagonalMass j l * w.diagonalMass k m)) = 2 * (w.theta ^ 2) := by
    rw [hc, h9]
  have hc10 : (∑ j, ∑ k, ∑ l, ∑ m, 2 * (w.diagonalMass j m * w.diagonalMass k l)) = 2 * (w.theta ^ 2) := by
    rw [hc, h10]
  have hc11 : (∑ j, ∑ k, ∑ l, ∑ m, 2 * (|w.thirdDiagonalMass j k l| * |w.v m|)) = 2 * ((∑ j, |w.v j|) ^ 2) := by
    rw [hc, h11]
  have hc12 : (∑ j, ∑ k, ∑ l, ∑ m, 2 * (|w.thirdDiagonalMass j k m| * |w.v l|)) = 2 * ((∑ j, |w.v j|) ^ 2) := by
    rw [hc, h12]
  have hc13 : (∑ j, ∑ k, ∑ l, ∑ m, 2 * (|w.thirdDiagonalMass j l m| * |w.v k|)) = 2 * ((∑ j, |w.v j|) ^ 2) := by
    rw [hc, h13]
  have hc14 : (∑ j, ∑ k, ∑ l, ∑ m, 2 * (|w.thirdDiagonalMass k l m| * |w.v j|)) = 2 * ((∑ j, |w.v j|) ^ 2) := by
    rw [hc, h14]
  have hc15 : (∑ j, ∑ k, ∑ l, ∑ m, 1 * (w.fourthDiagonalMass j k l m)) = 1 * (w.theta) := by
    rw [hc, h15]
  have hA : 0 ≤ ∑ j, |w.v j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hAle := w.sum_abs_v_le_one
  have hAtheta := w.sum_abs_v_le_theta
  have hA2 : (∑ j, |w.v j|) ^ 2 ≤ ∑ j, |w.v j| := by
    nlinarith only [hA, hAle, mul_nonneg hA (sub_nonneg.mpr hAle)]
  have hA4 : (∑ j, |w.v j|) ^ 4 ≤ w.theta := by
    have hh := mul_self_le_mul_self (sq_nonneg (∑ j, |w.v j|)) hA2
    nlinarith only [hh, hA2, hAtheta]
  have hmix : w.theta * (∑ j, |w.v j|) ^ 2 ≤ w.theta := by
    exact (mul_le_mul_of_nonneg_left hA2 w.theta_nonneg).trans
      (by simpa using mul_le_mul_of_nonneg_left hAle w.theta_nonneg)
  have htheta2 : w.theta ^ 2 ≤ w.theta := by
    nlinarith only [mul_nonneg w.theta_nonneg (sub_nonneg.mpr w.theta_lt_one.le)]
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m,
        (24 * (|w.v j| * |w.v k| * |w.v l| * |w.v m|) +
          6 * (w.diagonalMass j k * |w.v l| * |w.v m|) +
          6 * (w.diagonalMass j l * |w.v k| * |w.v m|) +
          6 * (w.diagonalMass j m * |w.v k| * |w.v l|) +
          6 * (w.diagonalMass k l * |w.v j| * |w.v m|) +
          6 * (w.diagonalMass k m * |w.v j| * |w.v l|) +
          6 * (w.diagonalMass l m * |w.v j| * |w.v k|) +
          2 * (w.diagonalMass j k * w.diagonalMass l m) +
          2 * (w.diagonalMass j l * w.diagonalMass k m) +
          2 * (w.diagonalMass j m * w.diagonalMass k l) +
          2 * (|w.thirdDiagonalMass j k l| * |w.v m|) +
          2 * (|w.thirdDiagonalMass j k m| * |w.v l|) +
          2 * (|w.thirdDiagonalMass j l m| * |w.v k|) +
          2 * (|w.thirdDiagonalMass k l m| * |w.v j|) +
          1 * (w.fourthDiagonalMass j k l m)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact Finset.sum_le_sum fun m _ => hpoint j k l m
    _ = 24 * (∑ j, |w.v j|) ^ 4 + 36 * (w.theta * (∑ j, |w.v j|) ^ 2) +
        6 * w.theta ^ 2 + 8 * (∑ j, |w.v j|) ^ 2 + w.theta := by
      simp_rw [Finset.sum_add_distrib]
      rw [hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15]
      ring
    _ ≤ 75 * w.theta := by linarith only [hA4, hmix, htheta2, hA2, hAtheta]

theorem abs_v_le_coordinateMass (j : Fin p) : |w.v j| ≤ w.coordinateMass j := by
  unfold v coordinateMass
  apply abs_le.mpr
  constructor <;> linarith [w.pi_nonneg (j, true), w.pi_nonneg (j, false)]

noncomputable def thirdAbsDiagonalMass (j k l : Fin p) : ℝ :=
  if j = k ∧ j = l then w.coordinateMass j else 0

theorem thirdAbsDiagonalMass_nonneg (j k l : Fin p) : 0 ≤ w.thirdAbsDiagonalMass j k l := by
  unfold thirdAbsDiagonalMass
  split_ifs
  · exact w.coordinateMass_nonneg j
  · rfl

theorem abs_thirdDiagonalMass_le (j k l : Fin p) :
    |w.thirdDiagonalMass j k l| ≤ w.thirdAbsDiagonalMass j k l := by
  unfold thirdDiagonalMass thirdAbsDiagonalMass
  split_ifs
  · exact w.abs_v_le_coordinateMass j
  · simp

noncomputable def thirdMajorant (j k l : Fin p) : ℝ :=
  6 * w.coordinateMass j * w.coordinateMass k * w.coordinateMass l +
    2 * (w.diagonalMass j k * w.coordinateMass l +
      w.diagonalMass j l * w.coordinateMass k +
      w.diagonalMass k l * w.coordinateMass j) + w.thirdAbsDiagonalMass j k l

noncomputable def fourthMajorant (j k l m : Fin p) : ℝ :=
  24 * w.coordinateMass j * w.coordinateMass k * w.coordinateMass l * w.coordinateMass m +
    6 * (w.diagonalMass j k * w.coordinateMass l * w.coordinateMass m +
      w.diagonalMass j l * w.coordinateMass k * w.coordinateMass m +
      w.diagonalMass j m * w.coordinateMass k * w.coordinateMass l +
      w.diagonalMass k l * w.coordinateMass j * w.coordinateMass m +
      w.diagonalMass k m * w.coordinateMass j * w.coordinateMass l +
      w.diagonalMass l m * w.coordinateMass j * w.coordinateMass k) +
    2 * (w.diagonalMass j k * w.diagonalMass l m +
      w.diagonalMass j l * w.diagonalMass k m +
      w.diagonalMass j m * w.diagonalMass k l) +
    2 * (w.thirdAbsDiagonalMass j k l * w.coordinateMass m +
      w.thirdAbsDiagonalMass j k m * w.coordinateMass l +
      w.thirdAbsDiagonalMass j l m * w.coordinateMass k +
      w.thirdAbsDiagonalMass k l m * w.coordinateMass j) + w.fourthDiagonalMass j k l m

theorem sum_thirdMajorant :
    (∑ j, ∑ k, ∑ l, w.thirdMajorant j k l) =
      6 * w.theta ^ 3 + 6 * w.theta ^ 2 + w.theta := by
  have hif (P : Prop) [Decidable P] (f : Fin p → ℝ) :
      (∑ i, if P then f i else 0) = if P then ∑ i, f i else 0 := by
    by_cases h : P <;> simp [h]
  simp only [thirdMajorant, thirdAbsDiagonalMass, diagonalMass,
    ite_and, ite_mul, mul_ite, zero_mul, mul_zero, mul_add, Finset.sum_add_distrib]
  simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
  ring

theorem sum_fourthMajorant :
    (∑ j, ∑ k, ∑ l, ∑ m, w.fourthMajorant j k l m) =
      24 * w.theta ^ 4 + 36 * w.theta ^ 3 + 14 * w.theta ^ 2 + w.theta := by
  have hif (P : Prop) [Decidable P] (f : Fin p → ℝ) :
      (∑ i, if P then f i else 0) = if P then ∑ i, f i else 0 := by
    by_cases h : P <;> simp [h]
  simp only [fourthMajorant, thirdAbsDiagonalMass, fourthDiagonalMass, diagonalMass,
    ite_and, ite_mul, mul_ite, zero_mul, mul_zero, mul_add, Finset.sum_add_distrib]
  simp only [hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, w.sum_coordinateMass]
  ring


theorem sum_thirdMajorant_le :
    (∑ j, ∑ k, ∑ l, w.thirdMajorant j k l) ≤ 13 * w.theta := by
  rw [w.sum_thirdMajorant]
  have hpow (n : ℕ) : w.theta ^ (n + 1) ≤ w.theta := by
    simpa [pow_succ] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ w.theta_nonneg w.theta_lt_one.le : w.theta ^ n ≤ 1) w.theta_nonneg
  have h2 : w.theta ^ 2 ≤ w.theta := by simpa using hpow 1
  have h3 : w.theta ^ 3 ≤ w.theta := by simpa using hpow 2
  linarith only [h2, h3]

theorem sum_fourthMajorant_le :
    (∑ j, ∑ k, ∑ l, ∑ m, w.fourthMajorant j k l m) ≤ 75 * w.theta := by
  rw [w.sum_fourthMajorant]
  have hpow (n : ℕ) : w.theta ^ (n + 1) ≤ w.theta := by
    simpa [pow_succ] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ w.theta_nonneg w.theta_lt_one.le : w.theta ^ n ≤ 1) w.theta_nonneg
  have h2 : w.theta ^ 2 ≤ w.theta := by simpa using hpow 1
  have h3 : w.theta ^ 3 ≤ w.theta := by simpa using hpow 2
  have h4 : w.theta ^ 4 ≤ w.theta := by simpa using hpow 3
  linarith only [h2, h3, h4]

theorem abs_thirdFactor_le_majorant (j k l : Fin p) :
    |w.thirdFactor j k l| ≤ w.thirdMajorant j k l := by
  have hmass0 := w.coordinateMass_nonneg j
  have hmass1 := w.coordinateMass_nonneg k
  have hmass2 := w.coordinateMass_nonneg l
  have hDjk := w.diagonalMass_nonneg j k
  have hDjl := w.diagonalMass_nonneg j l
  have hDkl := w.diagonalMass_nonneg k l
  let terms : Fin 5 → ℝ := ![-6 * w.v j * w.v k * w.v l,
    2 * w.diagonalMass j k * w.v l,
    2 * w.diagonalMass j l * w.v k,
    2 * w.diagonalMass k l * w.v j,
    -w.thirdDiagonalMass j k l]
  let bounds : Fin 5 → ℝ := ![6 * w.coordinateMass j * w.coordinateMass k * w.coordinateMass l,
    2 * w.diagonalMass j k * w.coordinateMass l,
    2 * w.diagonalMass j l * w.coordinateMass k,
    2 * w.diagonalMass k l * w.coordinateMass j,
    w.thirdAbsDiagonalMass j k l]
  have hterms : (∑ i, terms i) = w.thirdFactor j k l := by
    simp [terms, thirdFactor, Fin.sum_univ_succ]
    ring
  have hbounds : (∑ i, bounds i) = w.thirdMajorant j k l := by
    simp [bounds, thirdMajorant, Fin.sum_univ_succ]
    ring
  have hpoint (i : Fin 5) : |terms i| ≤ bounds i := by
    fin_cases i <;> simp only [terms, bounds, Matrix.cons_val_zero, Matrix.cons_val_succ, abs_mul, abs_neg]
    all_goals norm_num
    all_goals try simp only [abs_mul, abs_neg, abs_of_nonneg hDjk, abs_of_nonneg hDjl, abs_of_nonneg hDkl, show |(6 : ℝ)| = 6 by norm_num, show |(2 : ℝ)| = 2 by norm_num]
    all_goals first | exact w.abs_thirdDiagonalMass_le _ _ _ | (gcongr <;> exact w.abs_v_le_coordinateMass _)
  rw [← hterms, ← hbounds]
  exact (Finset.abs_sum_le_sum_abs terms Finset.univ).trans
    (Finset.sum_le_sum fun i _ => hpoint i)

theorem abs_fourthFactor_le_majorant (j k l m : Fin p) :
    |w.fourthFactor j k l m| ≤ w.fourthMajorant j k l m := by
  have hmass0 := w.coordinateMass_nonneg j
  have hmass1 := w.coordinateMass_nonneg k
  have hmass2 := w.coordinateMass_nonneg l
  have hmass3 := w.coordinateMass_nonneg m
  have hDjk := w.diagonalMass_nonneg j k
  have hDjl := w.diagonalMass_nonneg j l
  have hDkl := w.diagonalMass_nonneg k l
  have hDjm := w.diagonalMass_nonneg j m
  have hDkm := w.diagonalMass_nonneg k m
  have hDlm := w.diagonalMass_nonneg l m
  have hG : 0 ≤ w.fourthDiagonalMass j k l m := by
    unfold fourthDiagonalMass
    split_ifs
    · exact w.coordinateMass_nonneg j
    · rfl
  have hEjkl := w.thirdAbsDiagonalMass_nonneg j k l
  have hEjkm := w.thirdAbsDiagonalMass_nonneg j k m
  have hEjlm := w.thirdAbsDiagonalMass_nonneg j l m
  have hEklm := w.thirdAbsDiagonalMass_nonneg k l m
  let terms : Fin 15 → ℝ := ![24 * w.v j * w.v k * w.v l * w.v m,
    -6 * w.diagonalMass j k * w.v l * w.v m,
    -6 * w.diagonalMass j l * w.v k * w.v m,
    -6 * w.diagonalMass j m * w.v k * w.v l,
    -6 * w.diagonalMass k l * w.v j * w.v m,
    -6 * w.diagonalMass k m * w.v j * w.v l,
    -6 * w.diagonalMass l m * w.v j * w.v k,
    2 * w.diagonalMass j k * w.diagonalMass l m,
    2 * w.diagonalMass j l * w.diagonalMass k m,
    2 * w.diagonalMass j m * w.diagonalMass k l,
    2 * w.thirdDiagonalMass j k l * w.v m,
    2 * w.thirdDiagonalMass j k m * w.v l,
    2 * w.thirdDiagonalMass j l m * w.v k,
    2 * w.thirdDiagonalMass k l m * w.v j,
    -w.fourthDiagonalMass j k l m]
  let bounds : Fin 15 → ℝ := ![24 * w.coordinateMass j * w.coordinateMass k * w.coordinateMass l * w.coordinateMass m,
    6 * w.diagonalMass j k * w.coordinateMass l * w.coordinateMass m,
    6 * w.diagonalMass j l * w.coordinateMass k * w.coordinateMass m,
    6 * w.diagonalMass j m * w.coordinateMass k * w.coordinateMass l,
    6 * w.diagonalMass k l * w.coordinateMass j * w.coordinateMass m,
    6 * w.diagonalMass k m * w.coordinateMass j * w.coordinateMass l,
    6 * w.diagonalMass l m * w.coordinateMass j * w.coordinateMass k,
    2 * w.diagonalMass j k * w.diagonalMass l m,
    2 * w.diagonalMass j l * w.diagonalMass k m,
    2 * w.diagonalMass j m * w.diagonalMass k l,
    2 * w.thirdAbsDiagonalMass j k l * w.coordinateMass m,
    2 * w.thirdAbsDiagonalMass j k m * w.coordinateMass l,
    2 * w.thirdAbsDiagonalMass j l m * w.coordinateMass k,
    2 * w.thirdAbsDiagonalMass k l m * w.coordinateMass j,
    w.fourthDiagonalMass j k l m]
  have hterms : (∑ i, terms i) = w.fourthFactor j k l m := by
    simp [terms, fourthFactor, Fin.sum_univ_succ]
    ring
  have hbounds : (∑ i, bounds i) = w.fourthMajorant j k l m := by
    simp [bounds, fourthMajorant, Fin.sum_univ_succ]
    ring
  have hpoint (i : Fin 15) : |terms i| ≤ bounds i := by
    fin_cases i <;> simp only [terms, bounds, Matrix.cons_val_zero, Matrix.cons_val_succ, abs_mul, abs_neg]
    all_goals norm_num
    all_goals try simp only [abs_mul, abs_neg, abs_of_nonneg hDjk, abs_of_nonneg hDjl, abs_of_nonneg hDkl, abs_of_nonneg hDjm, abs_of_nonneg hDkm, abs_of_nonneg hDlm, abs_of_nonneg hG, show |(24 : ℝ)| = 24 by norm_num, show |(6 : ℝ)| = 6 by norm_num, show |(2 : ℝ)| = 2 by norm_num]
    all_goals first | rfl | (gcongr <;> first | exact w.abs_v_le_coordinateMass _ | exact w.abs_thirdDiagonalMass_le _ _ _)
  rw [← hterms, ← hbounds]
  exact (Finset.abs_sum_le_sum_abs terms Finset.univ).trans
    (Finset.sum_le_sum fun i _ => hpoint i)


theorem thirdMajorant_nonneg (j k l : Fin p) : 0 ≤ w.thirdMajorant j k l :=
  (abs_nonneg _).trans (w.abs_thirdFactor_le_majorant j k l)

theorem fourthMajorant_nonneg (j k l m : Fin p) : 0 ≤ w.fourthMajorant j k l m :=
  (abs_nonneg _).trans (w.abs_fourthFactor_le_majorant j k l m)

theorem coordinateMass_le_power (w' : FaceWeights p) {K : ℝ} (hK : 1 ≤ K)
    (hmass : ∀ j, w'.coordinateMass j ≤ K * w.coordinateMass j)
    {n : ℕ} (hn : 1 ≤ n) (j : Fin p) :
    w'.coordinateMass j ≤ K ^ n * w.coordinateMass j := by
  exact (hmass j).trans (mul_le_mul_of_nonneg_right
    (by simpa only [pow_one] using pow_le_pow_right₀ hK hn) (w.coordinateMass_nonneg j))

theorem diagonalMass_le_power (w' : FaceWeights p) {K : ℝ} (hK : 1 ≤ K)
    (hmass : ∀ j, w'.coordinateMass j ≤ K * w.coordinateMass j)
    {n : ℕ} (hn : 1 ≤ n) (j k : Fin p) :
    w'.diagonalMass j k ≤ K ^ n * w.diagonalMass j k := by
  by_cases hjk : j = k
  · simpa only [diagonalMass, hjk, ↓reduceIte] using
      w.coordinateMass_le_power w' hK hmass hn j
  · simp only [diagonalMass, hjk, ↓reduceIte, mul_zero, le_refl]

theorem thirdAbsDiagonalMass_le_power (w' : FaceWeights p) {K : ℝ} (hK : 1 ≤ K)
    (hmass : ∀ j, w'.coordinateMass j ≤ K * w.coordinateMass j)
    {n : ℕ} (hn : 1 ≤ n) (j k l : Fin p) :
    w'.thirdAbsDiagonalMass j k l ≤ K ^ n * w.thirdAbsDiagonalMass j k l := by
  unfold thirdAbsDiagonalMass
  split_ifs
  · exact w.coordinateMass_le_power w' hK hmass hn j
  · simp only [mul_zero, le_refl]

theorem fourthDiagonalMass_le_power (w' : FaceWeights p) {K : ℝ} (hK : 1 ≤ K)
    (hmass : ∀ j, w'.coordinateMass j ≤ K * w.coordinateMass j)
    {n : ℕ} (hn : 1 ≤ n) (j k l m : Fin p) :
    w'.fourthDiagonalMass j k l m ≤ K ^ n * w.fourthDiagonalMass j k l m := by
  unfold fourthDiagonalMass
  split_ifs
  · exact w.coordinateMass_le_power w' hK hmass hn j
  · simp only [mul_zero, le_refl]

theorem thirdMajorant_le_of_coordinateMass_le (w' : FaceWeights p) {K : ℝ}
    (hK : 1 ≤ K) (hmass : ∀ j, w'.coordinateMass j ≤ K * w.coordinateMass j)
    (j k l : Fin p) : w'.thirdMajorant j k l ≤ K ^ 3 * w.thirdMajorant j k l := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hM := w.coordinateMass_nonneg
  have hD := w.diagonalMass_nonneg
  have hBM0 := w.coordinateMass_nonneg j
  have hBM1 := w.coordinateMass_nonneg k
  have hBM2 := w.coordinateMass_nonneg l
  have hBD0 := w.diagonalMass_nonneg j k
  have hBD1 := w.diagonalMass_nonneg j l
  have hBD2 := w.diagonalMass_nonneg k l
  have hSM0 := w'.coordinateMass_nonneg j
  have hSM1 := w'.coordinateMass_nonneg k
  have hSM2 := w'.coordinateMass_nonneg l
  have hSD0 := w'.diagonalMass_nonneg j k
  have hSD1 := w'.diagonalMass_nonneg j l
  have hSD2 := w'.diagonalMass_nonneg k l
  calc
    _ ≤ 6 * (K * w.coordinateMass j) * (K * w.coordinateMass k) *
          (K * w.coordinateMass l) +
        2 * ((K ^ 2 * w.diagonalMass j k) * (K * w.coordinateMass l) +
          (K ^ 2 * w.diagonalMass j l) * (K * w.coordinateMass k) +
          (K ^ 2 * w.diagonalMass k l) * (K * w.coordinateMass j)) +
        K ^ 3 * w.thirdAbsDiagonalMass j k l := by
      unfold thirdMajorant
      gcongr <;> first
        | exact hmass _
        | exact w.diagonalMass_le_power w' hK hmass (n := 2) (by norm_num) _ _
        | exact w.thirdAbsDiagonalMass_le_power w' hK hmass (n := 3) (by norm_num) _ _ _
    _ = _ := by unfold thirdMajorant; ring

theorem fourthMajorant_le_of_coordinateMass_le (w' : FaceWeights p) {K : ℝ}
    (hK : 1 ≤ K) (hmass : ∀ j, w'.coordinateMass j ≤ K * w.coordinateMass j)
    (j k l m : Fin p) :
    w'.fourthMajorant j k l m ≤ K ^ 4 * w.fourthMajorant j k l m := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hM := w.coordinateMass_nonneg
  have hD := w.diagonalMass_nonneg
  have hE := w.thirdAbsDiagonalMass_nonneg
  have hBM0 := w.coordinateMass_nonneg j
  have hBM1 := w.coordinateMass_nonneg k
  have hBM2 := w.coordinateMass_nonneg l
  have hBM3 := w.coordinateMass_nonneg m
  have hBD0 := w.diagonalMass_nonneg j k
  have hBD1 := w.diagonalMass_nonneg j l
  have hBD2 := w.diagonalMass_nonneg j m
  have hBD3 := w.diagonalMass_nonneg k l
  have hBD4 := w.diagonalMass_nonneg k m
  have hBD5 := w.diagonalMass_nonneg l m
  have hBE0 := w.thirdAbsDiagonalMass_nonneg j k l
  have hBE1 := w.thirdAbsDiagonalMass_nonneg j k m
  have hBE2 := w.thirdAbsDiagonalMass_nonneg j l m
  have hBE3 := w.thirdAbsDiagonalMass_nonneg k l m
  have hSM0 := w'.coordinateMass_nonneg j
  have hSM1 := w'.coordinateMass_nonneg k
  have hSM2 := w'.coordinateMass_nonneg l
  have hSM3 := w'.coordinateMass_nonneg m
  have hSD0 := w'.diagonalMass_nonneg j k
  have hSD1 := w'.diagonalMass_nonneg j l
  have hSD2 := w'.diagonalMass_nonneg j m
  have hSD3 := w'.diagonalMass_nonneg k l
  have hSD4 := w'.diagonalMass_nonneg k m
  have hSD5 := w'.diagonalMass_nonneg l m
  have hSE0 := w'.thirdAbsDiagonalMass_nonneg j k l
  have hSE1 := w'.thirdAbsDiagonalMass_nonneg j k m
  have hSE2 := w'.thirdAbsDiagonalMass_nonneg j l m
  have hSE3 := w'.thirdAbsDiagonalMass_nonneg k l m
  calc
    _ ≤ 24 * (K * w.coordinateMass j) * (K * w.coordinateMass k) *
          (K * w.coordinateMass l) * (K * w.coordinateMass m) +
        6 * ((K ^ 2 * w.diagonalMass j k) * (K * w.coordinateMass l) * (K * w.coordinateMass m) +
          (K ^ 2 * w.diagonalMass j l) * (K * w.coordinateMass k) * (K * w.coordinateMass m) +
          (K ^ 2 * w.diagonalMass j m) * (K * w.coordinateMass k) * (K * w.coordinateMass l) +
          (K ^ 2 * w.diagonalMass k l) * (K * w.coordinateMass j) * (K * w.coordinateMass m) +
          (K ^ 2 * w.diagonalMass k m) * (K * w.coordinateMass j) * (K * w.coordinateMass l) +
          (K ^ 2 * w.diagonalMass l m) * (K * w.coordinateMass j) * (K * w.coordinateMass k)) +
        2 * ((K ^ 2 * w.diagonalMass j k) * (K ^ 2 * w.diagonalMass l m) +
          (K ^ 2 * w.diagonalMass j l) * (K ^ 2 * w.diagonalMass k m) +
          (K ^ 2 * w.diagonalMass j m) * (K ^ 2 * w.diagonalMass k l)) +
        2 * ((K ^ 3 * w.thirdAbsDiagonalMass j k l) * (K * w.coordinateMass m) +
          (K ^ 3 * w.thirdAbsDiagonalMass j k m) * (K * w.coordinateMass l) +
          (K ^ 3 * w.thirdAbsDiagonalMass j l m) * (K * w.coordinateMass k) +
          (K ^ 3 * w.thirdAbsDiagonalMass k l m) * (K * w.coordinateMass j)) +
        K ^ 4 * w.fourthDiagonalMass j k l m := by
      unfold fourthMajorant
      gcongr <;> first
        | exact hmass _
        | exact w.diagonalMass_le_power w' hK hmass (n := 2) (by norm_num) _ _
        | exact w.thirdAbsDiagonalMass_le_power w' hK hmass (n := 3) (by norm_num) _ _ _
        | exact w.fourthDiagonalMass_le_power w' hK hmass (n := 4) (by norm_num) _ _ _ _
    _ = _ := by unfold fourthMajorant; ring

end FaceWeights

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- The derivative of the signed coordinate mass along a coordinate line. -/
theorem hasDerivAt_v_coordinate (x : Fin p → ℝ) (j l : Fin p) (t : ℝ) :
    HasDerivAt (fun r => (s.weights (line x (coordinateDirection l) r)).v j)
      (((s.weights (line x (coordinateDirection l) t)).diagonalMass j l -
        (s.weights (line x (coordinateDirection l) t)).v j *
          (s.weights (line x (coordinateDirection l) t)).v l) / s.bandwidth) t := by
  have hd := s.hasDerivAt_v_coordinate_line x (coordinateDirection l) j t
  by_cases hjl : j = l <;>
    simpa only [v, directionalMean_coordinate, coordinateDirection,
      FaceWeights.diagonalMass, hjl, ↓reduceIte, mul_one, mul_zero] using hd

/-- The derivative of the unsigned coordinate mass, proved from the two
actual normalized-face derivatives. -/
theorem hasDerivAt_coordinateMass_coordinate
    (x : Fin p → ℝ) (j l : Fin p) (t : ℝ) :
    HasDerivAt
      (fun r => (s.weights (line x (coordinateDirection l) r)).coordinateMass j)
      (((if j = l then (s.weights (line x (coordinateDirection l) t)).v j else 0) -
        (s.weights (line x (coordinateDirection l) t)).coordinateMass j *
          (s.weights (line x (coordinateDirection l) t)).v l) / s.bandwidth) t := by
  have hd := (s.hasDerivAt_pi_line (j, true) x (coordinateDirection l) t).add
    (s.hasDerivAt_pi_line (j, false) x (coordinateDirection l) t)
  have heq :
      (s.pi (line x (coordinateDirection l) t) (j, true) / s.bandwidth *
          (normalDot (j, true) (coordinateDirection l) -
            (s.weights (line x (coordinateDirection l) t)).directionalMean
              (coordinateDirection l)) +
        s.pi (line x (coordinateDirection l) t) (j, false) / s.bandwidth *
          (normalDot (j, false) (coordinateDirection l) -
            (s.weights (line x (coordinateDirection l) t)).directionalMean
              (coordinateDirection l))) =
        ((if j = l then (s.weights (line x (coordinateDirection l) t)).v j else 0) -
          (s.weights (line x (coordinateDirection l) t)).coordinateMass j *
            (s.weights (line x (coordinateDirection l) t)).v l) / s.bandwidth := by
    simp only [normalDot, Bool.false_eq_true, ↓reduceIte, directionalMean_coordinate,
      coordinateDirection, pi, FaceWeights.coordinateMass, FaceWeights.v]
    split_ifs <;> ring
  rw [heq] at hd
  exact hd

/-- Differentiation of the diagonal second raw moment, with repeated indices
handled explicitly rather than by assuming distinct coordinates. -/
theorem hasDerivAt_diagonalMass_coordinate
    (x : Fin p → ℝ) (j k l : Fin p) (t : ℝ) :
    HasDerivAt
      (fun r => (s.weights (line x (coordinateDirection l) r)).diagonalMass j k)
      (((s.weights (line x (coordinateDirection l) t)).thirdDiagonalMass j k l -
        (s.weights (line x (coordinateDirection l) t)).diagonalMass j k *
          (s.weights (line x (coordinateDirection l) t)).v l) / s.bandwidth) t := by
  by_cases hjk : j = k
  · subst k
    simpa only [FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass,
      true_and, ↓reduceIte] using s.hasDerivAt_coordinateMass_coordinate x j l t
  · simpa only [FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass,
      hjk, false_and, ↓reduceIte, zero_mul, sub_self, zero_div] using
      (hasDerivAt_const t (0 : ℝ))

/-- Differentiating the actual mixed second derivative along a coordinate line. -/
theorem hasDerivAt_mixedSecondDerivativeF_coordinate
    (x : Fin p → ℝ) (j k l : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.mixedSecondDerivativeF (line x (coordinateDirection l) r) j k)
      ((s.F (line x (coordinateDirection l) t) / s.bandwidth ^ 3) *
        (s.weights (line x (coordinateDirection l) t)).thirdFactor j k l) t := by
  simp_rw [s.mixedSecondDerivativeF_eq]
  have hd := ((s.hasDerivAt_F_line x (coordinateDirection l) t).div_const
      (s.bandwidth ^ 2)).mul
    ((((s.hasDerivAt_v_coordinate x j l t).const_mul 2).mul
      (s.hasDerivAt_v_coordinate x k l t)).sub
      (s.hasDerivAt_diagonalMass_coordinate x j k l t))
  convert hd using 1
  simp only [directionalMean_coordinate, FaceWeights.thirdFactor]
  field_simp [ne_of_gt s.bandwidth_pos]
  ring

/-- An actual iterated mixed third coordinate derivative. -/
noncomputable def mixedThirdDerivativeF (x : Fin p → ℝ) (j k l : Fin p) : ℝ :=
  deriv (fun t => s.mixedSecondDerivativeF (line x (coordinateDirection l) t) j k) 0

theorem mixedThirdDerivativeF_eq (x : Fin p → ℝ) (j k l : Fin p) :
    s.mixedThirdDerivativeF x j k l =
      (s.F x / s.bandwidth ^ 3) * (s.weights x).thirdFactor j k l := by
  simpa only [mixedThirdDerivativeF, line_zero] using
    (s.hasDerivAt_mixedSecondDerivativeF_coordinate x j k l 0).deriv

/-- The total absolute mass of actual ordered third coordinate derivatives,
with the pointwise constant `13`. -/
theorem sum_abs_mixedThirdDerivativeF_le_variance (x : Fin p → ℝ) :
    (∑ j, ∑ k, ∑ l, |s.mixedThirdDerivativeF x j k l|) ≤
      13 * s.F x * (1 - s.F x) / s.bandwidth ^ 3 := by
  have hc : 0 ≤ s.F x / s.bandwidth ^ 3 :=
    div_nonneg (s.F_pos x).le (pow_nonneg s.bandwidth_pos.le _)
  calc
    _ = (s.F x / s.bandwidth ^ 3) *
        (∑ j, ∑ k, ∑ l, |(s.weights x).thirdFactor j k l|) := by
      simp_rw [s.mixedThirdDerivativeF_eq, abs_mul, abs_of_nonneg hc]
      simp only [Finset.mul_sum]
    _ ≤ (s.F x / s.bandwidth ^ 3) * (13 * (s.weights x).theta) :=
      mul_le_mul_of_nonneg_left (s.weights x).sum_abs_third_factor_le hc
    _ = 13 * s.F x * (1 - s.F x) / s.bandwidth ^ 3 := by
      change (s.F x / s.bandwidth ^ 3) * (13 * (1 - s.F x)) = _
      ring

/-- The derivative of the third signed raw moment, including all repeated
coordinate patterns. -/
theorem hasDerivAt_thirdDiagonalMass_coordinate
    (x : Fin p → ℝ) (j k l m : Fin p) (t : ℝ) :
    HasDerivAt
      (fun r => (s.weights (line x (coordinateDirection m) r)).thirdDiagonalMass j k l)
      (((s.weights (line x (coordinateDirection m) t)).fourthDiagonalMass j k l m -
        (s.weights (line x (coordinateDirection m) t)).thirdDiagonalMass j k l *
          (s.weights (line x (coordinateDirection m) t)).v m) / s.bandwidth) t := by
  by_cases hjk : j = k
  · subst k
    by_cases hjl : j = l
    · subst l
      simpa only [FaceWeights.thirdDiagonalMass, FaceWeights.fourthDiagonalMass,
        FaceWeights.diagonalMass, true_and, ↓reduceIte] using
        s.hasDerivAt_v_coordinate x j m t
    · simpa only [FaceWeights.thirdDiagonalMass, FaceWeights.fourthDiagonalMass,
        hjl, true_and, false_and, ↓reduceIte, zero_mul, sub_self, zero_div] using
        (hasDerivAt_const t (0 : ℝ))
  · simpa only [FaceWeights.thirdDiagonalMass, FaceWeights.fourthDiagonalMass,
      hjk, false_and, ↓reduceIte, zero_mul, sub_self, zero_div] using
      (hasDerivAt_const t (0 : ℝ))

/-- Differentiating the actual mixed third derivative along a coordinate line. -/
theorem hasDerivAt_mixedThirdDerivativeF_coordinate
    (x : Fin p → ℝ) (j k l m : Fin p) (t : ℝ) :
    HasDerivAt
      (fun r => s.mixedThirdDerivativeF (line x (coordinateDirection m) r) j k l)
      ((s.F (line x (coordinateDirection m) t) / s.bandwidth ^ 4) *
        (s.weights (line x (coordinateDirection m) t)).fourthFactor j k l m) t := by
  simp_rw [s.mixedThirdDerivativeF_eq, FaceWeights.thirdFactor]
  have hprod := (((s.hasDerivAt_v_coordinate x j m t).const_mul (-6)).mul
      (s.hasDerivAt_v_coordinate x k m t)).mul
    (s.hasDerivAt_v_coordinate x l m t)
  have hpairs := (((s.hasDerivAt_diagonalMass_coordinate x j k m t).mul
        (s.hasDerivAt_v_coordinate x l m t)).add
      ((s.hasDerivAt_diagonalMass_coordinate x j l m t).mul
        (s.hasDerivAt_v_coordinate x k m t))).add
    ((s.hasDerivAt_diagonalMass_coordinate x k l m t).mul
      (s.hasDerivAt_v_coordinate x j m t))
  have hdFactor := (hprod.add (hpairs.const_mul 2)).sub
    (s.hasDerivAt_thirdDiagonalMass_coordinate x j k l m t)
  have hd := ((s.hasDerivAt_F_line x (coordinateDirection m) t).div_const
      (s.bandwidth ^ 3)).mul hdFactor
  convert hd using 1
  simp only [directionalMean_coordinate, FaceWeights.fourthFactor]
  ring_nf

/-- An actual iterated mixed fourth coordinate derivative. -/
noncomputable def mixedFourthDerivativeF (x : Fin p → ℝ) (j k l m : Fin p) : ℝ :=
  deriv (fun t => s.mixedThirdDerivativeF (line x (coordinateDirection m) t) j k l) 0

theorem mixedFourthDerivativeF_eq (x : Fin p → ℝ) (j k l m : Fin p) :
    s.mixedFourthDerivativeF x j k l m =
      (s.F x / s.bandwidth ^ 4) * (s.weights x).fourthFactor j k l m := by
  simpa only [mixedFourthDerivativeF, line_zero] using
    (s.hasDerivAt_mixedThirdDerivativeF_coordinate x j k l m 0).deriv

/-- The total absolute mass of actual ordered fourth coordinate derivatives,
with the pointwise constant `75`. -/
theorem sum_abs_mixedFourthDerivativeF_le_variance (x : Fin p → ℝ) :
    (∑ j, ∑ k, ∑ l, ∑ m, |s.mixedFourthDerivativeF x j k l m|) ≤
      75 * s.F x * (1 - s.F x) / s.bandwidth ^ 4 := by
  have hc : 0 ≤ s.F x / s.bandwidth ^ 4 :=
    div_nonneg (s.F_pos x).le (pow_nonneg s.bandwidth_pos.le _)
  calc
    _ = (s.F x / s.bandwidth ^ 4) *
        (∑ j, ∑ k, ∑ l, ∑ m, |(s.weights x).fourthFactor j k l m|) := by
      simp_rw [s.mixedFourthDerivativeF_eq, abs_mul, abs_of_nonneg hc]
      simp only [Finset.mul_sum]
    _ ≤ (s.F x / s.bandwidth ^ 4) * (75 * (s.weights x).theta) :=
      mul_le_mul_of_nonneg_left (s.weights x).sum_abs_fourth_factor_le hc
    _ = 75 * s.F x * (1 - s.F x) / s.bandwidth ^ 4 := by
      change (s.F x / s.bandwidth ^ 4) * (75 * (1 - s.F x)) = _
      ring


/-- Every normalized coordinate mass changes by at most `exp 2` under a shift
of maximum norm at most the bandwidth. -/
theorem coordinateMass_shift_le_bandwidth (x : Fin p → ℝ) {z : Fin p → ℝ}
    (hz : ‖z‖ ≤ s.bandwidth) (j : Fin p) :
    (s.weights (x + z)).coordinateMass j ≤
      Real.exp 2 * (s.weights x).coordinateMass j := by
  have hplus := s.pi_shift_le x hz (j, true)
  have hminus := s.pi_shift_le x hz (j, false)
  have hratio : 2 * s.bandwidth / s.bandwidth = (2 : ℝ) := by
    field_simp [ne_of_gt s.bandwidth_pos]
  rw [hratio] at hplus hminus
  simpa only [pi, FaceWeights.coordinateMass, mul_add] using add_le_add hplus hminus

private theorem F_shift_le_exp_two (x : Fin p → ℝ) {z : Fin p → ℝ}
    (hz : ‖z‖ ≤ s.bandwidth) : s.F (x + z) ≤ Real.exp 2 * s.F x := by
  have hF := s.F_shift_le x hz
  rw [div_self (ne_of_gt s.bandwidth_pos)] at hF
  exact hF.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2)) (s.F_pos x).le)

/-- A nonnegative bound for each third derivative throughout the whole
bandwidth-sized cube. It is fixed at the center before a shift is chosen. -/
noncomputable def thirdLocalMajorant (x : Fin p → ℝ) (j k l : Fin p) : ℝ :=
  (Real.exp 2) ^ 4 * (s.F x / s.bandwidth ^ 3) *
    (s.weights x).thirdMajorant j k l

noncomputable def fourthLocalMajorant (x : Fin p → ℝ) (j k l m : Fin p) : ℝ :=
  (Real.exp 2) ^ 5 * (s.F x / s.bandwidth ^ 4) *
    (s.weights x).fourthMajorant j k l m

theorem thirdLocalMajorant_nonneg (x : Fin p → ℝ) (j k l : Fin p) :
    0 ≤ s.thirdLocalMajorant x j k l := by
  exact mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _)
    (div_nonneg (s.F_pos x).le (pow_nonneg s.bandwidth_pos.le _)))
    ((s.weights x).thirdMajorant_nonneg j k l)

theorem fourthLocalMajorant_nonneg (x : Fin p → ℝ) (j k l m : Fin p) :
    0 ≤ s.fourthLocalMajorant x j k l m := by
  exact mul_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _)
    (div_nonneg (s.F_pos x).le (pow_nonneg s.bandwidth_pos.le _)))
    ((s.weights x).fourthMajorant_nonneg j k l m)

/-- Each actual third derivative is bounded by a center-dependent majorant,
uniformly for all shifts in the bandwidth cube. -/
theorem abs_mixedThirdDerivativeF_shift_le (x : Fin p → ℝ) {z : Fin p → ℝ}
    (hz : ‖z‖ ≤ s.bandwidth) (j k l : Fin p) :
    |s.mixedThirdDerivativeF (x + z) j k l| ≤ s.thirdLocalMajorant x j k l := by
  have hK : 1 ≤ Real.exp (2 : ℝ) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2)
  have hc : 0 ≤ s.F (x + z) / s.bandwidth ^ 3 :=
    div_nonneg (s.F_pos _).le (pow_nonneg s.bandwidth_pos.le _)
  have hc' : 0 ≤ Real.exp 2 * s.F x / s.bandwidth ^ 3 :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le (s.F_pos _).le)
      (pow_nonneg s.bandwidth_pos.le _)
  calc
    _ = (s.F (x + z) / s.bandwidth ^ 3) *
        |(s.weights (x + z)).thirdFactor j k l| := by
      rw [s.mixedThirdDerivativeF_eq, abs_mul, abs_of_nonneg hc]
    _ ≤ (s.F (x + z) / s.bandwidth ^ 3) *
        (s.weights (x + z)).thirdMajorant j k l :=
      mul_le_mul_of_nonneg_left ((s.weights (x + z)).abs_thirdFactor_le_majorant j k l) hc
    _ ≤ (Real.exp 2 * s.F x / s.bandwidth ^ 3) *
        ((Real.exp 2) ^ 3 * (s.weights x).thirdMajorant j k l) :=
      mul_le_mul
        (div_le_div_of_nonneg_right (s.F_shift_le_exp_two x hz)
          (pow_nonneg s.bandwidth_pos.le _))
        ((s.weights x).thirdMajorant_le_of_coordinateMass_le (s.weights (x + z)) hK
          (s.coordinateMass_shift_le_bandwidth x hz) j k l)
        ((s.weights (x + z)).thirdMajorant_nonneg j k l) hc'
    _ = _ := by unfold thirdLocalMajorant; ring

/-- The fourth-derivative counterpart, with the same majorant for every
admissible shift. -/
theorem abs_mixedFourthDerivativeF_shift_le (x : Fin p → ℝ) {z : Fin p → ℝ}
    (hz : ‖z‖ ≤ s.bandwidth) (j k l m : Fin p) :
    |s.mixedFourthDerivativeF (x + z) j k l m| ≤ s.fourthLocalMajorant x j k l m := by
  have hK : 1 ≤ Real.exp (2 : ℝ) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2)
  have hc : 0 ≤ s.F (x + z) / s.bandwidth ^ 4 :=
    div_nonneg (s.F_pos _).le (pow_nonneg s.bandwidth_pos.le _)
  have hc' : 0 ≤ Real.exp 2 * s.F x / s.bandwidth ^ 4 :=
    div_nonneg (mul_nonneg (Real.exp_pos _).le (s.F_pos _).le)
      (pow_nonneg s.bandwidth_pos.le _)
  calc
    _ = (s.F (x + z) / s.bandwidth ^ 4) *
        |(s.weights (x + z)).fourthFactor j k l m| := by
      rw [s.mixedFourthDerivativeF_eq, abs_mul, abs_of_nonneg hc]
    _ ≤ (s.F (x + z) / s.bandwidth ^ 4) *
        (s.weights (x + z)).fourthMajorant j k l m :=
      mul_le_mul_of_nonneg_left ((s.weights (x + z)).abs_fourthFactor_le_majorant j k l m) hc
    _ ≤ (Real.exp 2 * s.F x / s.bandwidth ^ 4) *
        ((Real.exp 2) ^ 4 * (s.weights x).fourthMajorant j k l m) :=
      mul_le_mul
        (div_le_div_of_nonneg_right (s.F_shift_le_exp_two x hz)
          (pow_nonneg s.bandwidth_pos.le _))
        ((s.weights x).fourthMajorant_le_of_coordinateMass_le (s.weights (x + z)) hK
          (s.coordinateMass_shift_le_bandwidth x hz) j k l m)
        ((s.weights (x + z)).fourthMajorant_nonneg j k l m) hc'
    _ = _ := by unfold fourthLocalMajorant; ring

/-- Summable uniform entry bounds. Since each individual bound is independent
of the shift, this also controls the sum of the individual local suprema. -/
theorem sum_thirdLocalMajorant_le_variance (x : Fin p → ℝ) :
    (∑ j, ∑ k, ∑ l, s.thirdLocalMajorant x j k l) ≤
      (13 * (Real.exp 2) ^ 4) * s.F x * (1 - s.F x) / s.bandwidth ^ 3 := by
  have hc : 0 ≤ (Real.exp 2) ^ 4 * (s.F x / s.bandwidth ^ 3) := by
    exact mul_nonneg (pow_nonneg (Real.exp_pos _).le _)
      (div_nonneg (s.F_pos x).le (pow_nonneg s.bandwidth_pos.le _))
  calc
    _ = ((Real.exp 2) ^ 4 * (s.F x / s.bandwidth ^ 3)) *
        (∑ j, ∑ k, ∑ l, (s.weights x).thirdMajorant j k l) := by
      simp only [thirdLocalMajorant, Finset.mul_sum]
    _ ≤ ((Real.exp 2) ^ 4 * (s.F x / s.bandwidth ^ 3)) *
        (13 * (s.weights x).theta) :=
      mul_le_mul_of_nonneg_left (s.weights x).sum_thirdMajorant_le hc
    _ = _ := by
      change ((Real.exp 2) ^ 4 * (s.F x / s.bandwidth ^ 3)) *
        (13 * (1 - s.F x)) = _
      ring

theorem sum_fourthLocalMajorant_le_variance (x : Fin p → ℝ) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m) ≤
      (75 * (Real.exp 2) ^ 5) * s.F x * (1 - s.F x) / s.bandwidth ^ 4 := by
  have hc : 0 ≤ (Real.exp 2) ^ 5 * (s.F x / s.bandwidth ^ 4) := by
    exact mul_nonneg (pow_nonneg (Real.exp_pos _).le _)
      (div_nonneg (s.F_pos x).le (pow_nonneg s.bandwidth_pos.le _))
  calc
    _ = ((Real.exp 2) ^ 5 * (s.F x / s.bandwidth ^ 4)) *
        (∑ j, ∑ k, ∑ l, ∑ m, (s.weights x).fourthMajorant j k l m) := by
      simp only [fourthLocalMajorant, Finset.mul_sum]
    _ ≤ ((Real.exp 2) ^ 5 * (s.F x / s.bandwidth ^ 4)) *
        (75 * (s.weights x).theta) :=
      mul_le_mul_of_nonneg_left (s.weights x).sum_fourthMajorant_le hc
    _ = _ := by
      change ((Real.exp 2) ^ 5 * (s.F x / s.bandwidth ^ 4)) *
        (75 * (1 - s.F x)) = _
      ring

end FaceSmoother
end RectangleCLT
