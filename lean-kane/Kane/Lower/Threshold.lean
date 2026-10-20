import Kane.Halfspace
import Kane.Combinatorial
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Symmetric threshold halfspaces and their exact finite binomial distribution. -/

open scoped BigOperators

namespace Kane.Lower

/-- Number of positive coordinates. -/
def hammingWeight {n : ℕ} (x : Cube n) : ℕ :=
  ∑ i, if x i then 1 else 0

def trueCoordinates {n : ℕ} (x : Cube n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

theorem hammingWeight_eq_card {n : ℕ} (x : Cube n) :
    hammingWeight x = (trueCoordinates x).card := by
  simp only [hammingWeight, trueCoordinates, Finset.card_filter]

theorem hammingWeight_le {n : ℕ} (x : Cube n) : hammingWeight x ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> omega
    _ = n := by simp

/-- Boolean cubes are finite sets of their positive coordinates. -/
def cubeFinsetEquiv (n : ℕ) : Cube n ≃ Finset (Fin n) where
  toFun := trueCoordinates
  invFun s i := decide (i ∈ s)
  left_inv x := by
    funext i
    simp [trueCoordinates]
  right_inv s := by
    ext i
    simp [trueCoordinates]

/-- The exact size of every Hamming layer, including the empty out-of-range layers. -/
theorem layer_card (n r : ℕ) :
    (Finset.univ.filter (fun x : Cube n => hammingWeight x = r)).card = n.choose r := by
  classical
  calc
    _ = Fintype.card {x : Cube n // hammingWeight x = r} :=
      (Fintype.subtype_card _ (fun x => by simp)).symm
    _ = Fintype.card {s : Finset (Fin n) // s.card = r} :=
      Fintype.card_congr ((cubeFinsetEquiv n).subtypeEquiv
        (fun x => by
          change hammingWeight x = r ↔ (trueCoordinates x).card = r
          rw [hammingWeight_eq_card]))
    _ = n.choose r := by simp

/-- Summation on the cube can be grouped into binomially sized Hamming layers. -/
theorem sum_hammingWeight (n : ℕ) (g : ℕ → ℝ) :
    (∑ x : Cube n, g (hammingWeight x)) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * g j := by
  classical
  calc
    _ = ∑ j ∈ Finset.range (n + 1),
        ∑ x ∈ Finset.univ.filter (fun x : Cube n => hammingWeight x = j),
          g (hammingWeight x) :=
      (Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.range (n + 1)) (g := hammingWeight)
        (fun x _ => Finset.mem_range.mpr (by have := hammingWeight_le x; omega))
        (fun x => g (hammingWeight x))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∑ _x ∈ Finset.univ.filter (fun x : Cube n => hammingWeight x = j), g j := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := by simp [layer_card]

/-- The upper Hamming tail, with its threshold included. -/
def hammingThreshold (n r : ℕ) (x : Cube n) : Bool := decide (r ≤ hammingWeight x)

/-- A genuine closed real halfspace realizing the integer Hamming threshold. -/
noncomputable def thresholdHalfspace (n r : ℕ) : Halfspace n where
  weights _ := 1
  threshold := 2 * (r : ℝ) - (n : ℝ)

theorem hammingWeight_cast {n : ℕ} (x : Cube n) :
    (hammingWeight x : ℝ) = ∑ i, boolVal (x i) := by
  simp only [hammingWeight, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [hx, boolVal]

theorem thresholdHalfspace_score (n r : ℕ) (x : Cube n) :
    (thresholdHalfspace n r).score x = 2 * (hammingWeight x : ℝ) - n := by
  unfold Halfspace.score thresholdHalfspace
  simp only [one_mul]
  calc
    _ = ∑ i, (2 * boolVal (x i) - 1) := by
      apply Finset.sum_congr rfl
      intro i _
      cases hx : x i <;> norm_num [hx, boolVal]
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hammingWeight_cast]
      simp

theorem thresholdHalfspace_indicator (n r : ℕ) :
    (thresholdHalfspace n r).indicator = hammingThreshold n r := by
  classical
  funext x
  unfold Halfspace.indicator hammingThreshold
  rw [thresholdHalfspace_score]
  apply decide_eq_decide.mpr
  change (2 * (r : ℝ) - n ≤ 2 * (hammingWeight x : ℝ) - n) ↔ r ≤ hammingWeight x
  constructor
  · intro h
    have hr : (r : ℝ) ≤ hammingWeight x := by linarith
    exact_mod_cast hr
  · intro h
    have hr : (r : ℝ) ≤ hammingWeight x := by exact_mod_cast h
    linarith

/-- Exact upper-tail probability under the uniform Boolean-cube measure. -/
noncomputable def binomialTail (n r : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (n + 1), if r ≤ j then (n.choose j : ℝ) else 0) / (2 : ℝ) ^ n

theorem hammingThreshold_mass (n r : ℕ) :
    avg (fun x => boolVal (hammingThreshold n r x)) = binomialTail n r := by
  unfold avg binomialTail
  have hc : Fintype.card (Cube n) = 2 ^ n := by simp [Cube, Fintype.card_fun]
  rw [hc]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hs := sum_hammingWeight n (fun j => if r ≤ j then (1 : ℝ) else 0)
  have heq : (fun x : Cube n => boolVal (hammingThreshold n r x)) =
      (fun x => if r ≤ hammingWeight x then (1 : ℝ) else 0) := by
    funext x
    simp [hammingThreshold, boolVal]
  rw [heq, hs]
  simp only [mul_ite, mul_one, mul_zero]
  rw [div_eq_mul_inv]
  exact mul_comm _ _

/-- On a unate function, every sensitive edge is oriented toward its favorable
coordinate direction. This is the exact identity behind the lower bound. -/
theorem unate_edge_eq {n : ℕ} (f : UnateFunction n) (x : Cube n) (i : Fin n) :
    (if f.fn x = f.fn (flip x i) then (0 : ℝ) else 1) =
      signedCoord f.direction x i * (boolVal (f.fn x) - boolVal (f.fn (flip x i))) := by
  by_cases hx : x i = f.direction i
  · have hm := f.increasing x i hx
    cases ha : f.fn x <;> cases hb : f.fn (flip x i) <;>
      simp_all [signedCoord, boolVal, Bool.le_iff_imp]
  · have hflip : (flip x i) i = f.direction i := by
      simp only [flip, Function.update_self]
      cases hxi : x i <;> cases hsi : f.direction i <;> simp_all
    have hm : f.fn x ≤ f.fn (flip x i) := by
      simpa only [flip_flip] using f.increasing (flip x i) i hflip
    cases ha : f.fn x <;> cases hb : f.fn (flip x i) <;>
      simp_all [signedCoord, boolVal, Bool.le_iff_imp]

/-- The exact correlation formula for the average sensitivity of a unate function. -/
theorem unate_averageSensitivity_eq {n : ℕ} (f : UnateFunction n) :
    averageSensitivity f.fn =
      2 * avg (fun x => boolVal (f.fn x) * signedSum f.direction x) := by
  calc
    _ = avg (fun x => ∑ i : Fin n, signedCoord f.direction x i *
        (boolVal (f.fn x) - boolVal (f.fn (flip x i)))) := by
      apply avg_congr
      intro x
      exact Finset.sum_congr rfl (fun i _ => unate_edge_eq f x i)
    _ = _ := avg_signed_difference f.direction (fun x => boolVal (f.fn x))

/-- Uniform-weight real halfspaces, with an arbitrary real threshold. -/
noncomputable def uniformHalfspace (n : ℕ) (a : ℝ) : Halfspace n where
  weights _ := 1
  threshold := a

theorem uniformHalfspace_score (n : ℕ) (a : ℝ) (x : Cube n) :
    (uniformHalfspace n a).score x = signedSum (fun _ => true) x := by
  unfold Halfspace.score uniformHalfspace signedSum signedCoord
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [hx]

theorem uniformHalfspace_direction (n : ℕ) (a : ℝ) :
    (uniformHalfspace n a).toUnate.direction = (fun _ => true) := by
  funext i
  simp [Halfspace.toUnate, Halfspace.direction, uniformHalfspace]

/-- The all-one halfspace tests the signed coordinate sum. -/
theorem uniformHalfspace_indicator (n : ℕ) (a : ℝ) (x : Cube n) :
    (uniformHalfspace n a).indicator x =
      (by classical exact decide (a ≤ signedSum (fun _ => true) x)) := by
  classical
  simp only [Halfspace.indicator, uniformHalfspace_score]
  rfl

theorem uniformHalfspace_averageSensitivity_eq (n : ℕ) (a : ℝ) :
    averageSensitivity (uniformHalfspace n a).indicator =
      2 * avg (fun x => boolVal ((uniformHalfspace n a).indicator x) *
        signedSum (fun _ => true) x) := by
  have h := unate_averageSensitivity_eq (uniformHalfspace n a).toUnate
  simpa only [Halfspace.toUnate_fn, uniformHalfspace_direction] using h

/-- Threshold times mass bounds the unate correlation from below. The statement
also holds for negative thresholds; no positivity assumption is needed. -/
theorem uniformHalfspace_averageSensitivity_ge (n : ℕ) (a : ℝ) :
    2 * a * avg (fun x => boolVal ((uniformHalfspace n a).indicator x)) ≤
      averageSensitivity (uniformHalfspace n a).indicator := by
  rw [uniformHalfspace_averageSensitivity_eq]
  have h : a * avg (fun x => boolVal ((uniformHalfspace n a).indicator x)) ≤
      avg (fun x => boolVal ((uniformHalfspace n a).indicator x) *
        signedSum (fun _ => true) x) := by
    rw [← avg_const_mul]
    apply avg_mono
    intro x
    rw [uniformHalfspace_indicator]
    by_cases hx : a ≤ signedSum (fun _ => true) x
    · simp [boolVal, hx]
    · simp [boolVal, hx]
  linarith

end Kane.Lower
