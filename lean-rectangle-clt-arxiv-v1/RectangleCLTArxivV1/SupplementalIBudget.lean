import RectangleCLTArxivV1.SupplementalIRestriction

/-! The exceptional budget counts original unordered coordinate pairs.
The fourth-derivative expansion uses ordered signed face pairs. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def correlationGap {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) : ℝ :=
  1-|S i j|

def exceptionalCoordinateWeight {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ)
    (c : ℝ) (i j : Fin p) : ℝ :=
  if 0 < correlationGap S i j ∧ correlationGap S i j < c then
    Real.sqrt (correlationGap S i j) else 0

def exceptionalCorrelationBudget {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then exceptionalCoordinateWeight S c i j else 0

def exceptionalFaceSine {p r : ℕ} (U : Face p → Vector r) (c : ℝ) (f g : Face p) : ℝ :=
  if 0 < 1-|faceDot (U f) (U g)| ∧ 1-|faceDot (U f) (U g)| < c then
    Real.sqrt (1-(faceDot (U f) (U g))^2) else 0

theorem exceptionalCoordinateWeight_nonneg {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) (i j : Fin p) :
    0 ≤ exceptionalCoordinateWeight S c i j := by
  unfold exceptionalCoordinateWeight
  split_ifs <;> positivity

theorem exceptionalCorrelationBudget_nonneg {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) : 0 ≤ exceptionalCorrelationBudget S c := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact exceptionalCoordinateWeight_nonneg S c i j
  · rfl

/-- Every symmetric off-diagonal array is twice its strict upper triangle. -/
theorem ordered_sum_eq_twice_upper {p : ℕ} (w : Fin p → Fin p → ℝ)
    (hsym : ∀ i j, w i j=w j i) (hdiag : ∀ i, w i i=0) :
    (∑ i, ∑ j, w i j) = 2*(∑ i, ∑ j, if i < j then w i j else 0) := by
  classical
  have he (i j : Fin p) : w i j =
      (if i < j then w i j else 0)+(if j < i then w i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_ge h.le]
    · subst j; simp [hdiag]
    · simp [h,not_lt_of_ge h.le]
  calc
    _ = (∑ i, ∑ j, if i < j then w i j else 0)+
        (∑ i, ∑ j, if j < i then w i j else 0) := by
      calc
        _ = ∑ i, ∑ j, ((if i < j then w i j else 0)+(if j < i then w i j else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_congr rfl (fun j _ => he i j)
        _ = _ := by simp only [Finset.sum_add_distrib]
    _ = 2*(∑ i, ∑ j, if i < j then w i j else 0) := by
      rw [Finset.sum_comm (f := fun i j => if j < i then w i j else 0)]
      have hx : (∑ i, ∑ j, if i < j then w j i else 0) =
          ∑ i, ∑ j, if i < j then w i j else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym j i]
      rw [hx]
      ring

theorem exceptional_ordered_coordinate_sum {p : ℕ}
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.IsSymm) (hdiag : ∀ i, S i i=1) (c : ℝ) :
    (∑ i, ∑ j, exceptionalCoordinateWeight S c i j)=2*exceptionalCorrelationBudget S c := by
  apply ordered_sum_eq_twice_upper
  · intro i j
    simp only [exceptionalCoordinateWeight,correlationGap,hS.apply i j]
  · intro i
    simp [exceptionalCoordinateWeight,correlationGap,hdiag]

theorem cap_signed_correlation_abs {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (f g : Face p) :
    |faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)|=
      |(A*A.transpose) f.1 g.1| := by
  rw [capRectangularFactorNormal_gram]
  cases hf : f.2 <;> cases hg : g.2 <;> simp [hf,hg]

theorem exceptional_sine_le_gap_weight {ρ c : ℝ} :
    (if 0 < 1-|ρ| ∧ 1-|ρ| < c then Real.sqrt (1-ρ^2) else 0) ≤
      Real.sqrt 2*(if 0 < 1-|ρ| ∧ 1-|ρ| < c then Real.sqrt (1-|ρ|) else 0) := by
  split_ifs with hg
  · have hr : 1-ρ^2 ≤ 2*(1-|ρ|) := by nlinarith [sq_abs ρ,sq_nonneg (1-|ρ|)]
    calc
      Real.sqrt (1-ρ^2) ≤ Real.sqrt (2*(1-|ρ|)) := Real.sqrt_le_sqrt hr
      _ = Real.sqrt 2*Real.sqrt (1-|ρ|) := Real.sqrt_mul (by norm_num) _
  · simp

/-- Four sign choices and two orders give the factor eight. Diagonal and
zero-gap pairs contribute zero, including the opposite faces of one coordinate. -/
theorem exceptional_signed_face_sine_sum_le_budget {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ i, (A*A.transpose) i i=1) (c : ℝ) :
    (∑ f, ∑ g, exceptionalFaceSine (capRectangularFactorNormal A) c f g) ≤
      8*Real.sqrt 2*exceptionalCorrelationBudget (A*A.transpose) c := by
  classical
  have hb (f g : Face p) : exceptionalFaceSine (capRectangularFactorNormal A) c f g ≤
      Real.sqrt 2*exceptionalCoordinateWeight (A*A.transpose) c f.1 g.1 := by
    have ht := exceptional_sine_le_gap_weight
      (ρ := faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)) (c := c)
    simpa only [exceptionalFaceSine,exceptionalCoordinateWeight,correlationGap,
      cap_signed_correlation_abs A f g] using ht
  calc
    _ ≤ ∑ f : Face p, ∑ g : Face p,
        Real.sqrt 2*exceptionalCoordinateWeight (A*A.transpose) c f.1 g.1 :=
      Finset.sum_le_sum (fun f _ => Finset.sum_le_sum (fun g _ => hb f g))
    _ = 4*Real.sqrt 2*(∑ i, ∑ j, exceptionalCoordinateWeight (A*A.transpose) c i j) := by
      simp only [Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib,
        ← Finset.mul_sum]
      ring
    _ = _ := by
      rw [exceptional_ordered_coordinate_sum (A*A.transpose) (by exact Matrix.transpose_mul _ _) hdiag c]
      ring

end
end RectangleCLTArxivV1
