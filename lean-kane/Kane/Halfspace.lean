import Kane.Cube

/-! Real affine halfspaces, their unateness, and the reduction from intersections
of halfspaces to unions of unate functions. -/

open scoped BigOperators

namespace Kane

/-- A closed affine halfspace on the Boolean cube, represented with coordinates
in `{-1, 1}`. Zero weights are allowed. -/
structure Halfspace (n : ℕ) where
  weights : Fin n → ℝ
  threshold : ℝ

namespace Halfspace

/-- The linear form defining a halfspace. -/
def score {n : ℕ} (h : Halfspace n) (x : Cube n) : ℝ :=
  ∑ i, h.weights i * (if x i then (1 : ℝ) else -1)

/-- The indicator of the closed halfspace, including points on its boundary. -/
noncomputable def indicator {n : ℕ} (h : Halfspace n) (x : Cube n) : Bool := by
  classical
  exact decide (h.threshold ≤ h.score x)

/-- The favorable direction of each coordinate, determined by its weight. -/
noncomputable def direction {n : ℕ} (h : Halfspace n) : Cube n := by
  classical
  exact fun i => decide (0 ≤ h.weights i)

/-- Flipping a favorable coordinate away from its preferred value cannot
increase the linear form. -/
theorem score_flip_le {n : ℕ} (h : Halfspace n) (x : Cube n) (i : Fin n)
    (hi : x i = h.direction i) : h.score (flip x i) ≤ h.score x := by
  classical
  unfold score
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j = i
  · subst j
    simp only [flip, Function.update_self]
    unfold direction at hi
    cases hxi : x i
    · have hw : h.weights i < 0 := by simpa [hxi] using hi.symm
      simp only [hxi, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      linarith
    · have hw : 0 ≤ h.weights i := by simpa [hxi] using hi.symm
      simp only [hxi, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      linarith
  · simp [flip, Function.update_of_ne hji]

/-- Every real halfspace indicator is unate. -/
noncomputable def toUnate {n : ℕ} (h : Halfspace n) : UnateFunction n where
  fn := h.indicator
  direction := h.direction
  increasing := by
    classical
    intro x i hi
    have hs := h.score_flip_le x i hi
    by_cases hh : h.threshold ≤ h.score (flip x i)
    · have hx : h.threshold ≤ h.score x := hh.trans hs
      simp [indicator, hh, hx]
    · simp [indicator, hh]

@[simp] theorem toUnate_fn {n : ℕ} (h : Halfspace n) :
    h.toUnate.fn = h.indicator := rfl

end Halfspace

namespace UnateFunction

/-- Complementation preserves unateness and reverses all favorable directions. -/
def complement {n : ℕ} (f : UnateFunction n) : UnateFunction n where
  fn x := !f.fn x
  direction i := !f.direction i
  increasing := by
    intro x i hi
    have hdir : (flip x i) i = f.direction i := by
      simp only [flip, Function.update_self]
      rw [hi, Bool.not_not]
    have hf := f.increasing (flip x i) i hdir
    rw [flip_flip] at hf
    cases ha : f.fn x <;> cases hb : f.fn (flip x i) <;> simp_all

@[simp] theorem complement_fn {n : ℕ} (f : UnateFunction n) (x : Cube n) :
    f.complement.fn x = !f.fn x := rfl

end UnateFunction

/-- Negating all output values does not change any sensitive edge. -/
theorem averageSensitivity_complement {n : ℕ} (f : Cube n → Bool) :
    averageSensitivity (fun x => !f x) = averageSensitivity f := by
  simp only [averageSensitivity, Bool.not_inj_iff]

/-- The Boolean indicator of an intersection of halfspaces. -/
noncomputable def intersection {n : ℕ} : List (Halfspace n) → Cube n → Bool
  | [], _ => true
  | h :: hs, x => h.indicator x && intersection hs x

/-- De Morgan's law reduces intersections of halfspaces to complements of unions
of unate functions. Strictness at a boundary is handled by Boolean complement. -/
theorem intersection_eq_complement_union {n : ℕ} (hs : List (Halfspace n)) :
    intersection hs =
      fun x => !(union (hs.map fun h => h.toUnate.complement) x) := by
  funext x
  induction hs with
  | nil => rfl
  | cons h hs ih =>
      simp [intersection, union, ih]

/-- The sensitivity of an intersection equals that of the associated union of
complementary unate functions. -/
theorem intersection_averageSensitivity_eq {n : ℕ} (hs : List (Halfspace n)) :
    averageSensitivity (intersection hs) =
      averageSensitivity (union (hs.map fun h => h.toUnate.complement)) := by
  rw [intersection_eq_complement_union, averageSensitivity_complement]

end Kane
