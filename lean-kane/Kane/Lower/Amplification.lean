import Kane.GeneralNoise

/-! Finite random-sign amplification for the lower-bound construction.
Every expectation is a uniform finite average; no probabilistic axioms or
independence assumptions are added. -/

open scoped BigOperators

namespace Kane

/-- Coordinatewise multiplication in the `{-1,1}` encoding. -/
def signTranslate {n : ℕ} (s x : Cube n) : Cube n := fun i => s i == x i

@[simp] theorem signTranslate_self {n : ℕ} (s x : Cube n) :
    signTranslate s (signTranslate s x) = x := by
  funext i
  cases hs : s i <;> cases hx : x i <;> simp [signTranslate, hs, hx]

theorem signTranslate_comm {n : ℕ} (s x : Cube n) :
    signTranslate s x = signTranslate x s := by
  funext i
  exact Bool.beq_comm

theorem signTranslate_flip {n : ℕ} (s x : Cube n) (i : Fin n) :
    signTranslate s (flip x i) = flip (signTranslate s x) i := by
  funext j
  by_cases hji : j = i
  · subst j
    cases hs : s i <;> cases hx : x i <;> simp [signTranslate, flip, hs, hx]
  · simp [signTranslate, flip, hji]

theorem avg_signTranslate {n : ℕ} (s : Cube n) (H : Cube n → ℝ) :
    avg (fun x => H (signTranslate s x)) = avg H := by
  let e : Cube n ≃ Cube n :=
    { toFun := signTranslate s
      invFun := signTranslate s
      left_inv := signTranslate_self s
      right_inv := signTranslate_self s }
  unfold avg
  congr 1
  exact e.sum_comp H

theorem avg_signTranslate_left {n : ℕ} (x : Cube n) (H : Cube n → ℝ) :
    avg (fun s => H (signTranslate s x)) = avg H := by
  simpa only [signTranslate_comm] using avg_signTranslate x H

/-- Uniform independent copies factor finite product expectations. -/
theorem avg_independent_product {α : Type*} [Fintype α] (H : α → ℝ) (m : ℕ) :
    avg (fun a : Fin m → α => ∏ r, H (a r)) = (avg H) ^ m := by
  have hsum : (∑ a : Fin m → α, ∏ r, H (a r)) = (∑ a : α, H a) ^ m := by
    rw [← Fintype.prod_sum]
    simp
  unfold avg
  rw [hsum, Fintype.card_fun]
  simp only [Fintype.card_fin, Nat.cast_pow, inv_pow, mul_pow]

/-- Boolean disjunction of a finite indexed family. -/
def finiteOr {m : ℕ} (u : Fin m → Bool) : Bool := decide (∃ r, u r = true)

/-- The union of `m` independently translated copies of a Boolean function. -/
def translatedUnion {n m : ℕ} (f : Cube n → Bool) (signs : Fin m → Cube n)
    (x : Cube n) : Bool := finiteOr (fun r => f (signTranslate (signs r) x))

private def edgeValue (a b : Bool) : ℝ := if a = b then 0 else 1

private def falsePair (a b : Bool) : ℝ := (1 - boolVal a) * (1 - boolVal b)

private theorem edgeValue_eq (a b : Bool) :
    edgeValue a b = (1 - boolVal a) + (1 - boolVal b) - 2 * falsePair a b := by
  cases a <;> cases b <;> norm_num [edgeValue, boolVal, falsePair]

private theorem finiteOr_absence {m : ℕ} (u : Fin m → Bool) :
    1 - boolVal (finiteOr u) = ∏ r, (1 - boolVal (u r)) := by
  have hcoord (r : Fin m) : 1 - boolVal (u r) = if u r = false then 1 else 0 := by
    cases u r <;> norm_num [boolVal]
  simp_rw [hcoord]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one]
  by_cases hh : ∃ r, u r = true
  · have hn : ¬∀ r, u r = false := by
      obtain ⟨r, hr⟩ := hh
      intro h
      have := h r
      simp_all
    simp [finiteOr, boolVal, hh, hn]
  · have hall : ∀ r, u r = false := by
      intro r
      cases hu : u r
      · rfl
      · exact False.elim (hh ⟨r, hu⟩)
    simp [finiteOr, boolVal, hh, hall]

private theorem falsePair_finiteOr {m : ℕ} (u v : Fin m → Bool) :
    falsePair (finiteOr u) (finiteOr v) = ∏ r, falsePair (u r) (v r) := by
  rw [falsePair, finiteOr_absence, finiteOr_absence, ← Finset.prod_mul_distrib]
  rfl

/-- The mass of the base set. -/
noncomputable def booleanMass {n : ℕ} (f : Cube n → Bool) : ℝ := avg (fun x => boolVal (f x))

theorem booleanMass_nonneg {n : ℕ} (f : Cube n → Bool) : 0 ≤ booleanMass f := by
  apply avg_nonneg
  intro x
  cases hf : f x <;> norm_num [boolVal, hf]

theorem booleanMass_le_one {n : ℕ} (f : Cube n → Bool) : booleanMass f ≤ 1 := by
  calc
    _ ≤ avg (fun _ : Cube n => (1 : ℝ)) := by
      apply avg_mono
      intro x
      cases hf : f x <;> norm_num [boolVal, hf]
    _ = 1 := avg_const 1

@[simp] theorem booleanMass_signTranslate {n : ℕ} (f : Cube n → Bool) (s : Cube n) :
    booleanMass (fun x => f (signTranslate s x)) = booleanMass f :=
  avg_signTranslate s (fun x => boolVal (f x))

@[simp] theorem averageSensitivity_signTranslate {n : ℕ} (f : Cube n → Bool) (s : Cube n) :
    averageSensitivity (fun x => f (signTranslate s x)) = averageSensitivity f := by
  unfold averageSensitivity
  simp_rw [signTranslate_flip]
  exact avg_signTranslate s (fun x => ∑ i : Fin n,
    if f x = f (flip x i) then (0 : ℝ) else 1)

theorem averageSensitivity_nonneg {n : ℕ} (f : Cube n → Bool) : 0 ≤ averageSensitivity f := by
  apply avg_nonneg
  intro x
  apply Finset.sum_nonneg
  intro i _
  split_ifs <;> norm_num

/-- Sensitivity contributed by a fixed coordinate. -/
noncomputable def coordinateSensitivity {n : ℕ} (f : Cube n → Bool) (i : Fin n) : ℝ :=
  avg (fun x => edgeValue (f x) (f (flip x i)))

private noncomputable def pairAbsence {n : ℕ} (f : Cube n → Bool) (i : Fin n) : ℝ :=
  avg (fun x => falsePair (f x) (f (flip x i)))

theorem averageSensitivity_eq_sum_coordinateSensitivity {n : ℕ} (f : Cube n → Bool) :
    averageSensitivity f = ∑ i, coordinateSensitivity f i := avg_sum _

theorem coordinateSensitivity_nonneg {n : ℕ} (f : Cube n → Bool) (i : Fin n) :
    0 ≤ coordinateSensitivity f i := by
  apply avg_nonneg
  intro x
  unfold edgeValue
  split_ifs <;> norm_num

private theorem avg_absence {n : ℕ} (f : Cube n → Bool) :
    avg (fun x => 1 - boolVal (f x)) = 1 - booleanMass f := by
  rw [avg_sub, avg_const]
  rfl

private theorem coordinateSensitivity_pairAbsence {n : ℕ} (f : Cube n → Bool) (i : Fin n) :
    coordinateSensitivity f i = 2 * ((1 - booleanMass f) - pairAbsence f i) := by
  unfold coordinateSensitivity
  simp_rw [edgeValue_eq]
  rw [avg_sub, avg_add, avg_const_mul, avg_absence]
  have hf : avg (fun x => 1 - boolVal (f (flip x i))) = 1 - booleanMass f := by
    rw [avg_flip (fun x => 1 - boolVal (f x)), avg_absence]
  rw [hf]
  unfold pairAbsence
  ring

private theorem pairAbsence_nonneg {n : ℕ} (f : Cube n → Bool) (i : Fin n) :
    0 ≤ pairAbsence f i := by
  apply avg_nonneg
  intro x
  cases h : f x <;> cases h' : f (flip x i) <;> norm_num [falsePair, boolVal, h, h']

private theorem pairAbsence_le_absence {n : ℕ} (f : Cube n → Bool) (i : Fin n) :
    pairAbsence f i ≤ 1 - booleanMass f := by
  rw [← avg_absence]
  apply avg_mono
  intro x
  cases h : f x <;> cases h' : f (flip x i) <;> norm_num [falsePair, boolVal, h, h']

private theorem pairAbsence_ge {n : ℕ} (f : Cube n → Bool) (i : Fin n) :
    1 - 2 * booleanMass f ≤ pairAbsence f i := by
  have hpoint (x : Cube n) : 1 - boolVal (f x) - boolVal (f (flip x i)) ≤
      falsePair (f x) (f (flip x i)) := by
    cases h : f x <;> cases h' : f (flip x i) <;> norm_num [falsePair, boolVal, h, h']
  have h := avg_mono hpoint
  rw [avg_sub, avg_sub, avg_const,
    avg_flip (fun x => boolVal (f x)) i] at h
  change 1 - booleanMass f - booleanMass f ≤ _ at h
  unfold pairAbsence
  linarith

private theorem translatedUnion_absence {n m : ℕ} (f : Cube n → Bool) (x : Cube n) :
    avg (fun signs : Fin m → Cube n => 1 - boolVal (translatedUnion f signs x)) =
      (1 - booleanMass f) ^ m := by
  calc
    _ = avg (fun signs : Fin m → Cube n =>
        ∏ r, (1 - boolVal (f (signTranslate (signs r) x)))) :=
      avg_congr (fun signs => finiteOr_absence _)
    _ = (avg (fun s : Cube n => 1 - boolVal (f (signTranslate s x)))) ^ m :=
      avg_independent_product (fun s : Cube n => 1 - boolVal (f (signTranslate s x))) m
    _ = _ := by
      rw [avg_signTranslate_left x (fun y => 1 - boolVal (f y)), avg_absence]

private theorem translatedUnion_pairAbsence {n m : ℕ} (f : Cube n → Bool)
    (x : Cube n) (i : Fin n) :
    avg (fun signs : Fin m → Cube n =>
      falsePair (translatedUnion f signs x) (translatedUnion f signs (flip x i))) =
        pairAbsence f i ^ m := by
  calc
    _ = avg (fun signs : Fin m → Cube n => ∏ r,
        falsePair (f (signTranslate (signs r) x)) (f (signTranslate (signs r) (flip x i)))) :=
      avg_congr (fun signs => falsePair_finiteOr _ _)
    _ = (avg (fun s : Cube n =>
        falsePair (f (signTranslate s x)) (f (signTranslate s (flip x i))))) ^ m :=
      avg_independent_product (fun s : Cube n =>
        falsePair (f (signTranslate s x)) (f (signTranslate s (flip x i)))) m
    _ = _ := by
      simp_rw [signTranslate_flip]
      congr 1
      exact avg_signTranslate_left x (fun y => falsePair (f y) (f (flip y i)))

private theorem translatedUnion_edge_expectation {n m : ℕ} (f : Cube n → Bool)
    (x : Cube n) (i : Fin n) :
    avg (fun signs : Fin m → Cube n =>
      edgeValue (translatedUnion f signs x) (translatedUnion f signs (flip x i))) =
        2 * ((1 - booleanMass f) ^ m - pairAbsence f i ^ m) := by
  simp_rw [edgeValue_eq]
  rw [avg_sub, avg_add, avg_const_mul, translatedUnion_absence,
    translatedUnion_absence, translatedUnion_pairAbsence]
  ring

/-- Exact expected sensitivity of a union of independent random translates.
The pair-absence expression is the probability that a translated base set
misses both endpoints of the corresponding edge. -/
private theorem translatedUnion_averageSensitivity_expectation {n m : ℕ}
    (f : Cube n → Bool) :
    avg (fun signs : Fin m → Cube n => averageSensitivity (translatedUnion f signs)) =
      ∑ i, 2 * ((1 - booleanMass f) ^ m - pairAbsence f i ^ m) := by
  change avg (fun signs : Fin m → Cube n => avg (fun x =>
    ∑ i, edgeValue (translatedUnion f signs x) (translatedUnion f signs (flip x i)))) = _
  rw [avg_commute]
  calc
    _ = avg (fun x : Cube n => ∑ i, avg (fun signs : Fin m → Cube n =>
        edgeValue (translatedUnion f signs x) (translatedUnion f signs (flip x i)))) := by
      apply avg_congr
      intro x
      exact avg_sum _
    _ = _ := by
      simp_rw [translatedUnion_edge_expectation]
      exact avg_const _

private theorem pow_sub_lower (a b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (r : ℕ) :
    ((r : ℝ) + 1) * (a - b) * b ^ r ≤ a ^ (r + 1) - b ^ (r + 1) := by
  have ha := hb.trans hba
  have hd := sub_nonneg.mpr hba
  induction r with
  | zero => simp
  | succ r ih =>
      have hK : 0 ≤ ((r : ℝ) + 1) * (a - b) * b ^ r := by positivity
      calc
        _ = b * (((r : ℝ) + 1) * (a - b) * b ^ r) + (a - b) * b ^ (r + 1) := by
          simp only [Nat.cast_add, Nat.cast_one, pow_succ]
          ring
        _ ≤ a * (((r : ℝ) + 1) * (a - b) * b ^ r) + (a - b) * b ^ (r + 1) :=
          add_le_add_right (mul_le_mul_of_nonneg_right hba hK) _
        _ ≤ a * (a ^ (r + 1) - b ^ (r + 1)) + (a - b) * b ^ (r + 1) :=
          add_le_add_right (mul_le_mul_of_nonneg_left ih ha) _
        _ = _ := by
          simp only [pow_succ]
          ring

private theorem coordinate_amplification {n : ℕ} (f : Cube n → Bool) (i : Fin n) (m : ℕ) :
    (m : ℝ) * coordinateSensitivity f i *
        (1 - 2 * ((m - 1 : ℕ) : ℝ) * booleanMass f) ≤
      2 * ((1 - booleanMass f) ^ m - pairAbsence f i ^ m) := by
  cases m with
  | zero => simp
  | succ r =>
      have hb := pairAbsence_nonneg f i
      have hba := pairAbsence_le_absence f i
      have hblow := pairAbsence_ge f i
      have hder := pow_sub_lower (1 - booleanMass f) (pairAbsence f i) hb hba r
      have hBern := one_add_mul_sub_le_pow (by linarith : -1 ≤ pairAbsence f i) r
      have hmul := mul_le_mul_of_nonneg_left hblow (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
      have hpow : 1 - 2 * (r : ℝ) * booleanMass f ≤ pairAbsence f i ^ r := by
        nlinarith
      have hK : 0 ≤ ((r : ℝ) + 1) * ((1 - booleanMass f) - pairAbsence f i) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr hba)
      have hh := mul_le_mul_of_nonneg_left hpow hK
      rw [coordinateSensitivity_pairAbsence]
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
      nlinarith

/-- Random-sign union amplification, in the form used in Kane's lower bound.
The factor comes from avoiding the other translated sets at both endpoints. -/
theorem translatedUnion_expected_sensitivity_ge {n : ℕ} (f : Cube n → Bool) (m : ℕ) :
    (m : ℝ) * averageSensitivity f *
        (1 - 2 * ((m - 1 : ℕ) : ℝ) * booleanMass f) ≤
      avg (fun signs : Fin m → Cube n => averageSensitivity (translatedUnion f signs)) := by
  rw [translatedUnion_averageSensitivity_expectation,
    averageSensitivity_eq_sum_coordinateSensitivity, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => coordinate_amplification f i m)

/-- When the expected total volume of the translates is at most one quarter,
at least half of the sum of their sensitivities survives in expectation. -/
theorem translatedUnion_expected_sensitivity_ge_half {n : ℕ} (f : Cube n → Bool) (m : ℕ)
    (hsmall : 4 * (m : ℝ) * booleanMass f ≤ 1) :
    (m : ℝ) * averageSensitivity f / 2 ≤
      avg (fun signs : Fin m → Cube n => averageSensitivity (translatedUnion f signs)) := by
  have hp := booleanMass_nonneg f
  have hcount : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  have hmul := mul_le_mul_of_nonneg_right hcount hp
  have hfactor : 1 / 2 ≤ 1 - 2 * ((m - 1 : ℕ) : ℝ) * booleanMass f := by nlinarith
  have hnonneg : 0 ≤ (m : ℝ) * averageSensitivity f :=
    mul_nonneg (Nat.cast_nonneg m) (averageSensitivity_nonneg f)
  calc
    _ = ((m : ℝ) * averageSensitivity f) * (1 / 2) := by ring
    _ ≤ (m : ℝ) * averageSensitivity f *
        (1 - 2 * ((m - 1 : ℕ) : ℝ) * booleanMass f) :=
      mul_le_mul_of_nonneg_left hfactor hnonneg
    _ ≤ _ := translatedUnion_expected_sensitivity_ge f m

end Kane
