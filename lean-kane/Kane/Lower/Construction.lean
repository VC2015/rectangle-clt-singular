import Kane.Lower.Amplification
import Mathlib.Data.Finset.Max

/-! Finite-cube complements and the geometric plumbing of the lower bound.
Complementary halfspaces use an actual gap in the finite score set, so weak
thresholds and boundary points are handled exactly. -/

open scoped BigOperators

namespace Kane

namespace Halfspace

/-- A halfspace complement restricted to the finite cube is again a closed
halfspace. The threshold generally changes; simply negating it would mishandle
points on the original boundary. -/
theorem exists_cubeComplement {n : ℕ} (h : Halfspace n) :
    ∃ g : Halfspace n, ∀ x : Cube n, g.indicator x = !(h.indicator x) := by
  classical
  let bad : Finset (Cube n) := Finset.univ.filter (fun x => h.score x < h.threshold)
  by_cases hb : bad.Nonempty
  · obtain ⟨y, hy, hmax⟩ := bad.exists_max_image h.score hb
    have hylt : h.score y < h.threshold := (Finset.mem_filter.mp hy).2
    let g : Halfspace n := ⟨fun i => -h.weights i, -h.score y⟩
    have hscore (x : Cube n) : g.score x = -h.score x := by
      change (∑ i, -h.weights i * (if x i then (1 : ℝ) else -1)) =
        -(∑ i, h.weights i * (if x i then (1 : ℝ) else -1))
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => neg_mul _ _)
    refine ⟨g, ?_⟩
    intro x
    have hiff : g.threshold ≤ g.score x ↔ ¬h.threshold ≤ h.score x := by
      rw [hscore]
      change -h.score y ≤ -h.score x ↔ ¬h.threshold ≤ h.score x
      constructor
      · intro hx
        exact not_le_of_gt (lt_of_le_of_lt (by linarith) hylt)
      · intro hx
        have hxmem : x ∈ bad := by
          simp [bad, lt_of_not_ge hx]
        have hxmax := hmax x hxmem
        linarith
    simp only [indicator, hiff, decide_not]
  · let g : Halfspace n := ⟨fun _ => 0, 1⟩
    have hfull (x : Cube n) : h.threshold ≤ h.score x := by
      by_cases hx : h.threshold ≤ h.score x
      · exact hx
      · exact False.elim (hb ⟨x, Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, lt_of_not_ge hx⟩⟩)
    refine ⟨g, ?_⟩
    intro x
    have hh : h.indicator x = true := by simp [indicator, hfull x]
    rw [hh]
    simp [indicator, g, score]

/-- Choose the exact complement on the Boolean cube. -/
noncomputable def cubeComplement {n : ℕ} (h : Halfspace n) : Halfspace n :=
  Classical.choose h.exists_cubeComplement

@[simp] theorem cubeComplement_indicator {n : ℕ} (h : Halfspace n) (x : Cube n) :
    h.cubeComplement.indicator x = !(h.indicator x) :=
  Classical.choose_spec h.exists_cubeComplement x

/-- Pull a halfspace back through multiplication by a fixed cube sign. -/
def signTranslated {n : ℕ} (h : Halfspace n) (s : Cube n) : Halfspace n :=
  h.blockPullback id s

@[simp] theorem signTranslated_indicator {n : ℕ} (h : Halfspace n) (s x : Cube n) :
    (h.signTranslated s).indicator x = h.indicator (signTranslate s x) := by
  simpa only [signTranslated, blockRestriction, signTranslate, id_eq] using
    h.blockPullback_indicator id s x

end Halfspace

namespace Lower

/-- A finite uniform average is no larger than one of its entries. -/
theorem exists_avg_le {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ x, avg f ≤ f x := by
  classical
  obtain ⟨x, _, hmax⟩ := Finset.univ.exists_max_image f Finset.univ_nonempty
  refine ⟨x, ?_⟩
  calc
    avg f ≤ avg (fun _ : α => f x) := avg_mono (fun y => hmax y (Finset.mem_univ y))
    _ = f x := avg_const _

/-- Intersect the complements of the selected signed translates. -/
noncomputable def translatedComplementFamily {n m : ℕ} (h : Halfspace n)
    (signs : Fin m → Cube n) : List (Halfspace n) :=
  (List.finRange m).map (fun r => (h.signTranslated (signs r)).cubeComplement)

@[simp] theorem translatedComplementFamily_length {n m : ℕ} (h : Halfspace n)
    (signs : Fin m → Cube n) : (translatedComplementFamily h signs).length = m := by
  simp [translatedComplementFamily]

private theorem intersection_true_iff {n : ℕ} (hs : List (Halfspace n)) (x : Cube n) :
    intersection hs x = true ↔ ∀ h ∈ hs, h.indicator x = true := by
  induction hs with
  | nil => simp [intersection]
  | cons h hs ih => simp [intersection, ih]

/-- De Morgan's law with genuine halfspaces, including ties at thresholds. -/
theorem translatedComplementFamily_intersection {n m : ℕ} (h : Halfspace n)
    (signs : Fin m → Cube n) :
    intersection (translatedComplementFamily h signs) =
      fun x => !(translatedUnion h.indicator signs x) := by
  classical
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [intersection_true_iff]
  simp [translatedComplementFamily, translatedUnion, finiteOr]

theorem translatedComplementFamily_sensitivity {n m : ℕ} (h : Halfspace n)
    (signs : Fin m → Cube n) :
    averageSensitivity (intersection (translatedComplementFamily h signs)) =
      averageSensitivity (translatedUnion h.indicator signs) := by
  rw [translatedComplementFamily_intersection, averageSensitivity_complement]

/-- Some family of exactly `m` halfspaces realizes the expected amplification. -/
theorem exists_intersection_amplification {n : ℕ} (h : Halfspace n) (m : ℕ)
    (hsmall : 4 * (m : ℝ) * booleanMass h.indicator ≤ 1) :
    ∃ hs : List (Halfspace n), hs.length = m ∧
      (m : ℝ) * averageSensitivity h.indicator / 2 ≤ averageSensitivity (intersection hs) := by
  obtain ⟨signs, hsigns⟩ := exists_avg_le
    (fun signs : Fin m → Cube n => averageSensitivity (translatedUnion h.indicator signs))
  refine ⟨translatedComplementFamily h signs, translatedComplementFamily_length h signs, ?_⟩
  rw [translatedComplementFamily_sensitivity]
  exact (translatedUnion_expected_sensitivity_ge_half h.indicator m hsmall).trans hsigns

/-- An amplification count uses at most `k` translates, covers constant mass,
and keeps the other translated sets from covering most sensitive edges. -/
theorem exists_amplification_count {p : ℝ} {k : ℕ}
    (hp : 0 < p) (hpquarter : p ≤ 1 / 4) (hk : 0 < k)
    (hpk : 1 / (k : ℝ) ≤ p) :
    ∃ m : ℕ, 0 < m ∧ m ≤ k ∧ 4 * (m : ℝ) * p ≤ 1 ∧
      1 / 8 ≤ (m : ℝ) * p := by
  let m := Nat.floor (1 / (4 * p))
  have hden : 0 < 4 * p := by positivity
  have hq : 1 ≤ 1 / (4 * p) := (le_div_iff₀ hden).2 (by linarith)
  have hmone : 1 ≤ m := Nat.le_floor (by simpa using hq)
  have hm : 0 < m := Nat.zero_lt_of_lt hmone
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hmone
  have hfloor : (m : ℝ) ≤ 1 / (4 * p) := Nat.floor_le (by positivity)
  have hsmall : 4 * (m : ℝ) * p ≤ 1 := by
    have hh := (le_div_iff₀ hden).mp hfloor
    nlinarith
  have hmass : 1 / 8 ≤ (m : ℝ) * p := by
    have hlt : 1 / (4 * p) < 2 * (m : ℝ) :=
      (Nat.lt_floor_add_one (1 / (4 * p))).trans_le (by linarith)
    have hh := (div_lt_iff₀ hden).mp hlt
    nlinarith
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hkp : 1 ≤ p * (k : ℝ) := (div_le_iff₀ hkreal).mp hpk
  have hratio : 1 / (4 * p) ≤ (k : ℝ) :=
    (div_le_iff₀ hden).2 (by nlinarith)
  have hmk : m ≤ k := by exact_mod_cast hfloor.trans hratio
  exact ⟨m, hm, hmk, hsmall, hmass⟩

/-- A positive-threshold halfspace of sufficient mass can be amplified into
at most `k` halfspaces with sensitivity at least one eighth of that threshold. -/
theorem exists_intersection_of_mass_and_sensitivity {n k : ℕ} (h : Halfspace n)
    (a : ℝ) (hk : 1 ≤ k) (ha : 0 ≤ a)
    (hpk : 1 / (k : ℝ) ≤ booleanMass h.indicator)
    (hAS : 2 * a * booleanMass h.indicator ≤ averageSensitivity h.indicator) :
    ∃ hs : List (Halfspace n), hs.length ≤ k ∧
      a / 8 ≤ averageSensitivity (intersection hs) := by
  by_cases hquarter : booleanMass h.indicator ≤ 1 / 4
  · have hkpos : 0 < k := Nat.zero_lt_of_lt hk
    have hp : 0 < booleanMass h.indicator :=
      (one_div_pos.mpr (Nat.cast_pos.mpr hkpos)).trans_le hpk
    obtain ⟨m, hm, hmk, hsmall, hmass⟩ :=
      exists_amplification_count hp hquarter hkpos hpk
    obtain ⟨hs, hlen, hbound⟩ := exists_intersection_amplification h m hsmall
    refine ⟨hs, hlen.trans_le hmk, ?_⟩
    have hscaled := mul_le_mul_of_nonneg_left hAS (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hlow := mul_le_mul_of_nonneg_left hmass ha
    nlinarith
  · refine ⟨[h], by simpa using hk, ?_⟩
    have hmass : 1 / 4 < booleanMass h.indicator := lt_of_not_ge hquarter
    have hprod := mul_le_mul_of_nonneg_left hmass.le ha
    have hnonneg : 0 ≤ averageSensitivity h.indicator := averageSensitivity_nonneg _
    simpa only [intersection, Bool.and_true] using
      (show a / 8 ≤ averageSensitivity h.indicator by nlinarith)

end Lower

end Kane
