import RectangleCLT.GaussianComponentTruncation
import Mathlib.Tactic.FieldSimp

/-!
# Quantitative finite approximation of an independent Gaussian component

There are `k^6` increments of size `k^-3`. Each base vector is cut off at
norm `k^2`; the resulting increments have envelope `k^-1`. The aggregate
fourth-moment cost is at most `M₄/k^6`, and the probability of any cutoff
is at most `M₄/k^2`. In particular, this approximation needs no central
limit theorem or nondegeneracy condition on the Gaussian component.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators symmDiff

namespace RectangleCLT

noncomputable section

def gaussianComponentFourthMoment {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∫ x : Vector p, ‖x‖ ^ 4 ∂gaussianLaw B

theorem gaussianComponentFourthMoment_nonneg {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ gaussianComponentFourthMoment B :=
  integral_nonneg fun _ => by positivity

theorem gaussianComponent_coordinate_fourth_le {p : ℕ} (hp : 1 ≤ p)
    (B : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    (∫ x : Vector p, x j ^ 4 ∂gaussianLaw B) ≤ gaussianComponentFourthMoment B := by
  apply integral_mono (gaussianComponent_integrable_coordinate_fourth B j)
    (gaussianComponent_integrable_norm_fourth hp B)
  intro x
  have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  simpa only [(show Even 4 from by decide).pow_abs] using
    pow_le_pow_left₀ (abs_nonneg (x j)) hj 4

theorem gaussianComponentIncrement_fourth_le {p : ℕ} (hp : 1 ≤ p)
    (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) (j : Fin p) :
    (∫ x, gaussianComponentIncrement k x j ^ 4 ∂gaussianLaw B) ≤
      gaussianComponentFourthMoment B / (k : ℝ) ^ 12 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hcut := (gaussianComponent_truncated_fourth_le B ((k : ℝ) ^ 2) j).trans
    (gaussianComponent_coordinate_fourth_le hp B j)
  calc
    _ = (((k : ℝ) ^ 3)⁻¹) ^ 4 *
        ∫ x, truncateVector ((k : ℝ) ^ 2) x j ^ 4 ∂gaussianLaw B := by
      simp only [gaussianComponentIncrement, Pi.smul_apply, smul_eq_mul, mul_pow,
        integral_const_mul]
    _ ≤ (((k : ℝ) ^ 3)⁻¹) ^ 4 * gaussianComponentFourthMoment B :=
      mul_le_mul_of_nonneg_left hcut (by positivity)
    _ = _ := by
      simp only [inv_pow, ← pow_mul, Nat.reduceMul, div_eq_mul_inv]
      ring

/-- Actual fourth moments of the whole finite independent increment array. -/
theorem gaussianComponentIncrement_array_fourth_le {p : ℕ} (hp : 1 ≤ p)
    (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) (j : Fin p) :
    (∑ i : Fin (k ^ 6), ∫ z, gaussianComponentIncrement k (z i) j ^ 4
      ∂gaussianComponentArrayLaw B (k ^ 6)) ≤
      gaussianComponentFourthMoment B / (k : ℝ) ^ 6 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hrow (i : Fin (k ^ 6)) :
      (∫ z, gaussianComponentIncrement k (z i) j ^ 4
        ∂gaussianComponentArrayLaw B (k ^ 6)) ≤
          gaussianComponentFourthMoment B / (k : ℝ) ^ 12 := by
    have hmap := integral_map (μ := gaussianComponentArrayLaw B (k ^ 6))
      (measurable_pi_apply i).aemeasurable
      ((((measurable_pi_apply j).comp
        (measurable_gaussianComponentIncrement k)).pow_const 4).aestronglyMeasurable)
    rw [gaussianComponentArrayLaw_map_eval B] at hmap
    simp only [Function.comp_def] at hmap
    rw [← hmap]
    exact gaussianComponentIncrement_fourth_le hp B hk j
  calc
    _ ≤ ∑ _i : Fin (k ^ 6), gaussianComponentFourthMoment B / (k : ℝ) ^ 12 :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp; push_cast; field_simp [hk']; ring

/-- Any family having the Gaussian marginals has the required cutoff
probability. Independence is not needed for this union bound. -/
theorem gaussianComponent_any_cutoff_probability_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ)
    {k : ℕ} (hk : k ≠ 0) (Z : Fin (k ^ 6) → Ω → Vector p)
    (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, μ.map (Z i) = gaussianLaw B) :
    μ.real {ω | ∃ i, (k : ℝ) ^ 2 < ‖Z i ω‖} ≤
      gaussianComponentFourthMoment B / (k : ℝ) ^ 2 := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hrow (i : Fin (k ^ 6)) :
      μ.real {ω | (k : ℝ) ^ 2 < ‖Z i ω‖} ≤
        gaussianComponentFourthMoment B / (k : ℝ) ^ 8 := by
    have hset : MeasurableSet {x : Vector p | (k : ℝ) ^ 2 < ‖x‖} :=
      measurableSet_lt measurable_const measurable_norm
    have heq : μ.real {ω | (k : ℝ) ^ 2 < ‖Z i ω‖} =
        (gaussianLaw B).real {x | (k : ℝ) ^ 2 < ‖x‖} := by
      rw [← hlaw i]
      simp only [Measure.real, Measure.map_apply (hZ i) hset]
      rfl
    rw [heq]
    convert gaussianComponent_norm_tail_le hp B (pow_pos hk' 2) using 1 <;>
      simp only [gaussianComponentFourthMoment, ← pow_mul]
  have heq : {ω | ∃ i, (k : ℝ) ^ 2 < ‖Z i ω‖} =
      ⋃ i, {ω | (k : ℝ) ^ 2 < ‖Z i ω‖} := by ext ω; simp
  rw [heq]
  calc
    _ ≤ ∑ i : Fin (k ^ 6), μ.real {ω | (k : ℝ) ^ 2 < ‖Z i ω‖} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin (k ^ 6), gaussianComponentFourthMoment B / (k : ℝ) ^ 8 :=
      Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by simp; push_cast; field_simp [ne_of_gt hk']; ring

/-- Rectangle probabilities agree outside the explicit cutoff event.
The arbitrary extra random vector may contain all original observations;
no continuity or absence of atoms is assumed for its distribution. -/
theorem gaussianComponent_rectangle_coupling_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ)
    {k : ℕ} (hk : k ≠ 0) (Z : Fin (k ^ 6) → Ω → Vector p)
    (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, μ.map (Z i) = gaussianLaw B)
    (W : Ω → Vector p) (hW : Measurable W) (R : Rect p) :
    |μ.real {ω | W ω + ((k : ℝ) ^ 3)⁻¹ • (∑ i, Z i ω) ∈ R.carrier} -
      μ.real {ω | W ω + (∑ i, gaussianComponentIncrement k (Z i ω)) ∈ R.carrier}| ≤
        gaussianComponentFourthMoment B / (k : ℝ) ^ 2 := by
  let E : Set Ω := {ω | ∃ i, (k : ℝ) ^ 2 < ‖Z i ω‖}
  let A : Set Ω := {ω | W ω + ((k : ℝ) ^ 3)⁻¹ • (∑ i, Z i ω) ∈ R.carrier}
  let D : Set Ω := {ω | W ω + (∑ i, gaussianComponentIncrement k (Z i ω)) ∈ R.carrier}
  have hA : MeasurableSet A := R.measurableSet_carrier.preimage
    (hW.add (measurable_const.smul
      (Finset.measurable_sum Finset.univ fun i _ => hZ i)))
  have hD : MeasurableSet D := R.measurableSet_carrier.preimage
    (hW.add (Finset.measurable_sum Finset.univ fun i _ =>
      (measurable_gaussianComponentIncrement k).comp (hZ i)))
  have hsub : A ∆ D ⊆ E := by
    intro ω hω
    by_contra hE
    have hgood (i : Fin (k ^ 6)) : ‖Z i ω‖ ≤ (k : ℝ) ^ 2 := by
      by_contra hi
      exact hE ⟨i, lt_of_not_ge hi⟩
    have heq : (∑ i, gaussianComponentIncrement k (Z i ω)) =
        ((k : ℝ) ^ 3)⁻¹ • ∑ i, Z i ω := by
      simp only [gaussianComponentIncrement, truncateVector, if_pos (hgood _)]
      simp only [Finset.smul_sum]
    have hmem : ω ∈ A ↔ ω ∈ D := by dsimp [A, D]; rw [heq]
    exact (Set.mem_symmDiff.mp hω).elim
      (fun h => h.2 (hmem.mp h.1)) (fun h => h.2 (hmem.mpr h.1))
  exact (abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet
    hD.nullMeasurableSet).trans ((measureReal_mono hsub).trans
      (gaussianComponent_any_cutoff_probability_le hp B hk Z hZ hlaw))

end

end RectangleCLT
