import RectangleCLT.Statement
import RectangleCLT.Interpolation
import Kane.NoiseSensitivity

/-!
# A probability law for the Bernoulli interpolation

The selectors have the actual independent product weights. Integrating over
them gives a finite mixture of pushforward measures, rather than an assumed
random-vector path. This file proves probability normalization, the two bounded
endpoints, and the retained summands' mixed-moment coefficients. Gaussian
convolution and differentiation of the resulting law are separate steps.
-/

open MeasureTheory
open scoped BigOperators

universe u v

namespace RectangleCLT

noncomputable section

/-- Mix pushforward laws with independent Bernoulli selector weights. -/
def bernoulliMixtureLaw {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E] {n : ℕ}
    (μ : Measure Ω) (F : Kane.Cube n → Ω → E) (q : ℝ) : Measure E :=
  ∑ mask : Kane.Cube n, ENNReal.ofReal (Kane.maskWeight q mask) • μ.map (F mask)

theorem bernoulliMixtureLaw_isProbability {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Kane.Cube n → Ω → E)
    (hF : ∀ mask, Measurable (F mask)) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    IsProbabilityMeasure (bernoulliMixtureLaw μ F q) := by
  constructor
  unfold bernoulliMixtureLaw
  rw [Measure.finset_sum_apply]
  have hm (mask : Kane.Cube n) : (μ.map (F mask)) Set.univ = 1 := by
    rw [Measure.map_apply (hF mask) MeasurableSet.univ]
    simp
  simp_rw [Measure.smul_apply, smul_eq_mul, hm, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun mask _ => Kane.maskWeight_nonneg hq hq1 mask),
    Kane.maskWeight_sum]
  norm_num

/-- The finite-mixture integral is exactly the selector-weighted integral. -/
theorem integral_bernoulliMixtureLaw {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E] {n : ℕ}
    (μ : Measure Ω) (F : Kane.Cube n → Ω → E) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (g : E → ℝ)
    (hg : ∀ mask, Integrable g (μ.map (F mask))) :
    (∫ x, g x ∂bernoulliMixtureLaw μ F q) =
      ∑ mask : Kane.Cube n, Kane.maskWeight q mask * ∫ x, g x ∂μ.map (F mask) := by
  unfold bernoulliMixtureLaw
  rw [integral_finset_sum_measure (fun mask _ =>
    (hg mask).smul_measure (ENNReal.ofReal_ne_top))]
  apply Finset.sum_congr rfl
  intro mask _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (Kane.maskWeight_nonneg hq hq1 mask)]
  rfl

/-- A selector coordinate is retained with probability exactly `q`. -/
theorem maskWeight_coordinate {n : ℕ} (q : ℝ) (i : Fin n) :
    (∑ mask : Kane.Cube n, Kane.maskWeight q mask * Kane.boolVal (mask i)) = q := by
  classical
  let w (j : Fin n) (b : Bool) : ℝ :=
    (if b then q else 1 - q) * (if j = i then Kane.boolVal b else 1)
  have hw (mask : Kane.Cube n) :
      (∏ j, w j (mask j)) = Kane.maskWeight q mask * Kane.boolVal (mask i) := by
    unfold w
    rw [Finset.prod_mul_distrib]
    simp [Kane.maskWeight]
  have hsum (j : Fin n) : (∑ b : Bool, w j b) = if j = i then q else 1 := by
    by_cases hj : j = i <;> simp [w, hj, Kane.boolVal]
  calc
    _ = ∑ mask : Kane.Cube n, ∏ j, w j (mask j) :=
      Finset.sum_congr rfl (fun mask _ => (hw mask).symm)
    _ = ∏ j, ∑ b : Bool, w j b := (Fintype.prod_sum w).symm
    _ = q := by simp_rw [hsum]; simp

/-- The actual retained and rescaled observations, for a fixed selector. -/
def retainedArray {Ω : Type u} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (t : ℝ) (mask : Kane.Cube n) (ω : Ω) : Fin n → Vector p :=
  fun i => if mask i then thinningScale t • ξ i ω else 0

theorem measurable_retainedArray {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (mask : Kane.Cube n) : Measurable (retainedArray ξ t mask) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : mask i = true
  · simpa [retainedArray, hi] using (hξ i).const_smul (thinningScale t)
  · simp only [retainedArray, hi, Bool.false_eq_true, ↓reduceIte]
    exact measurable_const

/-- The bounded part of the interpolation, as a genuine probability law. -/
def bernoulliArrayLaw {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (t : ℝ) :
    Measure (Fin n → Vector p) :=
  bernoulliMixtureLaw μ (retainedArray ξ t) (thinningProbability t)

theorem bernoulliArrayLaw_isProbability {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (bernoulliArrayLaw μ ξ t) :=
  bernoulliMixtureLaw_isProbability μ (retainedArray ξ t)
    (measurable_retainedArray ξ hξ t) _
    (thinningProbability_nonneg ht1) (thinningProbability_le_one ht)

theorem maskWeight_one {n : ℕ} (mask : Kane.Cube n) :
    Kane.maskWeight 1 mask = if mask = (fun _ => true) then 1 else 0 := by
  classical
  unfold Kane.maskWeight
  have hcoord (i : Fin n) :
      (if mask i then (1 : ℝ) else 1 - 1) = if mask i = true then 1 else 0 := by
    cases mask i <;> norm_num
  simp_rw [hcoord]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one]
  congr 1
  exact propext funext_iff.symm

/-- At the bounded endpoint no summand is changed. -/
theorem bernoulliArrayLaw_zero {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) :
    bernoulliArrayLaw μ ξ 0 = μ.map (fun ω i => ξ i ω) := by
  classical
  unfold bernoulliArrayLaw bernoulliMixtureLaw
  rw [thinningProbability_zero]
  simp_rw [maskWeight_one, apply_ite ENNReal.ofReal]
  simp [retainedArray]
  congr 1
  funext ω i
  simp [retainedArray]

/-- At the Gaussian endpoint every bounded summand has disappeared. -/
theorem bernoulliArrayLaw_one {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) :
    bernoulliArrayLaw μ ξ 1 = Measure.dirac 0 := by
  classical
  unfold bernoulliArrayLaw bernoulliMixtureLaw
  rw [thinningProbability_one]
  simp_rw [Kane.maskWeight_zero, apply_ite ENNReal.ofReal]
  simp [retainedArray, Measure.map_const]
  have heq : retainedArray ξ 1 (fun _ => false) =
      (fun _ => (0 : Fin n → Vector p)) := by
    funext ω i
    simp [retainedArray]
  rw [heq, Measure.map_const, measure_univ, one_smul]

end

end RectangleCLT
