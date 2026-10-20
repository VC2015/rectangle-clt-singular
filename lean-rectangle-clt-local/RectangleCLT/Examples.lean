import RectangleCLT.Statement
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Semantic regression checks for the rectangle-CLT definitions.
The finite weighted examples below calculate genuine centered marginal
moments, and distinguish a signed aggregate from a sum of absolute moments.
They do not assert a central limit theorem.
-/

open scoped BigOperators ENNReal
open MeasureTheory
open ProbabilityTheory

namespace RectangleCLT.SemanticExamples

noncomputable section

example (p : ℕ) : (Rect.univ p).carrier = Set.univ := by
  ext x
  simp [Rect.carrier, Rect.univ]

example : (Rect.empty 1).carrier = ∅ := by
  ext x
  simp [Rect.carrier, Rect.empty]

/-- An empty product has one point; this is why the intended CLT requires
positive dimension rather than silently treating an empty index set as a
nonempty family of rectangle constraints. -/
example : (Rect.empty 0).carrier = Set.univ := by
  ext x
  simp [Rect.carrier, Rect.empty]

example {p : ℕ} (x : Vector p) : (Rect.closedBox x x).carrier = {x} := by
  simp [Rect.carrier, Rect.closedBox, Set.univ_pi_singleton]

example : (Rect.closedBox (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 0)).carrier = ∅ := by
  have h : Set.Icc (1 : ℝ) 0 = ∅ := Set.Icc_eq_empty_of_lt (by norm_num)
  ext x
  simp [Rect.carrier, Rect.closedBox, h]

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (W : Ω → Vector p) :
    μ.real (W ⁻¹' (Rect.univ p).carrier) = 1 := by
  simp [Rect.carrier, Rect.univ]

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → Vector 1) :
    μ.real (W ⁻¹' (Rect.empty 1).carrier) = 0 := by
  have hempty : (Rect.empty 1).carrier = ∅ := by
    ext x
    simp [Rect.carrier, Rect.empty]
  simp [hempty]

/-- A singleton rectangle can carry all the probability for an atomic law.
The intended theorem must not assume its summand laws have densities. -/
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (x : Vector p) :
    μ.real ((fun _ : Ω => x) ⁻¹' (Rect.closedBox x x).carrier) = 1 := by
  have hevent : (fun _ : Ω => x) ⁻¹' (Rect.closedBox x x).carrier = Set.univ := by
    ext ω
    simp [Rect.carrier, Rect.closedBox]
  simp [hevent]

/-- The two-point law giving probabilities `2/3` and `1/3`. -/
private def skewExpectation (f : Bool → ℝ) : ℝ :=
  (2 / 3 : ℝ) * f false + (1 / 3 : ℝ) * f true

private def skewValue (s : Bool) : ℝ := if s then 2 else -1

/-- Two centered marginals with opposite skewness, each of variance `1/2`.
Independent copies of their states give a variance-one sum. -/
private def oppositeSkew (i s : Bool) : ℝ :=
  (if i then (-1 : ℝ) else 1) * skewValue s / 2

example (i : Bool) : skewExpectation (oppositeSkew i) = 0 := by
  cases i <;> norm_num [skewExpectation, oppositeSkew, skewValue]

example : (∑ i : Bool, skewExpectation (fun s => oppositeSkew i s ^ 2)) = 1 := by
  norm_num [Fintype.sum_bool, skewExpectation, oppositeSkew, skewValue]

example (i s : Bool) : |oppositeSkew i s| ≤ 1 := by
  cases i <;> cases s <;> norm_num [oppositeSkew, skewValue, abs_div]

example : skewExpectation (fun s => oppositeSkew false s ^ 3) = 1 / 4 := by
  norm_num [skewExpectation, oppositeSkew, skewValue]

example : skewExpectation (fun s => oppositeSkew true s ^ 3) = -1 / 4 := by
  norm_num [skewExpectation, oppositeSkew, skewValue]

/-- Taking the absolute value after aggregation preserves cancellation. -/
example : |∑ i : Bool, skewExpectation (fun s => oppositeSkew i s ^ 3)| = 0 := by
  norm_num [Fintype.sum_bool, skewExpectation, oppositeSkew, skewValue]

/-- Moving the absolute value inside the sum changes the quantity. -/
example : (∑ i : Bool, |skewExpectation (fun s => oppositeSkew i s ^ 3)|) = 1 / 2 := by
  norm_num [Fintype.sum_bool, skewExpectation, oppositeSkew, skewValue, abs_div]

/-- Vanishing aggregate third moments do not force fourth moments to vanish. -/
example : (∑ i : Bool, skewExpectation (fun s => oppositeSkew i s ^ 4)) = 3 / 4 := by
  norm_num [Fintype.sum_bool, skewExpectation, oppositeSkew, skewValue]

/-- The same two-point marginal calculation as an actual measure. -/
private def skewMeasure : Measure Bool :=
  ENNReal.ofReal (2 / 3 : ℝ) • Measure.dirac false +
    ENNReal.ofReal (1 / 3 : ℝ) • Measure.dirac true

private instance : IsProbabilityMeasure skewMeasure := by
  constructor
  norm_num [skewMeasure, Measure.smul_apply, Measure.add_apply]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

private theorem integral_skewMeasure (f : Bool → ℝ) :
    (∫ s, f s ∂skewMeasure) = skewExpectation f := by
  rw [skewMeasure, integral_add_measure
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)]
  norm_num [integral_smul_measure, integral_dirac, skewExpectation]

/-- This array tests the moment definitions only, without independence or
unit covariance assumptions. The separate Rademacher model below witnesses
all the bounded-CLT hypotheses. -/
private def cancellingObservation (i : Fin 2) (s : Bool) : Vector 1 :=
  fun _ => oppositeSkew (decide (i = 1)) s

example :
    gamma3 skewMeasure
      (fun (_ : Fin 1) (s : Bool) (_ : Fin 1) => oppositeSkew false s) = 1 / 4 := by
  letI : Unique (Fin 1 × Fin 1 × Fin 1) := Unique.mk' _
  unfold gamma3
  simp only [Finset.univ_unique, Finset.fold_singleton]
  norm_num [integral_skewMeasure, skewExpectation, oppositeSkew, skewValue, abs_div]

/-- This check directly uses the public `gamma3` definition; replacing its
absolute value of a sum by a sum of absolute values would break it. -/
example : gamma3 skewMeasure cancellingObservation = 0 := by
  letI : Unique (Fin 1 × Fin 1 × Fin 1) := Unique.mk' _
  unfold gamma3
  simp only [Finset.univ_unique, Finset.fold_singleton]
  norm_num [Fin.sum_univ_two, cancellingObservation,
    integral_skewMeasure, skewExpectation, oppositeSkew, skewValue]

example : gamma4 skewMeasure cancellingObservation = 3 / 4 := by
  unfold gamma4
  simp only [Finset.univ_unique, Finset.fold_singleton]
  norm_num [Fin.sum_univ_two, cancellingObservation,
    integral_skewMeasure, skewExpectation, oppositeSkew, skewValue]

/-- An actual finite probability space, independent of the Gaussian target
space, witnessing that the main probabilistic hypotheses are satisfiable. -/
private def rademacherMeasure : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac false + Measure.dirac true)

private instance : IsProbabilityMeasure rademacherMeasure := by
  constructor
  norm_num [rademacherMeasure, Measure.smul_apply, Measure.add_apply]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

private theorem integral_rademacherMeasure (f : Bool → ℝ) :
    (∫ s, f s ∂rademacherMeasure) = (f false + f true) / 2 := by
  rw [rademacherMeasure, integral_smul_measure,
    integral_add_measure integrable_dirac integrable_dirac]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

private def rademacherValue (s : Bool) : ℝ := if s then 1 else -1

private def rademacherObservation (_ : Fin 1) (s : Bool) : Vector 1 :=
  fun _ => rademacherValue s

private theorem rademacher_covariance :
    covariance rademacherMeasure (sumVector rademacherObservation) =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext j k
  have hjk : j = k := Subsingleton.elim _ _
  norm_num [covariance, sumVector, rademacherObservation, integral_rademacherMeasure,
    rademacherValue, Matrix.one_apply, hjk]

/-- Every substantive bounded-summand hypothesis holds for a one-dimensional
Rademacher observation with `δ = b = 1`. This is not a CLT proof. -/
theorem rademacher_boundedHypotheses :
    BoundedHypotheses rademacherMeasure rademacherObservation 1 1 := by
  refine
    { measurable := fun _ => measurable_of_finite _
      independent := iIndepFun.of_subsingleton
      centered := ?_
      bounded := ?_
      delta_nonneg := by norm_num
      b_pos := by norm_num
      b_le_one := le_rfl
      unit_diagonal := ?_
      spectral_lower := ?_ }
  · intro i j
    norm_num [rademacherObservation, integral_rademacherMeasure, rademacherValue]
  · intro i
    apply Filter.Eventually.of_forall
    intro s
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    cases s <;> norm_num [rademacherObservation, rademacherValue]
  · intro j
    rw [rademacher_covariance]
    simp
  · intro v
    rw [rademacher_covariance]
    simp [Finset.univ_unique, Matrix.one_apply, pow_two]

/-- The concrete Gaussian factor matches the actual covariance; it is not
an arbitrary comparison vector that could be chosen equal to the sum. -/
example :
    (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ).transpose =
      covariance rademacherMeasure (sumVector rademacherObservation) := by
  rw [rademacher_covariance]
  simp

example : gamma3 rademacherMeasure rademacherObservation = 0 := by
  letI : Unique (Fin 1 × Fin 1 × Fin 1) := Unique.mk' _
  unfold gamma3
  simp only [Finset.univ_unique, Finset.fold_singleton]
  norm_num [rademacherObservation,
    integral_rademacherMeasure, rademacherValue]

example : gamma4 rademacherMeasure rademacherObservation = 1 := by
  unfold gamma4
  simp only [Finset.univ_unique, Finset.fold_singleton]
  simp only [rademacherObservation]
  simp_rw [integral_rademacherMeasure]
  norm_num [rademacherValue]

/-- Even a model satisfying every bounded-summand hypothesis has atoms on
rectangle boundaries: this singleton has probability `1/2`. -/
example :
    rademacherMeasure.real
      ((sumVector rademacherObservation) ⁻¹'
        (Rect.closedBox (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1)).carrier) = 1 / 2 := by
  norm_num [measureReal_def, rademacherMeasure, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply, Rect.carrier, Rect.closedBox, sumVector,
    rademacherObservation, rademacherValue]

end

end RectangleCLT.SemanticExamples
