import RectangleCLTCompanion.SplitV4.Printed.Bernstein
import GenericChaining.MixedTail
import RectangleCLTArxivV1.SignedVariance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bounded-sum Bernstein increments

This is passage C2.2 of the frozen paper. The input consists of independent
centered bounded summands and their actual second moments. Bernstein's MGF is
imported from the archive; the Laplace parameter and both signs are optimized
here, including a zero envelope and a zero contrast variance.
-/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An explicit Laplace choice turns the archive's Bernstein MGF into an upper tail.
The variance scale may be zero; positivity of the envelope suffices for the choice. -/
theorem bounded_sum_upper_tail {n : ℕ} (Z : Fin n → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hZi : ∀ i, Integrable (Z i) μ)
    (hZ2 : ∀ i, Integrable (fun ω => Z i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (b : ℝ) (hb : 0 < b) (s : ℝ≥0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ b)
    (hvar : (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) ≤ (s : ℝ) ^ 2)
    {u : ℝ} (hu : 0 < u) :
    μ.real {ω | 2 * Real.sqrt u * (s : ℝ) + 2 * b * u ≤ ∑ i, Z i ω} ≤
      Real.exp (-u) := by
  let q := Real.sqrt u
  let θ := q / ((s : ℝ) + b * q)
  have hq : 0 < q := Real.sqrt_pos.mpr hu
  have hq2 : q ^ 2 = u := Real.sq_sqrt hu.le
  have hden : 0 < (s : ℝ) + b * q := by positivity
  have hθ : 0 < θ := div_pos hq hden
  have hid : θ * ((s : ℝ) + b * q) = q := by
    dsimp [θ]
    exact div_mul_cancel₀ _ hden.ne'
  have hθs : θ * (s : ℝ) ≤ q := by
    calc
      _ ≤ θ * (s : ℝ) + θ * b * q := le_add_of_nonneg_right (by positivity)
      _ = θ * ((s : ℝ) + b * q) := by ring
      _ = q := hid
  have hθb : θ * b ≤ 1 := by
    apply (mul_le_mul_right hq).mp
    calc
      θ * b * q = θ * ((s : ℝ) + b * q) - θ * (s : ℝ) := by ring
      _ = q - θ * (s : ℝ) := by rw [hid]
      _ ≤ 1 * q := by simpa only [one_mul] using sub_le_self q (mul_nonneg hθ.le s.property)
  have hm := RectangleCLT.Companion.SplitV4.Printed.independent_sum_bernstein_mgf_nonneg
    Z hZ hind hZi hZ2 hmean hb hθ.le (by linarith : θ * b < 3)
    (fun i => (hbound i).mono fun ω hω => (le_abs_self _).trans hω) hvar
  have hexp : θ ^ 2 * (s : ℝ) ^ 2 / (2 * (1 - θ * b / 3)) ≤ u := by
    have hd : 1 ≤ 2 * (1 - θ * b / 3) := by linarith
    have hnum : 0 ≤ θ ^ 2 * (s : ℝ) ^ 2 := by positivity
    have hsquare : θ ^ 2 * (s : ℝ) ^ 2 ≤ u := by
      have hh := (sq_le_sq₀ (mul_nonneg hθ.le s.property) hq.le).mpr hθs
      simpa only [mul_pow, hq2] using hh
    apply le_trans _ hsquare
    apply (div_le_iff₀ (by linarith : 0 < 2 * (1 - θ * b / 3))).mpr
    nlinarith [mul_nonneg hnum (sub_nonneg.mpr hd)]
  have hprod : θ * (2 * q * (s : ℝ) + 2 * b * u) = 2 * u := by
    rw [← hq2]
    calc
      _ = 2 * q * (θ * ((s : ℝ) + b * q)) := by ring
      _ = 2 * q * q := by rw [hid]
      _ = 2 * q ^ 2 := by ring
  calc
    _ ≤ Real.exp (-θ * (2 * q * (s : ℝ) + 2 * b * u)) *
        mgf (fun ω => ∑ i, Z i ω) μ θ :=
      measure_ge_le_exp_mul_mgf _ hθ.le hm.1
    _ ≤ Real.exp (-θ * (2 * q * (s : ℝ) + 2 * b * u)) *
        Real.exp (θ ^ 2 * (s : ℝ) ^ 2 / (2 * (1 - θ * b / 3))) :=
      mul_le_mul_of_nonneg_left hm.2 (Real.exp_nonneg _)
    _ = Real.exp (-(2 * u) + θ ^ 2 * (s : ℝ) ^ 2 / (2 * (1 - θ * b / 3))) := by
      rw [← Real.exp_add]
      congr 1
      rw [neg_mul, hprod]
    _ ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)

/-- Two-sided Bernstein increments with universal square-root and linear scales. -/
theorem bounded_sum_abs_tail {n : ℕ} (Z : Fin n → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hZi : ∀ i, Integrable (Z i) μ)
    (hZ2 : ∀ i, Integrable (fun ω => Z i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (b : ℝ) (hb : 0 ≤ b) (s : ℝ≥0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ b)
    (hvar : (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) ≤ (s : ℝ) ^ 2)
    {u : ℝ} (hu : 0 < u) :
    μ.real {ω | Real.sqrt u * (2 * (s : ℝ)) + u * (2 * b) < |∑ i, Z i ω|} ≤
      2 * Real.exp (-u) := by
  by_cases hb0 : b = 0
  · have hz : ∀ᵐ ω ∂μ, ∀ i, Z i ω = 0 := by
      apply ae_all_iff.mpr
      intro i
      exact (hbound i).mono fun ω hω => by
        have hh : |Z i ω| ≤ 0 := by simpa only [hb0] using hω
        exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    have hevent : {ω | Real.sqrt u * (2 * (s : ℝ)) + u * (2 * b) < |∑ i, Z i ω|} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hz] with ω hω
      apply propext
      change (Real.sqrt u * (2 * (s : ℝ)) + u * (2 * b) < |∑ i, Z i ω|) ↔ False
      simp only [hω, Finset.sum_const_zero, abs_zero, iff_false]
      exact not_lt_of_ge (by positivity)
    have hm := measure_congr hevent
    change (μ _).toReal ≤ _
    rw [hm, measure_empty, ENNReal.toReal_zero]
    positivity
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hp := bounded_sum_upper_tail Z hZ hind hZi hZ2 hmean b hbpos s hbound hvar hu
    have hn := bounded_sum_upper_tail (fun i ω => -Z i ω)
      (fun i => (hZ i).neg) (hind.comp (fun _ x => -x) (fun _ => measurable_neg))
      (fun i => (hZi i).neg) (fun i => by simpa only [neg_sq] using hZ2 i)
      (fun i => by rw [integral_neg, hmean i, neg_zero]) b hbpos s
      (fun i => by simpa only [abs_neg] using hbound i)
      (by simpa only [neg_sq] using hvar) hu
    simp only [Finset.sum_neg_distrib] at hn
    let R := 2 * Real.sqrt u * (s : ℝ) + 2 * b * u
    have hsub : {ω | Real.sqrt u * (2 * (s : ℝ)) + u * (2 * b) < |∑ i, Z i ω|} ⊆
        {ω | R ≤ ∑ i, Z i ω} ∪ {ω | R ≤ -(∑ i, Z i ω)} := by
      intro ω hω
      change Real.sqrt u * (2 * (s : ℝ)) + u * (2 * b) < |∑ i, Z i ω| at hω
      by_cases hz : 0 ≤ ∑ i, Z i ω
      · left
        rw [abs_of_nonneg hz] at hω
        dsimp [R]
        linarith
      · right
        rw [abs_of_neg (lt_of_not_ge hz)] at hω
        dsimp [R]
        linarith
    calc
      _ ≤ μ.real ({ω | R ≤ ∑ i, Z i ω} ∪ {ω | R ≤ -(∑ i, Z i ω)}) := measureReal_mono hsub
      _ ≤ μ.real {ω | R ≤ ∑ i, Z i ω} + μ.real {ω | R ≤ -(∑ i, Z i ω)} := measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-u) := by linarith


/-- Measurable bounded scalar variables have integrable first and second moments. -/
theorem integrable_and_sq_of_ae_bound (Z : Ω → ℝ) (hZ : Measurable Z)
    (b : ℝ) (_hb : 0 ≤ b) (hbound : ∀ᵐ ω ∂μ, |Z ω| ≤ b) :
    Integrable Z μ ∧ Integrable (fun ω => Z ω ^ 2) μ := by
  constructor
  · exact (integrable_const b).mono' hZ.aestronglyMeasurable
      (hbound.mono fun ω hω => by simpa only [Real.norm_eq_abs] using hω)
  · apply (integrable_const (b ^ 2)).mono' (hZ.pow_const 2).aestronglyMeasurable
    exact hbound.mono fun ω hω => by
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
        (pow_le_pow_left₀ (abs_nonneg (Z ω)) hω 2)

/-- The scalar two-sided bound requires no moment integrability assumptions
beyond those already implied by measurability and the bounded envelope. -/
theorem bounded_sum_abs_tail_of_bound {n : ℕ} (Z : Fin n → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hind : iIndepFun Z μ)
    (hmean : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (b : ℝ) (hb : 0 ≤ b) (s : ℝ≥0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ b)
    (hvar : (∑ i, ∫ ω, Z i ω ^ 2 ∂μ) ≤ (s : ℝ) ^ 2)
    {u : ℝ} (hu : 0 < u) :
    μ.real {ω | Real.sqrt u * (2 * (s : ℝ)) + u * (2 * b) < |∑ i, Z i ω|} ≤
      2 * Real.exp (-u) :=
  bounded_sum_abs_tail Z hZ hind
    (fun i => (integrable_and_sq_of_ae_bound (Z i) (hZ i) b hb (hbound i)).1)
    (fun i => (integrable_and_sq_of_ae_bound (Z i) (hZ i) b hb (hbound i)).2)
    hmean b hb s hbound hvar hu

/-- Actual independent bounded contrast arrays supply the mixed-tail hypothesis.
The distances here include the two numerical constants from Bernstein's bound. -/
theorem hasMixedTail_of_bounded_contrasts {T : Type*} {n : ℕ}
    (X : T → Ω → ℝ) (Z : T → T → Fin n → Ω → ℝ)
    (b s : T → T → ℝ≥0)
    (heq : ∀ a c ω, X a ω - X c ω = ∑ i, Z a c i ω)
    (hZ : ∀ a c i, Measurable (Z a c i))
    (hind : ∀ a c, iIndepFun (Z a c) μ)
    (hmean : ∀ a c i, ∫ ω, Z a c i ω ∂μ = 0)
    (hbound : ∀ a c i, ∀ᵐ ω ∂μ, |Z a c i ω| ≤ (b a c : ℝ))
    (hvar : ∀ a c, (∑ i, ∫ ω, Z a c i ω ^ 2 ∂μ) ≤ (s a c : ℝ) ^ 2) :
    GenericChaining.HasMixedTail μ X (fun a c => 2 * b a c) (fun a c => 2 * s a c) := by
  intro a c u hu
  have hh := bounded_sum_abs_tail_of_bound (Z a c) (hZ a c) (hind a c)
    (hmean a c) (b a c : ℝ) (b a c).property (s a c) (hbound a c) (hvar a c) hu
  simpa only [GenericChaining.badIncrement, heq, NNReal.coe_mul, NNReal.coe_ofNat] using hh


/-- The standard deviation of the actual signed observation contrast. -/
def signedVarianceMetric {p n : ℕ} (μ : Measure Ω)
    (ξ : Fin n → Ω → RectangleCLT.Vector p) (s t : SignedIndex p) : ℝ≥0 :=
  ⟨Real.sqrt (∑ i, ∫ ω, signedContrast ξ t s i ω ^ 2 ∂μ), Real.sqrt_nonneg _⟩

omit [IsProbabilityMeasure μ] in
/-- Its square is exactly the summed contrast second moment, including zero variance. -/
theorem signedVarianceMetric_sq {p n : ℕ} (ξ : Fin n → Ω → RectangleCLT.Vector p)
    (s t : SignedIndex p) :
    (signedVarianceMetric μ ξ s t : ℝ) ^ 2 = ∑ i, ∫ ω, signedContrast ξ t s i ω ^ 2 ∂μ :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)

/-- The variance scale agrees with the covariance quadratic form from the paper. -/
theorem signedVarianceMetric_sq_covariance {p n : ℕ} {ξ : Fin n → Ω → RectangleCLT.Vector p}
    {δ : ℝ} (h : RectangleCLT.BoundedIndependentHypotheses μ ξ δ) (s t : SignedIndex p) :
    (signedVarianceMetric μ ξ s t : ℝ) ^ 2 =
      RectangleCLT.matrixQuadratic (RectangleCLT.covariance μ (RectangleCLT.sumVector ξ))
        (signedDirection s - signedDirection t) := by
  rw [signedVarianceMetric_sq, sum_variance_signedContrast h]

/-- C2.2: the actual bounded independent signed-coordinate sum has mixed tails.
No spectral assumption or distributional comparison is required. The linear
scale is four times the paper's discrete distance, and the Gaussian scale is
twice the actual contrast standard deviation. -/
theorem signedProcess_hasMixedTail {p n : ℕ} {ξ : Fin n → Ω → RectangleCLT.Vector p}
    {δ : ℝ} (h : RectangleCLT.BoundedIndependentHypotheses μ ξ δ) :
    GenericChaining.HasMixedTail μ (signedProcess (RectangleCLT.sumVector ξ))
      (fun s t => 4 * signedDiscreteMetric ⟨δ, h.delta_nonneg⟩ s t)
      (fun s t => 2 * signedVarianceMetric μ ξ s t) := by
  let b : SignedIndex p → SignedIndex p → ℝ≥0 :=
    fun s t => 2 * signedDiscreteMetric ⟨δ, h.delta_nonneg⟩ s t
  have hh := hasMixedTail_of_bounded_contrasts (signedProcess (RectangleCLT.sumVector ξ))
    (fun s t => signedContrast ξ t s) b (signedVarianceMetric μ ξ)
    (fun s t ω => signedProcess_sumVector_sub ξ t s ω)
    (fun s t i => signedContrast_observation_measurable h t s i)
    (fun s t => signedContrast_independent h t s)
    (fun s t i => integral_signedContrast_zero h t s i)
    (fun s t i => by
      simpa only [b, NNReal.coe_mul, NNReal.coe_ofNat, signedDiscreteMetric, eq_comm]
        using signedContrast_discrete_bound h t s i)
    (fun s t => (signedVarianceMetric_sq ξ s t).ge)
  convert hh using 1
  funext s t
  dsimp [b]
  ring

end
end RectangleCLTArxivV1
