import RectangleCLTCompanion.Statement
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The cancellation condition is imposed on the full signed third tensor.
The concrete four-point example below has zero marginal third moments and
a nonzero mixed third moment, so marginal cancellation is insufficient. -/

open MeasureTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion

noncomputable section

/-- The signed tensor is summed over observations before any absolute value
is taken. This permits cancellation between different observations. -/
abbrev ThirdMomentCancellation {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) : Prop :=
  AggregateThirdMomentsVanish μ ξ

theorem gamma3_eq_zero_iff {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) :
    gamma3 μ ξ = 0 ↔ ThirdMomentCancellation μ ξ := by
  constructor
  · intro h j k l
    have hh : |∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ| ≤ gamma3 μ ξ := by
      apply (Finset.le_fold_max _).mpr
      exact Or.inr ⟨(j, k, l), Finset.mem_univ _, le_rfl⟩
    rw [h] at hh
    exact abs_nonpos_iff.mp hh
  · intro h
    apply le_antisymm _ (gamma3_nonneg μ ξ)
    apply (Finset.fold_max_le _).mpr
    refine ⟨le_rfl, ?_⟩
    intro jkl _
    rw [h jkl.1 jkl.2.1 jkl.2.2]
    simp

/-- A coordinate-free law formulation of central symmetry. -/
def CentrallySymmetric {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (X : Ω → Vector p) : Prop :=
  μ.map X = μ.map (fun ω => -X ω)

theorem integral_triple_eq_zero_of_centrallySymmetric
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    {μ : Measure Ω} {X : Ω → Vector p} (hX : Measurable X)
    (hsym : CentrallySymmetric μ X) (j k l : Fin p) :
    (∫ ω, X ω j * X ω k * X ω l ∂μ) = 0 := by
  let f : Vector p → ℝ := fun x => x j * x k * x l
  have hf : Measurable f :=
    ((measurable_pi_apply j).mul (measurable_pi_apply k)).mul (measurable_pi_apply l)
  have hi : (∫ ω, f (X ω) ∂μ) = ∫ ω, f (-X ω) ∂μ := by
    rw [← integral_map hX.aemeasurable hf.aestronglyMeasurable,
      ← integral_map hX.neg.aemeasurable hf.aestronglyMeasurable, hsym]
  have hneg : (∫ ω, f (-X ω) ∂μ) = -(∫ ω, f (X ω) ∂μ) := by
    simp only [f, Pi.neg_apply, neg_mul, mul_neg, neg_neg, integral_neg]
  change (∫ ω, f (X ω) ∂μ) = 0
  linarith

theorem thirdMomentCancellation_of_centrallySymmetric
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} {ξ : Fin n → Ω → Vector p}
    (hξ : ∀ i, Measurable (ξ i)) (hsym : ∀ i, CentrallySymmetric μ (ξ i)) :
    ThirdMomentCancellation μ ξ := by
  intro j k l
  apply Finset.sum_eq_zero
  intro i _
  exact integral_triple_eq_zero_of_centrallySymmetric (hξ i) (hsym i) j k l

theorem gamma3_eq_zero_of_centrallySymmetric
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} {ξ : Fin n → Ω → Vector p}
    (hξ : ∀ i, Measurable (ξ i)) (hsym : ∀ i, CentrallySymmetric μ (ξ i)) :
    gamma3 μ ξ = 0 :=
  (gamma3_eq_zero_iff μ ξ).mpr (thirdMomentCancellation_of_centrallySymmetric hξ hsym)

/-- Every mixed third moment of a deterministic linear image is the finite
tensor contraction of the original third moments. The integrability
assumptions concern the actual mixed moments being contracted. -/
theorem integral_mulVec_triple
    {Ω : Type*} [MeasurableSpace Ω] {p q : ℕ}
    (μ : Measure Ω) (X : Ω → Vector p) (A : Matrix (Fin q) (Fin p) ℝ)
    (hInt : ∀ r s t, Integrable (fun ω => X ω r * X ω s * X ω t) μ)
    (j k l : Fin q) :
    (∫ ω, A.mulVec (X ω) j * A.mulVec (X ω) k * A.mulVec (X ω) l ∂μ) =
      ∑ r, ∑ s, ∑ t, (A j r * A k s * A l t) *
        (∫ ω, X ω r * X ω s * X ω t ∂μ) := by
  let g : Fin p → Fin p → Fin p → Ω → ℝ := fun r s t ω =>
    (A j r * A k s * A l t) * (X ω r * X ω s * X ω t)
  have hg (r s t : Fin p) : Integrable (g r s t) μ :=
    (hInt r s t).const_mul _
  have hpnt (ω : Ω) :
      A.mulVec (X ω) j * A.mulVec (X ω) k * A.mulVec (X ω) l =
        ∑ r, ∑ s, ∑ t, g r s t ω := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    dsimp only [g]
    ring
  simp_rw [hpnt]
  rw [integral_finset_sum Finset.univ (fun r _ =>
    integrable_finset_sum Finset.univ (fun s _ =>
      integrable_finset_sum Finset.univ (fun t _ => hg r s t)))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finset_sum Finset.univ (fun s _ =>
    integrable_finset_sum Finset.univ (fun t _ => hg r s t))]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_finset_sum Finset.univ (fun t _ => hg r s t)]
  simp only [g, integral_const_mul]

/-- Cancellation can occur across observations and is preserved by any
deterministic linear map, including noninvertible maps and coordinate
projections. -/
theorem ThirdMomentCancellation.mulVec
    {Ω : Type*} [MeasurableSpace Ω] {p q n : ℕ}
    {μ : Measure Ω} {ξ : Fin n → Ω → Vector p}
    (hcancel : ThirdMomentCancellation μ ξ)
    (hInt : ∀ i r s t, Integrable (fun ω => ξ i ω r * ξ i ω s * ξ i ω t) μ)
    (A : Matrix (Fin q) (Fin p) ℝ) :
    ThirdMomentCancellation μ (fun i ω => A.mulVec (ξ i ω)) := by
  intro j k l
  simp_rw [integral_mulVec_triple μ _ A (hInt _) j k l]
  have hswap :
      (∑ i, ∑ r, ∑ s, ∑ t, (A j r * A k s * A l t) *
        (∫ ω, ξ i ω r * ξ i ω s * ξ i ω t ∂μ)) =
      ∑ r, ∑ s, ∑ t, (A j r * A k s * A l t) *
        (∑ i, ∫ ω, ξ i ω r * ξ i ω s * ξ i ω t ∂μ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  rw [hswap]
  apply Finset.sum_eq_zero
  intro r _
  apply Finset.sum_eq_zero
  intro s _
  apply Finset.sum_eq_zero
  intro t _
  rw [hcancel r s t, mul_zero]

theorem gamma3_mulVec_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {p q n : ℕ}
    {μ : Measure Ω} {ξ : Fin n → Ω → Vector p}
    (hzero : gamma3 μ ξ = 0)
    (hInt : ∀ i r s t, Integrable (fun ω => ξ i ω r * ξ i ω s * ξ i ω t) μ)
    (A : Matrix (Fin q) (Fin p) ℝ) :
    gamma3 μ (fun i ω => A.mulVec (ξ i ω)) = 0 :=
  (gamma3_eq_zero_iff _ _).mpr (((gamma3_eq_zero_iff _ _).mp hzero).mulVec hInt A)

theorem AggregateThirdMomentsVanish.mulVec
    {Ω : Type*} [MeasurableSpace Ω] {p q n : ℕ}
    {μ : Measure Ω} {ξ : Fin n → Ω → Vector p}
    (hcancel : AggregateThirdMomentsVanish μ ξ)
    (hInt : ∀ i r s t, Integrable (fun ω => ξ i ω r * ξ i ω s * ξ i ω t) μ)
    (A : Matrix (Fin q) (Fin p) ℝ) :
    AggregateThirdMomentsVanish μ (fun i ω => A.mulVec (ξ i ω)) :=
  ThirdMomentCancellation.mulVec hcancel hInt A

/-- Two opposite row laws cancel in the aggregate, regardless of the skew
of either row separately. This identity concerns only the third moments;
independence is an additional hypothesis of the CLT. -/
def pairedObservation {Ω : Type*} {p : ℕ} (X : Ω → Vector p) (i : Fin 2) (ω : Ω) : Vector p :=
  if i = 0 then X ω else -X ω

theorem aggregateThirdMomentsVanish_pairedObservation
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (X : Ω → Vector p) :
    AggregateThirdMomentsVanish μ (pairedObservation X) := by
  intro j k l
  simp [Fin.sum_univ_two, pairedObservation, neg_mul, mul_neg, integral_neg]

/-- Four equiprobable sign pairs. The two signs are independent under this
law, although the three output coordinates need not be independent. -/
def signPairLaw : Measure (Bool × Bool) :=
  (4 : ℝ≥0∞)⁻¹ • (Measure.dirac (false, false) + Measure.dirac (false, true) +
    Measure.dirac (true, false) + Measure.dirac (true, true))

instance signPairLaw_isProbability : IsProbabilityMeasure signPairLaw := by
  constructor
  norm_num [signPairLaw, Measure.smul_apply, Measure.add_apply]
  calc
    (4 : ℝ≥0∞)⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ = 4 * 4⁻¹ := by ring
    _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem integral_signPairLaw (f : Bool × Bool → ℝ) :
    (∫ ω, f ω ∂signPairLaw) =
      (f (false, false) + f (false, true) + f (true, false) + f (true, true)) / 4 := by
  have h₂ : Integrable f (Measure.dirac (false, false) + Measure.dirac (false, true)) :=
    integrable_dirac.add_measure integrable_dirac
  have h₃ : Integrable f (Measure.dirac (false, false) + Measure.dirac (false, true) +
      Measure.dirac (true, false)) := h₂.add_measure integrable_dirac
  rw [signPairLaw, integral_smul_measure, integral_add_measure h₃ integrable_dirac,
    integral_add_measure h₂ integrable_dirac, integral_add_measure integrable_dirac integrable_dirac]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

def signValue (b : Bool) : ℝ := if b then 1 else -1

/-- The vector `(X,Y,XY)`, with independent symmetric signs `X,Y`. -/
def mixedSignVector (ω : Bool × Bool) : Vector 3 :=
  ![signValue ω.1, signValue ω.2, signValue ω.1 * signValue ω.2]

def mixedSignObservation (_ : Fin 1) : Bool × Bool → Vector 3 := mixedSignVector

theorem mixedSignVector_centered (j : Fin 3) :
    (∫ ω, mixedSignVector ω j ∂signPairLaw) = 0 := by
  fin_cases j <;> norm_num [integral_signPairLaw, mixedSignVector, signValue]

theorem mixedSignVector_marginal_third_zero (j : Fin 3) :
    (∫ ω, (mixedSignVector ω j) ^ 3 ∂signPairLaw) = 0 := by
  fin_cases j <;> norm_num [integral_signPairLaw, mixedSignVector, signValue]

theorem mixedSignVector_mixed_third_one :
    (∫ ω, mixedSignVector ω 0 * mixedSignVector ω 1 * mixedSignVector ω 2
      ∂signPairLaw) = 1 := by
  norm_num [integral_signPairLaw, mixedSignVector, signValue, Matrix.cons_val_two]

theorem mixedSignVector_abs_coordinate (ω : Bool × Bool) (j : Fin 3) :
    |mixedSignVector ω j| = 1 := by
  rcases ω with ⟨x, y⟩
  fin_cases j <;> cases x <;> cases y <;>
    norm_num [mixedSignVector, signValue]

theorem mixedSignVector_norm_le_one (ω : Bool × Bool) : ‖mixedSignVector ω‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  simpa only [Real.norm_eq_abs, mixedSignVector_abs_coordinate] using (le_rfl : (1 : ℝ) ≤ 1)

theorem mixedSignVector_covariance :
    covariance signPairLaw mixedSignVector = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [covariance, integral_signPairLaw, mixedSignVector, signValue, Matrix.one_apply]

theorem mixedSignObservation_boundedIndependentHypotheses :
    BoundedIndependentHypotheses signPairLaw mixedSignObservation 1 := by
  refine
    { measurable := fun _ => measurable_of_finite _
      independent := ProbabilityTheory.iIndepFun.of_subsingleton
      centered := ?_
      bounded := ?_
      delta_nonneg := by norm_num }
  · intro i j
    exact mixedSignVector_centered j
  · intro i
    exact ae_of_all _ mixedSignVector_norm_le_one

theorem mixedSignVector_abs_integral_triple_le_one (j k l : Fin 3) :
    |∫ ω, mixedSignVector ω j * mixedSignVector ω k * mixedSignVector ω l
      ∂signPairLaw| ≤ 1 := by
  calc
    _ ≤ ∫ ω, |mixedSignVector ω j * mixedSignVector ω k * mixedSignVector ω l|
        ∂signPairLaw := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω => mixedSignVector ω j * mixedSignVector ω k * mixedSignVector ω l)
        (μ := signPairLaw)
    _ = 1 := by
      simp only [abs_mul, mixedSignVector_abs_coordinate, one_mul]
      simp

theorem mixedSignObservation_gamma3_eq_one :
    gamma3 signPairLaw mixedSignObservation = 1 := by
  apply le_antisymm
  · apply (Finset.fold_max_le _).mpr
    refine ⟨by norm_num, ?_⟩
    intro jkl _
    simpa only [Fintype.sum_unique, mixedSignObservation] using
      mixedSignVector_abs_integral_triple_le_one jkl.1 jkl.2.1 jkl.2.2
  · have hentry :
        |∑ i, ∫ ω, mixedSignObservation i ω 0 * mixedSignObservation i ω 1 *
          mixedSignObservation i ω 2 ∂signPairLaw| ≤ gamma3 signPairLaw mixedSignObservation := by
      apply (Finset.le_fold_max _).mpr
      exact Or.inr ⟨(0, 1, 2), Finset.mem_univ _, le_rfl⟩
    simpa only [Fintype.sum_unique, mixedSignObservation,
      mixedSignVector_mixed_third_one, abs_one] using hentry

theorem mixedSignObservation_not_cancellation :
    ¬ ThirdMomentCancellation signPairLaw mixedSignObservation := by
  intro h
  have hh := h 0 1 2
  simp only [mixedSignObservation, Fintype.sum_unique, mixedSignVector_mixed_third_one] at hh
  norm_num at hh

theorem mixedSignObservation_gamma3_ne_zero :
    gamma3 signPairLaw mixedSignObservation ≠ 0 := by
  intro h
  exact mixedSignObservation_not_cancellation ((gamma3_eq_zero_iff _ _).mp h)

/-- A genuine centered bounded probability model with identity covariance
and zero marginal third moments, but a nonzero aggregate mixed third tensor.
It satisfies the independent-row data hypotheses with a single vector row. -/
theorem marginal_third_moments_insufficient :
    ∃ (μ : Measure (Bool × Bool)) (ξ : Fin 1 → Bool × Bool → Vector 3),
      IsProbabilityMeasure μ ∧ BoundedIndependentHypotheses μ ξ 1 ∧
      covariance μ (sumVector ξ) = (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
      (∀ j, (∑ i, ∫ ω, (ξ i ω j) ^ 3 ∂μ) = 0) ∧ gamma3 μ ξ = 1 := by
  refine ⟨signPairLaw, mixedSignObservation, inferInstance,
    mixedSignObservation_boundedIndependentHypotheses, ?_, ?_, mixedSignObservation_gamma3_eq_one⟩
  · have hsum : sumVector mixedSignObservation = mixedSignVector := by
      funext ω
      simp only [sumVector, Fintype.sum_unique, mixedSignObservation]
    rw [hsum]
    exact mixedSignVector_covariance
  · intro j
    simpa only [Fintype.sum_unique, mixedSignObservation] using mixedSignVector_marginal_third_zero j

end
end RectangleCLT.Companion
