import RectangleCLTCompanion.LowerProductArray
import RectangleCLTCompanion.Statement

/-! # Actual zero-skew Rademacher product arrays -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

lemma rademacherLaw_map_neg : (lowerTwoPointLaw 1).map (fun x : ℝ => -x) = lowerTwoPointLaw 1 := by
  simp [lowerTwoPointLaw, Measure.map_add _ _ measurable_neg, Measure.map_dirac measurable_neg,
    add_comm]

lemma rademacherRowLaw_map_neg (p : ℕ) :
    (lowerRowLaw 1 p).map (fun x : Vector p => -x) = lowerRowLaw 1 p := by
  have hp := measurePreserving_pi (fun _ : Fin p => lowerTwoPointLaw 1)
    (fun _ : Fin p => lowerTwoPointLaw 1)
    (fun _ => (⟨measurable_neg, rademacherLaw_map_neg⟩ :
      MeasurePreserving (fun x : ℝ => -x) (lowerTwoPointLaw 1) (lowerTwoPointLaw 1)))
  exact hp.map_eq

lemma rademacherRowLaw_third {p : ℕ} (j k l : Fin p) :
    (∫ x, x j * x k * x l ∂lowerRowLaw 1 p) = 0 := by
  let f : Vector p → ℝ := fun x => x j * x k * x l
  have hf : Measurable f := ((measurable_pi_apply j).mul (measurable_pi_apply k)).mul
    (measurable_pi_apply l)
  have hh := integral_map (μ := lowerRowLaw 1 p) measurable_neg.aemeasurable hf.aestronglyMeasurable
  rw [rademacherRowLaw_map_neg] at hh
  have hodd : (fun x : Vector p => f (-x)) = fun x => -f x := by
    funext x
    simp only [f, Pi.neg_apply]
    ring
  rw [hodd, integral_neg] at hh
  change (∫ x, x j * x k * x l ∂lowerRowLaw 1 p) = _ at hh
  linarith

lemma rademacherRawRows_third {n p : ℕ} (i : Fin n) (j k l : Fin p) :
    (∫ z, lowerRawRows i z j * lowerRawRows i z k * lowerRawRows i z l
      ∂lowerArrayLaw 1 n p) = 0 := by
  have hm := integral_map (μ := lowerArrayLaw 1 n p)
    (measurable_pi_apply i).aemeasurable
    ((((measurable_pi_apply j).mul (measurable_pi_apply k)).mul
      (measurable_pi_apply l)).aestronglyMeasurable)
  change (∫ y, y j * y k * y l ∂(lowerArrayLaw 1 n p).map (lowerRawRows i)) = _ at hm
  rw [lowerArrayLaw_map_row 1 i, rademacherRowLaw_third] at hm
  exact hm.symm

lemma rademacherNormalizedRows_third {n p : ℕ} (i : Fin n) (j k l : Fin p) :
    (∫ z, lowerNormalizedRows i z j * lowerNormalizedRows i z k * lowerNormalizedRows i z l
      ∂lowerArrayLaw 1 n p) = 0 := by
  change (∫ z, ((1 / Real.sqrt n) * lowerRawRows i z j) *
      ((1 / Real.sqrt n) * lowerRawRows i z k) *
      ((1 / Real.sqrt n) * lowerRawRows i z l) ∂lowerArrayLaw 1 n p) = 0
  have heq : (fun z => ((1 / Real.sqrt n) * lowerRawRows i z j) *
      ((1 / Real.sqrt n) * lowerRawRows i z k) *
      ((1 / Real.sqrt n) * lowerRawRows i z l)) =
      fun z => (1 / Real.sqrt n)^3 * (lowerRawRows i z j * lowerRawRows i z k * lowerRawRows i z l) := by
    funext z
    ring
  rw [heq, integral_const_mul, rademacherRawRows_third, mul_zero]

lemma rademacherNormalizedRows_aggregateThird {n p : ℕ} :
    AggregateThirdMomentsVanish (lowerArrayLaw 1 n p)
      (lowerNormalizedRows (n := n) (p := p)) := by
  intro j k l
  simp_rw [rademacherNormalizedRows_third]
  simp

lemma rademacherNormalizedRows_boundedIndependent {B : ℝ} (hB : 1 ≤ B) (n p : ℕ) :
    BoundedIndependentHypotheses (lowerArrayLaw 1 n p)
      (lowerNormalizedRows (n := n) (p := p)) (B / Real.sqrt n) := by
  have hh := lowerNormalizedRows_boundedIndependent (by norm_num : (1 : ℝ) ≤ 1) n p
  have hδ : 1 / Real.sqrt n ≤ B / Real.sqrt n :=
    div_le_div_of_nonneg_right hB (Real.sqrt_nonneg _)
  exact ⟨hh.measurable, hh.independent, hh.centered,
    fun i => (hh.bounded i).mono (fun z hz => hz.trans hδ), by positivity⟩

lemma rademacher_pairGap_identity (p : ℕ) : pairGap (1 : Matrix (Fin p) (Fin p) ℝ) = 1 := by
  classical
  unfold pairGap maxOffDiagonal
  have hzero : (fun jk : Fin p × Fin p =>
      if jk.1 = jk.2 then (0 : ℝ) else |(1 : Matrix (Fin p) (Fin p) ℝ) jk.1 jk.2|) =
      fun _ => (0 : ℝ) := by
    funext jk
    by_cases h : jk.1 = jk.2 <;> simp [h, Matrix.one_apply]
  rw [hzero]
  have hf : (Finset.univ : Finset (Fin p × Fin p)).fold max 0 (fun _ => (0 : ℝ)) = 0 := by
    rw [Finset.fold_const (0 : ℝ) (by norm_num)]
    split_ifs <;> norm_num
  rw [hf]
  norm_num

lemma rademacherNormalizedRows_covariance {n p : ℕ} (hn : 1 ≤ n) :
    covariance (lowerArrayLaw 1 n p)
      (sumVector (lowerNormalizedRows (n := n) (p := p))) = 1 :=
  lowerNormalizedRows_covariance (by norm_num) hn

lemma rademacherNormalizedRows_pairGap {n p : ℕ} (hn : 1 ≤ n) :
    pairGap (covariance (lowerArrayLaw 1 n p)
      (sumVector (lowerNormalizedRows (n := n) (p := p)))) = 1 := by
  rw [rademacherNormalizedRows_covariance hn, rademacher_pairGap_identity]

end

end RectangleCLT.Companion
