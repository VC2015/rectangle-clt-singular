import RectangleCLT.BoundedEnvelope
import RectangleCLT.BoundedConcentrationShift

/-! The smaller-envelope estimate and summed uniform derivative majorants
for actual bounded independent sums plus arbitrary independent shifts. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

namespace FaceSmoother

/-- Boundedness of the concrete rational envelope supplies integrability for
every finite probability law. -/
theorem integrable_smallerEnvelope {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {p : ℕ} (s : FaceSmoother p)
    (W : Ω → Vector p) (hW : Measurable W) :
    Integrable (fun ω => s.F (W ω) * (1 - s.F (W ω))) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((s.continuous_F.measurable.comp hW).mul
      (measurable_const.sub (s.continuous_F.measurable.comp hW))).aestronglyMeasurable
  filter_upwards [] with ω
  change ‖s.F (W ω) * (1 - s.F (W ω))‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (s.F_pos _).le (by linarith [s.F_le_one (W ω)]))]
  nlinarith [s.F_le_one (W ω), sq_nonneg (s.F (W ω))]

private theorem sum_thirdLocalMajorant_eq {p : ℕ} (s : FaceSmoother p) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, s.thirdLocalMajorant x j k l) =
      (Real.exp 2) ^ 4 * (s.F x / s.bandwidth ^ 3) *
        (6 * (1 - s.F x) ^ 3 + 6 * (1 - s.F x) ^ 2 + (1 - s.F x)) := by
  simp only [thirdLocalMajorant, ← Finset.mul_sum, FaceWeights.sum_thirdMajorant]
  rfl

private theorem sum_fourthLocalMajorant_eq {p : ℕ} (s : FaceSmoother p) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m) =
      (Real.exp 2) ^ 5 * (s.F x / s.bandwidth ^ 4) *
        (24 * (1 - s.F x) ^ 4 + 36 * (1 - s.F x) ^ 3 +
          14 * (1 - s.F x) ^ 2 + (1 - s.F x)) := by
  simp only [fourthLocalMajorant, ← Finset.mul_sum, FaceWeights.sum_fourthMajorant]
  rfl

/-- An averaged smaller-envelope estimate controls the sum of the individual
uniform third-derivative bounds throughout the bandwidth cube. -/
theorem integral_sum_thirdLocalMajorant_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : ℕ} (s : FaceSmoother p) (W : Ω → Vector p) (hW : Measurable W)
    {B : ℝ} (hB : (∫ ω, s.F (W ω) * (1 - s.F (W ω)) ∂μ) ≤ B) :
    (∫ ω, ∑ j, ∑ k, ∑ l, s.thirdLocalMajorant (W ω) j k l ∂μ) ≤
      (13 * (Real.exp 2) ^ 4) * B / s.bandwidth ^ 3 := by
  let C := (13 * (Real.exp 2) ^ 4) / s.bandwidth ^ 3
  have hC : 0 ≤ C := by
    exact div_nonneg (by positivity) (pow_nonneg s.bandwidth_pos.le _)
  have hm : Measurable (fun ω => ∑ j, ∑ k, ∑ l, s.thirdLocalMajorant (W ω) j k l) := by
    simp_rw [sum_thirdLocalMajorant_eq]
    exact (s.continuous_F.measurable.comp hW |>.div_const _ |>.const_mul _).mul
      (((((s.continuous_F.measurable.comp hW).const_sub 1).pow_const 3).const_mul 6).add
        ((((s.continuous_F.measurable.comp hW).const_sub 1).pow_const 2).const_mul 6) |>.add
          ((s.continuous_F.measurable.comp hW).const_sub 1))
  have hnonneg (ω : Ω) : 0 ≤ ∑ j, ∑ k, ∑ l, s.thirdLocalMajorant (W ω) j k l :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => Finset.sum_nonneg
      (fun l _ => s.thirdLocalMajorant_nonneg (W ω) j k l)))
  have hib := (s.integrable_smallerEnvelope W hW (μ := μ)).const_mul C
  have hpoint (ω : Ω) : (∑ j, ∑ k, ∑ l, s.thirdLocalMajorant (W ω) j k l) ≤
      C * (s.F (W ω) * (1 - s.F (W ω))) := by
    convert s.sum_thirdLocalMajorant_le_variance (W ω) using 1; dsimp [C]; ring
  have hi : Integrable (fun ω => ∑ j, ∑ k, ∑ l, s.thirdLocalMajorant (W ω) j k l) μ :=
    hib.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)] using hpoint ω))
  have hh := integral_mono hi hib hpoint
  rw [integral_const_mul] at hh
  have ht := hh.trans (mul_le_mul_of_nonneg_left hB hC)
  convert ht using 1; dsimp [C]; ring

/-- Fourth-order counterpart of the averaged uniform third-derivative bound. -/
theorem integral_sum_fourthLocalMajorant_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {p : ℕ} (s : FaceSmoother p) (W : Ω → Vector p) (hW : Measurable W)
    {B : ℝ} (hB : (∫ ω, s.F (W ω) * (1 - s.F (W ω)) ∂μ) ≤ B) :
    (∫ ω, ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (W ω) j k l m ∂μ) ≤
      (75 * (Real.exp 2) ^ 5) * B / s.bandwidth ^ 4 := by
  let C := (75 * (Real.exp 2) ^ 5) / s.bandwidth ^ 4
  have hC : 0 ≤ C := by
    exact div_nonneg (by positivity) (pow_nonneg s.bandwidth_pos.le _)
  have hm : Measurable (fun ω => ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (W ω) j k l m) := by
    simp_rw [sum_fourthLocalMajorant_eq]
    exact (s.continuous_F.measurable.comp hW |>.div_const _ |>.const_mul _).mul
      (((((((s.continuous_F.measurable.comp hW).const_sub 1).pow_const 4).const_mul 24).add
        ((((s.continuous_F.measurable.comp hW).const_sub 1).pow_const 3).const_mul 36)).add
        ((((s.continuous_F.measurable.comp hW).const_sub 1).pow_const 2).const_mul 14)).add
          ((s.continuous_F.measurable.comp hW).const_sub 1))
  have hnonneg (ω : Ω) : 0 ≤ ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (W ω) j k l m :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => Finset.sum_nonneg
      (fun l _ => Finset.sum_nonneg (fun m _ => s.fourthLocalMajorant_nonneg (W ω) j k l m))))
  have hib := (s.integrable_smallerEnvelope W hW (μ := μ)).const_mul C
  have hpoint (ω : Ω) : (∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (W ω) j k l m) ≤
      C * (s.F (W ω) * (1 - s.F (W ω))) := by
    convert s.sum_fourthLocalMajorant_le_variance (W ω) using 1; dsimp [C]; ring
  have hi : Integrable (fun ω => ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (W ω) j k l m) μ :=
    hib.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)] using hpoint ω))
  have hh := integral_mono hi hib hpoint
  rw [integral_const_mul] at hh
  have ht := hh.trans (mul_le_mul_of_nonneg_left hB hC)
  convert ht using 1; dsimp [C]; ring

end FaceSmoother

namespace BoundedIndependentHypotheses

/-- The smaller derivative envelope bound, averaged over an arbitrary
independent shift by actual product integration. -/
theorem integral_smallerEnvelope_independent_shift_le
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p}
    {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (ν : Measure E) [IsProbabilityMeasure ν]
    (R : E → Vector p) (hR : Measurable R) :
    (∫ z, s.F (sumVector ξ z.1 + R z.2) * (1 - s.F (sumVector ξ z.1 + R z.2)) ∂μ.prod ν) ≤
      2147483648 * (s.bandwidth + η) * Real.sqrt (dimensionLog p / v) := by
  have hW : Measurable (fun z : Ω × E => sumVector ξ z.1 + R z.2) :=
    (h.measurable_sum.comp measurable_fst).add (hR.comp measurable_snd)
  have hi := s.integrable_smallerEnvelope _ hW (μ := μ.prod ν)
  rw [integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _r, 2147483648 * (s.bandwidth + η) * Real.sqrt (dimensionLog p / v) ∂ν :=
      integral_mono_ae hi.integral_prod_right (integrable_const _)
        (Filter.Eventually.of_forall (fun r => h.integral_smallerEnvelope_le hp hv hdiag s (R r)))
    _ = _ := by simp

/-- Actual bounded-base short-scale third-derivative averaging, also after an
arbitrary independent shift. Each entry majorizes every bandwidth-sized shift. -/
theorem integral_sum_thirdLocalMajorant_independent_shift_le
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p}
    {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (ν : Measure E) [IsProbabilityMeasure ν]
    (R : E → Vector p) (hR : Measurable R) :
    (∫ z, ∑ j, ∑ k, ∑ l, s.thirdLocalMajorant (sumVector ξ z.1 + R z.2) j k l ∂μ.prod ν) ≤
      (13 * (Real.exp 2) ^ 4) *
        (2147483648 * (s.bandwidth + η) * Real.sqrt (dimensionLog p / v)) / s.bandwidth ^ 3 := by
  exact s.integral_sum_thirdLocalMajorant_le _
    ((h.measurable_sum.comp measurable_fst).add (hR.comp measurable_snd))
    (h.integral_smallerEnvelope_independent_shift_le hp hv hdiag s ν R hR)

/-- Actual bounded-base short-scale fourth-derivative averaging. -/
theorem integral_sum_fourthLocalMajorant_independent_shift_le
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p}
    {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (ν : Measure E) [IsProbabilityMeasure ν]
    (R : E → Vector p) (hR : Measurable R) :
    (∫ z, ∑ j, ∑ k, ∑ l, ∑ m,
      s.fourthLocalMajorant (sumVector ξ z.1 + R z.2) j k l m ∂μ.prod ν) ≤
      (75 * (Real.exp 2) ^ 5) *
        (2147483648 * (s.bandwidth + η) * Real.sqrt (dimensionLog p / v)) / s.bandwidth ^ 4 := by
  exact s.integral_sum_fourthLocalMajorant_le _
    ((h.measurable_sum.comp measurable_fst).add (hR.comp measurable_snd))
    (h.integral_smallerEnvelope_independent_shift_le hp hv hdiag s ν R hR)

end BoundedIndependentHypotheses

end RectangleCLT
