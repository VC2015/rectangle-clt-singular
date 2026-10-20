import RectangleCLTCompanion.SelectorMatrixBound
import RectangleCLTCompanion.SharpGaussianSplit
import RectangleCLT.ThinnedHypotheses

/-! The actual full Bernoulli-array and independent half-Gaussian base.
Concentration is applied before averaging the retained array, never to an
individual mask. Only the displayed signed-trace estimate remains a premise
of the final matrix application. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

/-- A harmless common constant for the bounded and Gaussian time ranges. -/
def splitTransitionConstant : ℝ := 8589934592 + 2 * Real.exp (3 / 2 : ℝ)

theorem one_le_splitTransitionConstant : 1 ≤ splitTransitionConstant := by
  unfold splitTransitionConstant
  linarith [Real.exp_nonneg (3 / 2 : ℝ)]

theorem TransitionMassBound.mono {E : Type*} [MeasurableSpace E] {p : ℕ}
    {ν : Measure E} {V : E → Vector p} {h M N : ℝ}
    (hbound : TransitionMassBound ν V h M) (hMN : M ≤ N) :
    TransitionMassBound ν V h N := by
  intro s hs z
  exact (hbound s hs z).trans hMN

/-- Pull back the actual expectation along a measure-preserving map. -/
theorem TransitionMassBound.comp_measurePreserving
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] {p : ℕ}
    {ν : Measure E} {μ : Measure F} {V : F → Vector p} {f : E → F} {h M : ℝ}
    (hbound : TransitionMassBound μ V h M) (hV : Measurable V)
    (hf : MeasurePreserving f ν μ) :
    TransitionMassBound ν (V ∘ f) h M := by
  intro s hs z
  have hm : Measurable (fun y => s.F (V y + z) * s.theta (V y + z)) := by
    change Measurable (fun y => s.F (V y + z) * (1 - s.F (V y + z)))
    exact ((s.continuous_F.measurable.comp (hV.add_const z))).mul
      (measurable_const.sub (s.continuous_F.measurable.comp (hV.add_const z)))
  have heq := integral_map (μ := ν) hf.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hf.map_eq] at heq
  exact heq.symm.trans_le (hbound s hs z)

private theorem sqrt_dimensionLog_div_le_two_sqrt_quarter {p : ℕ}
    (hp : 1 ≤ p) {v : ℝ} (hv : 1 / 4 ≤ v) :
    Real.sqrt (dimensionLog p / v) ≤ 2 * Real.sqrt (dimensionLog p) := by
  have hv0 : 0 < v := by linarith
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  calc
    _ ≤ Real.sqrt (4 * dimensionLog p) := by
      apply Real.sqrt_le_sqrt
      apply (div_le_iff₀ hv0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hv hL]
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num),
        (Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 4)
          (by norm_num : (0 : ℝ) ≤ 2)).mpr (by norm_num)]

/-- Actual transition mass of the full retained-array/half-Gaussian base,
uniformly in the time parameter and the deterministic translation. -/
theorem transitionMassBound_splitBase
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (s : FaceSmoother p) (hband : 12 * δ ≤ s.bandwidth)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    TransitionMassBound (splitBaseLaw μ ξ t) (splitBaseValue A x t) s.bandwidth
      (splitTransitionConstant * s.bandwidth * Real.sqrt (dimensionLog p)) := by
  let B := bernoulliArrayLaw μ ξ t
  let G := splitGaussianScale t • A
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ hdata.measurable t ht ht1
  have hL0 : 0 ≤ Real.sqrt (dimensionLog p) := Real.sqrt_nonneg _
  by_cases hhalf : t ≤ 1 / 2
  · have hv : 0 < 1 - t := by linarith
    have hraw := transitionMassBound_bounded_shift (h := s.bandwidth) (hdata.thinned t ht ht1) hp hv
      (hdata.thinned_sum_unit_diagonal hunit t ht ht1) (standardGaussian p)
      (fun g => x + G.mulVec g) (measurable_const.add (measurable_mulVec G))
    have hsmall : s.bandwidth + 2 * δ ≤ 2 * s.bandwidth := by linarith [hdata.delta_nonneg]
    have hroot := sqrt_dimensionLog_div_le_two_sqrt_quarter hp (show 1 / 4 ≤ 1 - t by linarith)
    have hcap : 2147483648 * (s.bandwidth + 2 * δ) *
        Real.sqrt (dimensionLog p / (1 - t)) ≤
        splitTransitionConstant * s.bandwidth * Real.sqrt (dimensionLog p) := by
      calc
        _ ≤ 2147483648 * (2 * s.bandwidth) * (2 * Real.sqrt (dimensionLog p)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsmall (by norm_num)) hroot
            (Real.sqrt_nonneg _)
            (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) s.bandwidth_pos.le))
        _ = 8589934592 * s.bandwidth * Real.sqrt (dimensionLog p) := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hL0
          apply mul_le_mul_of_nonneg_right _ s.bandwidth_pos.le
          unfold splitTransitionConstant
          linarith [Real.exp_nonneg (3 / 2 : ℝ)]
    intro sm hsm z
    have hh := (hraw.mono hcap) sm hsm z
    simpa only [splitBaseLaw, splitBaseValue, sumVector, arraySum, B, G,
      add_assoc, add_left_comm, add_comm] using hh
  · have hthalf : 1 / 2 ≤ t := le_of_lt (lt_of_not_ge hhalf)
    have hv : 0 < t / 2 := by linarith
    have hdiag (j : Fin p) : (G * G.transpose) j j = t / 2 := by
      have hh := congrArg (fun M : Matrix (Fin p) (Fin p) ℝ => M j j)
        (interpolatedGaussian_covariance A (show 0 ≤ t / 2 by positivity))
      rw [covariance_gaussianLaw] at hh
      simpa only [interpolatedGaussianFactor, hA, Matrix.smul_apply, smul_eq_mul,
        hunit, mul_one, G, splitGaussianScale] using hh
    have hraw := transitionMassBound_gaussian_shift (h := s.bandwidth) hp G hv hdiag B
      (fun b => x + arraySum b) (measurable_const.add (measurable_arraySum p n))
    have hmap : MeasurePreserving
        (fun z : (Fin n → Vector p) × Vector p => (G.mulVec z.2, z.1))
        (B.prod (standardGaussian p)) ((gaussianLaw G).prod B) :=
      (Measure.measurePreserving_swap (μ := B) (ν := gaussianLaw G)).comp
        ((MeasurePreserving.id B).prod
          (show MeasurePreserving G.mulVec (standardGaussian p) (gaussianLaw G) from
            ⟨measurable_mulVec G, rfl⟩))
    have hpull := hraw.comp_measurePreserving
      (measurable_fst.add (measurable_const.add ((measurable_arraySum p n).comp measurable_snd))) hmap
    have hroot := sqrt_dimensionLog_div_le_two_sqrt_quarter hp (show 1 / 4 ≤ t / 2 by linarith)
    have hcap : Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p / (t / 2)) ≤
        splitTransitionConstant * s.bandwidth * Real.sqrt (dimensionLog p) := by
      calc
        _ ≤ Real.exp (3 / 2 : ℝ) * s.bandwidth * (2 * Real.sqrt (dimensionLog p)) :=
          mul_le_mul_of_nonneg_left hroot (mul_nonneg (Real.exp_nonneg _) s.bandwidth_pos.le)
        _ = (2 * Real.exp (3 / 2 : ℝ)) * s.bandwidth * Real.sqrt (dimensionLog p) := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hL0
          apply mul_le_mul_of_nonneg_right _ s.bandwidth_pos.le
          unfold splitTransitionConstant
          linarith
    intro sm hsm z
    have hh := (hpull.mono hcap) sm hsm z
    simpa only [splitBaseLaw, splitBaseValue, Function.comp_apply, B, G,
      add_assoc, add_left_comm, add_comm] using hh

/-- The normalized matrix constant, independent of dimension, order and time. -/
def splitSelectorMatrixConstant (D : ℝ) : ℝ :=
  splitTransitionConstant * selectorMatrixConstant D

theorem one_le_splitSelectorMatrixConstant {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ splitSelectorMatrixConstant D :=
  one_le_mul_of_one_le_of_one_le one_le_splitTransitionConstant (one_le_selectorMatrixConstant hD)

/-- Apply the proved selector matrix reduction to the concrete split base.
Only the actual signed trace estimate is retained explicitly. -/
theorem averagedSelectorMatrixEstimate_splitBase_of_signed_trace_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ D : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (s : FaceSmoother p) (hband : 12 * δ ≤ s.bandwidth)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hD : 0 ≤ D)
    (htrace : ∀ q : ℕ, 1 ≤ q →
      -(∫ ω, ∑ α : Fin q → Face p,
        Matrix.trace (selectorGaussianScore s (splitGaussianScale t • A)
          (splitBaseValue A x t) α ω) ∂splitBaseLaw μ ξ t) ≤
        D ^ (q + 1) * (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p))) :
    AveragedSelectorMatrixEstimate s (splitBaseLaw μ ξ t)
      (splitGaussianScale t • A) (splitBaseValue A x t)
      (splitSelectorMatrixConstant D) (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
  letI := splitBaseLaw_isProbability μ ξ hdata.measurable ht ht1
  let M := splitTransitionConstant * s.bandwidth * Real.sqrt (dimensionLog p)
  let T := s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)
  have hL : 0 < dimensionLog p := lt_of_lt_of_le zero_lt_one (log_exp_mul_nat_ge_one hp)
  have hM : 0 < M := mul_pos (mul_pos
    (lt_of_lt_of_le zero_lt_one one_le_splitTransitionConstant) s.bandwidth_pos)
      (Real.sqrt_pos.mpr hL)
  have hT : 0 ≤ T := mul_nonneg (mul_nonneg s.bandwidth_pos.le hL.le) (Real.sqrt_nonneg _)
  have hMT : M * dimensionLog p = splitTransitionConstant * T := by dsimp [M, T]; ring
  have hTM : T ≤ M * dimensionLog p := by
    rw [hMT]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right one_le_splitTransitionConstant hT
  have hrow (j : Fin p) : vectorNormSq (A j) = 1 := by
    have hh := congrArg (fun Q : Matrix (Fin p) (Fin p) ℝ => Q j j) hA
    change (A * A.transpose) j j = covariance μ (sumVector ξ) j j at hh
    rw [hunit] at hh
    simpa only [vectorNormSq, Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hh
  have hm := averagedSelectorMatrixEstimate_of_signed_trace_bound
    (splitBaseLaw μ ξ t) (splitBaseValue A x t) (measurable_splitBaseValue A x t)
    hM hD (transitionMassBound_splitBase hdata hp hunit A hA x s hband ht ht1)
    s rfl hp A hrow (splitGaussianScale t) (fun q hq =>
      (htrace q hq).trans (mul_le_mul_of_nonneg_left hTM (pow_nonneg hD _)))
  intro q hq b hb B hBm hB
  have hh := hm q hq b hb B hBm hB
  refine ⟨hh.1, ?_⟩
  have hK : splitTransitionConstant ≤ splitTransitionConstant ^ (q + 1) :=
    le_self_pow₀ one_le_splitTransitionConstant (by omega)
  have hC : 0 ≤ selectorMatrixConstant D := zero_le_one.trans (one_le_selectorMatrixConstant hD)
  calc
    _ ≤ b * selectorMatrixConstant D ^ (q + 1) * (M * dimensionLog p) := hh.2
    _ = b * (splitTransitionConstant * selectorMatrixConstant D ^ (q + 1)) * T := by rw [hMT]; ring
    _ ≤ b * ((splitTransitionConstant * selectorMatrixConstant D) ^ (q + 1)) * T := by
      apply mul_le_mul_of_nonneg_right _ hT
      apply mul_le_mul_of_nonneg_left _ hb
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hK (pow_nonneg hC _)
    _ = _ := rfl

end
end RectangleCLT.Companion
