import RectangleCLTCompanion.SplitV4.LogisticMatrixBound
import RectangleCLTCompanion.SplitV4.LogisticMatrixIntegrability
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual vanishing-padding and Fatou closure of Appendix B.4. The
original signed normal family may have repetitions and singular Gram matrix.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem transitionMassBound_of_map
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (V : Ω → Vector m) (hV : Measurable V) {h M : ℝ}
    (hc : TransitionMassBound (μ.map V) id h M) : TransitionMassBound μ V h M := by
  intro s hs z
  have hm : AEStronglyMeasurable (fun y : Vector m => s.F (y + z) * s.theta (y + z)) (μ.map V) :=
    ((s.continuous_F.comp (continuous_id.add continuous_const)).mul
      ((SignedSurface.continuous_smoother_theta s).comp (continuous_id.add continuous_const))).aestronglyMeasurable
  have hh := hc s hs z
  simp only [id_eq] at hh
  rw [integral_map hV.aemeasurable hm] at hh
  exact hh

theorem transition_budget_le_four {C δ h L : ℝ}
    (hC : 0 ≤ C) (hδh : δ ≤ h) (hh : 0 ≤ h) :
    2 * (C * (h * Real.log 2 + δ) * Real.sqrt L) ≤ 4 * C * h * Real.sqrt L := by
  have hlog : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at ht ⊢
    exact ht
  have he : h * Real.log 2 + δ ≤ 2 * h := by
    have ht := mul_le_mul_of_nonneg_left hlog hh
    linarith
  have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg L)) hC
  nlinarith

/-- The full actual logistic matrix estimate. Original signed faces may
repeat and the Gaussian covariance may be singular. The only concentration
premise is the paper's genuine uniform base-layer concentration. -/
theorem logistic_matrix_estimate {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    {C δ L h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hδh : δ ≤ h)
    (hσ : 0 < σ) (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ L) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore u a h σ α x) ∂μ) ≤
        logisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
  let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hlam : Tendsto lam atTop (𝓝 0) := by
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [lam, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using ht
  have hlampos (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have hlam0 (n : ℕ) : 0 ≤ lam n := (hlampos n).le
  have hlam1 (n : ℕ) : lam n < 1 := by
    dsimp [lam]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let f : ℕ → Vector r → ℝ := fun n x => ∑ α : Fin k → Fin m, symmetricNuclearNorm
    ((logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
      (logisticPaddedBase (m := m) (lam n) x)).submatrix (Fin.castAdd m) (Fin.castAdd m))
  let f₀ : Vector r → ℝ := fun x => ∑ α : Fin k → Fin m,
    symmetricNuclearNorm (logisticGaussianScore u a h σ α x)
  have hfi (n : ℕ) : Integrable (f n) μ := integrable_logistic_upperLeft_nuclear_sum μ
    (logisticPaddedBase (m := m) (lam n)) (measurable_logisticPaddedBase _) _ a hh σ
  have hf₀i : Integrable f₀ μ := integrable_logistic_nuclear_sum μ id measurable_id u a hh σ
  apply integral_nonnegative_limit_le_uniform_bound μ f f₀ hfi hf₀i
    (fun n x => Finset.sum_nonneg (fun α _ => symmetricNuclearNorm_nonneg _))
    (fun x => Finset.sum_nonneg (fun α _ => symmetricNuclearNorm_nonneg _))
    (fun x => logisticPaddedScore_upperLeft_nuclear_sum_tendsto u a h hh lam hlam hlam0 hlam1 x σ)
  intro n
  let U := logisticPaddedNormals u (lam n)
  let X : Vector r → Vector (r + m) := logisticPaddedBase (m := m) (lam n)
  let ν := μ.map X
  have hX : Measurable X := measurable_logisticPaddedBase _
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hX.aemeasurable
  have hU : ∀ j, vectorNormSq (U j) = 1 := logisticPaddedNormals_unit u hu (hlam0 n) (hlam1 n)
  have hi : LinearIndependent ℝ U := logisticPaddedNormals_linearIndependent u (hlampos n).ne'
  have hcν : PolyhedralBaseConcentration ν U C δ L :=
    logisticPaddedBase_concentrated μ u hc (hlam0 n) (hlam1 n)
  have hmap : ν.map (Matrix.mulVec U) = μ.map (Matrix.mulVec u) := by
    rw [Measure.map_map (by fun_prop) hX]
    exact logisticPaddedBase_projected_law μ u (hlam0 n) (hlam1 n)
  have htm : TransitionMassBound (ν.map (Matrix.mulVec U)) id h
      (2 * (C * (h * Real.log 2 + δ) * Real.sqrt L)) := by
    rw [hmap]
    exact hc.transitionMassBound opposite hopp hh
  have htν : TransitionMassBound ν (Matrix.mulVec U) h (4 * C * h * Real.sqrt L) := by
    intro s hs z
    exact ((transitionMassBound_of_map ν (Matrix.mulVec U) (by fun_prop) htm) s hs z).trans
      (transition_budget_le_four hC.le hδh hh.le)
  have hn := logistic_matrix_bound_unit_independent hm ν U a hU hi hC hδ hh hσ hL hscale hcν htν k hk
  have hnative : (∫ y, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore U a h σ α y) ∂ν) ≤
        logisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
    apply (integral_mono (integrable_logistic_nuclear_sum ν id measurable_id U a hh σ)
      (integrable_selector_nuclear_sum ν (upperFaceSmoother a h hh) (σ • U) (Matrix.mulVec U) (by fun_prop))
      (fun y => logisticGaussianScore_nuclear_sum_le_upper_selector U a h hh σ y)).trans hn
  have hmNative : AEStronglyMeasurable (fun y : Vector (r + m) => ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore U a h σ α y)) ν := by
    simpa only [id_eq] using
      (integrable_logistic_nuclear_sum (k := k) ν id measurable_id U a hh σ).aestronglyMeasurable
  rw [integral_map hX.aemeasurable hmNative] at hnative
  exact (integral_mono (hfi n)
    (integrable_logistic_nuclear_sum μ X hX U a hh σ)
    (fun x => Finset.sum_le_sum (fun α _ => symmetricNuclearNorm_upperLeft_le _))).trans hnative

theorem logistic_matrix_estimate_rectangle {m r p : ℕ}
    (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m ≤ 2 * p)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    {C δ h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hδh : δ ≤ h)
    (hσ : 0 < σ) (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ (dimensionLog p)) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore u a h σ α x) ∂μ) ≤
        logisticMatrixConstant ^ (k + 1) * C *
          (h * dimensionLog p * Real.sqrt (dimensionLog p)) :=
  logistic_matrix_estimate hm μ u a hu opposite hopp hC hδ hh hδh hσ
    (threshold_dimensionLog_faces_le hm hp hmp) hscale hc k hk

end

end RectangleCLT.Companion.SplitV4
