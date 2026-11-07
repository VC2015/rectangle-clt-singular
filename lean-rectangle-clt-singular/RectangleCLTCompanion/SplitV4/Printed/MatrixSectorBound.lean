import RectangleCLTCompanion.SplitV4.LogisticMatrixBound
import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorAveraging

/-! The printed B.4 matrix estimate with its analytic threshold input
supplied by the separately checked full-sector and radial-tail route.
Earlier endpoints and their proof values remain unchanged. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
open SignedSurface

theorem sector_averaged_upper_power_trace_le {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L h σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hh : 0 < h) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ 2 * L) (hc : PolyhedralBaseConcentration μ u C δ L) (n : ℕ) :
    |averagedGaussianPowerTrace (μ.map (Matrix.mulVec u)) (upperFaceSmoother a h hh)
      (σ • u) n| ≤
        h * (sectorAveragedThresholdPaperConstant * C * (σ * L * Real.sqrt L + δ * L ^ 2)) /
          (σ * ((n : ℝ) + 1)) := by
  rw [averagedGaussianPowerTrace_map_eq_integral μ (Matrix.mulVec u) (by fun_prop)
    (upperFaceSmoother a h hh) (σ • u) n]
  simp only [gaussianPowerTrace, gaussian_projected_sum]
  apply averaged_logistic_power_trace_le_of_L1_budget μ u hu hi a hh hσ
  · intro b
    exact integrable_gaussianThresholdDerivative_sector_base hm μ u b σ hu hi
  · intro b
    exact averagedGaussianThresholdDerivative_sector_bound_of_log_le_two hm μ u b hu hi hC hδ hσ hL hc.to_threshold

theorem sector_averaged_upper_power_trace_le_scale {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L h σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hh : 0 < h) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ L) (n : ℕ) :
    |averagedGaussianPowerTrace (μ.map (Matrix.mulVec u)) (upperFaceSmoother a h hh)
      (σ • u) n| ≤
        (2 * sectorAveragedThresholdPaperConstant) * C * (h * L * Real.sqrt L) / ((n : ℝ) + 1) := by
  have hL0 : 0 ≤ L := by
    have hmLog : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
    linarith only [hmLog, hL]
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0
  have he : δ * L ^ 2 ≤ σ * L * Real.sqrt L := by
    have ht := mul_le_mul_of_nonneg_right hscale (mul_nonneg hL0 (Real.sqrt_nonneg L))
    have heq : δ * Real.sqrt L * (L * Real.sqrt L) = δ * L ^ 2 := by
      calc
        _ = δ * L * (Real.sqrt L * Real.sqrt L) := by ring
        _ = _ := by rw [hsq]; ring
    simpa only [heq, mul_assoc] using ht
  apply (sector_averaged_upper_power_trace_le hm μ u a hu hi hC hδ hh hσ hL hc n).trans
  calc
    _ ≤ h * (sectorAveragedThresholdPaperConstant * C *
        (σ * L * Real.sqrt L + σ * L * Real.sqrt L)) / (σ * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_left he _)
          (mul_nonneg sectorAveragedThresholdPaperConstant_pos.le hC)) hh.le)
        (mul_nonneg hσ.le (by positivity))
    _ = _ := by field_simp; ring

theorem sector_signed_upper_selector_trace_le {m r k : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L h σ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hh : 0 < h) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ L) (hk : 1 ≤ k) :
    -(∫ x, ∑ α : Fin k → Face m, Matrix.trace
      (selectorGaussianScore (upperFaceSmoother a h hh) (σ • u) (Matrix.mulVec u) α x) ∂μ) ≤
        (2 : ℝ) ^ (k - 1) * ((2 * sectorAveragedThresholdPaperConstant) * C * (h * L * Real.sqrt L)) := by
  letI : IsProbabilityMeasure (μ.map (Matrix.mulVec u)) := isProbabilityMeasure_map (by fun_prop)
  rw [integral_selectorGaussianScore_trace_eq_averaged μ (Matrix.mulVec u) (by fun_prop)]
  apply (neg_le_abs _).trans
  apply abs_averagedGaussianSelectorTrace_le_of_power_bounds _ _ _ hk
  · have hL0 : 0 ≤ L := by
      have hmLog : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
      linarith only [hmLog, hL]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) sectorAveragedThresholdPaperConstant_pos.le) hC)
      (mul_nonneg (mul_nonneg hh.le hL0) (Real.sqrt_nonneg _))
  · intro n _
    exact sector_averaged_upper_power_trace_le_scale hm μ u a hu hi hC hδ hh hσ hL hscale hc n

def sectorLogisticMatrixConstant : ℝ :=
  16 * (Real.exp (13 / 2 : ℝ) + 8) + 2 * sectorAveragedThresholdPaperConstant + 4

theorem sectorLogisticMatrixConstant_pos : 0 < sectorLogisticMatrixConstant := by
  unfold sectorLogisticMatrixConstant
  linarith [Real.exp_pos (13 / 2 : ℝ), sectorAveragedThresholdPaperConstant_pos]

theorem sector_logistic_matrix_coefficient_le (k : ℕ) :
    16 * (Real.exp (13 / 2 : ℝ) + 8) * (k : ℝ) +
      (2 : ℝ) ^ (k - 1) * (2 * sectorAveragedThresholdPaperConstant) ≤ sectorLogisticMatrixConstant ^ (k + 1) := by
  let a := 16 * (Real.exp (13 / 2 : ℝ) + 8) + 2
  let b := 2 * sectorAveragedThresholdPaperConstant + 2
  have ha : 2 ≤ a := by dsimp [a]; linarith [Real.exp_pos (13 / 2 : ℝ)]
  have hb : 2 ≤ b := by dsimp [b]; linarith [sectorAveragedThresholdPaperConstant_pos]
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, div_one] using
      Nat.cast_le_pow_div_sub (show (1 : ℝ) < 2 by norm_num) k
  have hlin : 16 * (Real.exp (13 / 2 : ℝ) + 8) * (k : ℝ) ≤ a ^ (k + 1) := by
    calc
      _ ≤ a * (k : ℝ) := mul_le_mul_of_nonneg_right (by dsimp [a]; linarith) (Nat.cast_nonneg k)
      _ ≤ a * a ^ k := mul_le_mul_of_nonneg_left
        (hk.trans (pow_le_pow_left₀ (by norm_num) ha k)) (by linarith)
      _ = _ := by rw [pow_succ]; ring
  have hexp : (2 : ℝ) ^ (k - 1) * (2 * sectorAveragedThresholdPaperConstant) ≤ b ^ (k + 1) := by
    calc
      _ ≤ b ^ k * b := mul_le_mul
        ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : k - 1 ≤ k)).trans
          (pow_le_pow_left₀ (by norm_num) hb k)) (by dsimp [b]; linarith)
        (mul_nonneg (by norm_num) sectorAveragedThresholdPaperConstant_pos.le) (pow_nonneg (by linarith) _)
      _ = _ := (pow_succ _ _).symm
  exact (add_le_add hlin hexp).trans (by
    convert
      pow_add_pow_le (show 0 ≤ a by linarith) (show 0 ≤ b by linarith) (by omega : k + 1 ≠ 0) using 1
    congr 1
    dsimp [a, b, sectorLogisticMatrixConstant]
    ring)

theorem sector_logistic_matrix_bound_unit_independent {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u)
    {C δ L h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ L)
    (htransition : TransitionMassBound μ (Matrix.mulVec u) h (4 * C * h * Real.sqrt L))
    (q : ℕ) (hq : 1 ≤ q) :
    (∫ x, ∑ α : Fin q → Face m, symmetricNuclearNorm
      (selectorGaussianScore (upperFaceSmoother a h hh) (σ • u) (Matrix.mulVec u) α x) ∂μ) ≤
        sectorLogisticMatrixConstant ^ (q + 1) * C * (h * L * Real.sqrt L) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have hL1 : 0 < L := by
    have hmLog : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
    linarith only [hmLog, hL]
  have hM : 0 < 4 * C * h * Real.sqrt L := by positivity
  have hmean := integral_selectorMeanEnergy_le (k := k) μ (Matrix.mulVec u) (by fun_prop)
    hM htransition (upperFaceSmoother a h hh) rfl hm u hu σ
  have htrace := sector_signed_upper_selector_trace_le hm μ u a hu hi hC.le hδ hh hσ hL hscale hc (by omega : 1 ≤ k + 1)
  have hred := integral_selector_nuclear_sum_le μ (upperFaceSmoother a h hh) (σ • u)
    (Matrix.mulVec u) (by fun_prop) hmean htrace
  have hT : 0 ≤ C * (h * L * Real.sqrt L) := by positivity
  calc
    _ ≤ 2 * ((Real.exp (13 / 2 : ℝ) + 8) * (k + 1 : ℝ) *
        (4 * C * h * Real.sqrt L) * dimensionLog m) +
      (2 : ℝ) ^ (k + 1 - 1) * ((2 * sectorAveragedThresholdPaperConstant) * C * (h * L * Real.sqrt L)) := hred
    _ ≤ (16 * (Real.exp (13 / 2 : ℝ) + 8) * ((k + 1 : ℕ) : ℝ) +
        (2 : ℝ) ^ (k + 1 - 1) * (2 * sectorAveragedThresholdPaperConstant)) * (C * (h * L * Real.sqrt L)) := by
      have ht := mul_le_mul_of_nonneg_left hL
        (show 0 ≤ 2 * ((Real.exp (13 / 2 : ℝ) + 8) * (k + 1 : ℝ) *
          (4 * C * h * Real.sqrt L)) by positivity)
      push_cast
      nlinarith
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (sector_logistic_matrix_coefficient_le (k + 1)) hT


end
end RectangleCLT.Companion.SplitV4.Printed
