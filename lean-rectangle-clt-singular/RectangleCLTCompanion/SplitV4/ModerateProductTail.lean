import RectangleCLTCompanion.SplitV4.ModerateProductCumulants
import RectangleCLTCompanion.LowerLogTailError

/-! Actual strict-tail Esscher and logarithmic comparisons for nonidentical laws. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section
variable {n : ℕ}

def moderateProductTailScale (ν : Fin n → Measure ℝ) (t : ℝ) : ℝ := t * Real.sqrt (genericTiltTotalVariance ν t)

def moderateProductWeightedTail (ν : Fin n → Measure ℝ) (t : ℝ) : ℝ :=
  ∫ z, lowerStrictTailWeight (moderateProductTailScale ν t) (genericTiltedStandardizedSum ν t z)
    ∂genericTiltedProduct ν t

def moderateWeightedConstant : ℝ := 16 * scalarBerryEsseenConstant / standardNormalPDF 0

theorem moderateWeightedConstant_pos : 0 < moderateWeightedConstant :=
  div_pos (mul_pos (by norm_num) scalarBerryEsseenConstant_pos) (standardNormalPDF_pos 0)

theorem moderateProduct_strict_tail_tilt (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    {δ : ℝ} (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t a : ℝ) :
    (Measure.pi ν).real {z | a < ∑ i, z i} = Real.exp ((∑ i, cgf id (ν i) t) - t * a) *
      ∫ z, lowerStrictTailWeight t ((∑ i, z i) - a) ∂genericTiltedProduct ν t := by
  have hs : MeasurableSet {z : Fin n → ℝ | a < ∑ i, z i} :=
    measurableSet_lt measurable_const (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
  rw [← integral_indicator_one hs,
    ← genericTiltedProduct_inverse_integral ν hbound t (Set.indicator {z | a < ∑ i, z i} (1 : (Fin n → ℝ) → ℝ)),
    ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [smul_eq_mul, lowerStrictTailWeight]
  by_cases hz : a < ∑ i, z i
  · have hzin : z ∈ {z : Fin n → ℝ | a < ∑ i, z i} := hz
    rw [Set.indicator_of_mem hzin]
    simp only [Pi.one_apply, mul_one, sub_pos.mpr hz, if_true]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp [hz, not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hz))]

theorem moderateProduct_strict_tail_standardized (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ} (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ)
    (t : ℝ) (hV : 0 < genericTiltTotalVariance ν t) {x : ℝ}
    (hroot : (∑ i, genericTiltMean (ν i) t) = x) :
    (Measure.pi ν).real {z | x < ∑ i, z i} =
      Real.exp ((∑ i, cgf id (ν i) t) - t * x) * moderateProductWeightedTail ν t := by
  rw [moderateProduct_strict_tail_tilt ν hbound t x]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro z
  change lowerStrictTailWeight t ((∑ i, z i) - x) =
    lowerStrictTailWeight (moderateProductTailScale ν t) (genericTiltedStandardizedSum ν t z)
  rw [genericTiltedStandardizedSum_eq, hroot]
  have hsqrt := Real.sqrt_pos.mpr hV
  unfold lowerStrictTailWeight moderateProductTailScale
  have hsign : 0 < ((∑ i, z i) - x) / Real.sqrt (genericTiltTotalVariance ν t) ↔ 0 < (∑ i, z i) - x :=
    div_pos_iff_of_pos_right hsqrt
  simp only [hsign]
  split_ifs
  · congr 1
    field_simp
    ring
  · rfl

theorem moderateProductWeightedTail_abs_error (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ)
    (hV : 1 / 2 ≤ genericTiltTotalVariance ν t) (hs : 0 < moderateProductTailScale ν t) :
    |moderateProductWeightedTail ν t - normalWeightedTail (moderateProductTailScale ν t)| ≤
      8 * scalarBerryEsseenConstant * δ := by
  letI := genericTiltedProduct_isProbability ν hbound t
  have hm := genericTiltedStandardizedSum_measurable ν t
  letI : IsProbabilityMeasure ((genericTiltedProduct ν t).map (genericTiltedStandardizedSum ν t)) :=
    isProbabilityMeasure_map hm.aemeasurable
  have hC := scalarBerryEsseenConstant_pos
  have hh := lower_strict_weighted_tail_comparison
    ((genericTiltedProduct ν t).map (genericTiltedStandardizedSum ν t)) (gaussianReal 0 1)
    (by positivity : 0 ≤ 4 * scalarBerryEsseenConstant * δ) hs
    (genericTiltedStandardizedSum_cdf_of_variance_lower ν hn hδ hbound t hV)
  rw [integral_map hm.aemeasurable (lowerStrictTailWeight_measurable _).aestronglyMeasurable,
    ← normalWeightedTail_eq_integral] at hh
  convert hh using 1 <;> ring

theorem moderateProductWeightedTail_log_error (ν : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ)
    (hV : 1 / 2 ≤ genericTiltTotalVariance ν t) (hs : 1 ≤ moderateProductTailScale ν t)
    (hsmall : moderateWeightedConstant * δ * moderateProductTailScale ν t ≤ 1 / 2) :
    0 < moderateProductWeightedTail ν t ∧
    |Real.log (moderateProductWeightedTail ν t) - Real.log (normalWeightedTail (moderateProductTailScale ν t))| ≤
      2 * moderateWeightedConstant * δ * moderateProductTailScale ν t := by
  have hs0 : 0 < moderateProductTailScale ν t := by linarith
  have hJ := normalWeightedTail_pos (moderateProductTailScale ν t)
  have herr := moderateProductWeightedTail_abs_error ν hn hδ hbound t hV hs0
  have hrelative : |moderateProductWeightedTail ν t / normalWeightedTail (moderateProductTailScale ν t) - 1| ≤
      moderateWeightedConstant * δ * moderateProductTailScale ν t := by
    rw [show moderateProductWeightedTail ν t / normalWeightedTail (moderateProductTailScale ν t) - 1 =
      (moderateProductWeightedTail ν t - normalWeightedTail (moderateProductTailScale ν t)) /
        normalWeightedTail (moderateProductTailScale ν t) by field_simp, abs_div, abs_of_pos hJ]
    apply (div_le_iff₀ hJ).mpr
    calc
      _ ≤ 8 * scalarBerryEsseenConstant * δ := herr
      _ = (moderateWeightedConstant * δ * moderateProductTailScale ν t) *
          (standardNormalPDF 0 / (2 * moderateProductTailScale ν t)) := by
        unfold moderateWeightedConstant
        field_simp [(standardNormalPDF_pos 0).ne', hs0.ne']
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (normalWeightedTail_ge_simple hs)
        (by have := moderateWeightedConstant_pos; positivity)
  have hh := lower_abs_log_of_abs_sub_one hrelative hsmall
  have hE : 0 < moderateProductWeightedTail ν t := by
    have hp := mul_pos hh.1 hJ
    simpa only [div_mul_cancel₀ _ hJ.ne'] using hp
  refine ⟨hE, ?_⟩
  rw [← Real.log_div hE.ne' hJ.ne']
  simpa only [mul_assoc] using hh.2


theorem moderateProduct_log_esscher (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    {δ : ℝ} (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ)
    (hV : 0 < genericTiltTotalVariance ν t) {x : ℝ}
    (hroot : (∑ i, genericTiltMean (ν i) t) = x) (hE : 0 < moderateProductWeightedTail ν t) :
    Real.log ((Measure.pi ν).real {z | x < ∑ i, z i} / standardNormalUpperTail x) =
      ((∑ i, cgf id (ν i) t) - t * x + x ^ 2 / 2) +
        (Real.log (moderateProductWeightedTail ν t) - Real.log (normalWeightedTail (moderateProductTailScale ν t))) +
        (Real.log (normalWeightedTail (moderateProductTailScale ν t)) - Real.log (normalWeightedTail x)) := by
  have hT := standardNormalUpperTail_pos x
  have hJx : Real.log (normalWeightedTail x) = x ^ 2 / 2 + Real.log (standardNormalUpperTail x) := by
    rw [normalWeightedTail, Real.log_mul (Real.exp_pos _).ne' hT.ne', Real.log_exp]
  rw [moderateProduct_strict_tail_standardized ν hbound t hV hroot,
    Real.log_div (mul_pos (Real.exp_pos _) hE).ne' hT.ne',
    Real.log_mul (Real.exp_pos _).ne' hE.ne', Real.log_exp, hJx]
  ring

theorem moderateProduct_log_esscher_error (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ)
    (hV : 1 / 2 ≤ genericTiltTotalVariance ν t) {x : ℝ} (hx : 0 < x)
    (hroot : (∑ i, genericTiltMean (ν i) t) = x)
    (hs : 1 ≤ moderateProductTailScale ν t)
    (hsmall : moderateWeightedConstant * δ * moderateProductTailScale ν t ≤ 1 / 2) :
    0 < (Measure.pi ν).real {z | x < ∑ i, z i} ∧
    |Real.log ((Measure.pi ν).real {z | x < ∑ i, z i} / standardNormalUpperTail x) -
      ((∑ i, cgf id (ν i) t) - t * x + x ^ 2 / 2)| ≤
        2 * moderateWeightedConstant * δ * moderateProductTailScale ν t +
          |moderateProductTailScale ν t - x| / min (moderateProductTailScale ν t) x := by
  have hVpos : 0 < genericTiltTotalVariance ν t := by linarith
  have hE := moderateProductWeightedTail_log_error ν hn hδ hbound t hV hs hsmall
  constructor
  · rw [moderateProduct_strict_tail_standardized ν hbound t hVpos hroot]
    exact mul_pos (Real.exp_pos _) hE.1
  · rw [moderateProduct_log_esscher ν hbound t hVpos hroot hE.1]
    have hh := (abs_add
      (Real.log (moderateProductWeightedTail ν t) - Real.log (normalWeightedTail (moderateProductTailScale ν t)))
      (Real.log (normalWeightedTail (moderateProductTailScale ν t)) - Real.log (normalWeightedTail x))).trans
      (add_le_add hE.2 (log_normalWeightedTail_lipschitz (by linarith : 0 < moderateProductTailScale ν t) hx))
    convert hh using 1 <;> ring

end
end RectangleCLT.Companion.SplitV4
