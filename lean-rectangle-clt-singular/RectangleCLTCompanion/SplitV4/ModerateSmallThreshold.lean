import RectangleCLTCompanion.SplitV4.ModerateArrayCumulants
import RectangleCLTCompanion.LowerLogTailError

/-! The strict moderate tail at all thresholds in [0,2], including atoms at zero. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {η : Fin n → Ω → ℝ} {δ : ℝ}

def moderateScalarRows (η : Fin n → Ω → ℝ) (i : Fin n) (ω : Ω) : Vector 1 := fun _ => η i ω

def moderateScalarSum (η : Fin n → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, η i ω

theorem moderateScalarRows_boundedIndependent (hη : ∀ i, Measurable (η i))
    (hind : iIndepFun η μ) (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ)
    (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0) : BoundedIndependentHypotheses μ (moderateScalarRows η) δ := by
  refine ⟨fun i => measurable_pi_lambda _ (fun _ => hη i), ?_, ?_, ?_, hδ⟩
  · exact hind.comp (fun _ x => fun _ : Fin 1 => x)
      (fun _ => measurable_pi_lambda _ (fun _ => measurable_id))
  · intro i j
    exact hc i
  · intro i
    filter_upwards [hbound i] with ω hω
    exact (pi_norm_le_iff_of_nonneg hδ).mpr (fun _ => hω)

theorem moderateScalarSum_berryEsseen (hn : 1 ≤ n) (hη : ∀ i, Measurable (η i))
    (hind : iIndepFun η μ) (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ)
    (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0) (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) (x : ℝ) :
    |μ.real {ω | x < moderateScalarSum η ω} - standardNormalUpperTail x| ≤
      scalarBerryEsseenConstant * δ := by
  let hd := moderateScalarRows_boundedIndependent hη hind hδ hbound hc
  have hu (j : Fin 1) : covariance μ (sumVector (moderateScalarRows η)) j j = 1 := by
    rw [hd.covariance_sum]
    simpa only [moderateScalarRows, ← pow_two] using hv
  have hh := scalarBerryEsseenCDF μ hn (moderateScalarRows η) hd hu x
  have hm : Measurable (moderateScalarSum η) := Finset.measurable_sum _ (fun i _ => hη i)
  have heq : (fun ω => sumVector (moderateScalarRows η) ω 0) = moderateScalarSum η := by
    funext ω
    simp [sumVector, moderateScalarRows, moderateScalarSum]
  rw [heq] at hh
  haveI : IsProbabilityMeasure (μ.map (moderateScalarSum η)) := isProbabilityMeasure_map hm.aemeasurable
  have htail : μ.real {ω | x < moderateScalarSum η ω} = 1 - (μ.map (moderateScalarSum η)).real (Iic x) := by
    calc
      _ = (μ.map (moderateScalarSum η)).real (Ioi x) :=
        congrArg ENNReal.toReal (Measure.map_apply hm measurableSet_Ioi).symm
      _ = _ := by rw [← compl_Iic, measureReal_compl measurableSet_Iic, measureReal_univ_eq_one]
  rw [htail, standardNormalUpperTail_eq_one_sub]
  simpa only [standardNormalCDF, sub_sub_sub_cancel_left, abs_sub_comm] using hh

def moderateSmallTailConstant : ℝ := 2 * scalarBerryEsseenConstant / standardNormalUpperTail 2 + 2

theorem moderateSmallTailConstant_pos : 0 < moderateSmallTailConstant := by
  unfold moderateSmallTailConstant
  have hh := div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) scalarBerryEsseenConstant_pos) (standardNormalUpperTail_pos 2)
  linarith

theorem moderateScalarTail_small_threshold (hn : 1 ≤ n) (hη : ∀ i, Measurable (η i))
    (hind : iIndepFun η μ) (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ)
    (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0) (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1)
    {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 2)
    (hsmall : scalarBerryEsseenConstant * δ / standardNormalUpperTail 2 ≤ 1 / 2) :
    0 < μ.real {ω | x < moderateScalarSum η ω} ∧
    |Real.log (μ.real {ω | x < moderateScalarSum η ω} / standardNormalUpperTail x) -
      moderateArrayGamma μ η * x ^ 3 / 6| ≤ moderateSmallTailConstant * δ := by
  have hC := scalarBerryEsseenConstant_pos
  have hT := standardNormalUpperTail_pos x
  have hT2 := standardNormalUpperTail_pos 2
  have htailmono : standardNormalUpperTail 2 ≤ standardNormalUpperTail x :=
    measureReal_mono (Ioi_subset_Ioi hx2)
  have herr := moderateScalarSum_berryEsseen hn hη hind hδ hbound hc hv x
  have hrelative : |μ.real {ω | x < moderateScalarSum η ω} / standardNormalUpperTail x - 1| ≤
      scalarBerryEsseenConstant * δ / standardNormalUpperTail 2 := by
    rw [show μ.real {ω | x < moderateScalarSum η ω} / standardNormalUpperTail x - 1 =
      (μ.real {ω | x < moderateScalarSum η ω} - standardNormalUpperTail x) / standardNormalUpperTail x by field_simp,
      abs_div, abs_of_pos hT]
    exact (div_le_div_of_nonneg_right herr hT.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hC.le hδ) hT2 htailmono)
  have hlog := lower_abs_log_of_abs_sub_one hrelative hsmall
  have hq : 0 < μ.real {ω | x < moderateScalarSum η ω} := by
    have hh := mul_pos hlog.1 hT
    simpa only [div_mul_cancel₀ _ hT.ne'] using hh
  refine ⟨hq, ?_⟩
  have hgamma := moderateArrayGamma_abs_le hη hδ hbound hv
  have hcube : |moderateArrayGamma μ η * x ^ 3 / 6| ≤ 2 * δ := by
    rw [abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ x ^ 3)]
    norm_num
    have hx3 : x ^ 3 ≤ 8 := by nlinarith [sq_nonneg (x - 2)]
    nlinarith [mul_le_mul_of_nonneg_right hgamma (show 0 ≤ x ^ 3 by positivity),
      mul_le_mul_of_nonneg_left hx3 hδ]
  have hh := (abs_sub _ _).trans (add_le_add hlog.2 hcube)
  apply hh.trans_eq
  unfold moderateSmallTailConstant
  ring

end
end RectangleCLT.Companion.SplitV4
