import RectangleCLTCompanion.SplitV4.Printed.LowerModerateArray
import RectangleCLTCompanion.SplitV4.Printed.LowerLaplace

/-! Strict tilted tails at every nonnegative Laplace parameter, including
zero. This supplies the small-threshold part of the printed Esscher route. -/
open MeasureTheory ProbabilityTheory Set
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem integrable_strict_tail_weight (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0≤s) : Integrable (lowerStrictTailWeight s) μ := by
  apply (integrable_const (1:ℝ)).mono' (lowerStrictTailWeight_measurable s).aestronglyMeasurable
  exact ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs,abs_of_nonneg (lowerStrictTailWeight_nonneg s y)] using lowerStrictTailWeight_le_one hs y)

theorem strict_weighted_tail_comparison_nonneg (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {ε s : ℝ} (hε : 0≤ε) (hs : 0≤s)
    (hCDF : ∀x,|μ.real (Iic x)-ν.real (Iic x)|≤ε) :
    |(∫y,lowerStrictTailWeight s y ∂μ)-(∫y,lowerStrictTailWeight s y ∂ν)|≤2*ε := by
  exact strict_laplace_tail_comparison μ ν hε hs hCDF

theorem normalWeightedTail_antitone_nonneg {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    normalWeightedTail t≤normalWeightedTail s := by
  rw [normalWeightedTail_eq_integral,normalWeightedTail_eq_integral]
  apply integral_mono (integrable_strict_tail_weight _ (hs.trans hst)) (integrable_strict_tail_weight _ hs)
  intro y
  unfold lowerStrictTailWeight
  split_ifs with hy
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · exact le_rfl

theorem normalWeightedTail_printed_lower {s : ℝ} (hs : 0≤s) :
    standardNormalPDF 0/(2*(1+s))≤normalWeightedTail s := by
  by_cases h1 : s≤1
  · have hm := normalWeightedTail_antitone_nonneg hs h1
    have hb := normalWeightedTail_mills_lower (by norm_num : (0:ℝ)<1)
    norm_num only [one_pow,show (1:ℝ)+1=2 by norm_num,mul_one] at hb
    have hpdf := standardNormalPDF_pos 0
    have hdiv : standardNormalPDF 0/(2*(1+s))≤standardNormalPDF 0/2 :=
      div_le_div_of_nonneg_left hpdf.le (by norm_num) (by linarith)
    exact hdiv.trans (hb.trans hm)
  · have hs1 : 1≤s := le_of_not_ge h1
    have hsp : 0<s := by linarith
    have hb := normalWeightedTail_mills_lower hsp
    have hd : standardNormalPDF 0/(2*(1+s))≤standardNormalPDF 0*s/(s^2+1) := by
      apply (div_le_div_iff₀ (by positivity : 0<2*(1+s)) (by positivity : 0<s^2+1)).mpr
      have hpdf := standardNormalPDF_pos 0
      nlinarith [mul_nonneg hpdf.le (show 0≤s^2+2*s-1 by nlinarith)]
    exact hd.trans hb

theorem normalWeightedTail_printed_upper {s : ℝ} (hs : 0≤s) :
    normalWeightedTail s≤2*(standardNormalPDF 0+1)/(1+s) := by
  have hpdf := standardNormalPDF_pos 0
  by_cases h1 : s≤1
  · have hj : normalWeightedTail s≤1 := by
      rw [normalWeightedTail_eq_integral]
      have he := integral_mono (μ:=gaussianReal 0 1) (integrable_strict_tail_weight _ hs) (integrable_const (1:ℝ))
        (lowerStrictTailWeight_le_one hs)
      simpa using he
    apply hj.trans
    apply (le_div_iff₀ (by positivity : 0<1+s)).mpr
    nlinarith
  · have hp : 0<s := by linarith
    apply (normalWeightedTail_le hp).trans
    apply (div_le_div_iff₀ hp (by positivity : 0<1+s)).mpr
    nlinarith

theorem abs_log_normalWeightedTail_deriv_printed {s : ℝ} (hs : 0≤s) :
    |(s*normalWeightedTail s-standardNormalPDF 0)/normalWeightedTail s|≤8/(1+s) := by
  have hJ := normalWeightedTail_pos s
  have hpdf := standardNormalPDF_pos 0
  by_cases h1 : 1≤s
  · have hp : 0<s := by linarith
    apply (abs_log_normalWeightedTail_deriv_le hp).trans
    apply (div_le_div_iff₀ hp (by positivity : 0<1+s)).mpr
    linarith
  · have hs1 : s≤1 := le_of_not_ge h1
    have hnum : s*normalWeightedTail s-standardNormalPDF 0≤0 := by
      rcases hs.eq_or_lt with he | he
      · rw [←he]; simp only [zero_mul,zero_sub]; linarith
      · have hh := (le_div_iff₀ he).mp (normalWeightedTail_le he)
        nlinarith
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum hJ.le)]
    rw [show -((s*normalWeightedTail s-standardNormalPDF 0)/normalWeightedTail s)=
      (standardNormalPDF 0-s*normalWeightedTail s)/normalWeightedTail s by ring]
    apply (div_le_div_iff₀ hJ (by positivity : 0<1+s)).mpr
    have hl := (div_le_iff₀ (by positivity : 0<2*(1+s))).mp (normalWeightedTail_printed_lower hs)
    have hsprod : 0≤s*normalWeightedTail s := mul_nonneg hs hJ.le
    have hbound := mul_le_mul_of_nonneg_right hl (by positivity : 0≤1+s)
    have hcoef : 2*(1+s)^2≤8 := by nlinarith [sq_nonneg (1-s)]
    have hh := mul_le_mul_of_nonneg_right hcoef hJ.le
    nlinarith

theorem moderateProductWeightedTail_abs_error_nonneg {n : ℕ} (ν : Fin n→Measure ℝ)
    [∀i,IsProbabilityMeasure (ν i)] (hn : 1≤n) {δ : ℝ} (hδ : 0≤δ)
    (hb : ∀i,∀ᵐ x ∂ν i,|x|≤δ) (t : ℝ)
    (hV : 1/2≤genericTiltTotalVariance ν t) (hs : 0≤moderateProductTailScale ν t) :
    |moderateProductWeightedTail ν t-normalWeightedTail (moderateProductTailScale ν t)|≤
      8*scalarBerryEsseenConstant*δ := by
  letI := genericTiltedProduct_isProbability ν hb t
  have hm := genericTiltedStandardizedSum_measurable ν t
  letI : IsProbabilityMeasure ((genericTiltedProduct ν t).map (genericTiltedStandardizedSum ν t)) :=
    isProbabilityMeasure_map hm.aemeasurable
  have hC := scalarBerryEsseenConstant_pos
  have hc := strict_weighted_tail_comparison_nonneg
    ((genericTiltedProduct ν t).map (genericTiltedStandardizedSum ν t)) (gaussianReal 0 1)
    (by positivity : 0≤4*scalarBerryEsseenConstant*δ) hs
    (genericTiltedStandardizedSum_cdf_of_variance_lower ν hn hδ hb t hV)
  rw [integral_map hm.aemeasurable (lowerStrictTailWeight_measurable _).aestronglyMeasurable,
    ←normalWeightedTail_eq_integral] at hc
  convert hc using 1 <;> ring

theorem moderateProductWeightedTail_log_error_nonneg {n : ℕ} (ν : Fin n→Measure ℝ)
    [∀i,IsProbabilityMeasure (ν i)] (hn : 1≤n) {δ : ℝ} (hδ : 0≤δ)
    (hb : ∀i,∀ᵐ x ∂ν i,|x|≤δ) (t : ℝ)
    (hV : 1/2≤genericTiltTotalVariance ν t) (hs : 0≤moderateProductTailScale ν t)
    (hsmall : moderateWeightedConstant*δ*(1+moderateProductTailScale ν t)≤1/2) :
    0<moderateProductWeightedTail ν t ∧
    |Real.log (moderateProductWeightedTail ν t)-Real.log (normalWeightedTail (moderateProductTailScale ν t))|≤
      2*moderateWeightedConstant*δ*(1+moderateProductTailScale ν t) := by
  have hJ := normalWeightedTail_pos (moderateProductTailScale ν t)
  have hpdf := standardNormalPDF_pos 0
  have hW := moderateWeightedConstant_pos
  have herr := moderateProductWeightedTail_abs_error_nonneg ν hn hδ hb t hV hs
  have hlower := normalWeightedTail_printed_lower hs
  have hrel : |moderateProductWeightedTail ν t/normalWeightedTail (moderateProductTailScale ν t)-1|≤
      moderateWeightedConstant*δ*(1+moderateProductTailScale ν t) := by
    rw [div_sub_one hJ.ne',abs_div,abs_of_pos hJ]
    apply (div_le_iff₀ hJ).mpr
    have hh := (div_le_iff₀ (by positivity : 0<2*(1+moderateProductTailScale ν t))).mp hlower
    have hC := scalarBerryEsseenConstant_pos
    have hfac : 0≤8*scalarBerryEsseenConstant*δ/standardNormalPDF 0 :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) hδ) hpdf.le
    have hc := mul_le_mul_of_nonneg_left hh hfac
    have hleft : (8*scalarBerryEsseenConstant*δ/standardNormalPDF 0)*standardNormalPDF 0=8*scalarBerryEsseenConstant*δ := by
      exact div_mul_cancel₀ _ hpdf.ne'
    rw [hleft] at hc
    have hright : (8*scalarBerryEsseenConstant*δ/standardNormalPDF 0)*
        (normalWeightedTail (moderateProductTailScale ν t)*(2*(1+moderateProductTailScale ν t)))=
      moderateWeightedConstant*δ*(1+moderateProductTailScale ν t)*normalWeightedTail (moderateProductTailScale ν t) := by
      unfold moderateWeightedConstant
      ring
    rw [hright] at hc
    exact herr.trans hc
  have hratio : 0<moderateProductWeightedTail ν t/normalWeightedTail (moderateProductTailScale ν t) := by
    have hh := (abs_le.mp (hrel.trans hsmall)).1
    linarith
  have hpos := (div_pos_iff_of_pos_right hJ).mp hratio
  refine ⟨hpos,?_⟩
  have hc := (lower_abs_log_of_abs_sub_one hrel hsmall).2
  rw [Real.log_div hpos.ne' hJ.ne'] at hc
  nlinarith

end
end RectangleCLT.Companion.SplitV4.Printed
