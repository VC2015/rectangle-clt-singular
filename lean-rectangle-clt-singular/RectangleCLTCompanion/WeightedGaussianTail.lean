import RectangleCLTCompanion.NormalTailAsymptotics
import RectangleCLTCompanion.WeightedTailComparison
import Mathlib.Analysis.Calculus.MeanValue

/-! The actual exponentially weighted strict Gaussian tail used in the
Esscher comparison. Mills bounds control its logarithmic derivative. -/

open MeasureTheory ProbabilityTheory Set

namespace RectangleCLT.Companion

noncomputable section

def normalWeightedTail (s : ℝ) : ℝ :=
  Real.exp (s ^ 2 / 2) * standardNormalUpperTail s

lemma normalWeightedTail_pos (s : ℝ) : 0 < normalWeightedTail s :=
  mul_pos (Real.exp_pos _) (standardNormalUpperTail_pos _)

lemma exp_mul_standardNormalPDF (s y : ℝ) :
    Real.exp (-s * y) * standardNormalPDF y =
      Real.exp (s ^ 2 / 2) * standardNormalPDF (y + s) := by
  rw [standardNormalPDF_eq, standardNormalPDF_eq]
  have he : Real.exp (-s * y) * Real.exp (-y ^ 2 / 2) =
      Real.exp (s ^ 2 / 2) * Real.exp (-(y + s) ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        (Real.exp (-s * y) * Real.exp (-y ^ 2 / 2)) := by ring
    _ = _ := by rw [he]; ring

lemma normalWeightedTail_eq_integral (s : ℝ) :
    normalWeightedTail s =
      ∫ y, lowerStrictTailWeight s y ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hpoint (y : ℝ) :
      gaussianPDFReal 0 1 y • lowerStrictTailWeight s y =
        (Ioi (0 : ℝ)).indicator
          (fun y => Real.exp (s ^ 2 / 2) * standardNormalPDF (y + s)) y := by
    simp only [smul_eq_mul, lowerStrictTailWeight, Set.indicator_apply, mem_Ioi]
    split_ifs with hy
    · exact (mul_comm _ _).trans (exp_mul_standardNormalPDF s y)
    · ring
  simp_rw [hpoint]
  rw [integral_indicator measurableSet_Ioi, integral_const_mul]
  unfold normalWeightedTail
  congr 1
  rw [standardNormalUpperTail_eq_integral]
  have ht := integral_add_right_eq_self
    ((Ioi s).indicator standardNormalPDF) s (μ := volume)
  have htrans : (fun y => (Ioi s).indicator standardNormalPDF (y + s)) =
      (Ioi (0 : ℝ)).indicator (fun y => standardNormalPDF (y + s)) := by
    ext y
    simp only [Set.indicator_apply, mem_Ioi]
    congr 1
    apply propext
    constructor <;> intro hh <;> linarith
  rw [htrans, integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Ioi] at ht
  exact ht.symm

lemma standardNormalUpperTail_eq_exp_mul_weighted (x : ℝ) :
    standardNormalUpperTail x = Real.exp (-x ^ 2 / 2) * normalWeightedTail x := by
  unfold normalWeightedTail
  rw [← mul_assoc, ← Real.exp_add]
  simp only [show -x ^ 2 / 2 + x ^ 2 / 2 = 0 by ring, Real.exp_zero, one_mul]

lemma normalWeightedTail_le {s : ℝ} (hs : 0 < s) :
    normalWeightedTail s ≤ standardNormalPDF 0 / s := by
  have hm := mul_le_mul_of_nonneg_left (standardNormalUpperTail_le_mills hs)
    (Real.exp_pos (s ^ 2 / 2)).le
  have he : Real.exp (s ^ 2 / 2) * standardNormalPDF s = standardNormalPDF 0 := by
    rw [standardNormalPDF_eq, standardNormalPDF_eq]
    simp only [neg_sq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      neg_zero, zero_div, Real.exp_zero, mul_one]
    rw [mul_left_comm, ← Real.exp_add]
    simp only [show s ^ 2 / 2 + -s ^ 2 / 2 = 0 by ring, Real.exp_zero, mul_one]
  unfold normalWeightedTail
  calc
    _ ≤ Real.exp (s ^ 2 / 2) * (standardNormalPDF s / s) := hm
    _ = _ := by rw [← mul_div_assoc, he]

lemma normalWeightedTail_mills_lower {s : ℝ} (hs : 0 < s) :
    standardNormalPDF 0 * s / (s ^ 2 + 1) ≤ normalWeightedTail s := by
  have hm := mul_le_mul_of_nonneg_left (mills_le_standardNormalUpperTail hs)
    (Real.exp_pos (s ^ 2 / 2)).le
  have he : Real.exp (s ^ 2 / 2) * standardNormalPDF s = standardNormalPDF 0 := by
    rw [standardNormalPDF_eq, standardNormalPDF_eq]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, zero_div,
      Real.exp_zero, mul_one]
    rw [mul_left_comm, ← Real.exp_add]
    simp only [show s ^ 2 / 2 + -s ^ 2 / 2 = 0 by ring, Real.exp_zero, mul_one]
  calc
    _ = Real.exp (s ^ 2 / 2) * (standardNormalPDF s * s / (s ^ 2 + 1)) := by
      rw [← mul_div_assoc, ← mul_assoc, he]
    _ ≤ _ := hm

lemma hasDerivAt_normalWeightedTail (s : ℝ) :
    HasDerivAt normalWeightedTail
      (s * normalWeightedTail s - standardNormalPDF 0) s := by
  have htail : HasDerivAt standardNormalUpperTail (-standardNormalPDF s) s := by
    convert (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_standardNormalCDF s) using 1
    · exact funext standardNormalUpperTail_eq_one_sub
    · simp
  have hh := ((((hasDerivAt_id s).pow 2).div_const 2).exp).mul htail
  have he : Real.exp (s ^ 2 / 2) * standardNormalPDF s = standardNormalPDF 0 := by
    rw [standardNormalPDF_eq, standardNormalPDF_eq]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, zero_div,
      Real.exp_zero, mul_one]
    rw [mul_left_comm, ← Real.exp_add]
    simp only [show s ^ 2 / 2 + -s ^ 2 / 2 = 0 by ring, Real.exp_zero, mul_one]
  convert hh using 1
  simp only [id_eq, normalWeightedTail]
  rw [show Real.exp (s^2/2) * (-standardNormalPDF s) = -standardNormalPDF 0 by
    rw [mul_neg, he]]
  ring

lemma hasDerivAt_log_normalWeightedTail (s : ℝ) :
    HasDerivAt (fun u => Real.log (normalWeightedTail u))
      ((s * normalWeightedTail s - standardNormalPDF 0) / normalWeightedTail s) s :=
  (hasDerivAt_normalWeightedTail s).log (normalWeightedTail_pos s).ne'

lemma abs_log_normalWeightedTail_deriv_le {s : ℝ} (hs : 0 < s) :
    |(s * normalWeightedTail s - standardNormalPDF 0) / normalWeightedTail s| ≤ 1 / s := by
  have hJ := normalWeightedTail_pos s
  have hu := (le_div_iff₀ hs).mp (normalWeightedTail_le hs)
  have hl := (div_le_iff₀ (by positivity : 0 < s^2+1)).mp
    (normalWeightedTail_mills_lower hs)
  have hnum : s * normalWeightedTail s - standardNormalPDF 0 ≤ 0 := by nlinarith
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hnum hJ.le)]
  apply (le_div_iff₀ hs).mpr
  calc
    _ = (-(s * normalWeightedTail s - standardNormalPDF 0) * s) /
        normalWeightedTail s := by ring
    _ ≤ 1 := (div_le_iff₀ hJ).mpr (by nlinarith)

lemma log_normalWeightedTail_lipschitz {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    |Real.log (normalWeightedTail s) - Real.log (normalWeightedTail x)| ≤
      |s - x| / min s x := by
  have hm : 0 < min s x := lt_min hs hx
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => Real.log (normalWeightedTail u))
    (f' := fun u => (u * normalWeightedTail u - standardNormalPDF 0) / normalWeightedTail u)
    (s := Ici (min s x)) (C := 1 / min s x)
    (fun u _ => (hasDerivAt_log_normalWeightedTail u).hasDerivWithinAt)
    (fun u hu => by
      rw [Real.norm_eq_abs]
      exact (abs_log_normalWeightedTail_deriv_le (hm.trans_le hu)).trans
        (one_div_le_one_div_of_le hm hu))
    (convex_Ici _) (min_le_right s x) (min_le_left s x)
  simpa only [Real.norm_eq_abs, one_div_mul_eq_div] using hh

end

end RectangleCLT.Companion
