import RectangleCLTArxivV1.LowerMaskedProfile
import RectangleCLTCompanion.SplitV4.MaskedFourthCalibration
import Mathlib.Data.Complex.ExponentialBounds

/-! Width-sensitive numerical scales for the growing fourth-moment model. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerMaskedFourthRawWidth (n : ℕ) (ell B g : ℝ) : ℝ :=
  maskedFourthAmplitude n ell B*maskedFourthCount ell B*g/Real.sqrt n

def lowerMaskedFourthIntrinsicRate (n : ℕ) (L B g : ℝ) : ℝ :=
  B*g*L^(3/4 : ℝ)/((n : ℝ)^(1/4 : ℝ)*Real.log (Real.exp 1+B)^(3/4 : ℝ))

theorem lowerMaskedFourth_log_bounds {B : ℝ} (hB : 2 ≤ B) :
    0 < Real.log (Real.exp 1+B) ∧ Real.log (Real.exp 1+B) ≤ maskedFourthLog B ∧
      maskedFourthLog B ≤ 3*Real.log (Real.exp 1+B) := by
  have hB0 : 0 < B := by linarith
  have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he0 := Real.exp_pos (1 : ℝ)
  have harg : Real.exp 1+B ≤ 2*B^2 := by nlinarith [sq_nonneg (B-2)]
  have hlogpos : 0 < Real.log (Real.exp 1+B) := Real.log_pos (by linarith)
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ Real.exp 1+B by linarith)
  have hlogB := Real.log_le_log hB0 (show B ≤ Real.exp 1+B by linarith)
  refine ⟨hlogpos,Real.log_le_log (by linarith : 0 < Real.exp 1+B) harg,?_⟩
  unfold maskedFourthLog
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos hB0 2).ne',Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem lowerMaskedFourthRawWidth_eq (n : ℕ) {ell B g : ℝ} (hell : 0 < ell) :
    lowerMaskedFourthRawWidth n ell B g = maskedFourthScale n ell B*g/Real.sqrt ell := by
  have he := (Real.sqrt_pos.mpr hell).ne'
  unfold lowerMaskedFourthRawWidth maskedFourthScale
  symm
  calc
    _ = (maskedFourthAmplitude n ell B*maskedFourthCount ell B*g/Real.sqrt n)*Real.sqrt ell/Real.sqrt ell := by ring
    _ = _ := mul_div_cancel_right₀ _ he

theorem lowerMaskedFourthRawWidth_fourth {n : ℕ} {ell B g : ℝ}
    (hn : 0 < n) (hell : 0 < ell) (hB : 2 ≤ B) :
    lowerMaskedFourthRawWidth n ell B g^4 = B^4*ell^3*g^4/(1024*(n : ℝ)*maskedFourthLog B^3) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : 0 < maskedFourthLog B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1
  have hs4 : (Real.sqrt ell)^4 = ell^2 := by
    calc
      _ = ((Real.sqrt ell)^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hell.le]
  rw [lowerMaskedFourthRawWidth_eq n hell,div_pow,mul_pow,maskedFourthScale_fourth hn hell hB,hs4]
  field_simp
  ring

private theorem lowerMaskedFourth_rpow_four {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    (x^a)^4 = x^(a*4) := by rw [← Real.rpow_natCast,← Real.rpow_mul hx]; norm_num

theorem lowerMaskedFourthIntrinsicRate_fourth {n : ℕ} {L B g : ℝ}
    (hL : 0 ≤ L) (hB : 2 ≤ B) :
    lowerMaskedFourthIntrinsicRate n L B g^4 =
      B^4*g^4*L^3/((n : ℝ)*Real.log (Real.exp 1+B)^3) := by
  have hlog := (lowerMaskedFourth_log_bounds hB).1.le
  unfold lowerMaskedFourthIntrinsicRate
  rw [div_pow,mul_pow,mul_pow,mul_pow,lowerMaskedFourth_rpow_four hL,
    lowerMaskedFourth_rpow_four (Nat.cast_nonneg n),lowerMaskedFourth_rpow_four hlog]
  norm_num [← Real.rpow_natCast]

theorem lowerMaskedFourthRawWidth_le_intrinsicRate {n : ℕ} {ell L B g : ℝ}
    (hn : 0 < n) (hell : 0 < ell) (hL : ell ≤ L) (hB : 2 ≤ B) (hg : 0 ≤ g) :
    lowerMaskedFourthRawWidth n ell B g ≤ lowerMaskedFourthIntrinsicRate n L B g := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogs := lowerMaskedFourth_log_bounds hB
  have hΛ : 0 < maskedFourthLog B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1
  have hRaw0 : 0 ≤ lowerMaskedFourthRawWidth n ell B g := by
    unfold lowerMaskedFourthRawWidth
    exact div_nonneg (mul_nonneg (mul_nonneg (maskedFourthAmplitude_pos hn hell hB).le
      (maskedFourthCount_pos hell hB).le) hg) (Real.sqrt_nonneg _)
  have hTarget0 : 0 ≤ lowerMaskedFourthIntrinsicRate n L B g := by
    unfold lowerMaskedFourthIntrinsicRate
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith : 0 ≤ B) hg) (Real.rpow_nonneg (hell.le.trans hL) _))
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg hlogs.1.le _))
  apply (pow_le_pow_iff_left₀ hRaw0 hTarget0 (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [lowerMaskedFourthRawWidth_fourth hn hell hB,lowerMaskedFourthIntrinsicRate_fourth (hell.le.trans hL) hB]
  have hnum := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hell.le hL 3)
    (mul_nonneg (pow_nonneg (by linarith : 0 ≤ B) 4) (pow_nonneg hg 4))
  have hden := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogs.1.le hlogs.2.1 3) hn0.le
  have hden' : (n : ℝ)*Real.log (Real.exp 1+B)^3 ≤ 1024*(n : ℝ)*maskedFourthLog B^3 :=
    hden.trans (by nlinarith [mul_nonneg hn0.le (pow_nonneg hΛ.le 3)])
  apply div_le_div₀ (mul_nonneg (mul_nonneg (pow_nonneg (by linarith : 0 ≤ B) 4) (pow_nonneg hg 4))
    (pow_nonneg (hell.le.trans hL) 3)) _ (mul_pos hn0 (pow_pos hlogs.1 3)) hden'
  convert hnum using 1 <;> ring

theorem lowerMaskedFourthRawWidth_fourth_count {n : ℕ} {ell B g : ℝ}
    (hn : 0 < n) (hell : 0 < ell) (hB : 2 ≤ B) :
    lowerMaskedFourthRawWidth n ell B g^4 =
      (B^4/16)*maskedFourthCount ell B^2*g^4*maskedFourthTheta n ell B := by
  rw [lowerMaskedFourthRawWidth_fourth hn hell hB]
  unfold maskedFourthTheta maskedFourthCount
  ring

theorem lowerMaskedFourthTheta_le_raw_fourth {n : ℕ} {ell B g c : ℝ}
    (hn : 0 < n) (hell : 0 < ell) (hB : 2 ≤ B) (hc : 0 < c) (hg : c ≤ g)
    (hk : 1 ≤ maskedFourthCount ell B) :
    maskedFourthTheta n ell B ≤ lowerMaskedFourthRawWidth n ell B g^4/c^4 := by
  have hB4 : (16 : ℝ) ≤ B^4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hB 4
    norm_num at hh
    exact hh
  have hk2 : (1 : ℝ) ≤ maskedFourthCount ell B^2 := by nlinarith
  have h1 : (1 : ℝ) ≤ (B^4/16)*maskedFourthCount ell B^2 := by
    have hh := mul_le_mul (show (1 : ℝ) ≤ B^4/16 by linarith) hk2
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ B^4/16)
    simpa only [one_mul] using hh
  have hg4 := pow_le_pow_left₀ hc.le hg 4
  have hcoef : c^4 ≤ (B^4/16)*maskedFourthCount ell B^2*g^4 := by
    exact hg4.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr h1) (pow_nonneg (hc.le.trans hg) 4)])
  apply (le_div_iff₀ (pow_pos hc 4)).mpr
  rw [lowerMaskedFourthRawWidth_fourth_count hn hell hB]
  have hh := mul_le_mul_of_nonneg_right hcoef (maskedFourthTheta_pos hn hell hB).le
  convert hh using 1 <;> ring

theorem lowerMaskedFourthIntrinsicRate_le_raw {n : ℕ} {ell L B G g : ℝ}
    (hn : 0 < n) (hell : 0 < ell) (hL0 : 0 ≤ L) (hL : L ≤ 3*ell)
    (hB : 2 ≤ B) (hG0 : 0 ≤ G) (hg : 0 ≤ g) (hG : G ≤ 2*g) :
    lowerMaskedFourthIntrinsicRate n L B G ≤ 128*lowerMaskedFourthRawWidth n ell B g := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlogs := lowerMaskedFourth_log_bounds hB
  have hΛ : 0 < maskedFourthLog B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hB).1
  have hRaw0 : 0 ≤ lowerMaskedFourthRawWidth n ell B g := by
    unfold lowerMaskedFourthRawWidth
    exact div_nonneg (mul_nonneg (mul_nonneg (maskedFourthAmplitude_pos hn hell hB).le
      (maskedFourthCount_pos hell hB).le) hg) (Real.sqrt_nonneg _)
  have hTarget0 : 0 ≤ lowerMaskedFourthIntrinsicRate n L B G := by
    unfold lowerMaskedFourthIntrinsicRate
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith : 0 ≤ B) hG0) (Real.rpow_nonneg hL0 _))
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.rpow_nonneg hlogs.1.le _))
  apply (pow_le_pow_iff_left₀ hTarget0 (mul_nonneg (by norm_num) hRaw0) (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [mul_pow,lowerMaskedFourthIntrinsicRate_fourth hL0 hB,lowerMaskedFourthRawWidth_fourth hn hell hB]
  have hG4 := pow_le_pow_left₀ hG0 hG 4
  have hL3 := pow_le_pow_left₀ hL0 hL 3
  have hnum := mul_le_mul_of_nonneg_left
    (mul_le_mul hG4 hL3 (pow_nonneg hL0 3) (pow_nonneg (mul_nonneg (by norm_num) hg) 4))
    (pow_nonneg (by linarith : 0 ≤ B) 4)
  have hloglower : maskedFourthLog B/3 ≤ Real.log (Real.exp 1+B) := by linarith [hlogs.2.2]
  have hden := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (div_nonneg hΛ.le (by norm_num)) hloglower 3) hn0.le
  have hfirst := div_le_div₀
    (mul_nonneg (pow_nonneg (by linarith : 0 ≤ B) 4)
      (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hg) 4) (pow_nonneg (mul_nonneg (by norm_num) hell.le) 3)))
    hnum (mul_pos hn0 (pow_pos (div_pos hΛ (by norm_num)) 3)) hden
  have hfirst' : B^4*G^4*L^3/((n : ℝ)*Real.log (Real.exp 1+B)^3) ≤
      B^4*((2*g)^4*(3*ell)^3)/((n : ℝ)*(maskedFourthLog B/3)^3) := by
    convert hfirst using 1 <;> ring
  apply hfirst'.trans
  have hlast : (11664 : ℝ)*(B^4*ell^3*g^4/((n : ℝ)*maskedFourthLog B^3)) ≤
      262144*(B^4*ell^3*g^4/((n : ℝ)*maskedFourthLog B^3)) :=
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  convert hlast using 1 <;> ring

end
end RectangleCLTArxivV1
