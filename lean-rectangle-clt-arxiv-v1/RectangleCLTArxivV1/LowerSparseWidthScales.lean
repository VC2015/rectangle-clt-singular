import RectangleCLTArxivV1.LowerMaskedProfile
import RectangleCLTArxivV1.LowerDenseParameters
import RectangleCLTCompanion.SplitV4.SparseFamilyCalibration
import RectangleCLTCompanion.SplitV4.SparseLowerPaperRate

/-! Width-sensitive sparse scales with two independent coordinate counts. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerSparseIntrinsicK (n : ℕ) (L q B : ℝ) : ℝ := B * ((n : ℝ) / L) ^ (2 / q - 1 / 2)

def lowerSparseIntrinsicRate (n : ℕ) (L q B g : ℝ) : ℝ :=
  B * g * L ^ (1 - 1 / q) / ((n : ℝ) ^ (1 / 2 - 1 / q) *
    Real.log (Real.exp 1 + lowerSparseIntrinsicK n L q B) ^ (1 - 1 / q))

def lowerSparseRawWidth (n : ℕ) (ell q B g : ℝ) : ℝ :=
  sparseLowerAmplitude n ell q B * sparseLowerCount n ell q B * g / Real.sqrt n

def lowerSparseCoordinateWidth (n : ℕ) (ell B g : ℝ) : ℝ :=
  sparseLowerCoordinateRate n ell B * g / Real.sqrt ell

def lowerSparseLogSlack (q : ℝ) : ℝ := |2 / q - 1 / 2| * Real.log 3

theorem lowerSparseKhat_factor {n : ℕ} {ell L q B : ℝ} (hell : 0 < ell) (hL : 0 < L) :
    sparseLowerKhat n ell q B = lowerSparseIntrinsicK n L q B * (L / ell) ^ (2 / q - 1 / 2) := by
  unfold sparseLowerKhat lowerSparseIntrinsicK
  rw [mul_assoc, ← Real.mul_rpow (div_nonneg (Nat.cast_nonneg n) hL.le) (div_nonneg hL.le hell.le)]
  congr 2
  field_simp

theorem lowerSparse_logKhat_sub_bound {n : ℕ} {ell L q B : ℝ}
    (hn : 0 < n) (hell : 0 < ell) (hB : 0 < B) (hellL : ell ≤ L) (hLell : L ≤ 3 * ell) :
    |Real.log (sparseLowerKhat n ell q B) - Real.log (lowerSparseIntrinsicK n L q B)| ≤
      lowerSparseLogSlack q := by
  have hL : 0 < L := hell.trans_le hellL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < lowerSparseIntrinsicK n L q B := by
    unfold lowerSparseIntrinsicK
    positivity
  have hratio : 0 < L / ell := div_pos hL hell
  have hlog0 : 0 ≤ Real.log (L / ell) := Real.log_nonneg ((one_le_div hell).mpr hellL)
  have hlog3 : Real.log (L / ell) ≤ Real.log 3 :=
    Real.log_le_log hratio ((div_le_iff₀ hell).mpr hLell)
  rw [lowerSparseKhat_factor hell hL, Real.log_mul hk.ne' (Real.rpow_pos_of_pos hratio _).ne',
    Real.log_rpow hratio, add_sub_cancel_left, abs_mul, abs_of_nonneg hlog0]
  exact mul_le_mul_of_nonneg_left hlog3 (abs_nonneg _)

theorem lowerSparseRawWidth_eq (n : ℕ) {ell q B g : ℝ} (hell : 0 < ell) :
    lowerSparseRawWidth n ell q B g = sparseLowerScale n ell q B * g / Real.sqrt ell := by
  have he := (Real.sqrt_pos.mpr hell).ne'
  unfold lowerSparseRawWidth sparseLowerScale
  symm
  calc
    _ = (sparseLowerAmplitude n ell q B * sparseLowerCount n ell q B * g / Real.sqrt n) *
        Real.sqrt ell / Real.sqrt ell := by ring
    _ = _ := mul_div_cancel_right₀ _ he

theorem lowerSparseRawWidth_factor {n : ℕ} {ell q B g : ℝ}
    (hn : 0 < n) (hell : 0 < ell) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    lowerSparseRawWidth n ell q B g = B * g * ell ^ (1 - 1 / q) /
      (2 * (4 * sparseLowerLog n ell q B) ^ (1 - 1 / q) * (n : ℝ) ^ (1 / 2 - 1 / q)) := by
  have hpow : ell ^ (3 / 2 - 1 / q) = ell ^ (1 - 1 / q) * Real.sqrt ell := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hell]
    congr 1
    ring
  rw [lowerSparseRawWidth_eq n hell, sparseLowerScale_factor hn hell hK, hpow]
  have hroot := (Real.sqrt_pos.mpr hell).ne'
  calc
    _ = (B * g * ell ^ (1 - 1 / q) /
        (2 * (4 * sparseLowerLog n ell q B) ^ (1 - 1 / q) * (n : ℝ) ^ (1 / 2 - 1 / q))) *
          Real.sqrt ell / Real.sqrt ell := by ring
    _ = _ := mul_div_cancel_right₀ _ hroot

theorem lowerSparseCoordinateWidth_fourth {n : ℕ} {ell B g : ℝ} (hell : 0 < ell) (hB : 0 ≤ B) :
    lowerSparseCoordinateWidth n ell B g ^ 4 = B ^ 2 * ell ^ 3 * g ^ 4 / (n : ℝ) := by
  have hs : (Real.sqrt ell) ^ 4 = ell ^ 2 := by
    calc
      _ = ((Real.sqrt ell) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hell.le]
  unfold lowerSparseCoordinateWidth
  rw [div_pow, mul_pow, sparseLowerCoordinateRate_fourth hell.le hB, hs]
  calc
    _ = (B ^ 2 * ell ^ 3 * g ^ 4 / (n : ℝ)) * ell ^ 2 / ell ^ 2 := by ring
    _ = _ := mul_div_cancel_right₀ _ (pow_ne_zero 2 hell.ne')

theorem lowerSparseRawWidth_pos {n : ℕ} {ell q B g : ℝ}
    (hn : 0 < n) (hell : 0 < ell) (hB : 0 < B) (hg : 0 < g)
    (hK : 2 ≤ sparseLowerKhat n ell q B) : 0 < lowerSparseRawWidth n ell q B g := by
  unfold lowerSparseRawWidth
  exact div_pos (mul_pos (mul_pos (sparseLowerAmplitude_pos hn hell hB hK)
    (sparseLowerCount_pos hell hK)) hg) (Real.sqrt_pos.mpr (by exact_mod_cast hn))

theorem lowerSparse_cube_div_le_coordinateWidth_fourth {n : ℕ} {ell B g c : ℝ}
    (hell : 0 < ell) (hB : 2 ≤ B) (hc : 0 < c) (hg : c ≤ g) :
    ell ^ 3 / (n : ℝ) ≤ lowerSparseCoordinateWidth n ell B g ^ 4 / (4 * c ^ 4) := by
  have hB2 : (4 : ℝ) ≤ B ^ 2 := by nlinarith
  have hg4 := pow_le_pow_left₀ hc.le hg 4
  have hcoef : 4 * c ^ 4 ≤ B ^ 2 * g ^ 4 :=
    mul_le_mul hB2 hg4 (pow_nonneg hc.le 4) (sq_nonneg B)
  apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos hc 4))).mpr
  rw [lowerSparseCoordinateWidth_fourth hell (by linarith : 0 ≤ B)]
  have hh := mul_le_mul_of_nonneg_right hcoef
    (div_nonneg (pow_nonneg hell.le 3) (Nat.cast_nonneg n))
  convert hh using 1 <;> ring

theorem lowerSparseRawWidth_le_intrinsicRate {n : ℕ} {ell L q B g : ℝ}
    (hq : 2 < q) (hn : 0 < n) (hell : 0 < ell) (hellL : ell ≤ L)
    (hB : 0 < B) (hg : 0 ≤ g) (hK : 2 ≤ sparseLowerKhat n ell q B)
    (hlog : Real.log (Real.exp 1 + lowerSparseIntrinsicK n L q B) ≤ sparseLowerLog n ell q B) :
    lowerSparseRawWidth n ell q B g ≤ lowerSparseIntrinsicRate n L q B g := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < L := hell.trans_le hellL
  have hq0 : 0 < q := by linarith
  have hb : 0 ≤ 1 - 1 / q := by
    have hh : 1 / q < 1 := (div_lt_one hq0).mpr (by linarith)
    linarith
  have hk : 0 < lowerSparseIntrinsicK n L q B := by unfold lowerSparseIntrinsicK; positivity
  have hp : 0 < Real.log (Real.exp 1 + lowerSparseIntrinsicK n L q B) :=
    Real.log_pos (by have he := Real.add_one_le_exp (1 : ℝ); linarith)
  have hΛ : 0 < sparseLowerLog n ell q B := hp.trans_le hlog
  have hnum := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hell.le hellL hb) (mul_nonneg hB.le hg)
  have hpow := Real.rpow_le_rpow hp.le (show Real.log (Real.exp 1 + lowerSparseIntrinsicK n L q B) ≤
      4 * sparseLowerLog n ell q B by linarith) hb
  have hden : (n : ℝ) ^ (1 / 2 - 1 / q) *
      Real.log (Real.exp 1 + lowerSparseIntrinsicK n L q B) ^ (1 - 1 / q) ≤
      2 * (4 * sparseLowerLog n ell q B) ^ (1 - 1 / q) * (n : ℝ) ^ (1 / 2 - 1 / q) := by
    have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hn0.le (1 / 2 - 1 / q))
    have hh0 : 0 ≤ (n : ℝ) ^ (1 / 2 - 1 / q) * (4 * sparseLowerLog n ell q B) ^ (1 - 1 / q) := by positivity
    nlinarith only [hh,hh0]
  rw [lowerSparseRawWidth_factor hn hell hK]
  unfold lowerSparseIntrinsicRate
  exact div_le_div₀ (mul_nonneg (mul_nonneg hB.le hg) (Real.rpow_nonneg hL.le _)) hnum (by positivity) hden

theorem lowerSparseIntrinsicRate_le_raw {n : ℕ} {ell L q B G g : ℝ}
    (hq : 2 < q) (hn : 0 < n) (hell : 0 < ell) (hL0 : 0 < L) (hL : L ≤ 3 * ell)
    (hB : 0 < B) (hG : G ≤ 2 * g) (hg : 0 ≤ g) (hK : 2 ≤ sparseLowerKhat n ell q B)
    (hlog : sparseLowerLog n ell q B ≤ 3 * Real.log (Real.exp 1 + lowerSparseIntrinsicK n L q B)) :
    lowerSparseIntrinsicRate n L q B G ≤ 256 * lowerSparseRawWidth n ell q B g := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 < q := by linarith
  have hb : 0 ≤ 1 - 1 / q := by
    have hh : 1 / q < 1 := (div_lt_one hq0).mpr (by linarith)
    linarith
  have hb1 : 1 - 1 / q ≤ 1 := by
    have hh : (0 : ℝ) ≤ 1 / q := by positivity
    linarith
  have hk : 0 < lowerSparseIntrinsicK n L q B := by unfold lowerSparseIntrinsicK; positivity
  let P := Real.log (Real.exp 1 + lowerSparseIntrinsicK n L q B)
  let N := (n : ℝ) ^ (1 / 2 - 1 / q)
  let U := B * g * ell ^ (1 - 1 / q)
  let A := 2 * (4 * sparseLowerLog n ell q B) ^ (1 - 1 / q) * N
  let Q := N * P ^ (1 - 1 / q)
  have hp : 0 < P := Real.log_pos (by have he := Real.add_one_le_exp (1 : ℝ); linarith)
  have hΛ : 0 < sparseLowerLog n ell q B :=
    lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1
  have hA : 0 < A := by dsimp [A,N]; positivity
  have hQ : 0 < Q := by dsimp [Q,N]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have h3 : (3 : ℝ) ^ (1 - 1 / q) ≤ 3 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hb1
  have hLPow : L ^ (1 - 1 / q) ≤ 3 * ell ^ (1 - 1 / q) := by
    have hh := Real.rpow_le_rpow hL0.le hL hb
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hell.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hell.le _))
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hG hB.le) hLPow
    (Real.rpow_nonneg hL0.le _) (mul_nonneg hB.le (mul_nonneg (by norm_num) hg))
  have htarget : lowerSparseIntrinsicRate n L q B G ≤ 6 * (U / Q) := by
    have hh := div_le_div_of_nonneg_right hprod hQ.le
    convert hh using 1
    dsimp [lowerSparseIntrinsicRate,U,Q,P,N]
    ring
  have h12 : (12 : ℝ) ^ (1 - 1 / q) ≤ 12 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 12) hb1
  have hPow : (4 * sparseLowerLog n ell q B) ^ (1 - 1 / q) ≤ 12 * P ^ (1 - 1 / q) := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 4 * sparseLowerLog n ell q B)
      (show 4 * sparseLowerLog n ell q B ≤ 12 * P by dsimp [P]; linarith only [hlog]) hb
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) hp.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right h12 (Real.rpow_nonneg hp.le _))
  have hden : A ≤ 24 * Q := by
    have hh := mul_le_mul_of_nonneg_left hPow (show 0 ≤ 2 * N by dsimp [N]; positivity)
    dsimp only [A,Q]
    nlinarith only [hh]
  have hdiv := div_le_div_of_nonneg_left hU hA hden
  have hcore : U / Q ≤ 24 * (U / A) := by
    have hh := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 24)
    convert hh using 1
    ring
  have hraw : lowerSparseRawWidth n ell q B g = U / A := lowerSparseRawWidth_factor hn hell hK
  rw [hraw]
  have hnonneg : 0 ≤ U / A := div_nonneg hU hA.le
  have hh := mul_le_mul_of_nonneg_left hcore (by norm_num : (0 : ℝ) ≤ 6)
  nlinarith only [htarget,hh,hnonneg]

end
end RectangleCLTArxivV1
