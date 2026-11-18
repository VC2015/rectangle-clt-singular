import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Lattice

/- Scalar time integrals in the proof of the dimension-logarithm cap.
The crossing times are retained explicitly, as in the printed proof. -/
noncomputable section
open MeasureTheory Set

namespace RectangleCLTArxivV1

theorem cap_inv_sqrt_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun v : ℝ => 1 / Real.sqrt v) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab
  exact continuousOn_const.div Real.continuous_sqrt.continuousOn
    (fun v hv => (Real.sqrt_pos.2 (ha.trans_le hv.1)).ne')

theorem cap_inv_mul_sqrt_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun v : ℝ => 1 / (v * Real.sqrt v)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab
  exact continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
    (fun v hv => mul_ne_zero (ha.trans_le hv.1).ne'
      (Real.sqrt_pos.2 (ha.trans_le hv.1)).ne')

theorem cap_integral_inv_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ v in a..b, 1 / Real.sqrt v) = 2 * (Real.sqrt b - Real.sqrt a) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v : ℝ => 2 * Real.sqrt v)
    (f' := fun v : ℝ => 1 / Real.sqrt v) (a := a) (b := b) ?_
    (cap_inv_sqrt_intervalIntegrable ha hab)
  · simpa only [mul_sub] using h
  · intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    have hvpos : 0 < v := ha.trans_le hv'.1
    convert (Real.hasDerivAt_sqrt hvpos.ne').const_mul 2 using 1;
      field_simp

theorem cap_integral_inv_mul_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ v in a..b, 1 / (v * Real.sqrt v)) =
      2 / Real.sqrt a - 2 / Real.sqrt b := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v : ℝ => -2 / Real.sqrt v)
    (f' := fun v : ℝ => 1 / (v * Real.sqrt v)) (a := a) (b := b) ?_
    (cap_inv_mul_sqrt_intervalIntegrable ha hab)
  · convert h using 1; ring
  · intro v hv
    have hv' : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using hv
    have hvpos : 0 < v := ha.trans_le hv'.1
    have hs : Real.sqrt v ≠ 0 := (Real.sqrt_pos.2 hvpos).ne'
    convert (hasDerivAt_const v (-2 : ℝ)).div (Real.hasDerivAt_sqrt hvpos.ne') hs using 1
    field_simp
    nlinarith [Real.sq_sqrt hvpos.le]

theorem cap_const_inv_continuousOn {a b : ℝ} (ha : 0 < a) (A : ℝ) :
    ContinuousOn (fun v : ℝ => A / v) (Icc a b) :=
  continuousOn_const.div continuousOn_id (fun _ hv => (ha.trans_le hv.1).ne')

theorem cap_const_inv_sqrt_continuousOn {a b : ℝ} (ha : 0 < a) (A : ℝ) :
    ContinuousOn (fun v : ℝ => A / Real.sqrt v) (Icc a b) :=
  continuousOn_const.div Real.continuous_sqrt.continuousOn
    (fun _ hv => (Real.sqrt_pos.2 (ha.trans_le hv.1)).ne')

theorem cap_const_inv_mul_sqrt_continuousOn {a b : ℝ} (ha : 0 < a) (A : ℝ) :
    ContinuousOn (fun v : ℝ => A / (v * Real.sqrt v)) (Icc a b) :=
  continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
    (fun _ hv => mul_ne_zero (ha.trans_le hv.1).ne'
      (Real.sqrt_pos.2 (ha.trans_le hv.1)).ne')

theorem cap_integral_const_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (A : ℝ) :
    (∫ v in a..b, A / v) = A * Real.log (b / a) := by
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
  simp only [div_eq_mul_inv]

theorem cap_integral_const_inv_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (A : ℝ) :
    (∫ v in a..b, A / Real.sqrt v) = A * (2 * (Real.sqrt b - Real.sqrt a)) := by
  calc
    _ = ∫ v in a..b, A * (1 / Real.sqrt v) := by congr 1; funext v; ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, cap_integral_inv_sqrt ha hab]

theorem cap_integral_const_inv_mul_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (A : ℝ) :
    (∫ v in a..b, A / (v * Real.sqrt v)) =
      A * (2 / Real.sqrt a - 2 / Real.sqrt b) := by
  calc
    _ = ∫ v in a..b, A * (1 / (v * Real.sqrt v)) := by congr 1; funext v; ring
    _ = _ := by rw [intervalIntegral.integral_const_mul, cap_integral_inv_mul_sqrt ha hab]

/-- Literal first crossing estimate, including crossings outside the interval. -/
theorem cap_integral_single_minimum {a b A S : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hA : 0 < A) (hS : 0 < S) :
    (∫ v in a..b, min (A / v) (S / (v * Real.sqrt v))) ≤
      2 * A * (1 + max (Real.log (S / (A * Real.sqrt a))) 0) := by
  let c := (S / A) ^ 2
  have hc : 0 < c := sq_pos_of_pos (div_pos hS hA)
  have hsc : Real.sqrt c = S / A := Real.sqrt_sq (div_nonneg hS.le hA.le)
  have hs : S = A * Real.sqrt c := by rw [hsc]; field_simp
  have hb : 0 < b := ha.trans_le hab
  have hlog : Real.log (c / a) = 2 * Real.log (S / (A * Real.sqrt a)) := by
    rw [Real.log_div hc.ne' ha.ne', Real.log_div hS.ne' (mul_pos hA (Real.sqrt_pos.2 ha)).ne',
      Real.log_mul hA.ne' (Real.sqrt_pos.2 ha).ne', Real.log_sqrt ha.le]
    dsimp [c]
    rw [Real.log_pow, Real.log_div hS.ne' hA.ne']
    ring
  let f := fun v : ℝ => min (A / v) (S / (v * Real.sqrt v))
  have hi {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : IntervalIntegrable f volume x y :=
    ((cap_const_inv_continuousOn hx A).inf
      (cap_const_inv_mul_sqrt_continuousOn hx S)).intervalIntegrable_of_Icc hxy
  have hfirst {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
      (∫ v in x..y, f v) ≤ A * Real.log (y / x) := by
    apply (intervalIntegral.integral_mono_on hxy (hi hx hxy)
      ((cap_const_inv_continuousOn hx A).intervalIntegrable_of_Icc hxy)
      (fun _ _ => min_le_left _ _)).trans_eq
    exact cap_integral_const_inv hx (hx.trans_le hxy) A
  have hsecond {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
      (∫ v in x..y, f v) ≤ 2 * S / Real.sqrt x := by
    have h := (intervalIntegral.integral_mono_on hxy (hi hx hxy)
      ((cap_const_inv_mul_sqrt_continuousOn hx S).intervalIntegrable_of_Icc hxy)
      (fun _ _ => min_le_right _ _)).trans_eq (cap_integral_const_inv_mul_sqrt hx hxy S)
    have hn : 0 ≤ S * (2 / Real.sqrt y) := by positivity
    apply h.trans
    calc
      S * (2 / Real.sqrt x - 2 / Real.sqrt y) =
          2 * S / Real.sqrt x - S * (2 / Real.sqrt y) := by ring
      _ ≤ 2 * S / Real.sqrt x := sub_le_self _ hn
  have hmax : Real.log (S / (A * Real.sqrt a)) ≤ max (Real.log (S / (A * Real.sqrt a))) 0 := le_max_left _ _
  have hmax0 : 0 ≤ max (Real.log (S / (A * Real.sqrt a))) 0 := le_max_right _ _
  by_cases hca : c ≤ a
  · have hSa : S ≤ A * Real.sqrt a := by
      rw [hs]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hca) hA.le
    have hquot : S / Real.sqrt a ≤ A := (div_le_iff₀ (Real.sqrt_pos.2 ha)).2 hSa
    apply (hsecond ha hab).trans
    calc
      2 * S / Real.sqrt a = 2 * (S / Real.sqrt a) := by ring
      _ ≤ 2 * A := mul_le_mul_of_nonneg_left hquot (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg hA.le hmax0]
  · have hac : a ≤ c := (lt_of_not_ge hca).le
    by_cases hbc : b ≤ c
    · have hl := Real.log_le_log (div_pos hb ha) (div_le_div_of_nonneg_right hbc ha.le)
      have hle := (hfirst ha hab).trans (mul_le_mul_of_nonneg_left hl hA.le)
      rw [hlog] at hle
      exact hle.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hA.le])
    · have hcb : c ≤ b := (lt_of_not_ge hbc).le
      have heq := intervalIntegral.integral_add_adjacent_intervals (hi ha hac) (hi hc hcb)
      have htail : 2 * S / Real.sqrt c = 2 * A := by
        rw [hs]
        field_simp
        ring
      have hle := add_le_add (hfirst ha hac) (hsecond hc hcb)
      rw [heq, htail, hlog] at hle
      exact hle.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hA.le])

/-- Literal second crossing estimate, before bounding the upper endpoint. -/
theorem cap_integral_pair_minimum_crossing {a b A B : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hA : 0 < A) (hB : 0 < B) :
    (∫ v in a..b, min (A / v) (B / Real.sqrt v)) ≤
      2 * A + A * max (Real.log (b / (A / B) ^ 2)) 0 := by
  let c := (A / B) ^ 2
  have hc : 0 < c := sq_pos_of_pos (div_pos hA hB)
  have hsc : Real.sqrt c = A / B := Real.sqrt_sq (div_nonneg hA.le hB.le)
  have hs : B * Real.sqrt c = A := by rw [hsc]; field_simp
  have hb : 0 < b := ha.trans_le hab
  let f := fun v : ℝ => min (A / v) (B / Real.sqrt v)
  have hi {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : IntervalIntegrable f volume x y :=
    ((cap_const_inv_continuousOn hx A).inf
      (cap_const_inv_sqrt_continuousOn hx B)).intervalIntegrable_of_Icc hxy
  have hfirst {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
      (∫ v in x..y, f v) ≤ A * Real.log (y / x) := by
    apply (intervalIntegral.integral_mono_on hxy (hi hx hxy)
      ((cap_const_inv_continuousOn hx A).intervalIntegrable_of_Icc hxy)
      (fun _ _ => min_le_left _ _)).trans_eq
    exact cap_integral_const_inv hx (hx.trans_le hxy) A
  have hsecond {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
      (∫ v in x..y, f v) ≤ 2 * B * Real.sqrt y := by
    have h := (intervalIntegral.integral_mono_on hxy (hi hx hxy)
      ((cap_const_inv_sqrt_continuousOn hx B).intervalIntegrable_of_Icc hxy)
      (fun _ _ => min_le_right _ _)).trans_eq (cap_integral_const_inv_sqrt hx hxy B)
    exact h.trans (by nlinarith [Real.sqrt_nonneg x])
  have hmax : Real.log (b / c) ≤ max (Real.log (b / c)) 0 := le_max_left _ _
  have hmax0 : 0 ≤ max (Real.log (b / c)) 0 := le_max_right _ _
  change (∫ v in a..b, f v) ≤ 2 * A + A * max (Real.log (b / c)) 0
  by_cases hca : c ≤ a
  · have hl := Real.log_le_log (div_pos hb ha)
      (div_le_div_of_nonneg_left hb.le hc hca)
    have hle := (hfirst ha hab).trans (mul_le_mul_of_nonneg_left hl hA.le)
    exact hle.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hA.le])
  · have hac : a ≤ c := (lt_of_not_ge hca).le
    by_cases hbc : b ≤ c
    · have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbc) hB.le
      rw [hs] at hm
      exact (hsecond ha hab).trans (by nlinarith [mul_nonneg hA.le hmax0])
    · have hcb : c ≤ b := (lt_of_not_ge hbc).le
      have heq := intervalIntegral.integral_add_adjacent_intervals (hi ha hac) (hi hc hcb)
      have hle := add_le_add (hsecond ha hac) (hfirst hc hcb)
      rw [heq] at hle
      have hs' : 2 * B * Real.sqrt c = 2 * A := by nlinarith only [hs]
      rw [hs'] at hle
      exact hle.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hA.le])

/-- Since the seeded time interval ends below5/4, only log₊(B/A) remains. -/
theorem cap_integral_pair_minimum {a b A B : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 5 / 4) (hA : 0 < A) (hB : 0 < B) :
    (∫ v in a..b, min (A / v) (B / Real.sqrt v)) ≤
      4 * A * (1 + max (Real.log (B / A)) 0) := by
  have hbpos : 0 < b := ha.trans_le hab
  have hlog : Real.log (b / (A / B) ^ 2) = Real.log b + 2 * Real.log (B / A) := by
    rw [Real.log_div hbpos.ne' (pow_ne_zero 2 (div_pos hA hB).ne'), Real.log_pow,
      Real.log_div hA.ne' hB.ne', Real.log_div hB.ne' hA.ne']
    ring
  have hlogb : Real.log b ≤ 1 := (Real.log_le_sub_one_of_pos hbpos).trans (by linarith)
  have hmax : Real.log (B / A) ≤ max (Real.log (B / A)) 0 := le_max_left _ _
  have hmax0 : 0 ≤ max (Real.log (B / A)) 0 := le_max_right _ _
  have hbound : max (Real.log (b / (A / B) ^ 2)) 0 ≤ 1 + 2 * max (Real.log (B / A)) 0 := by
    apply max_le
    · rw [hlog]
      linarith
    · linarith
  have h := cap_integral_pair_minimum_crossing ha hab hA hB
  apply h.trans
  nlinarith [mul_le_mul_of_nonneg_left hbound hA.le, mul_nonneg hA.le hmax0]

/-- The seed removes the bandwidth from the first crossing ratio. -/
theorem cap_seed_single_ratio {δ κ L h m r : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hL : 0 < L) (hh : 0 < h) :
    (m * r * δ ^ 2) / ((δ ^ 2 * κ * L / h) * Real.sqrt (L * h ^ 2)) =
      m * r / (κ * L * Real.sqrt L) := by
  rw [Real.sqrt_mul hL.le, Real.sqrt_sq hh.le]
  field_simp
  ring

theorem cap_seed_pair_ratio {δ κ L h m r : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) (hL : 0 < L) (hh : 0 < h) :
    (m ^ 2 * Real.sqrt r * δ ^ 2 / h) / (δ ^ 2 * κ * L / h) =
      m ^ 2 * Real.sqrt r / (κ * L) := by
  field_simp
  ring

/-- Rank and face-count factors in the single crossing cost only a dimension logarithm. -/
theorem cap_single_ratio_log_le {P r κ L : ℝ}
    (hP : 1 ≤ P) (hr : 1 ≤ r) (hrP : r ≤ P) (hκ : 1 ≤ κ)
    (hL : 1 ≤ L) (hlog : Real.log P ≤ L) :
    max (Real.log ((2 * P * r) / (κ * L * Real.sqrt L))) 0 ≤ 4 * L := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hsqrt : 1 ≤ Real.sqrt L := (Real.one_le_sqrt).2 hL
  have hκL : 1 ≤ κ * L := by nlinarith [mul_nonneg (sub_nonneg.2 hκ) (sub_nonneg.2 hL)]
  have hd : 1 ≤ κ * L * Real.sqrt L := by
    nlinarith [mul_nonneg (sub_nonneg.2 hκL) (sub_nonneg.2 hsqrt)]
  have hnum : 0 ≤ 2 * P * r := by positivity
  have hdiv : (2 * P * r) / (κ * L * Real.sqrt L) ≤ 2 * P * r := by
    apply (div_le_iff₀ (by positivity : 0 < κ * L * Real.sqrt L)).2
    nlinarith [mul_nonneg hnum (sub_nonneg.2 hd)]
  have hn : 2 * P * r ≤ 2 * P ^ 2 := by nlinarith
  have hl := Real.log_le_log (by positivity : 0 < (2 * P * r) / (κ * L * Real.sqrt L))
    (hdiv.trans hn)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hPpos.ne'), Real.log_pow] at hl
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
  exact max_le (by linarith) (by linarith)

theorem cap_pair_ratio_log_le {P r κ L : ℝ}
    (hP : 1 ≤ P) (hr : 1 ≤ r) (hrP : r ≤ P) (hκ : 1 ≤ κ)
    (hL : 1 ≤ L) (hlog : Real.log P ≤ L) :
    max (Real.log (((2 * P) ^ 2 * Real.sqrt r) / (κ * L))) 0 ≤ 6 * L := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hd : 1 ≤ κ * L := by nlinarith [mul_nonneg (sub_nonneg.2 hκ) (sub_nonneg.2 hL)]
  have hsqrt : Real.sqrt r ≤ P := by
    apply (Real.sqrt_le_iff).2
    exact ⟨hPpos.le, by nlinarith⟩
  have hnum : 0 ≤ (2 * P) ^ 2 * Real.sqrt r := by positivity
  have hdiv : ((2 * P) ^ 2 * Real.sqrt r) / (κ * L) ≤ (2 * P) ^ 2 * Real.sqrt r := by
    apply (div_le_iff₀ (by positivity : 0 < κ * L)).2
    nlinarith [mul_nonneg hnum (sub_nonneg.2 hd)]
  have hn : (2 * P) ^ 2 * Real.sqrt r ≤ 4 * P ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (sq_nonneg (2 * P))]
  have hl := Real.log_le_log (by positivity : 0 < ((2 * P) ^ 2 * Real.sqrt r) / (κ * L))
    (hdiv.trans hn)
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (pow_ne_zero 3 hPpos.ne'), Real.log_pow] at hl
  have hfour : Real.log (4 : ℝ) ≤ 3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4) using 1; norm_num
  exact max_le (by linarith) (by linarith)

/-- Integrate the sum of the two actual crossing majorants. -/
theorem cap_integrated_remainder_dimension_bound {ε A S B C L : ℝ} {R : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hA : 0 < A) (hS : 0 < S) (hB : 0 < B)
    (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hlogS : max (Real.log (S / (A * Real.sqrt ε))) 0 ≤ 4 * L)
    (hlogB : max (Real.log (B / A)) 0 ≤ 6 * L)
    (hR : IntervalIntegrable R volume ε (1 + ε))
    (hpoint : ∀ v ∈ Ioo ε (1 + ε), |R v| ≤
      C * (min (A / v) (S / (v * Real.sqrt v)) + min (A / v) (B / Real.sqrt v))) :
    (∫ v in ε..1 + ε, |R v|) ≤ 38 * C * A * L := by
  have hab : ε ≤ 1 + ε := by linarith
  have hiS := ((cap_const_inv_continuousOn hε A).inf
    (cap_const_inv_mul_sqrt_continuousOn hε S)).intervalIntegrable_of_Icc (μ := volume) hab
  have hiB := ((cap_const_inv_continuousOn hε A).inf
    (cap_const_inv_sqrt_continuousOn hε B)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi := (hiS.add hiB).const_mul C
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hab hR.abs hi hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hiS hiB] at h
  have hs := cap_integral_single_minimum hε hab hA hS
  have hb := cap_integral_pair_minimum hε hab (by linarith : 1 + ε ≤ 5 / 4) hA hB
  have hsum := add_le_add hs hb
  have hsum' : (∫ v in ε..1 + ε, min (A / v) (S / (v * Real.sqrt v))) +
      (∫ v in ε..1 + ε, min (A / v) (B / Real.sqrt v)) ≤ 38 * A * L := by
    nlinarith [mul_le_mul_of_nonneg_left hlogS hA.le,
      mul_le_mul_of_nonneg_left hlogB hA.le]
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hsum' hC])

theorem cap_integrated_remainder_direct_bound {ε A C : ℝ} {R : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hR : IntervalIntegrable R volume ε (1 + ε))
    (hpoint : ∀ v ∈ Ioo ε (1 + ε), |R v| ≤ C * A / v) :
    (∫ v in ε..1 + ε, |R v|) ≤ C * A * (1 + Real.log (1 / ε)) := by
  have hab : ε ≤ 1 + ε := by linarith
  have hb : 0 < 1 + ε := by linarith
  have hi := (cap_const_inv_continuousOn hε (C * A)).intervalIntegrable_of_Icc (μ := volume) hab
  have h := (intervalIntegral.integral_mono_on_of_le_Ioo hab hR.abs hi hpoint).trans_eq
    (cap_integral_const_inv hε hb (C * A))
  have hlog : Real.log ((1 + ε) / ε) = Real.log (1 + ε) + Real.log (1 / ε) := by
    rw [Real.log_div hb.ne' hε.ne', Real.log_div one_ne_zero hε.ne', Real.log_one]
    ring
  have hl : Real.log (1 + ε) ≤ 1 := (Real.log_le_sub_one_of_pos hb).trans (by linarith)
  rw [hlog] at h
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hl (mul_nonneg hC hA)])

/-- The two independently integrated estimates give the printed minimum. -/
theorem cap_integrated_remainder_min_bound {ε A S B C L : ℝ} {R : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hA : 0 < A) (hS : 0 < S) (hB : 0 < B)
    (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hlogS : max (Real.log (S / (A * Real.sqrt ε))) 0 ≤ 4 * L)
    (hlogB : max (Real.log (B / A)) 0 ≤ 6 * L)
    (hR : IntervalIntegrable R volume ε (1 + ε))
    (hpoint : ∀ v ∈ Ioo ε (1 + ε), |R v| ≤
      C * (min (A / v) (S / (v * Real.sqrt v)) + min (A / v) (B / Real.sqrt v)))
    (hdirect : ∀ v ∈ Ioo ε (1 + ε), |R v| ≤ C * A / v) :
    (∫ v in ε..1 + ε, |R v|) ≤
      38 * C * A * min (1 + Real.log (1 / ε)) L := by
  have hdim := cap_integrated_remainder_dimension_bound hε hεsmall hA hS hB hC hL hlogS hlogB hR hpoint
  have hdir := cap_integrated_remainder_direct_bound hε (by linarith : ε ≤ 1) hA.le hC hR hdirect
  have hdiv : 1 ≤ 1 / ε := (le_div_iff₀ hε).2 (by linarith)
  have hD : 0 ≤ 1 + Real.log (1 / ε) := by linarith [Real.log_nonneg hdiv]
  have hCA : 0 ≤ 38 * C * A := by positivity
  rw [mul_min_of_nonneg _ _ hCA]
  apply le_min
  · exact hdir.trans (by nlinarith [mul_nonneg (mul_nonneg hC hA.le) hD])
  · exact hdim

end RectangleCLTArxivV1
