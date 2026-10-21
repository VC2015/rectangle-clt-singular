import RectangleCLT.RefinedProxyStatement
import RectangleCLT.GeneralOptimization

/-! Scalar rate comparisons used when an isotropic perturbation regularizes
an arbitrary unit-diagonal covariance. No approximation estimate is assumed
or asserted in this module. -/

namespace RectangleCLT
noncomputable section

theorem le_optionalMin {x parameter candidate fallback : ℝ}
    (hfall : x ≤ fallback) (hcand : 0 < parameter → x ≤ candidate) :
    x ≤ optionalMin parameter candidate fallback := by
  unfold optionalMin
  split_ifs with hp
  · exact le_min (hcand hp) hfall
  · exact hfall

theorem mul_optionalMin {k parameter candidate fallback : ℝ} (hk : 0 ≤ k) :
    k * optionalMin parameter candidate fallback =
      optionalMin parameter (k*candidate) (k*fallback) := by
  unfold optionalMin
  split_ifs
  · exact mul_min_of_nonneg _ _ hk
  · rfl

theorem inv_rpow_le_twice_of_half {c d q : ℝ}
    (hc : 0 < c) (hd : c/2 ≤ d) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    1 / d^q ≤ 2 / c^q := by
  have hd0 : 0 < d := lt_of_lt_of_le (by linarith : 0 < c/2) hd
  have hp : c^q ≤ 2 * d^q := by
    calc
      c^q ≤ (2*d)^q := Real.rpow_le_rpow hc.le (by linarith) hq
      _ = 2^q * d^q := Real.mul_rpow (by norm_num) hd0.le
      _ ≤ 2 * d^q := mul_le_mul_of_nonneg_right
        (by simpa using (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hq1))
        (Real.rpow_nonneg hd0.le _)
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hd0 _) (Real.rpow_pos_of_pos hc _)).mpr
  simpa using hp

theorem generalThirdRate_le_nonlinear (γ L b c a₃ : ℝ) :
    generalThirdRate γ L b c a₃ ≤ γ^(1/3:ℝ)*Real.sqrt L/c^(2/3:ℝ) :=
  (optionalMin_le_fallback _ _ _).trans (optionalMin_le_fallback _ _ _)

theorem generalThirdRate_le_global {γ L b c a₃ : ℝ} (hb : 0 < b) :
    generalThirdRate γ L b c a₃ ≤ γ*L*Real.sqrt L/b^2 :=
  optionalMin_le_candidate hb _ _

theorem generalFourthRate_le_nonlinear (γ L b c a₃ a₄ : ℝ) :
    generalFourthRate γ L b c a₃ a₄ ≤ γ^(1/4:ℝ)*Real.sqrt L/c^(3/4:ℝ) :=
  (optionalMin_le_fallback _ _ _).trans (optionalMin_le_fallback _ _ _)

theorem generalFourthRate_le_global {γ L b c a₃ a₄ : ℝ} (hb : 0 < b) :
    generalFourthRate γ L b c a₃ a₄ ≤ Real.sqrt γ*L/(b*Real.sqrt c) :=
  optionalMin_le_candidate hb _ _

theorem generalThirdRate_regularized {γ L b c a₃ b' c' a₃' : ℝ}
    (hγ : 0 ≤ γ) (hL : 0 ≤ L) (hc : 0 < c)
    (hb' : 0 < b') (hb'sq : c/2 ≤ b'^2) (hc' : c/2 ≤ c')
    (hbc : b^2 ≤ c) (ha₃ : a₃ ≤ 1) :
    generalThirdRate γ L b' c' a₃' ≤ 2*generalThirdRate γ L b c a₃ := by
  have hN : 0 ≤ γ*L*Real.sqrt L := by positivity
  have hlin : generalThirdRate γ L b' c' a₃' ≤ 2*(γ*L*Real.sqrt L/c) := by
    apply (generalThirdRate_le_global hb').trans
    have hh : γ*L*Real.sqrt L/b'^2 ≤ 2*(γ*L*Real.sqrt L/c) := by
      have hinv : 1 / b'^2 ≤ 2 / c := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hb') hc).mpr
        nlinarith
      have hm := mul_le_mul_of_nonneg_left hinv hN
      convert hm using 1 <;> ring
    exact hh
  unfold generalThirdRate
  rw [mul_optionalMin (by norm_num : (0:ℝ)≤2)]
  apply le_optionalMin
  · rw [mul_optionalMin (by norm_num : (0:ℝ)≤2)]
    apply le_optionalMin
    · apply (generalThirdRate_le_nonlinear _ _ _ _ _).trans
      have h := mul_le_mul_of_nonneg_left
        (inv_rpow_le_twice_of_half hc hc' (by norm_num : (0:ℝ)≤2/3) (by norm_num))
        (show 0 ≤ γ^(1/3:ℝ)*Real.sqrt L by positivity)
      convert h using 1 <;> ring
    · intro ha
      apply hlin.trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
      exact div_le_div_of_nonneg_left hN (mul_pos hc ha) (by nlinarith)
  · intro hb
    apply hlin.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
    exact div_le_div_of_nonneg_left hN (sq_pos_of_pos hb) hbc

theorem generalFourthRate_regularized {γ L b c a₃ a₄ b' c' a₃' a₄' : ℝ}
    (hγ : 0 ≤ γ) (hL : 0 ≤ L) (hc : 0 < c)
    (hb' : 0 < b') (hglobal : c/2 ≤ b'*Real.sqrt c') (hc' : c/2 ≤ c')
    (hbc : b*Real.sqrt c ≤ c)
    (hlocal : c^(5/6:ℝ)*(a₃*a₄)^(1/3:ℝ) ≤ c) :
    generalFourthRate γ L b' c' a₃' a₄' ≤ 2*generalFourthRate γ L b c a₃ a₄ := by
  have hc'0 : 0 < c' := lt_of_lt_of_le (by linarith : 0 < c/2) hc'
  have hN : 0 ≤ Real.sqrt γ*L := by positivity
  have hlin : generalFourthRate γ L b' c' a₃' a₄' ≤ 2*(Real.sqrt γ*L/c) := by
    apply (generalFourthRate_le_global hb').trans
    have hinv : 1 / (b'*Real.sqrt c') ≤ 2 / c := by
      apply (div_le_div_iff₀ (mul_pos hb' (Real.sqrt_pos.mpr hc'0)) hc).mpr
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hinv hN
    convert hm using 1 <;> ring
  unfold generalFourthRate
  rw [mul_optionalMin (by norm_num : (0:ℝ)≤2)]
  apply le_optionalMin
  · rw [mul_optionalMin (by norm_num : (0:ℝ)≤2)]
    apply le_optionalMin
    · apply (generalFourthRate_le_nonlinear _ _ _ _ _ _).trans
      have h := mul_le_mul_of_nonneg_left
        (inv_rpow_le_twice_of_half hc hc' (by norm_num : (0:ℝ)≤3/4) (by norm_num))
        (show 0 ≤ γ^(1/4:ℝ)*Real.sqrt L by positivity)
      convert h using 1 <;> ring
    · intro ha
      apply hlin.trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
      exact div_le_div_of_nonneg_left hN
        (mul_pos (Real.rpow_pos_of_pos hc _) (Real.rpow_pos_of_pos ha _)) hlocal
  · intro hb
    apply hlin.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
    exact div_le_div_of_nonneg_left hN (mul_pos hb (Real.sqrt_pos.mpr hc)) hbc

theorem generalThirdRate_mono {γ γ' L b c a₃ : ℝ}
    (hγ : 0 ≤ γ) (hγ' : γ ≤ γ') (hL : 0 ≤ L) (hc : 0 < c) :
    generalThirdRate γ L b c a₃ ≤ generalThirdRate γ' L b c a₃ := by
  unfold generalThirdRate
  apply optionalMin_mono
  · apply optionalMin_mono
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hγ hγ' (by norm_num))
          (Real.sqrt_nonneg L)) (Real.rpow_nonneg hc.le _)
    · intro ha
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγ' hL)
          (Real.sqrt_nonneg L)) (mul_nonneg hc.le ha.le)
  · intro hb
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγ' hL)
        (Real.sqrt_nonneg L)) (sq_nonneg b)

theorem generalCoefficientRate_mono_all {δ δ' γ₃ γ₃' γ₄ γ₄' L b c a₃ a₄ : ℝ}
    (hδ : δ ≤ δ') (hγ₃ : 0 ≤ γ₃) (h3 : γ₃ ≤ γ₃')
    (hγ₄ : 0 ≤ γ₄) (h4 : γ₄ ≤ γ₄') (hL : 0 ≤ L) (hc : 0 < c) :
    generalCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ ≤
      generalCoefficientRate δ' γ₃' γ₄' L b c a₃ a₄ := by
  exact add_le_add
    (add_le_add (generalThirdRate_mono hγ₃ h3 hL hc)
      (generalFourthRate_mono hγ₄ h4 hL hc))
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hδ (Real.sqrt_nonneg L)) hc.le)

theorem regularized_global_denominator {b' c' c : ℝ}
    (hc : 0 < c) (hb' : 0 ≤ b') (hb'sq : c/2 ≤ b'^2) (hc' : c/2 ≤ c') :
    c/2 ≤ b'*Real.sqrt c' := by
  have hc2 : 0 ≤ c/2 := by positivity
  have hs : Real.sqrt (c/2) ≤ b' := (Real.sqrt_le_iff).mpr ⟨hb', hb'sq⟩
  have ht : Real.sqrt (c/2) ≤ Real.sqrt c' := Real.sqrt_le_sqrt hc'
  have hm := mul_le_mul hs ht (Real.sqrt_nonneg _) hb'
  simpa only [← sq, Real.sq_sqrt hc2] using hm

theorem proxy_global_fourth_denominator {b c : ℝ} (hc : 0 < c)
    (hb : 0 ≤ b) (hbc : b^2 ≤ c) : b*Real.sqrt c ≤ c := by
  have hs : b ≤ Real.sqrt c := (Real.le_sqrt hb hc.le).mpr hbc
  have hm := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg c)
  simpa only [← sq, Real.sq_sqrt hc.le] using hm

theorem proxy_local_fourth_denominator {c a₃ a₄ : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1)
    (ha₃ : 0 ≤ a₃) (ha₃c : a₃ ≤ c) (ha₄ : 0 ≤ a₄) (ha₄c : a₄ ≤ c) :
    c^(5/6:ℝ)*(a₃*a₄)^(1/3:ℝ) ≤ c := by
  have hp : a₃*a₄ ≤ c^2 := by nlinarith [mul_le_mul ha₃c ha₄c ha₄ hc.le]
  have hr := Real.rpow_le_rpow (mul_nonneg ha₃ ha₄) hp (by norm_num : (0:ℝ)≤1/3)
  calc
    _ ≤ c^(5/6:ℝ)*(c^2)^(1/3:ℝ) :=
      mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg hc.le _)
    _ = c^(3/2:ℝ) := by
      rw [← Real.rpow_natCast_mul hc.le]
      rw [← Real.rpow_add hc]
      norm_num
    _ ≤ c := Real.rpow_le_self_of_le_one hc.le hc1 (by norm_num)

theorem generalCoefficientRate_regularized {δ γ₃ γ₄ L b c a₃ a₄ b' c' a₃' a₄' : ℝ}
    (hδ : 0 ≤ δ) (hγ₃ : 0 ≤ γ₃) (hγ₄ : 0 ≤ γ₄) (hL : 0 ≤ L)
    (hc : 0 < c) (hc1 : c ≤ 1) (hb : 0 ≤ b) (hbc : b^2 ≤ c)
    (ha₃ : 0 ≤ a₃) (ha₃c : a₃ ≤ c) (ha₄ : 0 ≤ a₄) (ha₄c : a₄ ≤ c)
    (hb' : 0 < b') (hb'sq : c/2 ≤ b'^2) (hc' : c/2 ≤ c') :
    generalCoefficientRate δ γ₃ γ₄ L b' c' a₃' a₄' ≤
      2*generalCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ := by
  have h3 := generalThirdRate_regularized (a₃' := a₃') hγ₃ hL hc hb' hb'sq hc' hbc (ha₃c.trans hc1)
  have h4 := generalFourthRate_regularized (a₃' := a₃') (a₄' := a₄') hγ₄ hL hc hb'
    (regularized_global_denominator hc hb'.le hb'sq hc') hc'
    (proxy_global_fourth_denominator hc hb hbc)
    (proxy_local_fourth_denominator hc hc1 ha₃ ha₃c ha₄ ha₄c)
  have hc'0 : 0 < c' := lt_of_lt_of_le (by linarith : 0 < c/2) hc'
  have h0 : δ*Real.sqrt L/c' ≤ 2*(δ*Real.sqrt L/c) := by
    have hinv : 1/c' ≤ 2/c := (div_le_div_iff₀ hc'0 hc).mpr (by linarith)
    convert mul_le_mul_of_nonneg_left hinv
      (show 0 ≤ δ*Real.sqrt L by positivity) using 1 <;> ring
  unfold generalCoefficientRate
  nlinarith only [h3, h4, h0]

theorem large_discrepancy_regularization_cost {Δ L b c : ℝ}
    (hL : 0 ≤ L) (hc : 0 < c) (hc1 : c ≤ 1) (hb : 0 ≤ b)
    (hbc : b^2 ≤ c) (hΔ : c/2 ≤ Δ) :
    Real.sqrt c*L ≤ 2*(Δ*L*gaussianComparisonCoefficient b c) := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hbs : b ≤ Real.sqrt c := (Real.le_sqrt hb hc.le).mpr hbc
  have hcs : c ≤ Real.sqrt c := by
    have hsq := Real.sq_sqrt hc.le
    nlinarith [Real.sqrt_nonneg c]
  have hmax : max b c ≤ Real.sqrt c := max_le hbs hcs
  have hcoef : 1/Real.sqrt c ≤ gaussianComparisonCoefficient b c := by
    rw [gaussianComparisonCoefficient_eq_inv_max hb hc]
    exact one_div_le_one_div_of_le (lt_of_lt_of_le hc (le_max_right b c)) hmax
  have hΔ0 : 0 ≤ Δ := (by positivity : (0:ℝ)≤c/2).trans hΔ
  have hm := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hΔ0 hL)
  have hΔs : Real.sqrt c*L ≤ 2*(Δ*L/Real.sqrt c) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hs).mpr
    have hmul := mul_le_mul_of_nonneg_right hΔ hL
    nlinarith [Real.sq_sqrt hc.le]
  apply hΔs.trans
  have hm' : Δ*L/Real.sqrt c ≤ Δ*L*gaussianComparisonCoefficient b c := by
    simpa only [div_eq_mul_inv, one_mul] using hm
  exact mul_le_mul_of_nonneg_left hm' (by norm_num)

end
end RectangleCLT
