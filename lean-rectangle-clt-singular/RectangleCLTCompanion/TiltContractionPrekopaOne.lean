import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
One-dimensional Prékopa--Leindler on a compact interval.  The monotone
transport is constructed from the actual interval integrals of the two
densities; no transport or covariance inequality is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace RectangleCLT.Companion

private theorem geometric_jacobian_bound {u v t : ℝ}
    (hu : 0 < u) (hv : 0 < v) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    u ≤ (u ^ (1 - t) * v ^ t) * ((1 - t) + t * (u / v)) := by
  have ham := Real.geom_mean_le_arith_mean2_weighted
    (sub_nonneg.mpr ht₁) ht₀ (by norm_num : (0 : ℝ) ≤ 1)
    (div_nonneg hu.le hv.le) (by ring : (1 - t) + t = 1)
  simp only [Real.one_rpow, one_mul, mul_one] at ham
  have heq : (u ^ (1 - t) * v ^ t) * (u / v) ^ t = u := by
    calc
      _ = u ^ (1 - t) * (v * (u / v)) ^ t := by
        rw [Real.mul_rpow hv.le (div_nonneg hu.le hv.le)]
        ring
      _ = u ^ (1 - t) * u ^ t := by rw [mul_div_cancel₀ u hv.ne']
      _ = u ^ ((1 - t) + t) := (Real.rpow_add hu _ _).symm
      _ = u := by ring_nf; rw [Real.rpow_one]
  calc
    u = (u ^ (1 - t) * v ^ t) * (u / v) ^ t := heq.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left ham
      (mul_nonneg (Real.rpow_nonneg hu.le _) (Real.rpow_nonneg hv.le _))

/-- The normalized compact-interval form. Strict positivity is global so
the interval primitives have globally injective derivatives and their
ordinary inverse functions give the required local transport. -/
theorem prekopa_leindler_interval_normalized
    {f g h : ℝ → ℝ} {a b t : ℝ}
    (hab : a < b) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hf₀ : ∀ x, 0 < f x) (hg₀ : ∀ x, 0 < g x) (hh₀ : ∀ x, 0 ≤ h x)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hf₁ : (∫ x in a..b, f x) = 1) (hg₁ : (∫ x in a..b, g x) = 1)
    (hgeom : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    1 ≤ ∫ x in a..b, h x := by
  let F : ℝ → ℝ := fun x => ∫ z in a..x, f z
  let G : ℝ → ℝ := fun x => ∫ z in a..x, g z
  have hFd (x : ℝ) : HasStrictDerivAt F (f x) x := hf.integral_hasStrictDerivAt a x
  have hGd (x : ℝ) : HasStrictDerivAt G (g x) x := hg.integral_hasStrictDerivAt a x
  have hFm : StrictMono F := strictMono_of_hasDerivAt_pos
    (fun x => (hFd x).hasDerivAt) hf₀
  have hGm : StrictMono G := strictMono_of_hasDerivAt_pos
    (fun x => (hGd x).hasDerivAt) hg₀
  have hFa : F a = 0 := by simp [F]
  have hGa : G a = 0 := by simp [G]
  have hFb : F b = 1 := hf₁
  have hGb : G b = 1 := hg₁
  let T : ℝ → ℝ := fun x => Function.invFun G (F x)
  have hGT (x : ℝ) (hx : x ∈ Ioo a b) : T x ∈ Ioo a b ∧ G (T x) = F x := by
    have hFx : F x ∈ Ioo 0 1 := by
      constructor
      · rw [← hFa]; exact hFm hx.1
      · rw [← hFb]; exact hFm hx.2
    obtain ⟨y, hy, hyx⟩ := intermediate_value_Icc hab.le
      ((continuous_iff_continuousAt.mpr (fun y => (hGd y).continuousAt)).continuousOn)
      (show F x ∈ Icc (G a) (G b) by rw [hGa, hGb]; exact Ioo_subset_Icc_self hFx)
    have hTy : T x = y := by
      dsimp [T]
      rw [← hyx, Function.leftInverse_invFun hGm.injective y]
    rw [hTy]
    refine ⟨⟨?_, ?_⟩, hyx⟩
    · exact lt_of_le_of_ne hy.1 (fun hya => by
        have he : G a = F x := by rw [hya]; exact hyx
        rw [hGa] at he
        linarith [hFx.1])
    · exact lt_of_le_of_ne hy.2 (fun hyb => by
        have he : G b = F x := by rw [← hyb]; exact hyx
        rw [hGb] at he
        linarith [hFx.2])
  have hTd (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt T (f x / g (T x)) x := by
    have hinv := (hGd (T x)).to_local_left_inverse (hg₀ (T x)).ne'
      (Filter.Eventually.of_forall (Function.leftInverse_invFun hGm.injective))
    rw [(hGT x hx).2] at hinv
    simpa only [T, div_eq_mul_inv, mul_comm] using
      hinv.hasDerivAt.comp x (hFd x).hasDerivAt
  let S : ℝ → ℝ := fun x => (1 - t) * x + t * T x
  let J : ℝ → ℝ := fun x => (1 - t) + t * (f x / g (T x))
  have hSd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt S (J x) x := by
    simpa only [S, J, mul_one] using
      ((hasDerivAt_id x).const_mul (1 - t)).add ((hTd x hx).const_mul t)
  have hJpos (x : ℝ) : 0 < J x := by
    have ham := Real.geom_mean_le_arith_mean2_weighted
      (sub_nonneg.mpr ht₁) ht₀ (by norm_num : (0 : ℝ) ≤ 1)
      (div_nonneg (hf₀ x).le (hg₀ (T x)).le) (by ring : (1 - t) + t = 1)
    simp only [Real.one_rpow, one_mul, mul_one] at ham
    exact (Real.rpow_pos_of_pos (div_pos (hf₀ x) (hg₀ (T x))) t).trans_le ham
  have hSm : StrictMonoOn S (Ioo a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo a b)
      (fun x hx => (hSd x hx).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ioo] at hx
    rw [(hSd x hx).deriv]
    exact hJpos x
  have hSrange : S '' Ioo a b ⊆ Ioo a b := by
    rintro y ⟨x, hx, rfl⟩
    exact convex_Ioo a b hx (hGT x hx).1 (sub_nonneg.mpr ht₁) ht₀ (by ring)
  have hJbound (x : ℝ) (hx : x ∈ Ioo a b) : f x ≤ J x * h (S x) := by
    calc
      f x ≤ (f x ^ (1 - t) * g (T x) ^ t) * J x :=
        geometric_jacobian_bound (hf₀ x) (hg₀ (T x)) ht₀ ht₁
      _ ≤ h (S x) * J x := mul_le_mul_of_nonneg_right
        (hgeom x (Ioo_subset_Icc_self hx) (T x) (Ioo_subset_Icc_self (hGT x hx).1))
        (hJpos x).le
      _ = _ := mul_comm _ _
  have hCoV := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (hSd x hx).hasDerivWithinAt) hSm.injOn h
  have hJint : IntegrableOn (fun x => J x * h (S x)) (Ioo a b) := by
    have hi : IntegrableOn h (S '' Ioo a b) :=
      hh.integrableOn_Icc.mono_set (hSrange.trans Ioo_subset_Icc_self)
    have hp := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := volume) measurableSet_Ioo
      (fun x hx => (hSd x hx).hasFDerivAt.hasFDerivWithinAt) hSm.injOn h).mp hi
    simpa only [ContinuousLinearMap.det_one_smulRight, abs_of_pos (hJpos _),
      smul_eq_mul] using hp
  have hleft : (∫ x in Ioo a b, f x) ≤ ∫ x in S '' Ioo a b, h x := by
    rw [hCoV]
    apply integral_mono_ae (hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    · simpa only [abs_of_pos (hJpos _), smul_eq_mul] using hJint
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simpa only [abs_of_pos (hJpos x), smul_eq_mul] using hJbound x hx
  have hright : (∫ x in S '' Ioo a b, h x) ≤ ∫ x in Icc a b, h x :=
    setIntegral_mono_set (hh.integrableOn_Icc)
      (Filter.Eventually.of_forall hh₀)
      (Filter.Eventually.of_forall (hSrange.trans Ioo_subset_Icc_self))
  have hfi : (∫ x in Ioo a b, f x) = ∫ x in a..b, f x := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
  have hhi : (∫ x in Icc a b, h x) = ∫ x in a..b, h x := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
  rw [hfi, hf₁] at hleft
  exact hleft.trans (hright.trans_eq hhi)

/-- One-dimensional Prékopa--Leindler for actual compact interval
integrals. The two source densities are strictly positive and continuous;
the target is continuous and nonnegative. The interpolation parameter
includes both endpoints. -/
theorem prekopa_leindler_interval
    {f g h : ℝ → ℝ} {a b t : ℝ}
    (hab : a < b) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (hf₀ : ∀ x, 0 < f x) (hg₀ : ∀ x, 0 < g x) (hh₀ : ∀ x, 0 ≤ h x)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hgeom : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫ x in a..b, f x) ^ (1 - t) * (∫ x in a..b, g x) ^ t ≤
      ∫ x in a..b, h x := by
  let M := ∫ x in a..b, f x
  let N := ∫ x in a..b, g x
  let K := M ^ (1 - t) * N ^ t
  have hM : 0 < M := intervalIntegral.intervalIntegral_pos_of_pos
    (hf.intervalIntegrable a b) hf₀ hab
  have hN : 0 < N := intervalIntegral.intervalIntegral_pos_of_pos
    (hg.intervalIntegrable a b) hg₀ hab
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos hM _) (Real.rpow_pos_of_pos hN _)
  have hp := prekopa_leindler_interval_normalized (f := fun x => f x / M)
    (g := fun x => g x / N) (h := fun x => h x / K) hab
    (hf.div_const M) (hg.div_const N) (hh.div_const K)
    (fun x => div_pos (hf₀ x) hM) (fun x => div_pos (hg₀ x) hN)
    (fun x => div_nonneg (hh₀ x) hK.le) ht₀ ht₁
    (by rw [intervalIntegral.integral_div]; exact div_self hM.ne')
    (by rw [intervalIntegral.integral_div]; exact div_self hN.ne')
    (by
      intro x hx y hy
      rw [Real.div_rpow (hf₀ x).le hM.le, Real.div_rpow (hg₀ y).le hN.le,
        div_mul_div_comm]
      exact div_le_div_of_nonneg_right (hgeom x hx y hy) hK.le)
  rw [intervalIntegral.integral_div] at hp
  simpa only [one_mul] using (le_div_iff₀ hK).mp hp

end RectangleCLT.Companion
