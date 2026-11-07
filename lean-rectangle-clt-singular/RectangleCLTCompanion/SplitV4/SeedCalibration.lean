import RectangleCLT.Interpolation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp

/-!
# Scalar identities for the current Appendix B seeded interpolation

The calibrated amplitude and retention probability are exactly the existing
`thinningScale` and `thinningProbability`. This module verifies their match to
the current manuscript and proves the signed-density moments and fourth-order
remainder kernel in Lemma B.1. The density below may be negative; it is not
asserted to be a probability density. These identities alone do not prove the
Bernoulli--Gaussian differentiation or the threshold estimate of Lemma B.5.
-/

open MeasureTheory
open scoped Interval

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- The scalar `eta` in Appendix B for calibrated thinning. -/
def calibratedEta (t : ℝ) : ℝ := (1 - t) / (1 + t)

/-- Appendix B's affine signed density. No positivity is imposed. -/
def signedDensity (eta s : ℝ) : ℝ := 2 * (1 + eta - (1 + 2 * eta) * s)

/-- Appendix B's generic same-copy fourth-order remainder kernel. -/
def seededFourthKernel (gamma eta s : ℝ) : ℝ :=
  gamma ^ 2 / 6 * (1 - s) ^ 2 * (eta - 1 + (1 + 2 * eta) * s)

theorem calibrated_retention_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    thinningProbability t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨thinningProbability_nonneg ht.2, thinningProbability_le_one ht.1⟩

theorem calibrated_covariance {t : ℝ} (ht : 0 ≤ t) :
    thinningProbability t * thinningScale t ^ 2 = 1 - t :=
  thinning_covariance ht

theorem calibrated_third_moment {t : ℝ} (ht : 0 ≤ t) :
    thinningProbability t * thinningScale t ^ 3 = 1 - t ^ 2 :=
  thinning_third_moment ht

/-- This derivative is the coefficient of the signed aggregate cubic tensor. -/
theorem calibrated_cubic_coefficient {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => thinningProbability u * thinningScale u ^ 3 / 6)
      (-t / 3) t :=
  hasDerivAt_thinning_third_coefficient ht

theorem signedDensity_mass (eta : ℝ) :
    (∫ s in (0 : ℝ)..1, signedDensity eta s) = 1 := by
  let F : ℝ → ℝ := fun s => 2 * (1 + eta) * s - (1 + 2 * eta) * s ^ 2
  have hd (s : ℝ) : HasDerivAt F (signedDensity eta s) s := by
    convert ((hasDerivAt_id s).const_mul (2 * (1 + eta))).sub
      (((hasDerivAt_id s).pow 2).const_mul (1 + 2 * eta)) using 1 <;>
      dsimp [F, signedDensity] <;> ring
  have hc : Continuous (signedDensity eta) := by
    unfold signedDensity
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  convert hi using 1
  dsimp [F]
  ring

theorem signedDensity_first_moment (eta : ℝ) :
    (∫ s in (0 : ℝ)..1, s * signedDensity eta s) = (1 - eta) / 3 := by
  let F : ℝ → ℝ := fun s => (1 + eta) * s ^ 2 -
    (2 / 3 : ℝ) * (1 + 2 * eta) * s ^ 3
  have hd (s : ℝ) : HasDerivAt F (s * signedDensity eta s) s := by
    convert (((hasDerivAt_id s).pow 2).const_mul (1 + eta)).sub
      (((hasDerivAt_id s).pow 3).const_mul ((2 / 3 : ℝ) * (1 + 2 * eta)))
      using 1 <;> dsimp [F, signedDensity] <;> ring
  have hc : Continuous (fun s => s * signedDensity eta s) := by
    unfold signedDensity
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  convert hi using 1
  dsimp [F]
  ring

/-- The signed Hessian expansion gives precisely the manuscript's kernel. -/
theorem seededFourthKernel_eq_integral (gamma eta s : ℝ) :
    -(gamma ^ 2 / 2) *
      (∫ v in s..1, (v - s) * signedDensity eta v) =
        seededFourthKernel gamma eta s := by
  let F : ℝ → ℝ := fun v =>
    (1 + eta + (1 + 2 * eta) * s) * v ^ 2 -
      2 * s * (1 + eta) * v - (2 / 3 : ℝ) * (1 + 2 * eta) * v ^ 3
  have hd (v : ℝ) : HasDerivAt F ((v - s) * signedDensity eta v) v := by
    convert ((((hasDerivAt_id v).pow 2).const_mul
      (1 + eta + (1 + 2 * eta) * s)).sub
        ((hasDerivAt_id v).const_mul (2 * s * (1 + eta)))).sub
      (((hasDerivAt_id v).pow 3).const_mul ((2 / 3 : ℝ) * (1 + 2 * eta)))
      using 1 <;> dsimp [F, signedDensity] <;> ring
  have hc : Continuous (fun v => (v - s) * signedDensity eta v) := by
    unfold signedDensity
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    (hc.intervalIntegrable s 1)]
  dsimp [F, seededFourthKernel]
  ring

theorem calibrated_fourth_kernel {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    seededFourthKernel (thinningScale t) (calibratedEta t) s =
      (1 + t) / 6 * (1 - s) ^ 2 * ((3 - t) * s - 2 * t) := by
  have hne : 1 + t ≠ 0 := by linarith
  unfold seededFourthKernel thinningScale calibratedEta
  field_simp [hne]
  ring

theorem calibrated_cubic_kernel {t : ℝ} (ht : 0 ≤ t) :
    (1 - t) / 6 * (1 - calibratedEta t) = t * (1 - t) / (3 * (1 + t)) := by
  have hne : 1 + t ≠ 0 := by linarith
  unfold calibratedEta
  field_simp [hne]
  ring

/-- Both independent-copy remainder coefficients have their actual factors. -/
theorem calibrated_independent_copy_kernel {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    thinningProbability t * thinningScale t ^ 2 * (1 - s) / 2 =
      (1 - t) / 2 * (1 - s) := by
  rw [calibrated_covariance ht]
  ring

/-- Bernoulli differentiation and amplitude differentiation give the
signed Hessian density, with its actual sign. -/
theorem calibrated_signed_hessian_coefficient {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    (t - 3) / (1 + t) ^ 3 * thinningScale t ^ 2 * (1 - s) +
      thinningProbability t * thinningScale t =
        -signedDensity (calibratedEta t) s / 2 := by
  have hne : 1 + t ≠ 0 := by linarith
  unfold thinningScale thinningProbability signedDensity calibratedEta
  field_simp [hne]
  ring

/-- Restoring the common cubic evaluation point supplies the cubic kernel
with an independent copy; its sign is retained before taking any bound. -/
theorem calibrated_cubic_restoration_coefficient {t : ℝ} (ht : 0 ≤ t) :
    -(-t / 3) * thinningProbability t * thinningScale t =
      (1 - t) / 6 * (1 - calibratedEta t) := by
  have hne : 1 + t ≠ 0 := by linarith
  unfold thinningProbability thinningScale calibratedEta
  field_simp [hne]
  ring

/-- The initial Slepian path has different scalar kernels from calibrated
thinning, even though both preserve the covariance cancellation. -/
theorem slepian_fourth_kernel (gamma s : ℝ) :
    seededFourthKernel gamma (-1 / 2) s = -(gamma ^ 2) / 4 * (1 - s) ^ 2 := by
  unfold seededFourthKernel
  ring

theorem calibrated_fourth_kernel_abs_le_one {t s : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    |seededFourthKernel (thinningScale t) (calibratedEta t) s| ≤ 1 := by
  rw [calibrated_fourth_kernel ht.1]
  have hsq : (1 - s) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hs.1 (show 0 ≤ 1 - s by linarith)]
  have hscalar0 : 0 ≤ (1 + t) / 6 := by linarith [ht.1]
  have hfac0 : 0 ≤ (1 + t) / 6 * (1 - s) ^ 2 :=
    mul_nonneg hscalar0 (sq_nonneg _)
  have hfac1 : (1 + t) / 6 * (1 - s) ^ 2 ≤ 1 / 3 := by
    calc
      _ ≤ (1 + t) / 6 * 1 := mul_le_mul_of_nonneg_left hsq hscalar0
      _ ≤ 1 / 3 := by linarith [ht.2]
  have hbracket : |(3 - t) * s - 2 * t| ≤ 3 := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_nonneg (show 0 ≤ 3 - t by linarith) hs.1]
    · nlinarith [mul_nonneg (show 0 ≤ 3 - t by linarith)
        (show 0 ≤ 1 - s by linarith)]
  rw [abs_mul, abs_of_nonneg hfac0]
  calc
    _ ≤ ((1 + t) / 6 * (1 - s) ^ 2) * 3 :=
      mul_le_mul_of_nonneg_left hbracket hfac0
    _ ≤ 1 := by linarith [hfac1]

/-- A uniform absolute-integral bound for the same-copy calibrated kernel.
This bound concerns only the scalar kernel, not its tensor contraction. -/
theorem calibrated_fourth_kernel_abs_integral_le_one {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1,
      |seededFourthKernel (thinningScale t) (calibratedEta t) s|) ≤ 1 := by
  have hc : Continuous (fun s =>
      |seededFourthKernel (thinningScale t) (calibratedEta t) s|) := by
    unfold seededFourthKernel
    fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (show (0 : ℝ) ≤ 1 by norm_num)
    (hc.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
    (fun s hs => calibrated_fourth_kernel_abs_le_one ht hs)
  simpa using hi

/-- The two signed moment identities do not entail positivity of the density. -/
theorem signedDensity_can_be_negative : signedDensity (1 : ℝ) 1 = -2 := by
  norm_num [signedDensity]

end
end RectangleCLT.Companion.SplitV4
