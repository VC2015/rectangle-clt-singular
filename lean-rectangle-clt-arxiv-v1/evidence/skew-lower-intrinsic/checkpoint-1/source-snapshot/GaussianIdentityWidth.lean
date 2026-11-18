import RectangleCLTArxivV1.LowerWidthCalibration
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMomentsConvergence

/-! Exact normalization of the actual Gaussian infinity-norm mean for
independent standard coordinates. The lower mean uses the checked printed
probability/uniform-integrability proof; the upper mean optimizes the
actual Gaussian exponential moment at sqrt(2log(2p)). -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion Filter
open scoped BigOperators Topology
noncomputable section

theorem gaussianMaximumMean_le_sqrt_two_log {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A*A.transpose) j j=1) :
    gaussianMaximumMean A ≤ Real.sqrt (2*Real.log (2*(p:ℝ))) := by
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 < Real.log (2*(p:ℝ)) := Real.log_pos (by linarith)
  let t := Real.sqrt (2*Real.log (2*(p:ℝ)))
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t^2=2*Real.log (2*(p:ℝ)) := Real.sq_sqrt (by positivity)
  have hj := exp_integral_le_integral_exp ((gaussianLaw_integrable_norm A).const_mul t)
    (gaussianLaw_integrable_exp_norm hp A t)
  rw [integral_const_mul] at hj
  have hb := hj.trans (gaussianLaw_integral_exp_norm_le hp A hdiag t)
  have he : (2*(p:ℝ))*Real.exp (t^2/2)=Real.exp (t^2) := by
    have hh : 2*Real.log (2*(p:ℝ))/2=Real.log (2*(p:ℝ)) := by ring
    calc
      _ = Real.exp (Real.log (2*(p:ℝ)))*Real.exp (Real.log (2*(p:ℝ))) := by
        rw [ht2,hh,Real.exp_log (by positivity : 0 < 2*(p:ℝ))]
      _ = _ := by
        rw [←Real.exp_add,ht2]
        congr 1
        ring
  rw [he] at hb
  have hc := Real.exp_le_exp.mp hb
  change gaussianMaximumMean A ≤ t
  change t*gaussianMaximumMean A≤t^2 at hc
  nlinarith

theorem independentAbsGaussianMean_ge_positiveMean {p : ℕ} (hp : 1 ≤ p) :
    RectangleCLT.Companion.SplitV4.gaussianMaximumMean p ≤ independentAbsGaussianMean p := by
  letI : NeZero p := ⟨by omega⟩
  rw [RectangleCLT.Companion.SplitV4.gaussianMaximumMean_eq_integral]
  unfold independentAbsGaussianMean
  apply integral_mono (RectangleCLT.Companion.SplitV4.integrable_finiteGaussianMaximum p)
    (standardGaussian_integrable_norm p)
  intro g
  exact (le_abs_self _).trans (RectangleCLT.Companion.SplitV4.abs_finiteMaximum_le_norm g)

theorem sqrt_two_log_two_mul_div_tendsto :
    Tendsto (fun p : ℕ => Real.sqrt (2*Real.log (2*(p:ℝ)))/
      Real.sqrt (2*Real.log (p:ℝ))) atTop (𝓝 1) := by
  have hlog : Tendsto (fun p : ℕ => Real.log (p:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := ((tendsto_const_nhds (x := Real.log 2)).div_atTop hlog).add_const (1:ℝ)
  have hh' : Tendsto (fun p : ℕ => Real.log 2/Real.log (p:ℝ)+1) atTop (𝓝 1) := by
    simpa only [zero_add] using hh
  have hroot := Real.continuous_sqrt.tendsto 1 |>.comp hh'
  simp only [zero_add,Real.sqrt_one] at hroot
  apply hroot.congr'
  filter_upwards [eventually_ge_atTop 2] with p hp
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0<p by omega)
  have hLp : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hp)
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast (show 1≤p by omega)
  have hL2 : 0 ≤ 2*Real.log (2*(p:ℝ)) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  change Real.sqrt (Real.log 2/Real.log (p:ℝ)+1) =
    Real.sqrt (2*Real.log (2*(p:ℝ)))/Real.sqrt (2*Real.log (p:ℝ))
  rw [←Real.sqrt_div hL2]
  congr 1
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hp0.ne']
  field_simp [hLp.ne']
  ring

theorem tendsto_independentAbsGaussianMean_div_sqrt_two_log :
    Tendsto (fun p : ℕ => independentAbsGaussianMean p/Real.sqrt (2*Real.log (p:ℝ)))
      atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    RectangleCLT.Companion.SplitV4.Printed.tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability
    sqrt_two_log_two_mul_div_tendsto
  · filter_upwards [eventually_ge_atTop 1] with p hp
    exact div_le_div_of_nonneg_right (independentAbsGaussianMean_ge_positiveMean hp) (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with p hp
    have hh := gaussianMaximumMean_le_sqrt_two_log hp (1:Matrix (Fin p) (Fin p) ℝ) (by intro j; simp)
    rw [←independentAbsGaussianMean_eq] at hh
    exact div_le_div_of_nonneg_right hh (Real.sqrt_nonneg _)

end
end RectangleCLTArxivV1
