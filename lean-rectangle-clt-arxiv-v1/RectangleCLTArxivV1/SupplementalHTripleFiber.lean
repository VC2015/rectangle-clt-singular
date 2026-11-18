import RectangleCLTArxivV1.SupplementalHSphericalPolar
import RectangleCLTArxivV1.SupplementalHFourthTubes
import Mathlib.Analysis.SpecialFunctions.Integrals

/-! Actual three-dimensional conical normal fibers with the fourth
radius weight. The angular factor is the actual spherical cone area. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set Metric RectangleCLT.Companion.SignedSurface
open RectangleCLT.Companion.SplitV4
open scoped InnerProductSpace
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem supplementalH_cone_ball_volume (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E=3) (C : Set E) (hC : MeasurableSet C)
    (hcone : ∀ t : ℝ, 0<t → ∀ x : E, t • x∈C ↔ x∈C)
    (ε : ℝ) (hε : 0<ε) :
    μ.real (C∩ball (0:E) ε)=(ε^3/3)*μ.toSphere.real (supplementalHSphericalSection C) := by
  have hD : MeasurableSet (C∩ball (0:E) ε) := hC.inter measurableSet_ball
  have hΩ : MeasurableSet (supplementalHSphericalSection C) :=
    hC.preimage continuous_subtype_val.measurable
  rw [←integral_indicator_one hD,supplementalH_integral_polar μ]
  change (∫ z : sphere (0:E) 1 × Ioi (0:ℝ),
    (C∩ball (0:E) ε).indicator (fun _ => (1:ℝ)) (z.2.1 • z.1.1)
    ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)))=_
  have he (z : sphere (0:E) 1 × Ioi (0:ℝ)) :
      (C∩ball (0:E) ε).indicator (fun _ => (1:ℝ)) (z.2.1 • z.1.1)=
      (Iio ε).indicator (fun _ => (1:ℝ)) z.2.1*
        (supplementalHSphericalSection C).indicator (fun _ => (1:ℝ)) z.1 := by
    have hn : ‖z.1.1‖=1 := mem_sphere_zero_iff_norm.mp z.1.2
    have hm : z.2.1 • z.1.1∈C∩ball (0:E) ε ↔ z.1∈supplementalHSphericalSection C ∧ z.2.1<ε := by
      simp only [mem_inter_iff,mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (show 0<z.2.1 from z.2.2),hn,mul_one,hcone _ z.2.2,supplementalHSphericalSection,mem_setOf_eq]
    by_cases ha : z.1∈supplementalHSphericalSection C <;> by_cases hb : z.2.1<ε <;>
      simp [hm,ha,hb]
  rw [integral_congr_ae (ae_of_all _ he)]
  change (∫ z : sphere (0:E) 1 × Ioi (0:ℝ),
    (Iio ε).indicator (fun _ => (1:ℝ)) z.2.1 •
      (supplementalHSphericalSection C).indicator (fun _ => (1:ℝ)) z.1
      ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E-1)))=_
  rw [supplementalH_integral_angular_radial,hdim]
  norm_num only [Nat.reduceSub]
  have hr : (∫ r : ℝ in Ioi 0, r^2*(Iio ε).indicator (fun _ => (1:ℝ)) r)=ε^3/3 := by
    have hi (r : ℝ) : r^2*(Iio ε).indicator (fun _ => (1:ℝ)) r=(Iio ε).indicator (fun r => r^2) r := by
      by_cases h : r<ε <;> simp [h]
    simp_rw [hi]
    rw [setIntegral_indicator measurableSet_Iio]
    have hs : Ioi (0:ℝ)∩Iio ε=Ioo 0 ε := by ext r; simp [and_comm]
    rw [hs,←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hε.le,
      integral_pow]
    norm_num
  rw [hr,integral_indicator hΩ,integral_const,measureReal_restrict_apply_univ]
  simp only [smul_eq_mul,mul_one]


/-- A genuine three-dimensional conical normal fiber with the actual
fourth radius weight retains radius times spherical cone area. -/
theorem adaptive_cone_gaussian_integral_lower_fourth
    (μ : Measure E) [μ.IsAddHaarMeasure] (hdim : Module.finrank ℝ E=3)
    (C : Set E) (hC : MeasurableSet C)
    (hcone : ∀ t : ℝ, 0<t → ∀ y : E, t • y∈C ↔ y∈C)
    (L : E →ₗᵢ[ℝ] F) (R : F → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖) (x : F) (z : E) (hz : ‖z‖≤R x) :
    Real.exp (-(3:ℝ)/2)*gaussianKernel z*
      (R x*μ.toSphere.real (supplementalHSphericalSection C)/3072)≤
      ∫ y in C∩ball (0:E) (1/(4*R x)),
        R (x+L y)^4*gaussianKernel (z+y) ∂μ := by
  have hRx : 0<R x := zero_lt_one.trans_le (hR x)
  let ε : ℝ := 1/(4*R x)
  let D := C∩ball (0:E) ε
  have hε : 0<ε := by dsimp only [ε]; positivity
  have hε1 : ε≤1 := by
    dsimp only [ε]
    apply (div_le_iff₀ (by positivity : 0<4*R x)).mpr
    linarith [hR x]
  have hRε : R x*ε≤1 := by
    dsimp only [ε]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0<4*R x)).mpr
    linarith
  have hcont : Continuous (fun y : E => R (x+L y)^4*gaussianKernel (z+y)) :=
    ((hRm.comp (by fun_prop)).pow 4).mul (by fun_prop)
  have hD : D⊆closedBall (0:E) ε := fun _ h => ball_subset_closedBall h.2
  have hi : IntegrableOn (fun y : E => R (x+L y)^4*gaussianKernel (z+y)) D μ :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall (0:E) ε)).mono_set hD
  have hconst : IntegrableOn (fun _ : E => (R x/2)^4*Real.exp (-(3:ℝ)/2)*gaussianKernel z) D μ :=
    ((continuous_const : Continuous (fun _ : E => (R x/2)^4*Real.exp (-(3:ℝ)/2)*gaussianKernel z)).continuousOn.integrableOn_compact (isCompact_closedBall (0:E) ε)).mono_set hD
  have hm : (∫ _ in D, (R x/2)^4*Real.exp (-(3:ℝ)/2)*gaussianKernel z ∂μ)≤
      ∫ y in D, R (x+L y)^4*gaussianKernel (z+y) ∂μ := by
    apply integral_mono_ae hconst hi
    filter_upwards [ae_restrict_mem (hC.inter measurableSet_ball)] with y hy
    have hn : ‖y‖≤ε := (mem_ball_zero_iff.mp hy.2).le
    have hinner : ⟪z,y⟫_ℝ≤1 := by
      calc
        _ ≤ |⟪z,y⟫_ℝ| := le_abs_self _
        _ ≤ ‖z‖*‖y‖ := abs_real_inner_le_norm _ _
        _ ≤ R x*ε := mul_le_mul hz hn (norm_nonneg _) hRx.le
        _ ≤ 1 := hRε
    have hk := gaussianKernel_shift_lower z y hinner (hn.trans hε1)
    have hL : ‖L y‖≤ε := by simpa using hn
    have hrad := adaptive_radius_at_endpoint_lower R hR hRadd x (L y) hL
    calc
      _ = (R x/2)^4*(Real.exp (-(3:ℝ)/2)*gaussianKernel z) := by ring
      _ ≤ R (x+L y)^4*gaussianKernel (z+y) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hrad 4) hk
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
          (pow_nonneg (zero_le_one.trans (hR _)) 4)
  rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at hm
  change μ.real (C∩ball (0:E) ε)*((R x/2)^4*Real.exp (-(3:ℝ)/2)*gaussianKernel z)≤_ at hm
  rw [supplementalH_cone_ball_volume μ hdim C hC hcone ε hε] at hm
  convert hm using 1
  dsimp only [ε]
  field_simp [hRx.ne']
  ring


/-- The actual spherical balance vector is paid for by the genuine
fourth-weight conical normal fiber, without counting its boundary edges. -/
theorem adaptive_cone_spherical_vector_fourth_bound
    (μ : Measure E) [μ.IsAddHaarMeasure] (hdim : Module.finrank ℝ E=3)
    (C : Set E) (hC : MeasurableSet C)
    (hcone : ∀ t : ℝ, 0<t → ∀ y : E, t • y∈C ↔ y∈C)
    (L : E →ₗᵢ[ℝ] F) (R : F → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖) (x : F) (z : E) (hz : ‖z‖≤R x) :
    abs (⟪z,(2:ℝ) • ∫ ω in supplementalHSphericalSection C, ω.1 ∂μ.toSphere⟫_ℝ)*gaussianKernel z≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ y in C∩ball (0:E) (1/(4*R x)),
        R (x+L y)^4*gaussianKernel (z+y) ∂μ) := by
  have harea : 0≤μ.toSphere.real (supplementalHSphericalSection C) := ENNReal.toReal_nonneg
  have hM := supplementalH_spherical_vectorIntegral_norm_le μ (supplementalHSphericalSection C)
  have hcoef : abs (⟪z,(2:ℝ) • ∫ ω in supplementalHSphericalSection C, ω.1 ∂μ.toSphere⟫_ℝ)≤
      2*R x*μ.toSphere.real (supplementalHSphericalSection C) := by
    have hh := abs_real_inner_le_norm z ((2:ℝ) • ∫ ω in supplementalHSphericalSection C, ω.1 ∂μ.toSphere)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
    exact hh.trans ((mul_le_mul hz (mul_le_mul_of_nonneg_left hM (by norm_num))
      (by positivity) (zero_le_one.trans (hR x))).trans_eq (by ring))
  have hf := adaptive_cone_gaussian_integral_lower_fourth μ hdim C hC hcone L R hRm hR hRadd x z hz
  have hexp : Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2)=1 := by
    rw [←Real.exp_add]
    norm_num
  calc
    _ ≤ (2*R x*μ.toSphere.real (supplementalHSphericalSection C))*gaussianKernel z :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = (6144*Real.exp ((3:ℝ)/2))*(Real.exp (-(3:ℝ)/2)*gaussianKernel z*
        (R x*μ.toSphere.real (supplementalHSphericalSection C)/3072)) := by
      calc
        _ = 2*(Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2))*R x*
            μ.toSphere.real (supplementalHSphericalSection C)*gaussianKernel z := by rw [hexp]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

end
end RectangleCLTArxivV1
