import RectangleCLTArxivV1.SupplementalHFourthTubes
import RectangleCLTArxivV1.SupplementalHSurfaceGeometry

/-! The leading angle-weighted ridge Green coefficient is controlled by
its actual fourth-radius two-dimensional normal fiber. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT.Companion.SignedSurface
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Jordan's inequality bounds the actual angle by a fixed multiple of
its chord, including both endpoint angular degeneracies. -/
theorem supplementalH_angle_le_pi_half_chord (u v : E) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    Real.arccos ⟪u,v⟫_ℝ≤(Real.pi/2)*‖u-v‖ := by
  let θ := Real.arccos ⟪u,v⟫_ℝ
  have hθ0 : 0≤θ := Real.arccos_nonneg _
  have hθπ : θ≤Real.pi := Real.arccos_le_pi _
  have hs : θ/Real.pi≤Real.sin (θ/2) := by
    simpa using Real.mul_le_sin (x := θ/2) (by positivity) (by linarith)
  have hsin : 0≤Real.sin (θ/2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by positivity,by linarith [Real.pi_pos]⟩
  have hdot : |⟪u,v⟫_ℝ|≤1 := by simpa only [hu,hv,one_mul] using abs_real_inner_le_norm u v
  have hc : Real.cos θ=⟪u,v⟫_ℝ := Real.cos_arccos (abs_le.mp hdot).1 (abs_le.mp hdot).2
  have hhalf := Real.sin_sq_eq_half_sub (θ/2)
  have harg : 2*(θ/2)=θ := by ring
  rw [harg,hc] at hhalf
  have hn := norm_sub_sq_real u v
  rw [hu,hv] at hn
  have hchord : ‖u-v‖=2*Real.sin (θ/2) :=
    (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hsin)).mp (by nlinarith)
  have hb := (div_le_iff₀ Real.pi_pos).mp hs
  rw [hchord]
  change θ≤_
  nlinarith

/-- The leading ridge coefficient in J_e is paid by an actual R4 normal
fiber, with an absolute constant and no inverse angular gap. -/
theorem adaptive_angle_ridge_fourth_bound
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖)
    (x u v z : E) (hu : ‖u‖=1) (hv : ‖v‖=1) (hp : u+v≠0) (hm : u-v≠0)
    (hz : ‖z‖≤R x) :
    abs (Real.arccos ⟪u,v⟫_ℝ*(‖z‖^2-2))*gaussianKernel z≤
      (6144*Real.pi*Real.exp ((3:ℝ)/2))*(∫ st in ridgeRectangle u v (1/(4*R x)),
        R (x+ridgeDisplacement u v st)^4*gaussianKernel (z+ridgeDisplacement u v st)
          ∂((volume : Measure ℝ).prod volume)) := by
  have hb : |⟪z,bisector u v⟫_ℝ|≤R x :=
    (abs_real_inner_le_norm _ _).trans (by rw [norm_bisector u v hp,mul_one]; exact hz)
  have hc : |⟪z,differenceDirection u v⟫_ℝ|≤R x :=
    (abs_real_inner_le_norm _ _).trans (by rw [norm_differenceDirection u v hm,mul_one]; exact hz)
  have hf := adaptive_ridge_gaussian_integral_lower_fourth R hRm hR hRadd x u v z hu hv hp hm hb hc
  have hR0 : 0≤R x := zero_le_one.trans (hR x)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hR2 : 1≤R x^2 := one_le_pow₀ (hR x)
  have hnorm : abs (‖z‖^2-2)≤3*R x^2 := by
    calc
      _ ≤ ‖z‖^2+2 := by
        have hh := abs_sub (‖z‖^2) (2:ℝ)
        simpa only [abs_of_nonneg (sq_nonneg (‖z‖ : ℝ)),abs_of_pos (by norm_num : (0:ℝ)<2)] using hh
      _ ≤ _ := by nlinarith
  have hangle := supplementalH_angle_le_pi_half_chord u v hu hv
  have hcoef : abs (Real.arccos ⟪u,v⟫_ℝ*(‖z‖^2-2))≤
      (3*Real.pi/2)*‖u-v‖*R x^2 := by
    rw [abs_mul,abs_of_nonneg (Real.arccos_nonneg _)]
    exact (mul_le_mul hangle hnorm (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hexp : Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2)=1 := by rw [←Real.exp_add]; norm_num
  calc
    _ ≤ ((3*Real.pi/2)*‖u-v‖*R x^2)*gaussianKernel z :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = (6144*Real.pi*Real.exp ((3:ℝ)/2))*(Real.exp (-(3:ℝ)/2)*gaussianKernel z*(R x^2*‖u-v‖/4096)) := by
      calc
        _ = (3*Real.pi/2)*(Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2))*‖u-v‖*R x^2*gaussianKernel z := by rw [hexp]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

end
end RectangleCLTArxivV1
