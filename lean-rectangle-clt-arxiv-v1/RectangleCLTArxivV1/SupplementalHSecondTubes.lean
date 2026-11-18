import RectangleCLTCompanion.SplitV4.AveragedThreshold
import RectangleCLTArxivV1.SupplementalHEdgeFourthBounds

/-! Actual second-radius adaptive ridge fibers for the sharp positive
edge-mass budget. The raw Gaussian rectangle proof is the archived
AveragedThreshold argument with the actual radius weight squared. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem adaptive_ridge_gaussian_integral_lower_second
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1 ≤ R x)
    (hRadd : ∀ x d, R (x + d) ≤ R x + ‖d‖)
    (x u v z : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    (hb : |⟪z, bisector u v⟫_ℝ| ≤ R x)
    (hc : |⟪z, differenceDirection u v⟫_ℝ| ≤ R x) :
    Real.exp (-(3 : ℝ) / 2) * gaussianKernel z * (‖u - v‖ / 1024) ≤
      ∫ st in ridgeRectangle u v (1 / (4 * R x)),
        R (x + ridgeDisplacement u v st) ^ 2 * gaussianKernel (z + ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume) := by
  have hRx : 0 < R x := zero_lt_one.trans_le (hR x)
  let ε := 1 / (4 * R x)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp only [ε]
    apply (div_le_iff₀ (by positivity : 0 < 4 * R x)).mpr
    linarith [hR x]
  have hRε : R x * ε ≤ 1 := by
    dsimp only [ε]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 4 * R x)).mpr
    linarith
  have hbase := ridgeRectangle_gaussian_integral_lower u v z hu hv hp hm hRx.le hε.le hε1 hRε hb hc
  have hk : Continuous (fun st => gaussianKernel (z + ridgeDisplacement u v st)) := by fun_prop
  have hw : Continuous (fun st =>
      R (x + ridgeDisplacement u v st) ^ 2 * gaussianKernel (z + ridgeDisplacement u v st)) :=
    ((hRm.comp (by fun_prop)).pow 2).mul hk
  have hcompact : IsCompact (ridgeRectangle u v ε) := isCompact_Icc.prod isCompact_Icc
  have hmono : (R x / 2) ^ 2 *
      (∫ st in ridgeRectangle u v ε, gaussianKernel (z + ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume)) ≤
      ∫ st in ridgeRectangle u v ε,
        R (x + ridgeDisplacement u v st) ^ 2 * gaussianKernel (z + ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume) := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      ((continuous_const.mul hk).continuousOn.integrableOn_compact hcompact)
      (hw.continuousOn.integrableOn_compact hcompact)
    filter_upwards [ae_restrict_mem hcompact.measurableSet] with st hst
    have hd := ridgeRectangle_displacement_norm_le u v hu hv hp hm hε.le hst
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg hRx.le (by norm_num))
        (adaptive_radius_at_endpoint_lower R hR hRadd x _ hd) 2)
      (Real.exp_nonneg _)
  have hh := (mul_le_mul_of_nonneg_left hbase
    (pow_nonneg (div_nonneg hRx.le (by norm_num)) 2)).trans hmono
  convert hh using 1
  dsimp only [ε]
  field_simp
  ring

/-- The actual positive angle coefficient uses second radius moments,
which retain the sharp square-root logarithmic edge mass. -/
theorem adaptive_angle_ridge_second_bound
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖)
    (x u v z : E) (hu : ‖u‖=1) (hv : ‖v‖=1) (hp : u+v≠0) (hm : u-v≠0)
    (hb : |⟪z,bisector u v⟫_ℝ|≤R x) (hc : |⟪z,differenceDirection u v⟫_ℝ|≤R x) :
    Real.arccos ⟪u,v⟫_ℝ*gaussianKernel z≤
      (512*Real.pi*Real.exp ((3:ℝ)/2))*(∫ st in ridgeRectangle u v (1/(4*R x)),
        R (x+ridgeDisplacement u v st)^2*gaussianKernel (z+ridgeDisplacement u v st)
          ∂((volume : Measure ℝ).prod volume)) := by
  have hf := adaptive_ridge_gaussian_integral_lower_second R hRm hR hRadd x u v z hu hv hp hm hb hc
  have ha := supplementalH_angle_le_pi_half_chord u v hu hv
  have hexp : Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2)=1 := by rw [←Real.exp_add]; norm_num
  calc
    _ ≤ ((Real.pi/2)*‖u-v‖)*gaussianKernel z := mul_le_mul_of_nonneg_right ha (Real.exp_nonneg _)
    _ = (512*Real.pi*Real.exp ((3:ℝ)/2))*(Real.exp (-(3:ℝ)/2)*gaussianKernel z*(‖u-v‖/1024)) := by
      calc
        _ = (Real.pi/2)*(Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2))*‖u-v‖*gaussianKernel z := by rw [hexp]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

/-- The radius-squared positive edge moment is separately paid by a
fourth-radius fiber; it is not used to weaken the unweighted mass. -/
theorem adaptive_angle_ridge_normSq_fourth_bound
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖)
    (x u v z : E) (hu : ‖u‖=1) (hv : ‖v‖=1) (hp : u+v≠0) (hm : u-v≠0)
    (hz : ‖z‖≤R x) :
    Real.arccos ⟪u,v⟫_ℝ*‖z‖^2*gaussianKernel z≤
      (2048*Real.pi*Real.exp ((3:ℝ)/2))*(∫ st in ridgeRectangle u v (1/(4*R x)),
        R (x+ridgeDisplacement u v st)^4*gaussianKernel (z+ridgeDisplacement u v st)
          ∂((volume : Measure ℝ).prod volume)) := by
  have hb : |⟪z,bisector u v⟫_ℝ|≤R x :=
    (abs_real_inner_le_norm _ _).trans (by rw [norm_bisector u v hp,mul_one]; exact hz)
  have hc : |⟪z,differenceDirection u v⟫_ℝ|≤R x :=
    (abs_real_inner_le_norm _ _).trans (by rw [norm_differenceDirection u v hm,mul_one]; exact hz)
  have hf := adaptive_ridge_gaussian_integral_lower_fourth R hRm hR hRadd x u v z hu hv hp hm hb hc
  have ha := supplementalH_angle_le_pi_half_chord u v hu hv
  have hcoef : Real.arccos ⟪u,v⟫_ℝ*‖z‖^2≤(Real.pi/2)*‖u-v‖*R x^2 :=
    mul_le_mul ha (pow_le_pow_left₀ (norm_nonneg _) hz 2) (sq_nonneg _) (by positivity)
  have hexp : Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2)=1 := by rw [←Real.exp_add]; norm_num
  calc
    _ ≤ ((Real.pi/2)*‖u-v‖*R x^2)*gaussianKernel z := mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = (2048*Real.pi*Real.exp ((3:ℝ)/2))*(Real.exp (-(3:ℝ)/2)*gaussianKernel z*(R x^2*‖u-v‖/4096)) := by
      calc
        _ = (Real.pi/2)*(Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2))*‖u-v‖*R x^2*gaussianKernel z := by rw [hexp]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

end
end RectangleCLTArxivV1
