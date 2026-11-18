import RectangleCLTCompanion.SplitV4.AveragedThreshold

/-! Actual fourth-radius adaptive facet/ridge fibers for Supplemental H.
These strengthen the archived cubic fibers using the proved lower radius
at the actual output point. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A facet fiber with the actual fourth radius weight leaves a cubic
base radius, matching the weighted facet Green coefficient. -/
theorem adaptive_facet_gaussian_integral_lower_fourth
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖)
    (x u z : E) (hu : ‖u‖=1) (hz : |⟪z,u⟫_ℝ|≤R x) :
    Real.exp (-(3:ℝ)/2)*gaussianKernel z*(R x^3/64)≤
      ∫ t in Set.Icc (0:ℝ) (1/(4*R x)),
        R (x+t • u)^4*gaussianKernel (z+t • u) := by
  have hRx : 0<R x := zero_lt_one.trans_le (hR x)
  have hb := adaptive_facet_gaussian_integral_lower R hRm hR hRadd x u z hu hz
  let ε := 1/(4*R x)
  have hk : Continuous (fun t : ℝ => gaussianKernel (z+t • u)) := by fun_prop
  have h3 : Continuous (fun t : ℝ => R (x+t • u)^3*gaussianKernel (z+t • u)) :=
    ((hRm.comp (by fun_prop)).pow 3).mul hk
  have h4 : Continuous (fun t : ℝ => R (x+t • u)^4*gaussianKernel (z+t • u)) :=
    ((hRm.comp (by fun_prop)).pow 4).mul hk
  have hm : (R x/2)*(∫ t in Set.Icc (0:ℝ) ε,
      R (x+t • u)^3*gaussianKernel (z+t • u))≤
      ∫ t in Set.Icc (0:ℝ) ε, R (x+t • u)^4*gaussianKernel (z+t • u) := by
    rw [←integral_const_mul]
    apply integral_mono_ae
      ((continuous_const.mul h3).continuousOn.integrableOn_Icc (μ := volume))
      (h4.continuousOn.integrableOn_Icc (μ := volume))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hd : ‖t • u‖≤ε := by
      simpa only [norm_smul,Real.norm_eq_abs,hu,mul_one,abs_of_nonneg ht.1] using ht.2
    have hl := adaptive_radius_at_endpoint_lower R hR hRadd x (t • u) hd
    calc
      _ = (R x/2)*(R (x+t • u)^3*gaussianKernel (z+t • u)) := rfl
      _ ≤ R (x+t • u)*(R (x+t • u)^3*gaussianKernel (z+t • u)) :=
        mul_le_mul_of_nonneg_right hl (mul_nonneg (pow_nonneg (zero_le_one.trans (hR _)) 3) (Real.exp_nonneg _))
      _ = _ := by ring
  have hh := (mul_le_mul_of_nonneg_left hb (div_nonneg hRx.le (by norm_num))).trans hm
  convert hh using 1
  ring

/-- The actual two-dimensional ridge fiber retains chord times squared
base radius, with no inverse correlation-gap constant. -/
theorem adaptive_ridge_gaussian_integral_lower_fourth
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖)
    (x u v z : E) (hu : ‖u‖=1) (hv : ‖v‖=1) (hp : u+v≠0) (hm : u-v≠0)
    (hb : |⟪z,bisector u v⟫_ℝ|≤R x) (hc : |⟪z,differenceDirection u v⟫_ℝ|≤R x) :
    Real.exp (-(3:ℝ)/2)*gaussianKernel z*(R x^2*‖u-v‖/4096)≤
      ∫ st in ridgeRectangle u v (1/(4*R x)),
        R (x+ridgeDisplacement u v st)^4*gaussianKernel (z+ridgeDisplacement u v st)
          ∂((volume : Measure ℝ).prod volume) := by
  have hRx : 0<R x := zero_lt_one.trans_le (hR x)
  have hbase := adaptive_ridge_gaussian_integral_lower R hRm hR hRadd x u v z hu hv hp hm hb hc
  let ε := 1/(4*R x)
  have hε : 0≤ε := by dsimp only [ε]; positivity
  have hk : Continuous (fun st : ℝ × ℝ => gaussianKernel (z+ridgeDisplacement u v st)) := by fun_prop
  have h3 : Continuous (fun st : ℝ × ℝ => R (x+ridgeDisplacement u v st)^3*gaussianKernel (z+ridgeDisplacement u v st)) :=
    ((hRm.comp (by fun_prop)).pow 3).mul hk
  have h4 : Continuous (fun st : ℝ × ℝ => R (x+ridgeDisplacement u v st)^4*gaussianKernel (z+ridgeDisplacement u v st)) :=
    ((hRm.comp (by fun_prop)).pow 4).mul hk
  have hcompact : IsCompact (ridgeRectangle u v ε) := isCompact_Icc.prod isCompact_Icc
  have hmono : (R x/2)*(∫ st in ridgeRectangle u v ε,
      R (x+ridgeDisplacement u v st)^3*gaussianKernel (z+ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume))≤
      ∫ st in ridgeRectangle u v ε,
        R (x+ridgeDisplacement u v st)^4*gaussianKernel (z+ridgeDisplacement u v st)
          ∂((volume : Measure ℝ).prod volume) := by
    rw [←integral_const_mul]
    apply integral_mono_ae
      ((continuous_const.mul h3).continuousOn.integrableOn_compact hcompact)
      (h4.continuousOn.integrableOn_compact hcompact)
    filter_upwards [ae_restrict_mem hcompact.measurableSet] with st hst
    have hd := ridgeRectangle_displacement_norm_le u v hu hv hp hm hε hst
    have hl := adaptive_radius_at_endpoint_lower R hR hRadd x _ hd
    calc
      _ ≤ R (x+ridgeDisplacement u v st)*
          (R (x+ridgeDisplacement u v st)^3*gaussianKernel (z+ridgeDisplacement u v st)) :=
        mul_le_mul_of_nonneg_right hl (mul_nonneg (pow_nonneg (zero_le_one.trans (hR _)) 3) (Real.exp_nonneg _))
      _ = _ := by ring
  have hh := (mul_le_mul_of_nonneg_left hbase (div_nonneg hRx.le (by norm_num))).trans hmono
  convert hh using 1
  ring

end
end RectangleCLTArxivV1
