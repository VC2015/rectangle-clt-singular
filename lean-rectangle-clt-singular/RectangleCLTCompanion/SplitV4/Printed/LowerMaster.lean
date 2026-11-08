import RectangleCLTCompanion.SplitV4.SymmetricFamilyMaster
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumSmoothness
import RectangleCLTCompanion.SplitV4.Printed.LowerGaussianShifts
import RectangleCLTCompanion.SplitV4.SymmetricBoundedRemainder

/-! The global F.2 route to the printed common symmetric master formula.
The explicit global Kolmogorov estimate remains an input here; its
separate printed maximum estimate supplies it later. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- Formula lower:eq:master-comparison, using the global Taylor lemma
F.2 and the actual global Gaussian maximum curvature. -/
theorem familyGlobal_master_comparison (P : SymmetricFamilyParameters)
    {n m : ℕ} [NeZero m] (hm : 2≤m) {ε : ℝ} (hε : 0≤ε)
    (hCDF : ∀x,|(familySignArrayLaw n m).real {z | familyRademacherMaximum z≤x}-normalMaximumCDF m x|≤ε)
    (t : ℝ) :
    |familyShiftedCDFDifference P n m t-normalMaximumDensity m t*familyShiftMeanDifference P n m|≤
      ε+(gaussianMaximumCurvatureConstant*dimensionLog m/2)*familyShiftSecondMoments P n m := by
  let μ := familySeparatedLaw P n m
  let ν := familyGaussianPairLaw m
  let A : FamilySeparatedSeed n m → ℝ := fun z => familyRademacherMaximum z.1
  let U : FamilySeparatedSeed n m → ℝ := fun z => familyObservationShift P z.2
  let G : Vector m × Vector m → ℝ := fun z => finiteMaximum z.1
  let V : Vector m × Vector m → ℝ := fun z => familyGaussianShift P z.2
  have hmax : Measurable (finiteMaximum : Vector m → ℝ) :=
    measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j)
  have hA : Measurable A := measurable_of_finite _
  have hU : Measurable U := measurable_of_finite _
  have hG : Measurable G := hmax.comp measurable_fst
  have hV : Measurable V := measurable_const.mul (hmax.comp measurable_snd)
  have hU2 : Integrable (fun z => U z ^ 2) μ := integrable_family_finite _ _
  have hsnd : MeasurePreserving Prod.snd ν (standardGaussian m) := by
    refine ⟨measurable_snd, ?_⟩
    simp only [ν, familyGaussianPairLaw, Measure.map_snd_prod, measure_univ, one_smul]
  have hV2 : Integrable (fun z => V z ^ 2) ν := by
    exact (hsnd.integrable_comp (familyGaussianShift_sq_integrable P m).aestronglyMeasurable).mpr
      (familyGaussianShift_sq_integrable P m)
  have hFG : realCDF ν G = normalMaximumCDF m := funext (familyGaussian_realCDF m)
  have hF : ContDiff ℝ 2 (realCDF ν G) := by rw [hFG]; exact contDiff_normalMaximumCDF_two m
  have hB' (x : ℝ) : |deriv (deriv (realCDF ν G)) x| ≤
      gaussianMaximumCurvatureConstant*dimensionLog m := by
    rw [hFG]
    exact normalMaximumCDF_second_derivative_global_bound hm x
  have hCDF' : realCDFDistance μ A ν G≤ε := by
    apply (realCDFDistance_le_iff μ A ν G ε).mpr
    intro x
    rw [familyRademacher_realCDF,familyGaussian_realCDF]
    exact hCDF x
  have hh := independent_shift_comparison_of_second_derivative_bound μ ν A U G V
    hA hU hG hV (familyObservationShift_independent P n m) (familyGaussianShift_independent P m)
    hU2 hV2 hF (gaussianMaximumCurvatureConstant*dimensionLog m) ε hε hB' hCDF' t
  rw [hFG,deriv_normalMaximumCDF] at hh
  have hUi : (∫ z, U z ∂μ) = ∫ z, familyObservationShift P z ∂familyRestArrayLaw P n m :=
    integral_product_snd_probability (familySignArrayLaw n m) (familyRestArrayLaw P n m) (familyObservationShift P)
  have hVi : (∫ z, V z ∂ν) = ∫ z, familyGaussianShift P z ∂standardGaussian m :=
    integral_product_snd_probability (standardGaussian m) (standardGaussian m) (familyGaussianShift P)
  have hU2i : (∫ z, U z ^ 2 ∂μ) = ∫ z, familyObservationShift P z ^ 2 ∂familyRestArrayLaw P n m :=
    integral_product_snd_probability (familySignArrayLaw n m) (familyRestArrayLaw P n m) (fun z => familyObservationShift P z ^ 2)
  have hV2i : (∫ z, V z ^ 2 ∂ν) = ∫ z, familyGaussianShift P z ^ 2 ∂standardGaussian m :=
    integral_product_snd_probability (standardGaussian m) (standardGaussian m) (fun z => familyGaussianShift P z ^ 2)
  rw [hUi, hVi, hU2i, hV2i] at hh
  exact hh

/-- Integration and passage to the asymptotic scale after the global
master comparison. All three inputs concern explicit intermediate errors
or means; none assumes the target probability discrepancy. -/
theorem familyGlobal_discrepancy_div_scale
    {P : ℕ→SymmetricFamilyParameters} {m : ℕ→ℕ} [∀n,NeZero (m n)]
    (hm : ∀n,2≤m n) (ε d : ℕ→ℝ) {c : ℝ}
    (hd : ∀ᶠ n in atTop,0<d n) (hε : ∀ᶠ n in atTop,0≤ε n)
    (hCDF : ∀ᶠ n in atTop,∀x,
      |(familySignArrayLaw n (m n)).real {z | familyRademacherMaximum z≤x}-normalMaximumCDF (m n) x|≤ε n)
    (hE : Tendsto (fun n => ε n/d n) atTop (𝓝 0))
    (hR : Tendsto (fun n => (gaussianMaximumCurvatureConstant*dimensionLog (m n)/2)*
      familyShiftSecondMoments (P n) n (m n)/d n) atTop (𝓝 0))
    (hLead : Tendsto (fun n => normalMaximumDensity (m n) (normalMaxThreshold (m n))*
      familyShiftMeanDifference (P n) n (m n)/d n) atTop (𝓝 c)) :
    Tendsto (fun n => familyShiftedCDFDifference (P n) n (m n) (normalMaxThreshold (m n))/d n)
      atTop (𝓝 c) := by
  let disc := fun n => familyShiftedCDFDifference (P n) n (m n) (normalMaxThreshold (m n))
  let lead := fun n => normalMaximumDensity (m n) (normalMaxThreshold (m n))*familyShiftMeanDifference (P n) n (m n)
  have hupper := hE.add hR
  simp only [zero_add] at hupper
  have hb : ∀ᶠ n in atTop, |(disc n-lead n)/d n|≤ε n/d n+
      (gaussianMaximumCurvatureConstant*dimensionLog (m n)/2)*familyShiftSecondMoments (P n) n (m n)/d n := by
    filter_upwards [hd,hε,hCDF] with n hnd hnε hnCDF
    have hc := div_le_div_of_nonneg_right
      (familyGlobal_master_comparison (P n) (hm n) hnε hnCDF (normalMaxThreshold (m n))) hnd.le
    rw [abs_div,abs_of_pos hnd]
    simpa only [disc,lead,add_div] using hc
  have habs := squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hb hupper
  have herr : Tendsto (fun n => (disc n-lead n)/d n) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero,Real.norm_eq_abs] using habs)
  have hh := hLead.add herr
  simp only [add_zero] at hh
  convert hh using 1
  funext n
  dsimp only [disc,lead]
  ring

/-- The same global transition at any specified threshold sequence. -/
theorem familyGlobal_discrepancy_div_scale_at
    {P : ℕ→SymmetricFamilyParameters} {m : ℕ→ℕ} [∀n,NeZero (m n)]
    (hm : ∀n,2≤m n) (u ε d : ℕ→ℝ) {c : ℝ}
    (hd : ∀ᶠ n in atTop,0<d n) (hε : ∀ᶠ n in atTop,0≤ε n)
    (hCDF : ∀ᶠ n in atTop,∀x,
      |(familySignArrayLaw n (m n)).real {z | familyRademacherMaximum z≤x}-normalMaximumCDF (m n) x|≤ε n)
    (hE : Tendsto (fun n => ε n/d n) atTop (𝓝 0))
    (hR : Tendsto (fun n => (gaussianMaximumCurvatureConstant*dimensionLog (m n)/2)*
      familyShiftSecondMoments (P n) n (m n)/d n) atTop (𝓝 0))
    (hLead : Tendsto (fun n => normalMaximumDensity (m n) (u n)*
      familyShiftMeanDifference (P n) n (m n)/d n) atTop (𝓝 c)) :
    Tendsto (fun n => familyShiftedCDFDifference (P n) n (m n) (u n)/d n)
      atTop (𝓝 c) := by
  let disc := fun n => familyShiftedCDFDifference (P n) n (m n) (u n)
  let lead := fun n => normalMaximumDensity (m n) (u n)*familyShiftMeanDifference (P n) n (m n)
  have hupper := hE.add hR
  simp only [zero_add] at hupper
  have hb : ∀ᶠ n in atTop, |(disc n-lead n)/d n|≤ε n/d n+
      (gaussianMaximumCurvatureConstant*dimensionLog (m n)/2)*familyShiftSecondMoments (P n) n (m n)/d n := by
    filter_upwards [hd,hε,hCDF] with n hnd hnε hnCDF
    have hc := div_le_div_of_nonneg_right
      (familyGlobal_master_comparison (P n) (hm n) hnε hnCDF (u n)) hnd.le
    rw [abs_div,abs_of_pos hnd]
    simpa only [disc,lead,add_div] using hc
  have habs := squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hb hupper
  have herr : Tendsto (fun n => (disc n-lead n)/d n) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero,Real.norm_eq_abs] using habs)
  have hh := hLead.add herr
  simp only [add_zero] at hh
  convert hh using 1
  funext n
  dsimp only [disc,lead]
  ring

theorem global_moment_cost_identity {K ell a s N k v C d : ℝ}
    (hN : 0<N) (hv : 0≤v) (hs : s≠0) (hd : d≠0) :
    (K*ell)*((a/(s*Real.sqrt N))^2*(k^2+k)+(Real.sqrt v/s)^2*(C*(1+ell)))/d=
      K/s^2*(ell*a^2*(k^2+k)/N/d+C*(ell*v*(1+ell)/d)) := by
  rw [div_pow,mul_pow,Real.sq_sqrt hN.le,div_pow,Real.sq_sqrt hv]
  field_simp
  ring

/-- The printed second-moment error, from the actual Q and Gaussian
maximum moments. The input limits are the primitive count/Gaussian
budgets appearing in the unmasked and masked parameter calculations. -/
theorem familyGlobal_remainder_tendsto
    {P : ℕ→SymmetricFamilyParameters} {m : ℕ→ℕ} [∀n,NeZero (m n)]
    (hm : ∀n,2≤m n) (hmTop : Tendsto m atTop atTop) (d : ℕ→ℝ)
    (hd : ∀ᶠ n in atTop,0<d n)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hU : Tendsto (fun n => Real.log (m n:ℝ)*(P n).amplitude^2*
      (((n:ℝ)*(P n).theta)^2+(n:ℝ)*(P n).theta)/n/d n) atTop (𝓝 0))
    (hV : Tendsto (fun n => Real.log (m n:ℝ)*(P n).variance*(1+Real.log (m n:ℝ))/d n) atTop (𝓝 0)) :
    Tendsto (fun n => (gaussianMaximumCurvatureConstant*dimensionLog (m n)/2)*
      familyShiftSecondMoments (P n) n (m n)/d n) atTop (𝓝 0) := by
  let K := gaussianMaximumCurvatureConstant
  have hK : 0≤K := gaussianMaximumCurvatureConstant_pos.le
  have hs : Tendsto (fun n => (P n).scale) atTop (𝓝 1) := by
    have he := Real.continuous_sqrt.continuousAt.tendsto.comp ((tendsto_const_nhds (x:=(1:ℝ))).sub hv)
    simpa only [sub_zero,Real.sqrt_one,SymmetricFamilyParameters.scale,Function.comp_apply] using he
  have hcoef := (tendsto_const_nhds (x:=K)).div (hs.pow 2) (by norm_num : (1:ℝ)^2≠0)
  have hup := hcoef.mul (hU.add (hV.const_mul (Real.exp (11/2))))
  norm_num only [mul_zero,add_zero] at hup
  have hlog : Tendsto (fun n => Real.log (m n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  apply squeeze_zero' _ _ hup
  · filter_upwards [hd] with n hn
    exact div_nonneg (mul_nonneg (by
      have hdim : 0≤dimensionLog (m n) := zero_le_one.trans (log_exp_mul_nat_ge_one (by have := hm n; omega))
      positivity) (familyShiftSecondMoments_nonneg _ _ _)) hn.le
  · filter_upwards [hd,hlog.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1] with n hnd hL hn
    have hN : (0:ℝ)<n := by exact_mod_cast hn
    have hDim : dimensionLog (m n)≤2*Real.log (m n:ℝ) := by
      rw [dimensionLog_eq_one_add_log (by have := hm n; omega)]
      linarith
    have hcost : gaussianMaximumCurvatureConstant*dimensionLog (m n)/2≤K*Real.log (m n:ℝ) := by
      dsimp only [K]; nlinarith [mul_le_mul_of_nonneg_left hDim hK]
    have hMom := add_le_add (familyObservationShift_sq_integral_le (P n) n (m n))
      (familyGaussianShift_sq_integral_le_printed (P n) (m n))
    rw [dimensionLog_eq_one_add_log (by have := hm n; omega)] at hMom
    have hprod := mul_le_mul hcost hMom (familyShiftSecondMoments_nonneg _ _ _) (by positivity : 0≤K*Real.log (m n:ℝ))
    exact (div_le_div_of_nonneg_right hprod hnd.le).trans_eq
      (global_moment_cost_identity hN (P n).variance_pos.le (P n).scale_pos.ne' hnd.ne')

end
end RectangleCLT.Companion.SplitV4.Printed
