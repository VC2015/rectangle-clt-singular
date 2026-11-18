import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Polar integration for the spherical balance argument in Supplemental H.1.
The angular measure is the measure induced by Euclidean volume through polar
coordinates. In particular its normalization is fixed by Euclidean volume,
rather than by the diameter convention for an abstract Hausdorff measure. -/

namespace RectangleCLTArxivV1
open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Polar integration, retaining the angular variable. -/
theorem supplementalH_integral_polar (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : E → F) :
    (∫ x, f x ∂μ) =
      ∫ z : sphere (0 : E) 1 × Ioi (0 : ℝ), f (z.2.1 • z.1.1)
        ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
  calc
    _ = ∫ x : ({(0 : E)}ᶜ : Set E), f x.1 ∂μ.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,
        restrict_compl_singleton]
    _ = _ := by
      simpa only [← homeomorphUnitSphereProd_symm_apply_coe,
        Homeomorph.symm_apply_apply] using
        μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _)
          (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (z.2.1 • z.1.1))

/-- The radial density in polar coordinates can be written as an ordinary
Lebesgue integral, including for totalized Bochner integrals. -/
theorem supplementalH_integral_radial_density (n : ℕ) (f : ℝ → F) :
    (∫ r : Ioi (0 : ℝ), f r.1 ∂Measure.volumeIoiPow n) =
      ∫ r in Ioi (0 : ℝ), r^n • f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi
      (fun r : ℝ => (r^n).toNNReal • f r)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- Separation of a radial scalar factor from an angular vector factor. -/
theorem supplementalH_integral_angular_radial (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : sphere (0 : E) 1 → F) (b : ℝ → ℝ) :
    (∫ z : sphere (0 : E) 1 × Ioi (0 : ℝ), b z.2.1 • a z.1
      ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) =
    (∫ r in Ioi (0 : ℝ), r^(Module.finrank ℝ E - 1) * b r) •
      ∫ ω, a ω ∂μ.toSphere := by
  rw [← integral_prod_swap]
  simp only [Prod.swap]
  rw [integral_prod_smul (fun r : Ioi (0 : ℝ) => b r.1) a]
  rw [supplementalH_integral_radial_density]
  rfl

/-- The radial first-moment coefficient in dimension three. -/
theorem supplementalH_integral_radial_three :
    (∫ r : ℝ in Ioi 0, r^3 * Real.exp (-r^2/2)) = 2 := by
  have hd (x : ℝ) : HasDerivAt
      (fun r : ℝ => -(r^2+2)*Real.exp (-r^2/2))
      (x^3*Real.exp (-x^2/2)) x := by
    convert (((hasDerivAt_pow 2 x).add_const 2).neg.mul
      (((hasDerivAt_pow 2 x).neg.div_const 2).exp)) using 1 <;> ring
  have hi : IntegrableOn (fun r : ℝ => r^3*Real.exp (-r^2/2)) (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ)<1/2) (by norm_num : (-1 : ℝ)<(3 : ℝ)) using 1
    ext r
    rw [← Real.rpow_natCast r 3]
    congr 2
    ring
  have he : Tendsto (fun t : ℝ => Real.exp (-(1/2)*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop_of_neg
        (by norm_num : -(1/2 : ℝ)<0))
  have ht : Tendsto (fun t : ℝ => (t+2)*Real.exp (-(1/2)*t)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/2)
      (by norm_num)).add (he.const_mul 2)
    simpa only [Real.rpow_one, add_mul, zero_add, mul_zero] using hh
  have hp : Tendsto (fun r : ℝ => -(r^2+2)*Real.exp (-r^2/2)) atTop (𝓝 0) := by
    convert (ht.comp (tendsto_pow_atTop (by decide : (2 : ℕ)≠0))).neg using 1
    · ext r
      dsimp only [Function.comp_def]
      congr 1 <;> ring
    · norm_num
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hi hp
  norm_num at hh ⊢
  exact hh

/-- The radial area coefficient in dimension two. -/
theorem supplementalH_integral_radial_two :
    (∫ r : ℝ in Ioi 0, r * Real.exp (-r^2/2)) = 1 := by
  have hd (x : ℝ) : HasDerivAt (fun r : ℝ => -Real.exp (-r^2/2))
      (x*Real.exp (-x^2/2)) x := by
    convert (((hasDerivAt_pow 2 x).neg.div_const 2).exp.neg) using 1 <;> ring
  have hi : IntegrableOn (fun r : ℝ => r*Real.exp (-r^2/2)) (Ioi 0) := by
    convert (integrable_mul_exp_neg_mul_sq
      (by norm_num : (0 : ℝ)<1/2)).integrableOn using 1
    ext r
    congr 2
    ring
  have hp : Tendsto (fun r : ℝ => -Real.exp (-r^2/2)) atTop (𝓝 0) := by
    convert (Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by decide : (2 : ℕ)≠0)).const_mul_atTop_of_neg
        (by norm_num : -(1/2 : ℝ)<0))).neg using 1
    · ext r
      dsimp only [Function.comp_def]
      congr 2
      ring
    · norm_num
  simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hd x) hi hp

/-- The spherical section of an actual cone. -/
def supplementalHSphericalSection (C : Set E) : Set (sphere (0 : E) 1) :=
  {ω | ω.1 ∈ C}

/-- The Gaussian first moment of a three-dimensional cone equals twice
the vector integral of its spherical section. Only positive dilation
invariance of the actual set is required. -/
theorem supplementalH_cone_gaussian_firstMoment (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = 3) (C : Set E) (hC : MeasurableSet C)
    (hcone : ∀ (r : ℝ), 0 < r → ∀ x : E, r • x ∈ C ↔ x ∈ C) :
    (∫ x in C, Real.exp (-‖x‖^2/2) • x ∂μ) =
      (2 : ℝ) • ∫ ω in supplementalHSphericalSection C, ω.1 ∂μ.toSphere := by
  have hΩ : MeasurableSet (supplementalHSphericalSection C) :=
    hC.preimage continuous_subtype_val.measurable
  rw [← integral_indicator hC, supplementalH_integral_polar μ]
  have he (z : sphere (0 : E) 1 × Ioi (0 : ℝ)) :
      C.indicator (fun x => Real.exp (-‖x‖^2/2) • x) (z.2.1 • z.1.1) =
        (z.2.1 * Real.exp (-z.2.1^2/2)) •
          (supplementalHSphericalSection C).indicator Subtype.val z.1 := by
    have hn : ‖z.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.1.2
    have hh := hcone z.2.1 z.2.2 z.1.1
    by_cases hz : z.1.1 ∈ C
    · rw [Set.indicator_of_mem (hh.mpr hz),
        Set.indicator_of_mem (show z.1 ∈ supplementalHSphericalSection C from hz)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos z.2.2, hn, mul_one, smul_smul]
      congr 1
      ring
    · rw [Set.indicator_of_not_mem (fun h => hz (hh.mp h)),
        Set.indicator_of_not_mem (show z.1 ∉ supplementalHSphericalSection C from hz),
        smul_zero]
  rw [integral_congr_ae (ae_of_all _ he),
    supplementalH_integral_angular_radial μ
      ((supplementalHSphericalSection C).indicator Subtype.val)
      (fun r : ℝ => r*Real.exp (-r^2/2))]
  rw [integral_indicator hΩ, hdim]
  norm_num only [Nat.reduceSub]
  have hr : (∫ r : ℝ in Ioi 0, r^2*(r*Real.exp (-r^2/2))) = 2 := by
    convert supplementalH_integral_radial_three using 1
    congr 1
    ext r
    ring
  rw [hr]

/-- The vector integral of any measurable spherical set has norm at most
its area, with the normalization supplied by the ambient Haar measure. -/
theorem supplementalH_spherical_vectorIntegral_norm_le (μ : Measure E)
    [μ.IsAddHaarMeasure] (Ω : Set (sphere (0 : E) 1)) :
    ‖∫ ω in Ω, ω.1 ∂μ.toSphere‖ ≤ μ.toSphere.real Ω := by
  simpa only [one_mul] using
    (norm_setIntegral_le_of_norm_le_const (measure_lt_top μ.toSphere Ω)
      (fun ω _ => (mem_sphere_zero_iff_norm.mp ω.2).le))

/-- The resulting dimension-free first-moment bound uses the area of the
actual spherical cone section, and does not count its facets. -/
theorem supplementalH_cone_gaussian_firstMoment_norm_le (μ : Measure E)
    [μ.IsAddHaarMeasure] (hdim : Module.finrank ℝ E = 3)
    (C : Set E) (hC : MeasurableSet C)
    (hcone : ∀ (r : ℝ), 0 < r → ∀ x : E, r • x ∈ C ↔ x ∈ C) :
    ‖∫ x in C, Real.exp (-‖x‖^2/2) • x ∂μ‖ ≤
      2 * μ.toSphere.real (supplementalHSphericalSection C) := by
  rw [supplementalH_cone_gaussian_firstMoment μ hdim C hC hcone,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact mul_le_mul_of_nonneg_left
    (supplementalH_spherical_vectorIntegral_norm_le μ _) (by norm_num)

/-- In a plane, the unnormalized Gaussian area of an actual cone is the
angular area of its spherical section. This is the boundary coefficient
used in the three-dimensional balance identity. -/
theorem supplementalH_planar_cone_gaussian_mass (μ : Measure E) [μ.IsAddHaarMeasure]
    (hdim : Module.finrank ℝ E = 2) (C : Set E) (hC : MeasurableSet C)
    (hcone : ∀ (r : ℝ), 0 < r → ∀ x : E, r • x ∈ C ↔ x ∈ C) :
    (∫ x in C, Real.exp (-‖x‖^2/2) ∂μ) =
      μ.toSphere.real (supplementalHSphericalSection C) := by
  have hΩ : MeasurableSet (supplementalHSphericalSection C) :=
    hC.preimage continuous_subtype_val.measurable
  rw [← integral_indicator hC, supplementalH_integral_polar μ]
  have he (z : sphere (0 : E) 1 × Ioi (0 : ℝ)) :
      C.indicator (fun x => Real.exp (-‖x‖^2/2)) (z.2.1 • z.1.1) =
        Real.exp (-z.2.1^2/2) •
          (supplementalHSphericalSection C).indicator (fun _ => (1 : ℝ)) z.1 := by
    have hn : ‖z.1.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.1.2
    have hh := hcone z.2.1 z.2.2 z.1.1
    by_cases hz : z.1.1 ∈ C
    · rw [Set.indicator_of_mem (hh.mpr hz),
        Set.indicator_of_mem (show z.1 ∈ supplementalHSphericalSection C from hz)]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos z.2.2, hn, mul_one, smul_eq_mul, mul_one]
    · rw [Set.indicator_of_not_mem (fun h => hz (hh.mp h)),
        Set.indicator_of_not_mem (show z.1 ∉ supplementalHSphericalSection C from hz),
        smul_zero]
  rw [integral_congr_ae (ae_of_all _ he),
    supplementalH_integral_angular_radial μ
      ((supplementalHSphericalSection C).indicator (fun _ => (1 : ℝ)))
      (fun r : ℝ => Real.exp (-r^2/2))]
  rw [hdim]
  norm_num only [Nat.reduceSub, pow_one]
  rw [supplementalH_integral_radial_two, one_smul, integral_indicator hΩ,
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one]

/-- The first-moment kernel used in the three-dimensional argument is
genuinely Bochner integrable. -/
theorem supplementalH_gaussian_firstMoment_integrable (μ : Measure E)
    [μ.IsAddHaarMeasure] (hdim : Module.finrank ℝ E = 3) :
    Integrable (fun x : E => Real.exp (-‖x‖^2/2) • x) μ := by
  have hr : (∫ r : ℝ in Ioi 0, r^2*(Real.exp (-r^2/2)*r)) = 2 := by
    convert supplementalH_integral_radial_three using 1
    congr 1
    ext r
    ring
  have hn : (∫ x : E, ‖Real.exp (-‖x‖^2/2) • x‖ ∂μ) =
      (3 : ℝ)*μ.real (ball 0 1)*2 := by
    calc
      _ = ∫ x : E, Real.exp (-‖x‖^2/2)*‖x‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ = _ := by
        rw [integral_fun_norm_addHaar μ (fun r => Real.exp (-r^2/2)*r), hdim]
        norm_num only [Nat.reduceSub, nsmul_eq_mul, smul_eq_mul]
        rw [hr]
        ring
  have hb : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  apply (integrable_norm_iff (show AEStronglyMeasurable
    (fun x : E => Real.exp (-‖x‖^2/2) • x) μ from
      (by fun_prop : Continuous (fun x : E => Real.exp (-‖x‖^2/2) • x)).aestronglyMeasurable)).mp
  apply Integrable.of_integral_ne_zero
  rw [hn]
  positivity

/-- Continuous linear functionals of the spherical vector integral are
ordinary integrals of those same functionals over the actual section. -/
theorem supplementalH_spherical_vectorIntegral_apply (μ : Measure E)
    [μ.IsAddHaarMeasure] [CompleteSpace F]
    (Ω : Set (sphere (0 : E) 1)) (L : E →L[ℝ] F) :
    L (∫ ω in Ω, ω.1 ∂μ.toSphere) = ∫ ω in Ω, L ω.1 ∂μ.toSphere := by
  have hi : Integrable (fun ω : sphere (0 : E) 1 => ω.1) μ.toSphere := by
    apply (integrable_const (1 : ℝ)).mono' continuous_subtype_val.aestronglyMeasurable
    filter_upwards with ω
    exact (mem_sphere_zero_iff_norm.mp ω.2).le
  exact (L.integral_comp_comm hi.integrableOn).symm

end
end RectangleCLTArxivV1
