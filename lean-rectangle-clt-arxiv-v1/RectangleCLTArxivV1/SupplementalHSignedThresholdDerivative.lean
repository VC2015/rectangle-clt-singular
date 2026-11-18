import RectangleCLTArxivV1.SupplementalHWeightedThresholdDerivative

/-! Local unweighted signed first coarea, without family independence. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem measurable_gaussianThresholdTrace_threshold {m r : ℕ} (u : Fin m → Vector r) :
    Measurable (gaussianThresholdTrace u) := by
  let E : Set (Vector m × Vector r) := {z | ∀ k,faceDot (u k) z.2≤z.1 k}
  have hE : MeasurableSet E := by
    unfold E
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_le
      ((continuous_faceDot_left _).measurable.comp measurable_snd)
      ((measurable_pi_apply k).comp measurable_fst))
  let P := fun z : Vector m × Vector r => vectorNormSq z.2-(r:ℝ)
  have hP : Measurable P := by unfold P vectorNormSq; fun_prop
  exact (hP.indicator hE).stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_thresholdSignedSection_of_unit {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1) :
    Integrable (Printed.thresholdSignedSection u b j) (gaussianReal 0 1) := by
  apply ((standardRealGaussian_integrable_pow 2).add (integrable_const (2*(r:ℝ)))).mono'
    (measurable_thresholdSignedSection_parameter u b j).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    simpa only [Real.norm_eq_abs] using Printed.abs_thresholdSignedSection_le u b j hu t)

theorem hasDerivAt_gaussianThresholdTrace_update_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (c : ℝ)
    (hreg : ∀ l∈Finset.univ.erase j,
      gaussianNormalProjection (u j) (u l)≠0 ∨ b l-c*faceDot (u l) (u j)≠0) :
    HasDerivAt (fun t => gaussianThresholdTrace u (Function.update b j t))
      (gaussianPDFReal 0 1 c*Printed.thresholdSignedSection u b j c) c := by
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have hm := (measurable_gaussianPDFReal 0 1).mul (measurable_thresholdSignedSection_parameter u b j)
  have hi := standardRealGaussian_integrable_density_mul (integrable_thresholdSignedSection_of_unit u b j hu)
  have hd := hasDerivAt_integral_Iic_of_continuousAt_integrable _ hm.stronglyMeasurable hi c
    (hpdf.continuousAt.mul (continuousAt_thresholdSignedSection_of_slack u b j hu c hreg))
  exact hd.congr_of_eventuallyEq (Eventually.of_forall
    (fun t => Printed.gaussianThresholdTrace_update_eq_signed_section_integral u b j hu t))

theorem ae_hasDerivAt_gaussianThresholdTrace_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j,vectorNormSq (u j)=1) :
    ∀ᵐ b : Vector m ∂volume,∀ j,
      HasDerivAt (fun t => gaussianThresholdTrace u (Function.update b j t))
        (gaussianPDFReal 0 1 (b j)*Printed.thresholdSignedSection u b j (b j)) (b j) := by
  filter_upwards [ae_localThresholdRegularity u] with b hb
  intro j
  exact hasDerivAt_gaussianThresholdTrace_update_of_slack u b j (hu j) (b j)
    (fun l hl => hb j l (Finset.mem_erase.mp hl).1)

def gaussianSignedFaceDensityBudget (r : ℕ) : ℝ := (Real.sqrt (2*Real.pi))⁻¹*(2+2*(r:ℝ))

theorem gaussianSignedFaceDensityBudget_nonneg (r : ℕ) : 0≤gaussianSignedFaceDensityBudget r := by
  unfold gaussianSignedFaceDensityBudget
  positivity

theorem norm_gaussianSignedFace_section_density_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1) (t : ℝ) :
    ‖gaussianPDFReal 0 1 t*Printed.thresholdSignedSection u b j t‖≤gaussianSignedFaceDensityBudget r := by
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  exact (mul_le_mul_of_nonneg_left (Printed.abs_thresholdSignedSection_le u b j hu t)
    (gaussianPDFReal_nonneg _ _ _)).trans (Printed.gaussianPDFReal_mul_sq_add_dimension_le r t)

theorem gaussianThresholdTrace_update_increment_bound {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1) (c d : ℝ) :
    ‖gaussianThresholdTrace u (Function.update b j c)-gaussianThresholdTrace u (Function.update b j d)‖≤
      gaussianSignedFaceDensityBudget (n+1)*|c-d| := by
  have hi := standardRealGaussian_integrable_density_mul (integrable_thresholdSignedSection_of_unit u b j hu)
  rw [Printed.gaussianThresholdTrace_update_eq_signed_section_integral u b j hu c,
    Printed.gaussianThresholdTrace_update_eq_signed_section_integral u b j hu d,
    intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => norm_gaussianSignedFace_section_density_le u b j hu t)

theorem lipschitzWith_gaussianThresholdTrace_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1) :
    LipschitzWith ⟨gaussianSignedFaceDensityBudget (n+1),gaussianSignedFaceDensityBudget_nonneg _⟩
      (fun t => gaussianThresholdTrace u (Function.update b j t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  simpa only [dist_eq_norm,Real.norm_eq_abs] using gaussianThresholdTrace_update_increment_bound u b j hu c d

end
end RectangleCLTArxivV1
