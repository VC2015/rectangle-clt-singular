import RectangleCLT.GlobalDerivativeAveragedCaps
import RectangleCLT.CombinedCorollaries

/-! The combined bounded rectangle theorem. Every derivative-integral
premise of the generic assembly is discharged using the actual averaged
full-dual caps. The public conclusions have only the substantive data and
covariance hypotheses. -/

open MeasureTheory Set

universe u

namespace RectangleCLT

noncomputable section

theorem fullGaussianIntegralCaps : FullGaussianIntegralCaps.{u}
    (2 * globalThirdAverageConstant) (3 * globalFourthAverageConstant) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hlocal hA hν s hband hsmall
  let Q := covariance μ (sumVector ξ)
  let ν := fullEigenvalue Q
  let L := dimensionLog p
  have hlower (v : Vector p) : ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v := by
    rw [hA]
    exact fullEigenvalue_lower hlocal.posSemidef v
  have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by
    rw [hA]
    exact hlocal.unit_diagonal j
  constructor
  · have hD : IntervalIntegrable (fun t => t * s.sharpThirdAverage μ ξ A t) volume 0 1 :=
      (continuousOn_id.mul
        (s.continuousOn_sharpThirdAverage μ ξ hdata.measurable A)).intervalIntegrable_of_Icc
          (by norm_num)
    have hh := integral_time_mul_third_le
      (B := globalThirdAverageConstant * L * Real.sqrt L / ν) hD (fun t ht => by
        have hb := s.sharpThirdAverage_global_le μ ξ hdata.measurable hp A hν hlower
          hdiag ht.1 ht.2.le
        convert hb using 1 <;> ring)
    convert hh using 1 <;> ring
  · have hC : 0 ≤ globalFourthAverageConstant := globalFourthAverageConstant_pos.le
    have hCshort : 75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant ≤
        globalFourthAverageConstant :=
      gaussianFourthConstant_ge_short.trans globalFourthAverageConstant_ge_short
    have hD : IntervalIntegrable (s.sharpFourthAverage μ ξ A δ) volume 0 1 :=
      (s.continuousOn_sharpFourthAverage μ ξ hdata.measurable A hdata.delta_nonneg).
        intervalIntegrable_of_Icc (by norm_num)
    have hsmallCap (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
        s.sharpFourthAverage μ ξ A δ t ≤
          globalFourthAverageConstant * Real.sqrt L / s.bandwidth ^ 3 :=
      (s.sharpFourthAverage_shortScale_le μ ξ hdata hp hlocal.unit_diagonal A hA hband
        ht.1.le ht.2.le).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCshort (Real.sqrt_nonneg L))
          (pow_nonneg s.bandwidth_pos.le 3))
    exact integral_fourth_time_le_full_eigenvalue hC hν (log_exp_mul_nat_ge_one hp)
      s.bandwidth_pos hD hsmallCap (fun t ht htime =>
        s.sharpFourthAverage_global_largeTime_le hdata hp hlocal.unit_diagonal
          A hA hν hlower hband ht.1 ht.2 htime)

def combinedCLTIntegralConstant : ℝ :=
  combinedIntegralAssemblyConstant (2 * globalThirdAverageConstant) (3 * globalFourthAverageConstant)

theorem combinedCLTIntegralConstant_pos : 0 < combinedCLTIntegralConstant :=
  combinedIntegralAssemblyConstant_pos (by positivity) (by positivity)

theorem combinedGaussianIntegralCaps : CombinedGaussianIntegralCaps.{u} combinedCLTIntegralConstant :=
  combinedGaussianIntegralCaps_of_full_integralCaps
    (by positivity) (by positivity) fullGaussianIntegralCaps

def combinedCLTMasterConstant : ℝ := combinedMasterAssemblyConstant combinedCLTIntegralConstant

theorem combinedCLTMasterConstant_ge_one : 1 ≤ combinedCLTMasterConstant :=
  combinedMasterAssemblyConstant_ge_one combinedCLTIntegralConstant_pos.le

theorem combinedCLTMasterEstimate : CombinedMasterEstimate.{u} combinedCLTMasterConstant :=
  combinedMasterEstimate_of_integralCaps combinedCLTIntegralConstant_pos.le combinedGaussianIntegralCaps

def combinedCLTConstant : ℝ := max 1 (13 * combinedCLTMasterConstant)

theorem combinedCLTConstant_ge_one : 1 ≤ combinedCLTConstant := le_max_left _ _

/-- The actual combined local/full-covariance bounded rectangle CLT,
including singular full covariances. -/
theorem combinedRectangleCLT : CombinedRectangleCLT.{u} combinedCLTConstant :=
  combinedRectangleCLT_of_master
    (zero_le_one.trans combinedCLTMasterConstant_ge_one) combinedCLTMasterEstimate

/-- The original full-spectral bounded target is now a proved theorem. -/
theorem boundedRectangleCLT : BoundedRectangleCLT.{u} combinedCLTConstant :=
  boundedRectangleCLT_of_combined
    (zero_le_one.trans combinedCLTConstant_ge_one) combinedRectangleCLT

theorem boundedRectangleCLTExists : BoundedRectangleCLTExists.{u} :=
  ⟨combinedCLTConstant, combinedCLTConstant_ge_one, boundedRectangleCLT⟩

end

end RectangleCLT
