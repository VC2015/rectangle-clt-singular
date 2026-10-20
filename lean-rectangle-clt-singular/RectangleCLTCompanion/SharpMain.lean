import RectangleCLTCompanion.SharpMainAssembly
import RectangleCLTCompanion.SharpTraceApplication

/-! The companion CLT rates for arbitrary covariance, including singular
covariance, with universal constants and no analytic estimate as a premise. -/

open MeasureTheory Set

universe u

namespace RectangleCLT.Companion

noncomputable section

/-- One universal constant for the gap-sensitive and zero-skew rates. -/
def companionUniversalConstant : ℝ :=
  max 1 (sharpMasterConstant sharpSplitMatrixConstant *
    (sharpBandwidthConstant sharpSplitMatrixConstant +
      3 / sharpBandwidthConstant sharpSplitMatrixConstant))

theorem one_le_companionUniversalConstant : 1 ≤ companionUniversalConstant :=
  le_max_left _ _

/-- The actual unconditional split-base matrix estimate supplies the
only analytic family used by the sharp interpolation assembly. -/
theorem splitMatrixEstimateFamily :
    SplitMatrixEstimateFamily.{u}
      (sharpBandwidthConstant sharpSplitMatrixConstant) sharpSplitMatrixConstant := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hA s hband t ht hlate
  have hband12 : 12 * δ ≤ s.bandwidth :=
    (mul_le_mul_of_nonneg_right
      (sharpBandwidthConstant_ge_twelve one_le_sharpSplitMatrixConstant)
      hdata.delta_nonneg).trans hband
  exact averagedSelectorMatrixEstimate_splitBase hdata hp hunit A hA 0 s hband12 ht.1.le ht.2.le hlate

/-- The full fourth-order variational bound, uniformly over all actual rectangles. -/
theorem variationalEstimate :
    VariationalEstimate.{u} (sharpBandwidthConstant sharpSplitMatrixConstant)
      (sharpMasterConstant sharpSplitMatrixConstant) :=
  variationalEstimate_of_splitMatrixEstimateFamily
    one_le_sharpSplitMatrixConstant splitMatrixEstimateFamily

/-- Cancellation of the complete signed third tensor removes the cubic
contribution before optimization. -/
theorem zeroSkewVariationalEstimate :
    ZeroSkewVariationalEstimate.{u} (sharpBandwidthConstant sharpSplitMatrixConstant)
      (sharpMasterConstant sharpSplitMatrixConstant) :=
  zeroSkewVariationalEstimate_of_splitMatrixEstimateFamily
    one_le_sharpSplitMatrixConstant splitMatrixEstimateFamily

/-- The covariance-sensitive companion rate; positive correlation gap is optional. -/
theorem gapSensitiveCLT : GapSensitiveCLT.{u} companionUniversalConstant :=
  (companion_rates_of_splitMatrixEstimateFamily
    one_le_sharpSplitMatrixConstant splitMatrixEstimateFamily).1

/-- The sharper companion rate under cancellation of all aggregate mixed
third moments. Marginal third-moment cancellation alone is insufficient. -/
theorem zeroSkewCLT : ZeroSkewCLT.{u} companionUniversalConstant :=
  (companion_rates_of_splitMatrixEstimateFamily
    one_le_sharpSplitMatrixConstant splitMatrixEstimateFamily).2

/-- The unrestricted covariance rate, including singular covariance. -/
theorem unrestrictedCLT : UnrestrictedCLT.{u} (2 * companionUniversalConstant) :=
  unrestrictedCLT_of_splitMatrixEstimateFamily
    one_le_sharpSplitMatrixConstant splitMatrixEstimateFamily

theorem gapSensitiveCLTExists : GapSensitiveCLTExists.{u} :=
  ⟨companionUniversalConstant, one_le_companionUniversalConstant, gapSensitiveCLT⟩

theorem zeroSkewCLTExists : ZeroSkewCLTExists.{u} :=
  ⟨companionUniversalConstant, one_le_companionUniversalConstant, zeroSkewCLT⟩

theorem unrestrictedCLTExists : UnrestrictedCLTExists.{u} :=
  ⟨2 * companionUniversalConstant,
    by linarith [one_le_companionUniversalConstant], unrestrictedCLT⟩

/-- All three universal statements hold with constants fixed before the
probability model, dimensions, distributions, and covariance are chosen. -/
theorem companionCLTExists :
    UnrestrictedCLTExists.{u} ∧ GapSensitiveCLTExists.{u} ∧ ZeroSkewCLTExists.{u} :=
  ⟨unrestrictedCLTExists, gapSensitiveCLTExists, zeroSkewCLTExists⟩


/-- A single universal constant works simultaneously for all three rates. -/
theorem companionCLTExists_common : ∃ C : ℝ, 1 ≤ C ∧
    UnrestrictedCLT.{u} C ∧ GapSensitiveCLT.{u} C ∧ ZeroSkewCLT.{u} C := by
  have hK : 0 ≤ companionUniversalConstant := zero_le_one.trans one_le_companionUniversalConstant
  have hK2 : companionUniversalConstant ≤ 2 * companionUniversalConstant := by linarith
  refine ⟨2 * companionUniversalConstant, by linarith [one_le_companionUniversalConstant],
    unrestrictedCLT, ?_, ?_⟩
  · intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hA R
    exact (gapSensitiveCLT μ p n hp hn ξ δ A hdata hunit hA R).trans
      (mul_le_mul_of_nonneg_right hK2
        (le_min zero_le_one (gapRate_nonneg hdata.delta_nonneg
          (zero_le_one.trans (log_exp_mul_nat_ge_one hp)))))
  · intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hA hcancel R
    exact (zeroSkewCLT μ p n hp hn ξ δ A hdata hunit hA hcancel R).trans
      (mul_le_mul_of_nonneg_right hK2
        (le_min zero_le_one (zeroSkewRate_nonneg hdata.delta_nonneg
          (zero_le_one.trans (log_exp_mul_nat_ge_one hp)))))

end
end RectangleCLT.Companion
