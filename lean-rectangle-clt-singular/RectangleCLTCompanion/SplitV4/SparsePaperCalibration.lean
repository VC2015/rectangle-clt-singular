import RectangleCLTCompanion.SplitV4.SparseFamilyCalibration
import RectangleCLTCompanion.SplitV4.SparseMomentRates
import RectangleCLTCompanion.SplitV4.SparseCoordinateNegligible

/-! Original-paper hypotheses imply every primitive actual sparse-family calibration. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def sparseMomentRateConversion (q : ℝ) : ℝ := (2 : ℝ)^(11/2-4/q)
def sparseMomentLowerConstant (q : ℝ) : ℝ := Real.sqrt 2*Real.exp (-1)/sparseMomentRateConversion q

theorem sparseMomentRateConversion_pos (q : ℝ) : 0 < sparseMomentRateConversion q :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem sparseMomentLowerConstant_pos (q : ℝ) : 0 < sparseMomentLowerConstant q :=
  div_pos (by positivity) (sparseMomentRateConversion_pos q)

structure SparsePaperCalibration (q : ℝ) (B : ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  family : SparseFamilyCalibration q B m
  polynomialClass : ∀ᶠ n : ℕ in atTop,
    PolynomialIndependentHypotheses (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
      (familyRawObservations (sparseFamilyParameters q n (m n) (B n))) q (B n)
  rateRatio : Tendsto (fun n : ℕ => sparseMomentLowerRate n (m n) q (B n) /
    familyRareLowerScale (sparseFamilyParameters q n (m n) (B n)) n (m n)) atTop (𝓝 (sparseMomentRateConversion q))
  coordinateNegligible : Tendsto (fun n : ℕ => polynomialCoordinateRate n (m n*m n) (B n) /
    sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)

theorem sparsePaperCalibration {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hRate : Tendsto (fun n => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    SparsePaperCalibration q B m := by
  let ell := fun n : ℕ => Real.log (m n : ℝ)
  have he : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hK' : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop :=
    hK.congr' (Eventually.of_forall (fun n => sparseMomentK_eq n (m n) (hm n) q (B n)))
  have hLog' : Tendsto (fun n => Real.log (sparseLowerK n (ell n) q (B n))/(1+2*ell n)) atTop (𝓝 0) := by
    apply hLog.congr'
    exact Eventually.of_forall (fun n => by
      dsimp only
      rw [sparseMomentK_eq n (m n) (hm n) q (B n), dimensionLog_square (m n) (by have := hm n; omega)])
  have hRate' : Tendsto (fun n => sparseLowerRate n (ell n) q (B n)) atTop (𝓝 0) :=
    hRate.congr' (Eventually.of_forall (fun n => sparseMomentLowerRate_eq n (m n) (hm n) q (B n)))
  have hKh := tendsto_sparseLowerKhat ell B q he hK'
  have hΛ := tendsto_sparseLowerLog_div_ell ell B q he hK' hLog'
  have hd := tendsto_sparseLowerScale_of_paperRate ell B q he hK' hRate'
  have hgood := eventually_sparseFamily_parameters hq hB hmTop hKh hd
  refine ⟨sparseFamilyCalibration hq hB hm hmTop hKh hΛ hd,
    eventually_sparseFamily_polynomialIndependent hq hB hmTop hKh hd, ?_, ?_⟩
  · apply (tendsto_sparseLowerRate_div_scale ell B q he hK').congr'
    filter_upwards [hgood, eventually_ge_atTop 1] with n hn hn1
    rw [sparseMomentLowerRate_eq _ _ (hm n), (sparseFamily_identities hn1 hn).2.2.2]
  · apply (tendsto_sparseLower_coordinate_div_rate ell B q he hK').congr'
    exact Eventually.of_forall (fun n => by
      dsimp only
      rw [sparseMomentLowerRate_eq n (m n) (hm n) q (B n)]
      unfold polynomialCoordinateRate
      rw [dimensionLog_square _ (by have := hm n; omega)])

end
end RectangleCLT.Companion.SplitV4
