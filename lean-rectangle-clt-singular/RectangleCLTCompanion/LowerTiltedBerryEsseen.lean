import RectangleCLTCompanion.LowerTiltedArray
import RectangleCLTCompanion.WeightedTailComparison
import RectangleCLT.ScalarBerryEsseen

/-! An actual Berry--Esseen estimate under the tilted lower-construction
product measure, obtained by applying the checked scalar specialization
of the main rectangle CLT to the centered, standardized tilted array. -/

open MeasureTheory ProbabilityTheory Set

namespace RectangleCLT.Companion

noncomputable section

def lowerTiltedStandardizedSum (B t : ℝ) {n : ℕ} (z : Fin n → Vector 1) : ℝ :=
  sumVector (lowerTiltedNormalizedRows B t) z 0

theorem lowerTiltedStandardizedSum_measurable {B : ℝ} (hB : 1 ≤ B)
    (t : ℝ) (n : ℕ) :
    Measurable (lowerTiltedStandardizedSum (n := n) B t) := by
  exact (measurable_pi_apply 0).comp
    (Finset.measurable_sum _ (fun i _ =>
      (lowerTiltedNormalizedRows_boundedIndependent hB t n).measurable i))

theorem lowerTiltedStandardizedSum_cdf {B : ℝ} (hB : 1 ≤ B)
    (t : ℝ) {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    |((lowerTiltedArrayLaw B t n).map (lowerTiltedStandardizedSum B t)).real (Iic x) -
      (gaussianReal 0 1).real (Iic x)| ≤
        scalarBerryEsseenConstant * (lowerTiltedNormalization B t n * (2 * B)) := by
  apply scalarBerryEsseenCDF (lowerTiltedArrayLaw B t n) hn
    (lowerTiltedNormalizedRows B t)
    (lowerTiltedNormalizedRows_boundedIndependent hB t n)
  intro j
  rw [lowerTiltedNormalizedRows_covariance hB t hn]
  simp

/-- This is an unconditional estimate on genuine tilted probabilities.
In particular, no moderate-deviation approximation occurs in its inputs. -/
theorem lowerTiltedStandardizedSum_strict_weighted_tail {B : ℝ} (hB : 1 ≤ B)
    (t : ℝ) {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    |(∫ z, lowerStrictTailWeight s (lowerTiltedStandardizedSum B t z)
        ∂lowerTiltedArrayLaw B t n) -
      ∫ y, lowerStrictTailWeight s y ∂gaussianReal 0 1| ≤
        2 * (scalarBerryEsseenConstant * (lowerTiltedNormalization B t n * (2 * B))) := by
  let μ := (lowerTiltedArrayLaw B t n).map (lowerTiltedStandardizedSum B t)
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_map (lowerTiltedStandardizedSum_measurable hB t n).aemeasurable
  have hε : 0 ≤ scalarBerryEsseenConstant * (lowerTiltedNormalization B t n * (2 * B)) := by
    have hC := scalarBerryEsseenConstant_pos.le
    have hnorm : 0 ≤ lowerTiltedNormalization B t n := by
      unfold lowerTiltedNormalization
      positivity
    positivity
  have hh := lower_strict_weighted_tail_comparison μ (gaussianReal 0 1) hε hs
    (lowerTiltedStandardizedSum_cdf hB t hn)
  rw [integral_map (lowerTiltedStandardizedSum_measurable hB t n).aemeasurable
    (lowerStrictTailWeight_measurable s).aestronglyMeasurable] at hh
  exact hh

end

end RectangleCLT.Companion
