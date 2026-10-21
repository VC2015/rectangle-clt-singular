import RectangleCLTCompanion.LowerProductTilt
import RectangleCLTCompanion.LowerTiltTaylor
import RectangleCLTCompanion.LowerTiltedBerryEsseen

/-! Exact strict-tail changes of measure for the finite-product lower
construction. This identity holds for lattice laws without a correction
at the threshold. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

def lowerScalarSum {n : ℕ} (z : Fin n → ℝ) : ℝ := ∑ i, z i

theorem lowerScalarSum_measurable (n : ℕ) : Measurable (lowerScalarSum (n := n)) :=
  Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

theorem lowerScalarTilt_density (B t : ℝ) (n : ℕ) (z : Fin n → ℝ) :
    (∏ i : Fin n, Real.exp (t * z i) / mgf id (lowerTwoPointLaw B) t) =
      Real.exp (t * lowerScalarSum z - n * cgf id (lowerTwoPointLaw B) t) := by
  have hm : 0 < mgf id (lowerTwoPointLaw B) t := by
    rw [lowerTwoPointLaw_mgf]
    exact div_pos (lowerTiltNormalizer_pos B t) (lowerTwoPointDenominator_pos B)
  rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Real.exp_sub, Real.exp_nat_mul, cgf, Real.exp_log hm]
  congr 2
  exact (Finset.mul_sum Finset.univ (fun i => z i) t).symm

theorem lowerScalarTiltedArrayLaw_eq_expDensity (B t : ℝ) (n : ℕ) :
    lowerScalarTiltedArrayLaw B t n = (lowerScalarArrayLaw B n).withDensity
      (fun z => ENNReal.ofReal
        (Real.exp (t * lowerScalarSum z - n * cgf id (lowerTwoPointLaw B) t))) := by
  rw [lowerScalarTiltedArrayLaw_eq_withDensity]
  congr 1
  funext z
  rw [lowerScalarTilt_density]

theorem lowerScalarArrayLaw_eq_inverse_expDensity (B t : ℝ) (n : ℕ) :
    lowerScalarArrayLaw B n = (lowerScalarTiltedArrayLaw B t n).withDensity
      (fun z => ENNReal.ofReal
        (Real.exp (-t * lowerScalarSum z + n * cgf id (lowerTwoPointLaw B) t))) := by
  rw [lowerScalarTiltedArrayLaw_eq_expDensity, ← withDensity_mul _
    (((measurable_const.mul (lowerScalarSum_measurable n)).sub measurable_const).exp.ennreal_ofReal)
    (((measurable_const.mul (lowerScalarSum_measurable n)).add measurable_const).exp.ennreal_ofReal)]
  have hh :
      (fun z : Fin n → ℝ => ENNReal.ofReal
        (Real.exp (t * lowerScalarSum z - n * cgf id (lowerTwoPointLaw B) t))) *
      (fun z : Fin n → ℝ => ENNReal.ofReal
        (Real.exp (-t * lowerScalarSum z + n * cgf id (lowerTwoPointLaw B) t))) = 1 := by
    funext z
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    ring_nf
    simp
  rw [hh, withDensity_one]

theorem lowerScalarArrayLaw_strict_tail_tilt (B t a : ℝ) (n : ℕ) :
    (lowerScalarArrayLaw B n).real {z | a < lowerScalarSum z} =
      Real.exp (n * cgf id (lowerTwoPointLaw B) t - t * a) *
        ∫ z, lowerStrictTailWeight t (lowerScalarSum z - a)
          ∂lowerScalarTiltedArrayLaw B t n := by
  have hs : MeasurableSet {z : Fin n → ℝ | a < lowerScalarSum z} :=
    measurableSet_lt measurable_const (lowerScalarSum_measurable n)
  rw [← integral_indicator_one hs, lowerScalarArrayLaw_eq_inverse_expDensity B t n,
    integral_withDensity_eq_integral_toReal_smul
      (((measurable_const.mul (lowerScalarSum_measurable n)).add measurable_const).exp.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul,
    lowerStrictTailWeight]
  by_cases hz : a < lowerScalarSum z
  · have hzin : z ∈ {z : Fin n → ℝ | a < lowerScalarSum z} := hz
    rw [Set.indicator_of_mem hzin]
    simp only [Pi.one_apply, mul_one, sub_pos.mpr hz, if_true]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp [hz, not_lt.mpr (sub_nonpos.mpr (le_of_not_gt hz))]

def lowerScalarToTiltedRows (B t : ℝ) {n : ℕ} (z : Fin n → ℝ) : Fin n → Vector 1 :=
  fun i => lowerTiltedRowMap B t (z i)

theorem lowerScalarToTiltedRows_measurePreserving (B t : ℝ) (n : ℕ) :
    MeasurePreserving (lowerScalarToTiltedRows B t)
      (lowerScalarTiltedArrayLaw B t n) (lowerTiltedArrayLaw B t n) := by
  exact measurePreserving_pi (fun _ : Fin n => lowerTwoPointTilt B t)
    (fun _ => lowerTiltedRowLaw B t)
    (fun _ => ⟨lowerTiltedRowMap_measurable B t, rfl⟩)

theorem lowerTiltedStandardizedSum_scalar (B t : ℝ) {n : ℕ} (z : Fin n → ℝ) :
    lowerTiltedStandardizedSum B t (lowerScalarToTiltedRows B t z) =
      lowerTiltedNormalization B t n * (lowerScalarSum z - n * lowerTiltMean B t) := by
  simp only [lowerTiltedStandardizedSum, sumVector, Finset.sum_apply,
    lowerTiltedNormalizedRows, Pi.smul_apply, smul_eq_mul, lowerTiltedRawRows,
    lowerScalarToTiltedRows, lowerTiltedRowMap]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [lowerScalarSum]

theorem lowerScalarArrayLaw_strict_tail_standardized {B : ℝ} (hB : 1 ≤ B)
    (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (lowerScalarArrayLaw B n).real
        {z | n * lowerTiltMean B t < lowerScalarSum z} =
      Real.exp (n * cgf id (lowerTwoPointLaw B) t - t * (n * lowerTiltMean B t)) *
        ∫ z, lowerStrictTailWeight
          (t * (Real.sqrt n * Real.sqrt (lowerTiltVariance B t)))
          (lowerTiltedStandardizedSum B t z) ∂lowerTiltedArrayLaw B t n := by
  have hBp : 0 < B := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hden : 0 < Real.sqrt n * Real.sqrt (lowerTiltVariance B t) :=
    mul_pos (Real.sqrt_pos.mpr hnpos) (Real.sqrt_pos.mpr (lowerTiltVariance_pos hBp t))
  rw [lowerScalarArrayLaw_strict_tail_tilt]
  congr 1
  have hp := lowerScalarToTiltedRows_measurePreserving B t n
  have hm := integral_map (μ := lowerScalarTiltedArrayLaw B t n) hp.measurable.aemeasurable
    (((lowerStrictTailWeight_measurable
      (t * (Real.sqrt n * Real.sqrt (lowerTiltVariance B t)))).comp
      (lowerTiltedStandardizedSum_measurable hB t n)).aestronglyMeasurable)
  rw [hp.map_eq] at hm
  simp only [Function.comp_apply] at hm
  rw [hm]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  rw [lowerTiltedStandardizedSum_scalar]
  have hnormpos : 0 < lowerTiltedNormalization B t n := one_div_pos.mpr hden
  have hsign : 0 < lowerTiltedNormalization B t n *
      (lowerScalarSum z - n * lowerTiltMean B t) ↔
        0 < lowerScalarSum z - n * lowerTiltMean B t := mul_pos_iff_of_pos_left hnormpos
  unfold lowerStrictTailWeight
  simp only [hsign]
  split_ifs
  · congr 1
    unfold lowerTiltedNormalization
    field_simp
    <;> ring
  · rfl

end

end RectangleCLT.Companion
