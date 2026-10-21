import RectangleCLTCompanion.LowerScalarTilt
import RectangleCLTCompanion.LowerProductArray

/-! A genuine independent triangular array under the tilted product law.
The observations are centered and standardized using their actual tilted
mean and variance. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

def lowerTiltedRowMap (B t : ℝ) (x : ℝ) : Vector 1 :=
  fun _ => x - lowerTiltMean B t

theorem lowerTiltedRowMap_measurable (B t : ℝ) :
    Measurable (lowerTiltedRowMap B t) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_id.sub measurable_const

def lowerTiltedRowLaw (B t : ℝ) : Measure (Vector 1) :=
  (lowerTwoPointTilt B t).map (lowerTiltedRowMap B t)

instance lowerTiltedRowLaw_isProbability (B t : ℝ) :
    IsProbabilityMeasure (lowerTiltedRowLaw B t) := by
  unfold lowerTiltedRowLaw
  exact MeasureTheory.isProbabilityMeasure_map (lowerTiltedRowMap_measurable B t).aemeasurable

theorem lowerTiltedRowLaw_integral (B t : ℝ) (f : Vector 1 → ℝ)
    (hf : Measurable f) :
    (∫ y, f y ∂lowerTiltedRowLaw B t) =
      ∫ x, f (lowerTiltedRowMap B t x) ∂lowerTwoPointTilt B t :=
  integral_map (lowerTiltedRowMap_measurable B t).aemeasurable hf.aestronglyMeasurable

theorem lowerTiltedRowLaw_centered (B t : ℝ) (j : Fin 1) :
    (∫ y, y j ∂lowerTiltedRowLaw B t) = 0 := by
  rw [lowerTiltedRowLaw_integral B t _ (measurable_pi_apply j)]
  exact lowerTwoPointTilt_centered B t

theorem lowerTiltedRowLaw_second (B t : ℝ) (j k : Fin 1) :
    (∫ y, y j * y k ∂lowerTiltedRowLaw B t) = lowerTiltVariance B t := by
  rw [lowerTiltedRowLaw_integral B t _ ((measurable_pi_apply j).mul (measurable_pi_apply k))]
  simpa only [lowerTiltedRowMap, ← pow_two] using lowerTwoPointTilt_variance B t

theorem lowerTiltedRowLaw_bounded {B : ℝ} (hB : 1 ≤ B) (t : ℝ) :
    ∀ᵐ y ∂lowerTiltedRowLaw B t, ‖y‖ ≤ 2 * B := by
  apply (ae_map_iff (lowerTiltedRowMap_measurable B t).aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mpr
  filter_upwards [lowerTwoPointTilt_envelope hB t] with x hx
  apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ 2 * B)).mpr
  intro j
  change |x - lowerTiltMean B t| ≤ 2 * B
  exact (abs_sub x _).trans (by linarith [lowerTiltMean_abs_le hB t])

def lowerTiltedArrayLaw (B t : ℝ) (n : ℕ) : Measure (Fin n → Vector 1) :=
  Measure.pi (fun _ : Fin n => lowerTiltedRowLaw B t)

instance lowerTiltedArrayLaw_isProbability (B t : ℝ) (n : ℕ) :
    IsProbabilityMeasure (lowerTiltedArrayLaw B t n) := by
  constructor
  simp [lowerTiltedArrayLaw, Measure.pi_univ]

def lowerTiltedRawRows {n : ℕ} (i : Fin n) (z : Fin n → Vector 1) : Vector 1 := z i

theorem lowerTiltedRawRows_boundedIndependent {B : ℝ} (hB : 1 ≤ B) (t : ℝ) (n : ℕ) :
    BoundedIndependentHypotheses (lowerTiltedArrayLaw B t n) lowerTiltedRawRows (2 * B) := by
  exact gaussianComponentPi_boundedIndependent (Equiv.refl (Fin n))
    (fun _ => lowerTiltedRowLaw B t) (by linarith)
    (fun _ => lowerTiltedRowLaw_centered B t) (fun _ => lowerTiltedRowLaw_bounded hB t)

theorem lowerTiltedRawRows_second (B t : ℝ) {n : ℕ} (i : Fin n) (j k : Fin 1) :
    (∫ z, lowerTiltedRawRows i z j * lowerTiltedRawRows i z k ∂lowerTiltedArrayLaw B t n) =
      lowerTiltVariance B t := by
  have hm := integral_map (μ := lowerTiltedArrayLaw B t n)
    (measurable_pi_apply i).aemeasurable
    (((measurable_pi_apply j).mul (measurable_pi_apply k)).aestronglyMeasurable)
  change (∫ y, y j * y k ∂(Measure.pi (fun _ : Fin n => lowerTiltedRowLaw B t)).map
    (fun z => z i)) = _ at hm
  rw [gaussianComponentPi_map_eval (fun _ : Fin n => lowerTiltedRowLaw B t) i] at hm
  exact hm.symm.trans (lowerTiltedRowLaw_second B t j k)

def lowerTiltedNormalization (B t : ℝ) (n : ℕ) : ℝ :=
  1 / (Real.sqrt n * Real.sqrt (lowerTiltVariance B t))

def lowerTiltedNormalizedRows {n : ℕ} (B t : ℝ) (i : Fin n)
    (z : Fin n → Vector 1) : Vector 1 :=
  lowerTiltedNormalization B t n • lowerTiltedRawRows i z

theorem lowerTiltedNormalizedRows_boundedIndependent {B : ℝ} (hB : 1 ≤ B)
    (t : ℝ) (n : ℕ) :
    BoundedIndependentHypotheses (lowerTiltedArrayLaw B t n)
      (lowerTiltedNormalizedRows B t) (lowerTiltedNormalization B t n * (2 * B)) := by
  exact (lowerTiltedRawRows_boundedIndependent hB t n).smul_of_nonneg
    (lowerTiltedNormalization B t n) (by unfold lowerTiltedNormalization; positivity)

theorem lowerTiltedNormalizedRows_covariance {B : ℝ} (hB : 1 ≤ B)
    (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    covariance (lowerTiltedArrayLaw B t n) (sumVector (lowerTiltedNormalizedRows B t)) = 1 := by
  classical
  have hBp : 0 < B := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hvpos := lowerTiltVariance_pos hBp t
  have hh := (lowerTiltedRawRows_boundedIndependent hB t n).covariance_sum_smul
    (lowerTiltedNormalization B t n)
  change covariance (lowerTiltedArrayLaw B t n)
    (sumVector (fun i z => lowerTiltedNormalization B t n • lowerTiltedRawRows i z)) = _
  rw [hh]
  ext j k
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [(lowerTiltedRawRows_boundedIndependent hB t n).covariance_sum]
  simp_rw [lowerTiltedRawRows_second]
  have hjk : j = k := Subsingleton.elim _ _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Matrix.one_apply, if_pos hjk, lowerTiltedNormalization,
    div_pow, one_pow, mul_pow, Real.sq_sqrt hnpos.le, Real.sq_sqrt hvpos.le]
  field_simp

end

end RectangleCLT.Companion
