import RectangleCLT.CombinedMain

/-! A genuine scalar Berry--Esseen bound supplied by the checked bounded
rectangle CLT. This auxiliary is used for exponentially tilted scalar
arrays; no independent Berry--Esseen estimate is assumed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def scalarBerryEsseenConstant : ℝ := 3 * combinedCLTConstant

theorem scalarBerryEsseenConstant_pos : 0 < scalarBerryEsseenConstant := by
  unfold scalarBerryEsseenConstant
  have h := combinedCLTConstant_ge_one
  linarith

/-- A centered independent scalar array with unit sum variance has a
uniform rectangle error of order its maximum increment, with an absolute
constant and no logarithm of the sample size. -/
theorem scalarBerryEsseenRectangle
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 1 ≤ n) (ξ : Fin n → Ω → Vector 1) {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (R : Rect 1) :
    rectangleError μ (sumVector ξ) (1 : Matrix (Fin 1) (Fin 1) ℝ) R ≤
      scalarBerryEsseenConstant * δ := by
  have hfull : BoundedHypotheses μ ξ δ 1 :=
    { measurable := hdata.measurable
      independent := hdata.independent
      centered := hdata.centered
      bounded := hdata.bounded
      delta_nonneg := hdata.delta_nonneg
      b_pos := by norm_num
      b_le_one := le_rfl
      unit_diagonal := hunit
      spectral_lower := by
        intro v
        simp only [Fin.sum_univ_one, hunit, one_pow, one_mul, mul_one]
        nlinarith only [sq_nonneg (v 0)] }
  have hfactor : (1 : Matrix (Fin 1) (Fin 1) ℝ) *
      (1 : Matrix (Fin 1) (Fin 1) ℝ).transpose = covariance μ (sumVector ξ) := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.one_apply, ite_true, hunit]
  have hraw := boundedRectangleCLT μ 1 n (by norm_num) hn ξ δ 1
    (1 : Matrix (Fin 1) (Fin 1) ℝ) hfull hfactor R
  have hC : 0 ≤ combinedCLTConstant := zero_le_one.trans combinedCLTConstant_ge_one
  have hthird := hdata.gamma3_le_delta hunit
  have hfourth := hdata.gamma4_le_delta_sq hunit
  have hsqrt : Real.sqrt (gamma4 μ ξ) ≤ δ := by
    have hh := Real.sqrt_le_sqrt hfourth
    simpa only [Real.sqrt_sq hdata.delta_nonneg] using hh
  have hL : dimensionLog 1 = 1 := by
    simp only [dimensionLog, Nat.cast_one, mul_one, Real.log_exp]
  have hrate : boundedRate μ ξ δ 1 ≤ 3 * δ := by
    simp only [boundedRate, hL, Real.sqrt_one, mul_one, one_pow, div_one]
    linarith
  calc
    _ ≤ combinedCLTConstant * min 1 (boundedRate μ ξ δ 1) := hraw
    _ ≤ combinedCLTConstant * (boundedRate μ ξ δ 1) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hC
    _ ≤ combinedCLTConstant * (3 * δ) := mul_le_mul_of_nonneg_left hrate hC
    _ = _ := by unfold scalarBerryEsseenConstant; ring


/-- The scalar CDF form, with the genuine standard normal law. The sum
may have atoms, and the endpoint is the closed half-line. -/
theorem scalarBerryEsseenCDF
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 1 ≤ n) (ξ : Fin n → Ω → Vector 1) {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (x : ℝ) :
    |(μ.map (fun ω => sumVector ξ ω 0)).real (Set.Iic x) -
      (gaussianReal 0 1).real (Set.Iic x)| ≤ scalarBerryEsseenConstant * δ := by
  let R : Rect 1 :=
    { interval := fun _ => Set.Iic x
      ordConnected := fun _ => Set.ordConnected_Iic
      measurable := fun _ => measurableSet_Iic }
  have hR : R.carrier = (fun v : Vector 1 => v 0) ⁻¹' Set.Iic x := by
    ext v
    simp only [Rect.carrier, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_preimage, Set.mem_Iic, R]
    simp only [Fin.forall_fin_one]
  have hsum : Measurable (fun ω => sumVector ξ ω 0) := by
    exact (measurable_pi_apply 0).comp (Finset.measurable_sum _ (fun i _ => hdata.measurable i))
  have hG := gaussianLaw_map_eval_eq_standard
    (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 (by simp)
  have hraw := scalarBerryEsseenRectangle μ hn ξ hdata hunit R
  unfold rectangleError at hraw
  rw [hR] at hraw
  have hGN : (gaussianReal 0 1).real (Set.Iic x) =
      (gaussianLaw (1 : Matrix (Fin 1) (Fin 1) ℝ)).real
        ((fun v : Vector 1 => v 0) ⁻¹' Set.Iic x) := by
    rw [← hG]
    exact congrArg ENNReal.toReal
      (Measure.map_apply (measurable_pi_apply (0 : Fin 1)) measurableSet_Iic)
  rw [hGN]
  simpa only [Measure.real, Measure.map_apply hsum measurableSet_Iic,
    Set.preimage_preimage] using hraw

end

end RectangleCLT
