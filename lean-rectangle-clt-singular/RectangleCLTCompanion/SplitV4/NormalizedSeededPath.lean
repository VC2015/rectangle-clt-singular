import RectangleCLTCompanion.SplitV4.SeededGaussianSplit
import RectangleCLTCompanion.SplitV4.DirectRelativeDerivatives
import RectangleCLT.GaussianDerivativeScaling
import RectangleCLT.InterpolationContinuity

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def seededNormalization (ε : ℝ) : ℝ := Real.sqrt (1 + ε)

theorem seededNormalization_pos {ε : ℝ} (hε : 0 ≤ ε) : 0 < seededNormalization ε :=
  Real.sqrt_pos.mpr (by linarith)

theorem seededNormalization_ge_one {ε : ℝ} (hε : 0 ≤ ε) : 1 ≤ seededNormalization ε := by
  have hs := Real.sq_sqrt (show 0 ≤ 1 + ε by linarith)
  have hp := seededNormalization_pos hε
  unfold seededNormalization at hp ⊢
  nlinarith

def seededRescaledSmoother {p : ℕ} (s : FaceSmoother p) (ε : ℝ) (hε : 0 ≤ ε) : FaceSmoother p :=
  s.scaleDown (seededNormalization ε)⁻¹ (inv_pos.mpr (seededNormalization_pos hε))

theorem seededRescaledSmoother_bandwidth {p : ℕ} (s : FaceSmoother p)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (seededRescaledSmoother s ε hε).bandwidth = s.bandwidth * seededNormalization ε := by
  simp only [seededRescaledSmoother, FaceSmoother.scaleDown_bandwidth, div_inv_eq_mul]

theorem seededRescaledSmoother_bandwidth_ge {p : ℕ} (s : FaceSmoother p)
    {ε : ℝ} (hε : 0 ≤ ε) : s.bandwidth ≤ (seededRescaledSmoother s ε hε).bandwidth := by
  rw [seededRescaledSmoother_bandwidth]
  exact le_mul_of_one_le_right s.bandwidth_pos.le (seededNormalization_ge_one hε)

theorem seededRescaledSmoother_F {p : ℕ} (s : FaceSmoother p)
    {ε : ℝ} (hε : 0 ≤ ε) (y : Vector p) :
    (seededRescaledSmoother s ε hε).F y = s.F ((seededNormalization ε)⁻¹ • y) := by
  have hh := s.F_scaleDown (seededNormalization ε)⁻¹
    (inv_pos.mpr (seededNormalization_pos hε)) ((seededNormalization ε)⁻¹ • y)
  simpa only [inv_inv, smul_smul, mul_inv_cancel₀ (seededNormalization_pos hε).ne', one_smul] using hh

theorem seededRescaledSmoother_third {p : ℕ} (s : FaceSmoother p)
    {ε : ℝ} (hε : 0 ≤ ε) (y : Vector p) (j k l : Fin p) :
    (seededRescaledSmoother s ε hε).mixedThirdDerivativeF y j k l =
      s.mixedThirdDerivativeF ((seededNormalization ε)⁻¹ • y) j k l / (seededNormalization ε) ^ 3 := by
  have hc := (seededNormalization_pos hε).ne'
  have hh := s.mixedThirdDerivativeF_scaleDown (seededNormalization ε)⁻¹
    (inv_pos.mpr (seededNormalization_pos hε)) ((seededNormalization ε)⁻¹ • y) j k l
  simp only [inv_inv, smul_smul, mul_inv_cancel₀ hc, one_smul] at hh
  change s.mixedThirdDerivativeF ((seededNormalization ε)⁻¹ • y) j k l =
    (seededRescaledSmoother s ε hε).mixedThirdDerivativeF y j k l /
      ((seededNormalization ε)⁻¹) ^ 3 at hh
  rw [inv_pow, div_inv_eq_mul] at hh
  exact (eq_div_iff (pow_ne_zero 3 hc)).mpr hh.symm

theorem seededRescaledSmoother_relativeCubic {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    {ε : ℝ} (hε : 0 ≤ ε) (y : Vector p) :
    relativeCubicContraction (seededRescaledSmoother s ε hε) μ ξ y =
      relativeCubicContraction s μ ξ ((seededNormalization ε)⁻¹ • y) / (seededNormalization ε) ^ 3 := by
  unfold relativeCubicContraction
  simp only [seededRescaledSmoother_third s hε, mul_div_assoc, Finset.sum_div]

def normalizedSeededInterpolationLaw {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) (ε t : ℝ) :
    Measure (Vector p) :=
  (seededInterpolationLaw μ ξ A ε t).map (fun y => (seededNormalization ε)⁻¹ • y)

theorem integral_normalizedSeeded_test {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    (∫ y, s.F y ∂normalizedSeededInterpolationLaw μ ξ A ε t) =
      ∫ y, (seededRescaledSmoother s ε hε).F y ∂seededInterpolationLaw μ ξ A ε t := by
  rw [normalizedSeededInterpolationLaw, integral_map (by fun_prop) s.continuous_F.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ (fun y => (seededRescaledSmoother_F s hε y).symm))

theorem continuous_relativeCubicContraction {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) :
    Continuous (relativeCubicContraction s μ ξ) := by
  unfold relativeCubicContraction
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  exact continuous_finset_sum _ (fun l _ => continuous_const.mul (s.continuous_thirdDerivative j k l))

theorem integral_normalizedSeeded_cubic {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    (∫ y, relativeCubicContraction (seededRescaledSmoother s ε hε) μ ξ y
      ∂seededInterpolationLaw μ ξ A ε t) =
      (∫ y, relativeCubicContraction s μ ξ y ∂normalizedSeededInterpolationLaw μ ξ A ε t) /
        (seededNormalization ε) ^ 3 := by
  rw [normalizedSeededInterpolationLaw, integral_map (by fun_prop)
    (continuous_relativeCubicContraction s μ ξ).aestronglyMeasurable, ← integral_div]
  exact integral_congr_ae (ae_of_all _ (fun y => seededRescaledSmoother_relativeCubic s μ ξ hε y))

theorem continuousOn_seeded_test_expectation
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ) (ε : ℝ) (x : Vector p) :
    ContinuousOn (s.seededSelectorHeatExpectation μ ξ A ε x) (Icc (0 : ℝ) 1) := by
  apply continuousOn_of_dominated (bound := fun _ => (1 : ℝ))
  · intro t ht
    exact ((s.measurable_selectorHeatExpectation_x μ ξ hξ A t).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable
  · intro t ht
    exact ae_of_all _ (fun z => s.norm_selectorHeatExpectation_le_one μ ξ A (x + z) ht.1 ht.2)
  · exact integrable_const _
  · exact ae_of_all _ (fun z => s.continuousOn_selectorHeatExpectation μ ξ hξ A (x + z))

end

end RectangleCLT.Companion.SplitV4
