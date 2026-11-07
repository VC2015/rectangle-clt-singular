import RectangleCLTCompanion.SplitV4.SlepianLaw
import RectangleCLTCompanion.SplitV4.NormalizedSeededEndpoints

/-! Exact joining of the two actual interpolation stages. This file
contains only law identification and the triangle inequality; no desired
initialization or derivative estimate is an assumption. -/

open MeasureTheory

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem integral_normalizedSeeded_zero_eq_directSlepianExpectation
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ y, s.F y ∂normalizedSeededInterpolationLaw μ ξ A ε 0) =
      directSlepianExpectation s μ ξ A (seededInitializationTime ε) := by
  rw [normalizedSeededInterpolationLaw_zero μ ξ hξ A hε]
  exact integral_map
    (measurable_directSlepianPoint ξ hξ (seededInitializationTime ε)).aemeasurable
    s.continuous_F.aestronglyMeasurable

theorem integral_normalizedSeeded_one_eq_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ y, s.F y ∂normalizedSeededInterpolationLaw μ ξ A ε 1) = ∫ g, s.F g ∂gaussianLaw A := by
  rw [normalizedSeededInterpolationLaw_one μ ξ A hε]

theorem smoother_gap_le_actual_two_stage_gaps
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ)-(∫ g, s.F g ∂gaussianLaw A)| ≤
      |(∫ ω, s.F (sumVector ξ ω) ∂μ)-directSlepianExpectation s μ ξ A (seededInitializationTime ε)|+
      |(∫ y, s.F y ∂normalizedSeededInterpolationLaw μ ξ A ε 1)-
        (∫ y, s.F y ∂normalizedSeededInterpolationLaw μ ξ A ε 0)| := by
  rw [integral_normalizedSeeded_one_eq_gaussian s μ ξ A hε,
    integral_normalizedSeeded_zero_eq_directSlepianExpectation s μ ξ hξ A hε,
    abs_sub_comm (∫ g, s.F g ∂gaussianLaw A)
      (directSlepianExpectation s μ ξ A (seededInitializationTime ε))]
  exact abs_sub_le _ _ _

end
end RectangleCLT.Companion.SplitV4
