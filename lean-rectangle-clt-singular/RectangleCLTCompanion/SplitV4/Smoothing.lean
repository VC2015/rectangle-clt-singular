import RectangleCLTCompanion.SharpEndpoint
import RectangleCLTCompanion.Rates
import RectangleCLTCompanion.RectangleDistance

/-!
# The current manuscript's smoothing reduction

This file specializes the existing atom-safe endpoint transfer to the
unrestricted covariance setting. The comparison term is the actual supremum
of logistic smooth-expectation discrepancies over all finite face thresholds.
Its finiteness follows from genuine integrability and the smoother's values
in `[0,1]`. The conclusion concerns the full measurable rectangle class,
including mixed endpoints, empty rectangles, and unbounded rectangles.

The reduction proves Lemma 2's conclusion by the existing logarithmic
concentration proof. It does not prove the separate intrinsic concentration
claims in Lemma 1 or the revised Appendix C argument.
-/

open MeasureTheory

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- Actual discrepancy for the logistic smoother at one pair of finite
coordinate thresholds. The lower thresholds need not lie below the upper
thresholds. -/
def closedBoxSmoothingGap {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (h : ℝ) (hh : 0 < h) (bounds : Vector p × Vector p) : ℝ :=
  let s := FaceSmoother.closedBox bounds.1 bounds.2 h hh
  |(∫ ω, s.F (W ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)|

/-- The current manuscript's `M_h`, as a real supremum over all finite
thresholds, rather than an assumed bound for those discrepancies. -/
def smoothingDiscrepancy {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (h : ℝ) (hh : 0 < h) : ℝ :=
  sSup (Set.range (closedBoxSmoothingGap μ W A h hh))

/-- Bounded smooth expectations are genuine Bochner integrals whenever the
underlying random vector is measurable. -/
theorem integrable_smoother_comp {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) :
    Integrable (fun ω => s.F (W ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (s.continuous_F.measurable.comp hW).aestronglyMeasurable
  exact ae_of_all _ (fun ω => s.norm_F_le_one _)

theorem smoother_mean_mem_Icc {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) :
    (∫ ω, s.F (W ω) ∂μ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun ω => (s.F_pos (W ω)).le)
  · have hi := integral_mono (integrable_smoother_comp s μ W hW)
      (integrable_const (1 : ℝ)) (fun ω => s.F_le_one (W ω))
    simpa using hi

theorem closedBoxSmoothingGap_le_one
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 < h)
    (bounds : Vector p × Vector p) :
    closedBoxSmoothingGap μ W A h hh bounds ≤ 1 := by
  let s := FaceSmoother.closedBox bounds.1 bounds.2 h hh
  have hm := smoother_mean_mem_Icc s μ W hW
  have hg := smoother_mean_mem_Icc s (gaussianLaw A) id measurable_id
  change |(∫ ω, s.F (W ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤ 1
  apply abs_le.mpr
  constructor <;> linarith [hm.1, hm.2, hg.1, hg.2]

theorem smoothingGaps_bddAbove
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 < h) :
    BddAbove (Set.range (closedBoxSmoothingGap μ W A h hh)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨bounds, rfl⟩
  exact closedBoxSmoothingGap_le_one μ W hW A h hh bounds

theorem smoothingGaps_nonempty
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 < h) :
    (Set.range (closedBoxSmoothingGap μ W A h hh)).Nonempty :=
  ⟨_, ⟨(0, 0), rfl⟩⟩

theorem closedBoxSmoothingGap_le_smoothingDiscrepancy
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 < h)
    (bounds : Vector p × Vector p) :
    closedBoxSmoothingGap μ W A h hh bounds ≤ smoothingDiscrepancy μ W A h hh :=
  le_csSup (smoothingGaps_bddAbove μ W hW A h hh) ⟨bounds, rfl⟩

theorem smoothingDiscrepancy_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 < h) :
    0 ≤ smoothingDiscrepancy μ W A h hh :=
  (abs_nonneg _).trans
    (closedBoxSmoothingGap_le_smoothingDiscrepancy μ W hW A h hh (0, 0))

theorem smoothingDiscrepancy_le_one
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 < h) :
    smoothingDiscrepancy μ W A h hh ≤ 1 := by
  apply csSup_le (smoothingGaps_nonempty μ W A h hh)
  rintro x ⟨bounds, rfl⟩
  exact closedBoxSmoothingGap_le_one μ W hW A h hh bounds

/-- The supremum contract and the uniform smooth-expectation contract are
equivalent. Finiteness has already been proved from the actual smoothers. -/
theorem smoothingDiscrepancy_le_iff
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 < h) (E : ℝ) :
    smoothingDiscrepancy μ W A h hh ≤ E ↔
      ∀ lo hi : Vector p, let s := FaceSmoother.closedBox lo hi h hh
        |(∫ ω, s.F (W ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤ E := by
  constructor
  · intro hE lo hi
    exact (closedBoxSmoothingGap_le_smoothingDiscrepancy μ W hW A h hh (lo, hi)).trans hE
  · intro hgap
    apply csSup_le (smoothingGaps_nonempty μ W A h hh)
    rintro x ⟨⟨lo, hi⟩, rfl⟩
    exact hgap lo hi

/-- A uniform smooth-comparison bound gives the all-rectangle smoothing
estimate. The constant is fixed before dimensions and probability models.
The premise bounds only the smooth expectations; it does not assume the
desired probability estimate. -/
theorem rectangleError_le_uniform_smoothing_add_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (h : ℝ) (hh : 0 < h) (hband : δ ≤ h) (E : ℝ)
    (hgap : ∀ lo hi : Vector p, let s := FaceSmoother.closedBox lo hi h hh
      |(∫ ω, s.F (sumVector ξ ω) ∂μ) - (∫ z, s.F z ∂gaussianLaw A)| ≤ E)
    (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤
      E + sharpEndpointConstant * h * Real.sqrt (dimensionLog p) * dimensionLog p := by
  apply (rectangleError_le_smoother_gap_add_sharp_endpoint
    hdata hp hunit A hA h hh hband E hgap R).trans
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left (kappa_le _ _)
    (mul_nonneg (mul_nonneg sharpEndpointConstant_nonneg hh.le) (Real.sqrt_nonneg _))

/-- Current Lemma 2, with the actual supremum `M_h` and the full rectangle
distance `rho`. The product `sqrt L * L` is exactly `L^(3/2)` for `L≥0`.
No positive covariance eigenvalue or positive pair gap is required. -/
theorem rectangleDistance_le_smoothingDiscrepancy_add_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (h : ℝ) (hh : 0 < h) (hband : δ ≤ h) :
    rectangleDistance μ (sumVector ξ) A ≤
      smoothingDiscrepancy μ (sumVector ξ) A h hh +
        sharpEndpointConstant * h * Real.sqrt (dimensionLog p) * dimensionLog p := by
  apply rectangleDistance_le
  intro R
  apply rectangleError_le_uniform_smoothing_add_endpoint hdata hp hunit A hA h hh hband
    (smoothingDiscrepancy μ (sumVector ξ) A h hh) _ R
  intro lo hi
  exact closedBoxSmoothingGap_le_smoothingDiscrepancy
    μ (sumVector ξ) hdata.measurable_sum A h hh (lo, hi)

end
end RectangleCLT.Companion.SplitV4
