import RectangleCLTCompanion.SplitV4.NuclearSelectorMatrixInterface

/-!
# The intrinsic boundary coefficient in the selector matrix estimate

Frozen main source: B.4, lines 5051–5070; proof 5072–5417. The archived
nuclear-norm and signed-trace argument permits a variable concentration
constant. Rescaling that constant, while retaining the actual dimension
parameter in every threshold and seed-scale condition, yields the printed
factor `h * κ * L`. No matrix, trace or derivative bound is an input here.
-/

namespace RectangleCLTArxivV1

set_option autoImplicit false

open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- Actual translated rectangle-layer concentration with an intrinsic coefficient. -/
def IntrinsicRectangleConcentration {p : ℕ} (μ : Measure (Vector p)) (C₀ δ κ : ℝ) : Prop :=
  ∀ t : FaceSmoother p, ∀ z : Vector p, ∀ s : ℝ, 0 < s →
    μ.real {x | x + z ∈ t.boundaryLayer s} ≤ C₀ * κ * (s + δ)

/-- The intrinsic concentrated-base premise in support coordinates. -/
def IntrinsicPolyhedralConcentration {m r : ℕ} (μ : Measure (Vector r))
    (u : Fin m → Vector r) (C₀ δ κ : ℝ) : Prop :=
  ∀ a : Vector m, ∀ s : ℝ, 0 < s →
    μ.real (gaussianPolyhedronLayer u a s) ≤ C₀ * κ * (s + δ)

theorem intrinsicPolyhedralConcentration_rescale {m r : ℕ}
    (μ : Measure (Vector r)) (u : Fin m → Vector r) {C₀ δ κ L : ℝ}
    (hL : 0 < L) (hc : IntrinsicPolyhedralConcentration μ u C₀ δ κ) :
    PolyhedralBaseConcentration μ u (C₀ * κ / Real.sqrt L) δ L := by
  have hroot : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  intro a s hs
  have hh := hc a s hs
  convert hh using 1
  field_simp [hroot]

/-- The nuclear matrix estimate in support coordinates, for the complete
signed family of unit normals in the paper's rectangle representation. -/
theorem logistic_matrix_estimate_intrinsic {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    {C₀ δ κ L h σ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hh : 0 < h) (hδh : δ ≤ h) (hσ : 0 ≤ σ)
    (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : IntrinsicPolyhedralConcentration μ u C₀ δ κ) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore u a h σ α x) ∂μ) ≤
        logisticMatrixConstant ^ (k + 1) * C₀ * (h * L * κ) := by
  have hLm : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
  have hLp : 0 < L := by linarith only [hLm, hL]
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLp
  have hb := logistic_matrix_estimate_nonneg_scale hm μ u a hu opposite hopp
    (div_pos (mul_pos hC₀ hκ) hroot) hδ hh hδh hσ hL hscale
    (intrinsicPolyhedralConcentration_rescale μ u hLp hc) k hk
  convert hb using 1
  field_simp [hroot.ne']
  ring

/-- Expressing the intrinsic coefficient as a concentration constant preserves
all actual layer events and leaves the dimension parameter unchanged. -/
theorem intrinsicRectangleConcentration_rescale {p : ℕ} (hp : 1 ≤ p)
    (μ : Measure (Vector p)) {C₀ δ κ : ℝ}
    (hc : IntrinsicRectangleConcentration μ C₀ δ κ) :
    RectangleBaseConcentration μ (C₀ * κ / Real.sqrt (dimensionLog p)) δ (dimensionLog p) := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hroot : Real.sqrt (dimensionLog p) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL)
  intro t z s hs
  have hh := hc t z s hs
  convert hh using 1
  field_simp [hroot]

/-- The nuclear-norm assertion of B.4 for the actual Gaussian score matrices.
The integral over the base law and the inner Gaussian expectation are the
ones in the paper; the concentration coefficient is retained as `κ`. -/
theorem selector_nuclear_bound_intrinsic {p r : ℕ} (hp : 1 ≤ p)
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : ∀ j, vectorNormSq (A j) = 1)
    {C₀ δ κ σ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδh : δ ≤ s.bandwidth) (hσ : 0 ≤ σ)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hc : IntrinsicRectangleConcentration μ C₀ δ κ) (k : ℕ) (hk : 1 ≤ k) :
    (∫ v, ∑ α : Fin k → Face p,
      symmetricNuclearNorm (selectorGaussianScore s (σ • A) id α v) ∂μ) ≤
        logisticMatrixConstant ^ (k + 1) * C₀ * (s.bandwidth * dimensionLog p * κ) := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hroot : 0 < Real.sqrt (dimensionLog p) := Real.sqrt_pos.mpr hL
  have hb := selector_nuclear_bound_of_rectangle_concentration hp μ s A hA
    (div_pos (mul_pos hC₀ hκ) hroot) hδ hδh hσ hscale
    (intrinsicRectangleConcentration_rescale hp μ hc) k hk
  convert hb using 1
  field_simp [hroot.ne']
  ring

/-- This coefficient depends only on the fixed boundary constant, rather
than on `κ`, the dimension, the derivative order or either probability law. -/
noncomputable def intrinsicMatrixConstant (C₀ : ℝ) : ℝ :=
  logisticMatrixConstant * max 1 C₀

theorem intrinsicMatrixConstant_ge_one (C₀ : ℝ) : 1 ≤ intrinsicMatrixConstant C₀ :=
  one_le_mul_of_one_le_of_one_le logisticMatrixConstant_ge_one (le_max_left _ _)

/-- Absorbing the fixed concentration constant gives the paper's exponential
order dependence, retaining the linear dependence on `κ`. -/
theorem selector_nuclear_bound_intrinsic_paper {p r : ℕ} (hp : 1 ≤ p)
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : ∀ j, vectorNormSq (A j) = 1)
    {C₀ δ κ σ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδh : δ ≤ s.bandwidth) (hσ : 0 ≤ σ)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hc : IntrinsicRectangleConcentration μ C₀ δ κ) (k : ℕ) (hk : 1 ≤ k) :
    (∫ v, ∑ α : Fin k → Face p,
      symmetricNuclearNorm (selectorGaussianScore s (σ • A) id α v) ∂μ) ≤
        intrinsicMatrixConstant C₀ ^ (k + 1) * (s.bandwidth * dimensionLog p * κ) := by
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  exact (selector_nuclear_bound_intrinsic hp μ s A hA hC₀ hκ hδ hδh hσ hscale hc k hk).trans
    (mul_le_mul_of_nonneg_right (logistic_concentration_constant_absorption hC₀.le k)
      (mul_nonneg (mul_nonneg s.bandwidth_pos.le hL) hκ.le))

/-- B.4's actual averaged selector estimate with the intrinsic coefficient.
The fourth-moment contractions may subsequently use this estimate without
replacing the two distinct moment matrices by a common-copy assumption. -/
theorem averagedSelectorMatrixEstimate_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} (hp : 1 ≤ p)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (hA : ∀ j, vectorNormSq (A j) = 1)
    {C₀ δ κ σ : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hδ : 0 ≤ δ) (hδh : δ ≤ s.bandwidth) (hσ : 0 ≤ σ)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hc : IntrinsicRectangleConcentration (ν.map V) C₀ δ κ) :
    AveragedSelectorMatrixEstimate s ν (σ • A) V logisticMatrixConstant
      (C₀ * (s.bandwidth * dimensionLog p * κ)) := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hroot : 0 < Real.sqrt (dimensionLog p) := Real.sqrt_pos.mpr hL
  have hb := averagedSelectorMatrixEstimate_of_rectangle_concentration hp ν V hV s A hA
    (div_pos (mul_pos hC₀ hκ) hroot) hδ hδh hσ hscale
    (intrinsicRectangleConcentration_rescale hp (ν.map V) hc)
  convert hb using 1
  field_simp [hroot.ne']
  ring

end RectangleCLTArxivV1
