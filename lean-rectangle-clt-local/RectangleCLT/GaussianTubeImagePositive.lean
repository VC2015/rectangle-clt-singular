import RectangleCLT.GaussianTubeEvents
import RectangleCLT.GaussianTubeDifferential

/-! Positivity and measurability of actual augmented tube images. -/

open MeasureTheory

namespace RectangleCLT.GaussianTube

/-- Every augmented-map output has positive active exponential coordinates,
independently of the domain, when the exponential clock is positive. -/
theorem image_map_subset_positive_tube {p q : ℕ}
    (N : Matrix (Fin p) (Fin q) ℝ) (h : ℝ) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (a : Fin q → ℝ) (D : Set (Coordinates p q)) :
    map N h E₀ a '' D ⊆ {y : Coordinates p q | ∀ i, 0 < tube y i} := by
  rintro y ⟨w, _hw, rfl⟩ i
  exact tube_map_pos N h hE₀ a w i

/-- The augmented map is a measurable embedding when its active Gram matrix
is invertible. This follows from actual continuity and injectivity. -/
theorem measurableEmbedding_map {p q : ℕ}
    (N : Matrix (Fin p) (Fin q) ℝ) {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0)
    (hd : IsUnit (N.transpose * N).det) (a : Fin q → ℝ) :
    MeasurableEmbedding (map N h E₀ a) :=
  (contDiff_map N h E₀ a).continuous.measurableEmbedding (map_injective N hh hE₀ hd a)

theorem measurableSet_map_image {p q : ℕ}
    (N : Matrix (Fin p) (Fin q) ℝ) {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0)
    (hd : IsUnit (N.transpose * N).det) (a : Fin q → ℝ)
    {D : Set (Coordinates p q)} (hD : MeasurableSet D) :
    MeasurableSet (map N h E₀ a '' D) :=
  (measurableEmbedding_map N hh hE₀ hd a).measurableSet_image.mpr hD

/-- The actual face-tube source image lies inside the positive active region.
No Gram nondegeneracy is needed for this inclusion. -/
theorem image_sourceDomain_subset_positive_tube {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {E₀ : ℝ} (hE₀ : 0 < E₀) (e : Face p → ℝ) (width : ℝ) :
    map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
      sourceDomain S s A r E₀ e width ⊆
        {y : Coordinates p q | ∀ i, 0 < tube y i} :=
  image_map_subset_positive_tube (normalMatrix S A) s.bandwidth hE₀
    (activeOffsets S s r) _

/-- The image of the actual face-tube source is measurable under the same
active-Gram invertibility assumption used by the change of variables. -/
theorem measurableSet_image_sourceDomain {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {E₀ : ℝ} (hE₀ : 0 < E₀) (e : Face p → ℝ) (width : ℝ)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    MeasurableSet (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
      sourceDomain S s A r E₀ e width) :=
  measurableSet_map_image (normalMatrix S A) s.bandwidth_pos.ne' hE₀.ne' hd
    (activeOffsets S s r) (measurableSet_sourceDomain S s A r E₀ e width)

end RectangleCLT.GaussianTube
