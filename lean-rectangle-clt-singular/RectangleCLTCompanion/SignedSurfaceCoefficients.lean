import RectangleCLTCompanion.SignedSurfaceGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant
import RectangleCLT.GaussianTubeEvents

/-! The actual coefficient domain for the augmented two-face map. Its
volume, multiplied by the active Gram determinant, retains exactly the
factor canceled by the paired ridge numerator. -/

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pairCoordinateMatrix (u v : E) (σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ * ‖u + v‖ / 2, σ * ‖u + v‖ / 2;
     σ * ‖u - v‖ / 2, -(σ * ‖u - v‖ / 2)]

def pairCoordinateBox (u v : E) (ε : ℝ) : Set (Fin 2 → ℝ) :=
  Set.Icc ![ε / 4, -ε * ‖u - v‖ / 8] ![ε / 2, ε * ‖u - v‖ / 8]

def pairCoefficientDomain (u v : E) (σ ε : ℝ) : Set (Fin 2 → ℝ) :=
  (pairCoordinateMatrix u v σ).mulVec ⁻¹' pairCoordinateBox u v ε

omit [InnerProductSpace ℝ E] in
theorem pairCoordinateMatrix_det (u v : E) (σ : ℝ) :
    (pairCoordinateMatrix u v σ).det = -(σ ^ 2 * ‖u + v‖ * ‖u - v‖ / 2) := by
  rw [Matrix.det_fin_two]
  simp only [pairCoordinateMatrix, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  ring

theorem pairCoordinateMatrix_abs_det (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) (σ : ℝ) :
    |(pairCoordinateMatrix u v σ).det| = σ ^ 2 * Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) := by
  rw [pairCoordinateMatrix_det, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ σ ^ 2 * ‖u + v‖ * ‖u - v‖ / 2)]
  have hprod := norm_sum_mul_norm_sub u v hu hv hp hm
  nlinarith only [congrArg (fun t : ℝ => σ ^ 2 * t) hprod]

omit [InnerProductSpace ℝ E] in
theorem pairCoefficientDomain_measurable (u v : E) (σ ε : ℝ) :
    MeasurableSet (pairCoefficientDomain u v σ ε) := by
  exact measurableSet_Icc.preimage (measurable_mulVec _)

omit [InnerProductSpace ℝ E] in
theorem pairCoordinateBox_volume (u v : E) {ε : ℝ} (hε : 0 ≤ ε) :
    (volume : Measure (Fin 2 → ℝ)) (pairCoordinateBox u v ε) =
      ENNReal.ofReal (ε ^ 2 * ‖u - v‖ / 16) := by
  rw [pairCoordinateBox, Real.volume_Icc_pi]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ ε / 2 - ε / 4)]
  congr 1
  ring

theorem pairCoefficientDomain_volume (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 ≤ ε) :
    (volume : Measure (Fin 2 → ℝ)) (pairCoefficientDomain u v σ ε) =
      ENNReal.ofReal ((ε ^ 2 * ‖u - v‖ / 16) /
        (σ ^ 2 * Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2))) := by
  have he : 0 < ‖u + v‖ := norm_pos_iff.mpr hp
  have hd : 0 < ‖u - v‖ := norm_pos_iff.mpr hm
  have hs : 0 < Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) := by
    have hprod := norm_sum_mul_norm_sub u v hu hv hp hm
    nlinarith [mul_pos he hd]
  have hdet : LinearMap.det (Matrix.toLin' (pairCoordinateMatrix u v σ)) ≠ 0 := by
    rw [LinearMap.det_toLin']
    exact abs_pos.mp (by rw [pairCoordinateMatrix_abs_det u v hu hv hp hm]; positivity)
  rw [pairCoefficientDomain]
  change volume ((Matrix.toLin' (pairCoordinateMatrix u v σ)) ⁻¹' _) = _
  rw [Measure.addHaar_preimage_linearMap volume hdet,
    LinearMap.det_toLin', abs_inv, pairCoordinateMatrix_abs_det u v hu hv hp hm,
    pairCoordinateBox_volume u v hε]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity))]
  congr 1
  ring

omit [InnerProductSpace ℝ E] in
theorem pairCoefficientDomain_coordinates (u v : E) (σ : ℝ) (c : Fin 2 → ℝ) :
    (pairCoordinateMatrix u v σ).mulVec c =
      ![σ * ‖u + v‖ * (c 0 + c 1) / 2,
        σ * ‖u - v‖ * (c 0 - c 1) / 2] := by
  ext i
  fin_cases i <;> simp [pairCoordinateMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] <;> ring

theorem pairCoefficientDomain_displacement (u v : E)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) (σ : ℝ) (c : Fin 2 → ℝ) :
    σ • (c 0 • u + c 1 • v) =
      ridgeDisplacement u v
        (((pairCoordinateMatrix u v σ).mulVec c) 0,
         ((pairCoordinateMatrix u v σ).mulVec c) 1) := by
  rw [pairCoefficientDomain_coordinates, ridgeDisplacement_expansion]
  have he := norm_ne_zero_iff.mpr hp
  have hd := norm_ne_zero_iff.mpr hm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have ha : σ * ‖u + v‖ * (c 0 + c 1) / 2 / ‖u + v‖ +
      σ * ‖u - v‖ * (c 0 - c 1) / 2 / ‖u - v‖ = σ * c 0 := by
    field_simp
    ring
  have hb : σ * ‖u + v‖ * (c 0 + c 1) / 2 / ‖u + v‖ -
      σ * ‖u - v‖ * (c 0 - c 1) / 2 / ‖u - v‖ = σ * c 1 := by
    field_simp
    ring
  rw [ha, hb]
  simp only [smul_add, smul_smul]

omit [InnerProductSpace ℝ E] in
theorem pairCoefficientDomain_mem_rectangle (u v : E) (σ ε : ℝ) {c : Fin 2 → ℝ}
    (hc : c ∈ pairCoefficientDomain u v σ ε) :
    (((pairCoordinateMatrix u v σ).mulVec c) 0,
      ((pairCoordinateMatrix u v σ).mulVec c) 1) ∈ ridgeRectangle u v ε := by
  change ![ε / 4, -ε * ‖u - v‖ / 8] ≤ (pairCoordinateMatrix u v σ).mulVec c ∧
    (pairCoordinateMatrix u v σ).mulVec c ≤ ![ε / 2, ε * ‖u - v‖ / 8] at hc
  exact ⟨⟨hc.1 0, hc.2 0⟩, ⟨hc.1 1, hc.2 1⟩⟩

theorem pairCoefficientDomain_displacement_norm_le (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    (σ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {c : Fin 2 → ℝ}
    (hc : c ∈ pairCoefficientDomain u v σ ε) :
    ‖σ • (c 0 • u + c 1 • v)‖ ≤ ε := by
  rw [pairCoefficientDomain_displacement u v hp hm]
  exact ridgeRectangle_displacement_norm_le u v hu hv hp hm hε
    (pairCoefficientDomain_mem_rectangle u v σ ε hc)

theorem pairCoefficientDomain_positive (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) {c : Fin 2 → ℝ}
    (hc : c ∈ pairCoefficientDomain u v σ ε) : ∀ i, 0 < c i := by
  have he : 0 < ‖u + v‖ := norm_pos_iff.mpr hp
  have hd : 0 < ‖u - v‖ := norm_pos_iff.mpr hm
  have he2 : ‖u + v‖ < 2 := by
    have ha := norm_add_sq_real u v
    have hb := norm_sub_sq_real u v
    rw [hu, hv] at ha hb
    nlinarith [sq_pos_of_pos hd]
  let st : ℝ × ℝ := (((pairCoordinateMatrix u v σ).mulVec c) 0,
    ((pairCoordinateMatrix u v σ).mulVec c) 1)
  have hst : st ∈ ridgeRectangle u v ε := pairCoefficientDomain_mem_rectangle u v σ ε hc
  have ht : |st.2 / ‖u - v‖| ≤ ε / 8 := by
    rw [abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    have hh := hst.2
    have habs : |st.2| ≤ ε * ‖u - v‖ / 8 :=
      abs_le.mpr ⟨by nlinarith [hh.1], hh.2⟩
    nlinarith
  have hs : ε / 8 < st.1 / ‖u + v‖ := by
    apply (lt_div_iff₀ he).mpr
    nlinarith [hst.1.1, mul_pos hε (by linarith : 0 < 2 - ‖u + v‖)]
  have hc0 : σ * c 0 = st.1 / ‖u + v‖ + st.2 / ‖u - v‖ := by
    dsimp [st]
    rw [pairCoefficientDomain_coordinates]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    field_simp
    ring
  have hc1 : σ * c 1 = st.1 / ‖u + v‖ - st.2 / ‖u - v‖ := by
    dsimp [st]
    rw [pairCoefficientDomain_coordinates]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    field_simp
    ring
  intro i
  fin_cases i
  · change 0 < c 0
    have hh : 0 < σ * c 0 := by rw [hc0]; linarith [(abs_le.mp ht).1]
    exact (mul_pos_iff_of_pos_left hσ).mp hh
  · change 0 < c 1
    have hh : 0 < σ * c 1 := by rw [hc1]; linarith [(abs_le.mp ht).2]
    exact (mul_pos_iff_of_pos_left hσ).mp hh

theorem pairCoefficientDomain_real_volume (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) {σ ε : ℝ}
    (hσ : 0 < σ) (hε : 0 ≤ ε) :
    (volume : Measure (Fin 2 → ℝ)).real (pairCoefficientDomain u v σ ε) =
      (ε ^ 2 * ‖u - v‖ / 16) / (σ ^ 2 * Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2)) := by
  rw [measureReal_def, pairCoefficientDomain_volume u v hu hv hp hm hσ hε,
    ENNReal.toReal_ofReal (by positivity)]

end
end RectangleCLT.Companion.SignedSurface
