import RectangleCLT.GaussianTubeMap
import RectangleCLT.GaussianTubeJacobian
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Function.Jacobian

/-! The true derivative and Jacobian of the augmented exponential tube map. -/

open scoped BigOperators NNReal ENNReal

namespace RectangleCLT.GaussianTube

noncomputable section

def lineDerivative {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ) (h E₀ : ℝ)
    (a : Fin q → ℝ) (w y : Coordinates p q) : Coordinates p q :=
  Sum.elim (base y + N.mulVec (tube y))
    (fun i => tube (map N h E₀ a w) i / h * N.transpose.mulVec (base y) i)

theorem hasDerivAt_map_line {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w y : Coordinates p q) :
    HasDerivAt (fun t : ℝ => map N h E₀ a (w + t • y))
      (lineDerivative N h E₀ a w y) 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  cases j with
  | inl j =>
    have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      ((hasDerivAt_const 0 (w (.inr i))).add
        ((hasDerivAt_id 0).mul_const (y (.inr i)))).const_mul (N j i))
    have hd := ((hasDerivAt_const 0 (w (.inl j))).add
      ((hasDerivAt_id 0).mul_const (y (.inl j)))).add hs
    simpa only [map, lineDerivative, base, tube, Sum.elim_inl, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, zero_add,
      zero_mul, add_zero, mul_one, one_mul, id_eq] using hd
  | inr i =>
    have hs := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      ((hasDerivAt_const 0 (w (.inl j))).add
        ((hasDerivAt_id 0).mul_const (y (.inl j)))).const_mul (N j i))
    have hd := (((hs.sub_const (a i)).div_const h).exp).const_mul E₀
    convert hd using 1
    simp only [lineDerivative, map, tube, base, Sum.elim_inr,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, mul_one, one_mul, id_eq]
    ring

theorem lineDerivative_eq_jacobian {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w y : Coordinates p q) :
    lineDerivative N h E₀ a w y =
      (gaussianTubeJacobian N (fun i => tube (map N h E₀ a w) i / h)).mulVec y := by
  rw [gaussianTubeJacobian, Matrix.fromBlocks_mulVec]
  ext j
  cases j with
  | inl j => simp only [lineDerivative, Sum.elim_inl, Matrix.one_mulVec, base, tube,
      Function.comp_apply]
             rfl
  | inr i =>
    simp only [lineDerivative, Sum.elim_inr, Matrix.zero_mulVec, add_zero,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, base, Function.comp_apply]
    rfl

/-- Every directional derivative is identified with the concrete block
Jacobian, rather than merely defining that block to be a derivative. -/
theorem map_fderiv_apply {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w y : Coordinates p q) :
    fderiv ℝ (map N h E₀ a) w y =
      (gaussianTubeJacobian N (fun i => tube (map N h E₀ a w) i / h)).mulVec y := by
  have hf := ((contDiff_map N h E₀ a).differentiable (by simp) w).hasFDerivAt
  have hpath : HasDerivAt (fun t : ℝ => w + t • y) y 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) w).add ((hasDerivAt_id (0 : ℝ)).smul_const y)
  have hf0 : HasFDerivAt (map N h E₀ a) (fderiv ℝ (map N h E₀ a) w)
      (w + (0 : ℝ) • y) := by simpa using hf
  have hcomp := hf0.comp_hasDerivAt 0 hpath
  rw [← lineDerivative_eq_jacobian]
  exact hcomp.unique (hasDerivAt_map_line N h E₀ a w y)

theorem map_fderiv_det {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w : Coordinates p q) :
    (fderiv ℝ (map N h E₀ a) w).det =
      (gaussianTubeJacobian N (fun i => tube (map N h E₀ a w) i / h)).det := by
  classical
  change LinearMap.det ((fderiv ℝ (map N h E₀ a) w).toLinearMap) = _
  rw [← LinearMap.det_toMatrix']
  congr 1
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix'_apply]
  change fderiv ℝ (map N h E₀ a) w (fun k => if k = j then 1 else 0) i = _
  rw [map_fderiv_apply]
  simp [Matrix.mulVec, dotProduct]

/-- The exact absolute Jacobian factor used in exponential-mixture face
integration: one active exponential per normal, and the Gram determinant. -/
theorem map_abs_fderiv_det {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    {h E₀ : ℝ} (hh : 0 < h) (hE₀ : 0 < E₀) (a : Fin q → ℝ)
    (w : Coordinates p q) (hgram : 0 ≤ (N.transpose * N).det) :
    |(fderiv ℝ (map N h E₀ a) w).det| =
      ((∏ i, tube (map N h E₀ a w) i) / h ^ q) * (N.transpose * N).det := by
  rw [map_fderiv_det]
  exact gaussianTubeJacobian_abs_det_exp N _ h
    (fun i => (tube_map_pos N h hE₀ a w i).le) hh hgram

open MeasureTheory

/-- Actual injective change of variables on every measurable tube domain.
There is no coarea or Gaussian-face-integral premise in this statement. -/
theorem lintegral_image_map {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    {h E₀ : ℝ} (hh : 0 < h) (hE₀ : 0 < E₀)
    (hd : IsUnit (N.transpose * N).det) (a : Fin q → ℝ)
    (hgram : 0 ≤ (N.transpose * N).det) {D : Set (Coordinates p q)}
    (hD : MeasurableSet D) (g : Coordinates p q → ℝ≥0∞) :
    (∫⁻ y in map N h E₀ a '' D, g y) =
      ∫⁻ w in D, ENNReal.ofReal
        (((∏ i, tube (map N h E₀ a w) i) / h ^ q) * (N.transpose * N).det) *
          g (map N h E₀ a w) := by
  have hf : ∀ w ∈ D, HasFDerivWithinAt (map N h E₀ a)
      (fderiv ℝ (map N h E₀ a) w) D w := fun w _ =>
    (((contDiff_map N h E₀ a).differentiable (by simp) w).hasFDerivAt).hasFDerivWithinAt
  have hi := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD hf
    (map_injective N hh.ne' hE₀.ne' hd a).injOn g
  simpa only [map_abs_fderiv_det N hh hE₀ a _ hgram] using hi

theorem integral_image_map {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    {h E₀ : ℝ} (hh : 0 < h) (hE₀ : 0 < E₀)
    (hd : IsUnit (N.transpose * N).det) (a : Fin q → ℝ)
    (hgram : 0 ≤ (N.transpose * N).det) {D : Set (Coordinates p q)}
    (hD : MeasurableSet D) (g : Coordinates p q → ℝ) :
    (∫ y in map N h E₀ a '' D, g y) =
      ∫ w in D,
        (((∏ i, tube (map N h E₀ a w) i) / h ^ q) * (N.transpose * N).det) *
          g (map N h E₀ a w) := by
  have hf : ∀ w ∈ D, HasFDerivWithinAt (map N h E₀ a)
      (fderiv ℝ (map N h E₀ a) w) D w := fun w _ =>
    (((contDiff_map N h E₀ a).differentiable (by simp) w).hasFDerivAt).hasFDerivWithinAt
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume hD hf
    (map_injective N hh.ne' hE₀.ne' hd a).injOn g
  simpa only [map_abs_fderiv_det N hh hE₀ a _ hgram, smul_eq_mul] using hi

end

end RectangleCLT.GaussianTube
