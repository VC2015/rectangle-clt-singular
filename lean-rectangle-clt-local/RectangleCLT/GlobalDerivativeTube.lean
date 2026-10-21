import RectangleCLT.GaussianTubeDifferential
import RectangleCLT.GaussianTubeEvents
import RectangleCLT.GlobalDerivativeStein

/-!
# Gaussian exponential tubes in full coordinate dual directions

The local proof moves in the covariance-normal directions. For a full
covariance alternative one can move instead in dual directions `U`, where
`Nᵀ U = I`. The augmented map then has no Gram determinant in its Jacobian.
This file proves that map's inverse, injectivity, actual differential, and
change-of-variables formula. The averaged fourth-derivative cap is not yet
assembled from these facts.
-/

open scoped BigOperators NNReal ENNReal

namespace RectangleCLT.GaussianTube

noncomputable section

/-- Signed full coordinate duals, as columns indexed by active faces. -/
def fullDualMatrix {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin q) ℝ :=
  fun j i => faceSign (S.face i) * fullGaussianDual A (S.face i).1 j

theorem fullDualMatrix_factor_column {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det) (i : Fin q) :
    A.mulVec (fun j => fullDualMatrix S A j i) =
      faceSign (S.face i) • FaceSmoother.coordinateDirection (S.face i).1 := by
  change A.mulVec (faceSign (S.face i) • fullGaussianDual A (S.face i).1) = _
  rw [Matrix.mulVec_smul, fullGaussianDual_right_inverse A hd]

/-- The actual covariance normals and actual full coordinate duals are dual
on every compatible active face family. -/
theorem normalMatrix_transpose_mul_fullDualMatrix {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (A * A.transpose).det) :
    (normalMatrix S A).transpose * fullDualMatrix S A = 1 := by
  classical
  ext i j
  have hentry : ((normalMatrix S A).transpose * fullDualMatrix S A) i j =
      faceSign (S.face i) *
        (A.mulVec (fun k => fullDualMatrix S A k j) (S.face i).1) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, normalMatrix,
      Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hentry, fullDualMatrix_factor_column S A hd]
  by_cases hij : i = j
  · subst j
    simp [FaceSmoother.coordinateDirection, ← mul_assoc, ← pow_two, faceSign_sq]
  · have hcoord : (S.face i).1 ≠ (S.face j).1 := fun h => hij (S.coordinate_injective h)
    simp [Pi.smul_apply, smul_eq_mul, FaceSmoother.coordinateDirection, hcoord, hij]

/-- Full dual displacement leaves every different coordinate face unchanged;
in particular its action on any signed coordinate face has magnitude at most one. -/
theorem abs_normalDot_fullDualMatrix_factor_column_le_one {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (A * A.transpose).det) (i : Fin q) (f : Face p) :
    |FaceSmoother.normalDot f (A.mulVec (fun j => fullDualMatrix S A j i))| ≤ 1 := by
  rw [fullDualMatrix_factor_column S A hd]
  simp only [normalDot_eq_faceSign_mul, Pi.smul_apply, smul_eq_mul,
    FaceSmoother.coordinateDirection, abs_mul, abs_faceSign, one_mul]
  split_ifs <;> norm_num

theorem normalDot_fullDualMatrix_factor_column_eq_zero {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (A * A.transpose).det) (i : Fin q) (f : Face p)
    (hcoord : f.1 ≠ (S.face i).1) :
    FaceSmoother.normalDot f (A.mulVec (fun j => fullDualMatrix S A j i)) = 0 := by
  rw [fullDualMatrix_factor_column S A hd]
  simp [normalDot_eq_faceSign_mul, FaceSmoother.coordinateDirection, hcoord]

/-- Positive dual displacement violates every active equality plane. This
uses exact duality, so no lower Gram eigenvalue is lost. -/
theorem dual_outward_not_mem_polyhedron {p q : ℕ} {ι : Type*}
    (faces : Finset ι) (normal : ι → Fin p → ℝ) (offset : ι → ℝ)
    (active : Fin q → ι) (N U : Matrix (Fin p) (Fin q) ℝ)
    (hN : ∀ i j, N j i = normal (active i) j)
    (ha : ∀ i, active i ∈ faces) (hdual : N.transpose * U = 1)
    (hq : 0 < q) (z : Fin p → ℝ) (u : Fin q → ℝ)
    (hz : ∀ i, faceDot (normal (active i)) z = offset (active i))
    (hu : ∀ i, 0 < u i) :
    z + U.mulVec u ∉ facePolyhedron faces normal offset := by
  intro hy
  let i : Fin q := ⟨0, hq⟩
  have hrow (v : Fin p → ℝ) :
      N.transpose.mulVec v i = faceDot (normal (active i)) v := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hN, faceDot]
  have hdot : faceDot (normal (active i)) (z + U.mulVec u) =
      offset (active i) + u i := by
    rw [← hrow, Matrix.mulVec_add, Matrix.mulVec_mulVec, hdual, Matrix.one_mulVec]
    change N.transpose.mulVec z i + u i = _
    rw [hrow, hz]
  have hi := hy (active i) (ha i)
  rw [hdot] at hi
  linarith [hu i]

def dualMap {p q : ℕ} (N U : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w : Coordinates p q) : Coordinates p q :=
  Sum.elim (base w + U.mulVec (tube w))
    (fun i => E₀ * Real.exp ((N.transpose.mulVec (base w) i - a i) / h))

@[simp] theorem base_dualMap {p q : ℕ} (N U : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w : Coordinates p q) :
    base (dualMap N U h E₀ a w) = base w + U.mulVec (tube w) := rfl

@[simp] theorem tube_dualMap {p q : ℕ} (N U : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w : Coordinates p q) (i : Fin q) :
    tube (dualMap N U h E₀ a w) i =
      E₀ * Real.exp ((N.transpose.mulVec (base w) i - a i) / h) := rfl

theorem activeThreshold_dualMap {p q : ℕ} (N U : Matrix (Fin p) (Fin q) ℝ)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0)
    (a : Fin q → ℝ) (w : Coordinates p q) :
    activeThreshold h E₀ a (tube (dualMap N U h E₀ a w)) =
      N.transpose.mulVec (base w) := by
  funext i
  simp only [activeThreshold, tube_dualMap, mul_div_cancel_left₀ _ hE₀, Real.log_exp]
  field_simp

def dualRecoveredTube {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w : Coordinates p q) : Fin q → ℝ :=
  N.transpose.mulVec (base w) - activeThreshold h E₀ a (tube w)

def dualInverse {p q : ℕ} (N U : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w : Coordinates p q) : Coordinates p q :=
  Sum.elim (base w - U.mulVec (dualRecoveredTube N h E₀ a w))
    (dualRecoveredTube N h E₀ a w)

theorem dualRecoveredTube_dualMap {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (hdual : N.transpose * U = 1)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0)
    (a : Fin q → ℝ) (w : Coordinates p q) :
    dualRecoveredTube N h E₀ a (dualMap N U h E₀ a w) = tube w := by
  unfold dualRecoveredTube
  rw [base_dualMap, activeThreshold_dualMap N U hh hE₀, Matrix.mulVec_add,
    add_sub_cancel_left, Matrix.mulVec_mulVec, hdual, Matrix.one_mulVec]

theorem dualInverse_dualMap {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (hdual : N.transpose * U = 1)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0)
    (a : Fin q → ℝ) (w : Coordinates p q) :
    dualInverse N U h E₀ a (dualMap N U h E₀ a w) = w := by
  ext j
  cases j with
  | inl j =>
    change (base (dualMap N U h E₀ a w) -
      U.mulVec (dualRecoveredTube N h E₀ a (dualMap N U h E₀ a w))) j = _
    rw [base_dualMap, dualRecoveredTube_dualMap N U hdual hh hE₀,
      add_sub_cancel_right]
    rfl
  | inr i => exact congrFun (dualRecoveredTube_dualMap N U hdual hh hE₀ a w) i

theorem dualMap_injective {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (hdual : N.transpose * U = 1)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0) (a : Fin q → ℝ) :
    Function.Injective (dualMap N U h E₀ a) :=
  Function.LeftInverse.injective (dualInverse_dualMap N U hdual hh hE₀ a)

theorem dualMap_dualInverse {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (hdual : N.transpose * U = 1)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : 0 < E₀)
    (a : Fin q → ℝ) (y : Coordinates p q) (hE : ∀ i, 0 < tube y i) :
    dualMap N U h E₀ a (dualInverse N U h E₀ a y) = y := by
  have hscores : N.transpose.mulVec (base (dualInverse N U h E₀ a y)) =
      activeThreshold h E₀ a (tube y) := by
    change N.transpose.mulVec (base y - U.mulVec (dualRecoveredTube N h E₀ a y)) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hdual, Matrix.one_mulVec]
    unfold dualRecoveredTube
    rw [sub_sub_cancel]
  ext j
  cases j with
  | inl j =>
    change (base y - U.mulVec (dualRecoveredTube N h E₀ a y) +
      U.mulVec (dualRecoveredTube N h E₀ a y)) j = y (.inl j)
    rw [sub_add_cancel]
    rfl
  | inr i =>
    change E₀ * Real.exp ((N.transpose.mulVec (base (dualInverse N U h E₀ a y)) i - a i) / h) = _
    rw [hscores]
    have he : (activeThreshold h E₀ a (tube y) i - a i) / h = Real.log (tube y i / E₀) := by
      dsimp [activeThreshold]
      field_simp
    rw [he, Real.exp_log (div_pos (hE i) hE₀), mul_div_cancel₀ _ hE₀.ne']
    rfl

def dualTubeJacobian {p q : ℕ} (N U : Matrix (Fin p) (Fin q) ℝ)
    (d : Fin q → ℝ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  Matrix.fromBlocks 1 U ((Matrix.diagonal d) * N.transpose) 0

/-- The Gram determinant disappears because the displacement is dual to the
active constraints. This is the algebraic source of the sharper full scale. -/
theorem dualTubeJacobian_det {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (hdual : N.transpose * U = 1)
    (d : Fin q → ℝ) :
    (dualTubeJacobian N U d).det = (-1 : ℝ) ^ q * ∏ i, d i := by
  unfold dualTubeJacobian
  rw [Matrix.det_fromBlocks_one₁₁, zero_sub, Matrix.det_neg,
    Matrix.mul_assoc, hdual, Matrix.mul_one, Matrix.det_diagonal]
  simp only [Fintype.card_fin]

theorem dualTubeJacobian_abs_det_exp {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (hdual : N.transpose * U = 1)
    (E : Fin q → ℝ) (h : ℝ) (hE : ∀ i, 0 ≤ E i) (hh : 0 < h) :
    |(dualTubeJacobian N U (fun i => E i / h)).det| = (∏ i, E i) / h ^ q := by
  rw [dualTubeJacobian_det N U hdual, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul,
    abs_of_nonneg (Finset.prod_nonneg (fun i _ => div_nonneg (hE i) hh.le)),
    Finset.prod_div_distrib]
  simp

theorem contDiff_dualMap {p q : ℕ} (N U : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) : ContDiff ℝ ⊤ (dualMap N U h E₀ a) := by
  apply contDiff_pi.mpr
  intro j
  cases j with
  | inl j =>
    change ContDiff ℝ ⊤ (fun w : Coordinates p q =>
      w (.inl j) + ∑ i, U j i * w (.inr i))
    exact (contDiff_apply ℝ ℝ (Sum.inl j : Fin p ⊕ Fin q)).add
      (ContDiff.sum (fun i _ => contDiff_const.mul
        (contDiff_apply ℝ ℝ (Sum.inr i : Fin p ⊕ Fin q))))
  | inr i =>
    change ContDiff ℝ ⊤ (fun w : Coordinates p q =>
      E₀ * Real.exp (((∑ j, N j i * w (.inl j)) - a i) / h))
    exact contDiff_const.mul (((ContDiff.sum (fun j _ => contDiff_const.mul
      (contDiff_apply ℝ ℝ (Sum.inl j : Fin p ⊕ Fin q)))).sub contDiff_const).div_const h).exp

def dualLineDerivative {p q : ℕ} (N U : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w y : Coordinates p q) : Coordinates p q :=
  Sum.elim (base y + U.mulVec (tube y))
    (fun i => tube (dualMap N U h E₀ a w) i / h * N.transpose.mulVec (base y) i)

theorem hasDerivAt_dualMap_line {p q : ℕ} (N U : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w y : Coordinates p q) :
    HasDerivAt (fun t : ℝ => dualMap N U h E₀ a (w + t • y))
      (dualLineDerivative N U h E₀ a w y) 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  cases j with
  | inl j =>
    have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      ((hasDerivAt_const 0 (w (.inr i))).add
        ((hasDerivAt_id 0).mul_const (y (.inr i)))).const_mul (U j i))
    have hd := ((hasDerivAt_const 0 (w (.inl j))).add
      ((hasDerivAt_id 0).mul_const (y (.inl j)))).add hs
    simpa only [dualMap, dualLineDerivative, base, tube, Sum.elim_inl, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, zero_add,
      zero_mul, add_zero, mul_one, one_mul, id_eq] using hd
  | inr i =>
    have hs := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      ((hasDerivAt_const 0 (w (.inl j))).add
        ((hasDerivAt_id 0).mul_const (y (.inl j)))).const_mul (N j i))
    have hd := (((hs.sub_const (a i)).div_const h).exp).const_mul E₀
    convert hd using 1
    simp only [dualLineDerivative, dualMap, tube, base, Sum.elim_inr,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, mul_one, one_mul, id_eq]
    ring

theorem dualLineDerivative_eq_jacobian {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (h E₀ : ℝ) (a : Fin q → ℝ)
    (w y : Coordinates p q) :
    dualLineDerivative N U h E₀ a w y =
      (dualTubeJacobian N U (fun i => tube (dualMap N U h E₀ a w) i / h)).mulVec y := by
  rw [dualTubeJacobian, Matrix.fromBlocks_mulVec]
  ext j
  cases j with
  | inl j =>
    simp only [dualLineDerivative, Sum.elim_inl, Matrix.one_mulVec, base, tube,
      Function.comp_apply]
    rfl
  | inr i =>
    simp only [dualLineDerivative, Sum.elim_inr, Matrix.zero_mulVec, add_zero,
      ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, base, Function.comp_apply]
    rfl

theorem dualMap_fderiv_apply {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (h E₀ : ℝ) (a : Fin q → ℝ)
    (w y : Coordinates p q) :
    fderiv ℝ (dualMap N U h E₀ a) w y =
      (dualTubeJacobian N U (fun i => tube (dualMap N U h E₀ a w) i / h)).mulVec y := by
  have hf := ((contDiff_dualMap N U h E₀ a).differentiable (by simp) w).hasFDerivAt
  have hpath : HasDerivAt (fun t : ℝ => w + t • y) y 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) w).add ((hasDerivAt_id (0 : ℝ)).smul_const y)
  have hf0 : HasFDerivAt (dualMap N U h E₀ a) (fderiv ℝ (dualMap N U h E₀ a) w)
      (w + (0 : ℝ) • y) := by simpa using hf
  have hcomp := hf0.comp_hasDerivAt 0 hpath
  rw [← dualLineDerivative_eq_jacobian]
  exact hcomp.unique (hasDerivAt_dualMap_line N U h E₀ a w y)

theorem dualMap_abs_fderiv_det {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (hdual : N.transpose * U = 1)
    {h E₀ : ℝ} (hh : 0 < h) (hE₀ : 0 < E₀)
    (a : Fin q → ℝ) (w : Coordinates p q) :
    |(fderiv ℝ (dualMap N U h E₀ a) w).det| =
      (∏ i, tube (dualMap N U h E₀ a w) i) / h ^ q := by
  have hmatrix : LinearMap.toMatrix' (fderiv ℝ (dualMap N U h E₀ a) w).toLinearMap =
      dualTubeJacobian N U (fun i => tube (dualMap N U h E₀ a w) i / h) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    change fderiv ℝ (dualMap N U h E₀ a) w (fun k => if k = j then 1 else 0) i = _
    rw [dualMap_fderiv_apply]
    simp [Matrix.mulVec, dotProduct]
  change |LinearMap.det ((fderiv ℝ (dualMap N U h E₀ a) w).toLinearMap)| = _
  rw [← LinearMap.det_toMatrix', hmatrix]
  exact dualTubeJacobian_abs_det_exp N U hdual _ h
    (fun i => (mul_pos hE₀ (Real.exp_pos _)).le) hh

open MeasureTheory

/-- Genuine injective change of variables for the dual-direction tube.
Its Jacobian contains no covariance determinant or hidden spectral loss. -/
theorem lintegral_image_dualMap {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (hdual : N.transpose * U = 1)
    {h E₀ : ℝ} (hh : 0 < h) (hE₀ : 0 < E₀) (a : Fin q → ℝ)
    {D : Set (Coordinates p q)} (hD : MeasurableSet D) (g : Coordinates p q → ℝ≥0∞) :
    (∫⁻ y in dualMap N U h E₀ a '' D, g y) =
      ∫⁻ w in D, ENNReal.ofReal ((∏ i, tube (dualMap N U h E₀ a w) i) / h ^ q) *
        g (dualMap N U h E₀ a w) := by
  have hf : ∀ w ∈ D, HasFDerivWithinAt (dualMap N U h E₀ a)
      (fderiv ℝ (dualMap N U h E₀ a) w) D w := fun w _ =>
    (((contDiff_dualMap N U h E₀ a).differentiable (by simp) w).hasFDerivAt).hasFDerivWithinAt
  have hi := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hD hf
    (dualMap_injective N U hdual hh.ne' hE₀.ne' a).injOn g
  simpa only [dualMap_abs_fderiv_det N U hdual hh hE₀ a] using hi

end

end RectangleCLT.GaussianTube
