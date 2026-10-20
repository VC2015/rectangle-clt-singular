import RectangleCLT.GaussianFaces
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# An augmented exponential tube map

The active exponential thresholds are output coordinates. This makes the
Gaussian-face tube change of variables square and finite dimensional, without
using a Hausdorff integral or a coarea theorem.
-/

open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

abbrev Coordinates (p q : ℕ) := (Fin p ⊕ Fin q) → ℝ

def base {p q : ℕ} (w : Coordinates p q) : Fin p → ℝ := fun j => w (.inl j)
def tube {p q : ℕ} (w : Coordinates p q) : Fin q → ℝ := fun i => w (.inr i)

def activeThreshold {q : ℕ} (h E₀ : ℝ) (a E : Fin q → ℝ) : Fin q → ℝ :=
  fun i => a i + h * Real.log (E i / E₀)

/-- The first block is the outward normal displacement; the second block
records the exponential thresholds of its base point. -/
def map {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ) (h E₀ : ℝ)
    (a : Fin q → ℝ) (w : Coordinates p q) : Coordinates p q :=
  Sum.elim (base w + N.mulVec (tube w))
    (fun i => E₀ * Real.exp (((N.transpose).mulVec (base w) i - a i) / h))

@[simp] theorem base_map {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w : Coordinates p q) :
    base (map N h E₀ a w) = base w + N.mulVec (tube w) := rfl

@[simp] theorem tube_map {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) (w : Coordinates p q) (i : Fin q) :
    tube (map N h E₀ a w) i =
      E₀ * Real.exp (((N.transpose).mulVec (base w) i - a i) / h) := rfl

theorem tube_map_pos {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (h : ℝ) {E₀ : ℝ} (hE₀ : 0 < E₀) (a : Fin q → ℝ)
    (w : Coordinates p q) (i : Fin q) : 0 < tube (map N h E₀ a w) i :=
  mul_pos hE₀ (Real.exp_pos _)

theorem activeThreshold_map {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0) (a : Fin q → ℝ)
    (w : Coordinates p q) :
    activeThreshold h E₀ a (tube (map N h E₀ a w)) = N.transpose.mulVec (base w) := by
  funext i
  simp only [activeThreshold, tube_map, mul_div_cancel_left₀ _ hE₀, Real.log_exp]
  field_simp

def recoveredTube {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ) (h E₀ : ℝ)
    (a : Fin q → ℝ) (w : Coordinates p q) : Fin q → ℝ :=
  (N.transpose * N)⁻¹.mulVec
    (N.transpose.mulVec (base w) - activeThreshold h E₀ a (tube w))

def inverse {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ) (h E₀ : ℝ)
    (a : Fin q → ℝ) (w : Coordinates p q) : Coordinates p q :=
  Sum.elim (base w - N.mulVec (recoveredTube N h E₀ a w)) (recoveredTube N h E₀ a w)

theorem recoveredTube_map {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0)
    (hd : IsUnit (N.transpose * N).det) (a : Fin q → ℝ) (w : Coordinates p q) :
    recoveredTube N h E₀ a (map N h E₀ a w) = tube w := by
  unfold recoveredTube
  rw [base_map, activeThreshold_map N hh hE₀, Matrix.mulVec_add,
    add_sub_cancel_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]

theorem inverse_map {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0)
    (hd : IsUnit (N.transpose * N).det) (a : Fin q → ℝ) (w : Coordinates p q) :
    inverse N h E₀ a (map N h E₀ a w) = w := by
  ext j
  cases j with
  | inl j =>
    change (base (map N h E₀ a w) - N.mulVec (recoveredTube N h E₀ a (map N h E₀ a w))) j = _
    rw [base_map, recoveredTube_map N hh hE₀ hd, add_sub_cancel_right]
    rfl
  | inr i => exact congrFun (recoveredTube_map N hh hE₀ hd a w) i

/-- The augmented map is globally injective when its active Gram matrix is
invertible. Positivity of tube coordinates is needed only for localization. -/
theorem map_injective {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0)
    (hd : IsUnit (N.transpose * N).det) (a : Fin q → ℝ) :
    Function.Injective (map N h E₀ a) :=
  Function.LeftInverse.injective (inverse_map N hh hE₀ hd a)

theorem contDiff_map {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (h E₀ : ℝ) (a : Fin q → ℝ) : ContDiff ℝ ⊤ (map N h E₀ a) := by
  apply contDiff_pi.mpr
  intro j
  cases j with
  | inl j =>
    change ContDiff ℝ ⊤ (fun w : Coordinates p q =>
      w (.inl j) + ∑ i, N j i * w (.inr i))
    exact (contDiff_apply ℝ ℝ (Sum.inl j : Fin p ⊕ Fin q)).add
      (ContDiff.sum (fun i _ => contDiff_const.mul
        (contDiff_apply ℝ ℝ (Sum.inr i : Fin p ⊕ Fin q))))
  | inr i =>
    change ContDiff ℝ ⊤ (fun w : Coordinates p q =>
      E₀ * Real.exp (((∑ j, N j i * w (.inl j)) - a i) / h))
    exact contDiff_const.mul (((ContDiff.sum (fun j _ => contDiff_const.mul
      (contDiff_apply ℝ ℝ (Sum.inl j : Fin p ⊕ Fin q)))).sub contDiff_const).div_const h).exp

theorem faceDot_mulVec {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (u : Fin q → ℝ) (z : Fin p → ℝ) :
    faceDot (N.mulVec u) z = faceDot u (N.transpose.mulVec z) := by
  simp only [faceDot, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mulVec_ne_zero {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    (hd : IsUnit (N.transpose * N).det) {u : Fin q → ℝ} (hu : u ≠ 0) : N.mulVec u ≠ 0 := by
  intro hn
  have hBu : (N.transpose * N).mulVec u = 0 := by
    rw [← Matrix.mulVec_mulVec, hn, Matrix.mulVec_zero]
  have hh := congrArg ((N.transpose * N)⁻¹.mulVec) hBu
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec,
    Matrix.mulVec_zero] at hh
  exact hu hh

/-- A positive outward displacement from an active equality plane is outside
the original polyhedron. Only the active Gram matrix must be invertible. -/
theorem outward_not_mem_polyhedron {p q : ℕ} {ι : Type*}
    (faces : Finset ι) (normal : ι → Fin p → ℝ) (offset : ι → ℝ)
    (active : Fin q → ι) (N : Matrix (Fin p) (Fin q) ℝ)
    (hN : ∀ i j, N j i = normal (active i) j)
    (ha : ∀ i, active i ∈ faces) (hd : IsUnit (N.transpose * N).det)
    (hq : 0 < q) (z : Fin p → ℝ) (u : Fin q → ℝ)
    (hz : ∀ i, faceDot (normal (active i)) z = offset (active i))
    (hu : ∀ i, 0 < u i) :
    z + N.mulVec u ∉ facePolyhedron faces normal offset := by
  intro hy
  have hvar : faceDot (N.mulVec u) (N.mulVec u) ≤ 0 := by
    rw [faceDot_mulVec]
    apply Finset.sum_nonpos
    intro i _
    apply mul_nonpos_of_nonneg_of_nonpos (hu i).le
    have hi := hy (active i) (ha i)
    rw [← hz i] at hi
    simp only [faceDot, Pi.add_apply, mul_add, Finset.sum_add_distrib,
      Matrix.mulVec, dotProduct, hN] at hi
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hN]
    linarith
  have hun : u ≠ 0 := by
    intro h
    have hh := hu ⟨0, hq⟩
    simp only [h, Pi.zero_apply, lt_self_iff_false] at hh
  have hpositive := vectorNormSq_pos (mulVec_ne_zero N hd hun)
  have hnorm : faceDot (N.mulVec u) (N.mulVec u) = vectorNormSq (N.mulVec u) := by
    simp only [faceDot, vectorNormSq, pow_two]
  rw [hnorm] at hvar
  exact (not_le_of_gt hpositive) hvar

/-- The outward image lies in the outer annulus of width `q*width`. This is
the localization needed before conditioning on a bounded independent base. -/
theorem outward_mem_annulus {p q : ℕ} {ι : Type*}
    (faces : Finset ι) (normal : ι → Fin p → ℝ) (offset : ι → ℝ)
    (active : Fin q → ι) (N : Matrix (Fin p) (Fin q) ℝ)
    (hN : ∀ i j, N j i = normal (active i) j)
    (ha : ∀ i, active i ∈ faces) (hd : IsUnit (N.transpose * N).det)
    (hq : 0 < q) (z : Fin p → ℝ) (u : Fin q → ℝ) (width : ℝ)
    (hzmem : z ∈ facePolyhedron faces normal offset)
    (hz : ∀ i, faceDot (normal (active i)) z = offset (active i))
    (hu : ∀ i, 0 < u i ∧ u i ≤ width)
    (hcorr : ∀ f ∈ faces, ∀ i, |faceDot (normal f) (fun j => N j i)| ≤ 1) :
    z + N.mulVec u ∈
      facePolyhedron faces normal (fun f => offset f + (q : ℝ) * width) \
        facePolyhedron faces normal offset := by
  refine ⟨?_, outward_not_mem_polyhedron faces normal offset active N hN ha hd hq z u hz
    (fun i => (hu i).1)⟩
  intro f hf
  have hdot : faceDot (normal f) (N.mulVec u) ≤ (q : ℝ) * width := by
    rw [faceDot_comm, faceDot_mulVec]
    calc
      _ ≤ ∑ i, u i * 1 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hu i).1.le
        apply (le_abs_self _).trans
        simpa only [faceDot, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
          using hcorr f hf i
      _ ≤ ∑ _i : Fin q, width := Finset.sum_le_sum (fun i _ => by simpa using (hu i).2)
      _ = _ := by simp
  have hsum : faceDot (normal f) (z + N.mulVec u) =
      faceDot (normal f) z + faceDot (normal f) (N.mulVec u) := by
    simp only [faceDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hsum]
  exact add_le_add (hzmem f hf) hdot

end

end RectangleCLT.GaussianTube
