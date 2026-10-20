import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Concrete codimension-two geometry for the signed Gaussian surface
argument. A bisector rectangle replaces angular sectors, retaining the
cancellation for nearly equal and nearly opposite unit normals. -/

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def bisector (u v : E) : E := ‖u + v‖⁻¹ • (u + v)
def differenceDirection (u v : E) : E := ‖u - v‖⁻¹ • (u - v)

theorem norm_bisector (u v : E) (hp : u + v ≠ 0) : ‖bisector u v‖ = 1 := by
  simp only [bisector, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)

theorem norm_differenceDirection (u v : E) (hm : u - v ≠ 0) :
    ‖differenceDirection u v‖ = 1 := by
  simp only [differenceDirection, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hm)

theorem inner_bisector_differenceDirection (u v : E) (huv : ‖u‖ = ‖v‖) :
    ⟪bisector u v, differenceDirection u v⟫_ℝ = 0 := by
  simp only [bisector, differenceDirection, inner_smul_left, inner_smul_right,
    conj_trivial, (real_inner_add_sub_eq_zero_iff u v).mpr huv, mul_zero]

theorem orthonormal_pairFrame (u v : E) (huv : ‖u‖ = ‖v‖)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) :
    Orthonormal ℝ (![bisector u v, differenceDirection u v] : Fin 2 → E) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · change ⟪bisector u v, bisector u v⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, norm_bisector u v hp, one_pow]
  · exact inner_bisector_differenceDirection u v huv
  · change ⟪differenceDirection u v, bisector u v⟫_ℝ = 0
    rw [real_inner_comm]
    exact inner_bisector_differenceDirection u v huv
  · change ⟪differenceDirection u v, differenceDirection u v⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq, norm_differenceDirection u v hm, one_pow]

def normalConePair (u v : E) : Set E :=
  {y | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ y = a • u + b • v}

def ridgeRectangle (u v : E) (ε : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc (ε / 4) (ε / 2) ×ˢ Set.Icc (-ε * ‖u - v‖ / 8) (ε * ‖u - v‖ / 8)

def ridgeDisplacement (u v : E) (st : ℝ × ℝ) : E :=
  st.1 • bisector u v + st.2 • differenceDirection u v

theorem ridgeDisplacement_expansion (u v : E) (st : ℝ × ℝ) :
    ridgeDisplacement u v st =
      (st.1 / ‖u + v‖ + st.2 / ‖u - v‖) • u +
      (st.1 / ‖u + v‖ - st.2 / ‖u - v‖) • v := by
  simp only [ridgeDisplacement, bisector, differenceDirection, smul_add, smul_sub,
    smul_smul, div_eq_mul_inv, add_smul, sub_smul]
  module

/-- This rectangle has area proportional to `‖u−v‖`, precisely the factor
in the paired ridge coefficient. It stays in the outward cone at both
angular degeneracies, without an inverse sine bound. -/
theorem ridgeRectangle_maps_into_cone (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    {st : ℝ × ℝ} (hst : st ∈ ridgeRectangle u v ε) :
    ridgeDisplacement u v st ∈ normalConePair u v := by
  have he : 0 < ‖u + v‖ := norm_pos_iff.mpr hp
  have hd : 0 < ‖u - v‖ := norm_pos_iff.mpr hm
  have he2 : ‖u + v‖ ≤ 2 := by
    have h := norm_add_le u v
    rw [hu, hv] at h
    linarith
  have hs : ε / 4 ≤ st.1 := hst.1.1
  have ht : |st.2| ≤ ε * ‖u - v‖ / 8 :=
    abs_le.mpr ⟨by nlinarith [hst.2.1], hst.2.2⟩
  have hs0 : 0 ≤ st.1 := (div_nonneg hε (by norm_num)).trans hs
  have hratio : |st.2| / ‖u - v‖ ≤ st.1 / ‖u + v‖ := by
    have hleft : |st.2| / ‖u - v‖ ≤ ε / 8 := by
      apply (div_le_iff₀ hd).mpr
      nlinarith
    have hright : ε / 8 ≤ st.1 / ‖u + v‖ := by
      apply (le_div_iff₀ he).mpr
      nlinarith [mul_le_mul_of_nonneg_left he2 (div_nonneg hε (by norm_num : (0 : ℝ) ≤ 8))]
    exact hleft.trans hright
  have hdiv : |st.2 / ‖u - v‖| ≤ st.1 / ‖u + v‖ := by
    simpa only [abs_div, abs_of_pos hd] using hratio
  refine ⟨_, _, ?_, ?_, ridgeDisplacement_expansion u v st⟩
  · linarith [(abs_le.mp hdiv).1]
  · linarith [(abs_le.mp hdiv).2]

theorem ridgeRectangle_displacement_norm_le (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) {st : ℝ × ℝ} (hst : st ∈ ridgeRectangle u v ε) :
    ‖ridgeDisplacement u v st‖ ≤ ε := by
  have hd2 : ‖u - v‖ ≤ 2 := by
    have h := norm_sub_le u v
    rw [hu, hv] at h
    linarith
  have hs0 : 0 ≤ st.1 := (div_nonneg hε (by norm_num)).trans hst.1.1
  have ht : |st.2| ≤ ε * ‖u - v‖ / 8 :=
    abs_le.mpr ⟨by nlinarith [hst.2.1], hst.2.2⟩
  calc
    _ ≤ ‖st.1 • bisector u v‖ + ‖st.2 • differenceDirection u v‖ := norm_add_le _ _
    _ = st.1 + |st.2| := by
      simp only [norm_smul, Real.norm_eq_abs, norm_bisector u v hp,
        norm_differenceDirection u v hm, mul_one, abs_of_nonneg hs0]
    _ ≤ ε := by nlinarith [hst.1.2, mul_le_mul_of_nonneg_left hd2 hε]

theorem ridgeRectangle_displacement_ne_zero (u v : E) (huv : ‖u‖ = ‖v‖)
    (hp : u + v ≠ 0) {ε : ℝ} (hε : 0 < ε)
    {st : ℝ × ℝ} (hst : st ∈ ridgeRectangle u v ε) :
    ridgeDisplacement u v st ≠ 0 := by
  intro hz
  have hh := congrArg (fun y => ⟪bisector u v, y⟫_ℝ) hz
  simp only [ridgeDisplacement, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_bisector u v hp, one_pow,
    inner_bisector_differenceDirection u v huv, mul_one, mul_zero, add_zero, inner_zero_right] at hh
  have hs := hst.1.1
  nlinarith

/-- The sum of the two tangential ridge distances. Pairing them before
estimating removes the inverse-sine singularity. -/
def pairedRidgeCoefficient (u v z : E) : ℝ :=
  (⟪v, z⟫_ℝ - ⟪u, v⟫_ℝ * ⟪u, z⟫_ℝ) /
      Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) +
  (⟪u, z⟫_ℝ - ⟪u, v⟫_ℝ * ⟪v, z⟫_ℝ) /
      Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2)

theorem norm_sum_mul_norm_sub (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) :
    ‖u + v‖ * ‖u - v‖ = 2 * Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) := by
  have he : 0 < ‖u + v‖ := norm_pos_iff.mpr hp
  have hd : 0 < ‖u - v‖ := norm_pos_iff.mpr hm
  have heq : ‖u + v‖ ^ 2 = 2 + 2 * ⟪u, v⟫_ℝ := by
    have h := norm_add_sq_real u v
    rw [hu, hv] at h
    nlinarith
  have hdq : ‖u - v‖ ^ 2 = 2 - 2 * ⟪u, v⟫_ℝ := by
    have h := norm_sub_sq_real u v
    rw [hu, hv] at h
    nlinarith
  have habs : -1 < ⟪u, v⟫_ℝ ∧ ⟪u, v⟫_ℝ < 1 := by
    constructor <;> nlinarith [sq_pos_of_pos he, sq_pos_of_pos hd]
  have hD : 0 ≤ 1 - ⟪u, v⟫_ℝ ^ 2 := by nlinarith
  apply (sq_eq_sq₀ (mul_nonneg he.le hd.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _))).mp
  calc
    (‖u + v‖ * ‖u - v‖) ^ 2 = ‖u + v‖ ^ 2 * ‖u - v‖ ^ 2 := by ring
    _ = (2 + 2 * ⟪u, v⟫_ℝ) * (2 - 2 * ⟪u, v⟫_ℝ) := by rw [heq, hdq]
    _ = (2 * Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2)) ^ 2 := by
      nlinarith [Real.sq_sqrt hD]

theorem pairedRidgeCoefficient_eq (u v z : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) :
    pairedRidgeCoefficient u v z = ‖u - v‖ * ⟪bisector u v, z⟫_ℝ := by
  have he : 0 < ‖u + v‖ := norm_pos_iff.mpr hp
  have hd : 0 < ‖u - v‖ := norm_pos_iff.mpr hm
  have hprod := norm_sum_mul_norm_sub u v hu hv hp hm
  have hs : 0 < Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) := by nlinarith [mul_pos he hd]
  have hdq : ‖u - v‖ ^ 2 = 2 - 2 * ⟪u, v⟫_ℝ := by
    have h := norm_sub_sq_real u v
    rw [hu, hv] at h
    nlinarith
  have hc : (1 - ⟪u, v⟫_ℝ) / Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) =
      ‖u - v‖ / ‖u + v‖ := by
    apply (div_eq_div_iff hs.ne' he.ne').mpr
    nlinarith [mul_pos he hd]
  simp only [pairedRidgeCoefficient, bisector, inner_smul_left, conj_trivial,
    inner_add_left]
  calc
    _ = ((1 - ⟪u, v⟫_ℝ) / Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2)) *
        (⟪u, z⟫_ℝ + ⟪v, z⟫_ℝ) := by ring
    _ = _ := by rw [hc]; ring

theorem abs_pairedRidgeCoefficient_le (u v z : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : u + v ≠ 0) (hm : u - v ≠ 0) :
    |pairedRidgeCoefficient u v z| ≤ ‖u - v‖ * ‖z‖ := by
  rw [pairedRidgeCoefficient_eq u v z hu hv hp hm, abs_mul, abs_norm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [norm_bisector u v hp, one_mul] using
    abs_real_inner_le_norm (bisector u v) z

omit [InnerProductSpace ℝ E] in
/-- Exact two-dimensional Lebesgue area, including degenerate width. -/
theorem ridgeRectangle_area (u v : E) {ε : ℝ} (hε : 0 ≤ ε) :
    ((volume : Measure ℝ).prod volume) (ridgeRectangle u v ε) =
      ENNReal.ofReal (ε ^ 2 * ‖u - v‖ / 16) := by
  rw [ridgeRectangle, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ ε / 2 - ε / 4)]
  congr 1
  ring

/-- An outward normal is stated by its actual variational inequality. -/
def IsOutwardNormal (C : Set E) (z v : E) : Prop :=
  ∀ w ∈ C, ⟪v, w - z⟫_ℝ ≤ 0

theorem outward_base_unique {C : Set E} {z w v q : E}
    (hz : z ∈ C) (hw : w ∈ C)
    (hv : IsOutwardNormal C z v) (hq : IsOutwardNormal C w q)
    (hy : z + v = w + q) : z = w := by
  have hvw := hv w hw
  have hqz := hq z hz
  have hvw' : 0 ≤ ⟪v, z - w⟫_ℝ := by
    have hh : w - z = -(z - w) := by module
    rw [hh, inner_neg_right] at hvw
    linarith
  have hdiff : z - w = q - v := by
    rw [eq_sub_of_add_eq hy]
    module
  have hsq : ‖z - w‖ ^ 2 ≤ 0 := by
    calc
      ‖z - w‖ ^ 2 = ⟪q - v, z - w⟫_ℝ := by rw [← hdiff, real_inner_self_eq_norm_sq]
      _ = ⟪q, z - w⟫_ℝ - ⟪v, z - w⟫_ℝ := inner_sub_left _ _ _
      _ ≤ 0 := by linarith
  have : ‖z - w‖ = 0 := by nlinarith [norm_nonneg (z - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

theorem outward_point_not_mem {C : Set E} {z v : E}
    (hv : IsOutwardNormal C z v) (hv0 : v ≠ 0) : z + v ∉ C := by
  intro hy
  have h := hv (z + v) hy
  rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h
  have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
  exact hv0 (norm_eq_zero.mp this)

/-- Actual orthogonal projection onto the plane of the two normals. -/
def pairProjection (u v z : E) : E :=
  ⟪bisector u v, z⟫_ℝ • bisector u v +
    ⟪differenceDirection u v, z⟫_ℝ • differenceDirection u v

theorem pairProjection_add (u v z y : E) :
    pairProjection u v (z + y) = pairProjection u v z + pairProjection u v y := by
  simp only [pairProjection, inner_add_right, add_smul]
  module

theorem pairProjection_norm_sq (u v z : E) (huv : ‖u‖ = ‖v‖)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) :
    ‖pairProjection u v z‖ ^ 2 =
      ⟪bisector u v, z⟫_ℝ ^ 2 + ⟪differenceDirection u v, z⟫_ℝ ^ 2 := by
  unfold pairProjection
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, norm_bisector u v hp,
    norm_differenceDirection u v hm, mul_one, sq_abs, inner_smul_left,
    inner_smul_right, conj_trivial, inner_bisector_differenceDirection u v huv, mul_zero,
    zero_mul, add_zero]

theorem pairProjection_norm_le (u v z : E) (huv : ‖u‖ = ‖v‖)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) : ‖pairProjection u v z‖ ≤ ‖z‖ := by
  have hB := (orthonormal_pairFrame u v huv hp hm).sum_inner_products_le
    (s := Finset.univ) z
  simp only [Finset.mem_univ, Finset.sum_const_zero, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Real.norm_eq_abs, sq_abs] at hB
  rw [← pairProjection_norm_sq u v z huv hp hm] at hB
  nlinarith [norm_nonneg z, norm_nonneg (pairProjection u v z)]

theorem pairProjection_ridgeDisplacement (u v : E) (huv : ‖u‖ = ‖v‖)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) (st : ℝ × ℝ) :
    pairProjection u v (ridgeDisplacement u v st) = ridgeDisplacement u v st := by
  simp only [pairProjection, ridgeDisplacement, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_bisector u v hp, norm_differenceDirection u v hm,
    one_pow, mul_one, inner_bisector_differenceDirection u v huv, mul_zero, add_zero]
  have hcb : ⟪differenceDirection u v, bisector u v⟫_ℝ = 0 := by
    calc
      _ = ⟪bisector u v, differenceDirection u v⟫_ℝ := real_inner_comm _ _
      _ = 0 := inner_bisector_differenceDirection u v huv
  simp only [hcb, mul_zero, zero_add]

theorem pairProjection_shell_event (u v z y : E) (huv : ‖u‖ = ‖v‖)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0) {R : ℝ}
    (hbase : R ≤ ‖pairProjection u v z‖) (hy : ‖y‖ ≤ 1) :
    R - 1 ≤ ‖pairProjection u v (z + y)‖ := by
  have htriangle : ‖pairProjection u v z‖ ≤
      ‖pairProjection u v (z + y)‖ + ‖pairProjection u v y‖ := by
    have heq : pairProjection u v z =
        pairProjection u v (z + y) - pairProjection u v y := by
      rw [pairProjection_add]
      module
    rw [heq]
    exact norm_sub_le _ _
  have hproj := pairProjection_norm_le u v y huv hp hm
  linarith

/-- The paired numerator before the coarea factor. This is exactly the
quantity produced by tangent Gaussian Stein for the smooth selector. -/
def pairedRidgeNumerator (u v z : E) : ℝ :=
  (1 - ⟪u, v⟫_ℝ) * (⟪u, z⟫_ℝ + ⟪v, z⟫_ℝ)

theorem pairedRidgeNumerator_eq (u v z : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    pairedRidgeNumerator u v z = ‖u - v‖ *
      Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) * ⟪bisector u v, z⟫_ℝ := by
  by_cases hp : u + v = 0
  · simp only [pairedRidgeNumerator, ← inner_add_left, hp, inner_zero_left, mul_zero]
    simp [bisector, hp]
  by_cases hm : u - v = 0
  · have hvu : u = v := sub_eq_zero.mp hm
    subst v
    simp [pairedRidgeNumerator, real_inner_self_eq_norm_sq, hu]
  have he : 0 < ‖u + v‖ := norm_pos_iff.mpr hp
  have hd : 0 < ‖u - v‖ := norm_pos_iff.mpr hm
  have hprod := norm_sum_mul_norm_sub u v hu hv hp hm
  have hs : 0 < Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) := by nlinarith [mul_pos he hd]
  have hid : pairedRidgeNumerator u v z =
      pairedRidgeCoefficient u v z * Real.sqrt (1 - ⟪u, v⟫_ℝ ^ 2) := by
    unfold pairedRidgeNumerator pairedRidgeCoefficient
    field_simp
    ring
  rw [hid, pairedRidgeCoefficient_eq u v z hu hv hp hm]
  ring

end
end RectangleCLT.Companion.SignedSurface
