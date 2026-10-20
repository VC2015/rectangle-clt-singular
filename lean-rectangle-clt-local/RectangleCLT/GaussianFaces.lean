import RectangleCLT.LocalCovariance
import RectangleCLT.Statement
import RectangleCLT.SmootherConvolution
import Mathlib.Tactic.Ring

/-!
# Signed active faces and outward normal tubes

These are finite-dimensional algebraic and geometric ingredients for Gaussian
face estimates. In particular, the tube disjointness theorem below is an actual
geometric statement. No Gaussian face integral or coarea formula is assumed.
-/

open scoped BigOperators

namespace RectangleCLT

noncomputable section

def faceSign {p : ℕ} (f : Face p) : ℝ := if f.2 then 1 else -1

@[simp] theorem faceSign_sq {p : ℕ} (f : Face p) : faceSign f ^ 2 = 1 := by
  cases f with | mk j b => cases b <;> norm_num [faceSign]

@[simp] theorem abs_faceSign {p : ℕ} (f : Face p) : |faceSign f| = 1 := by
  cases f with | mk j b => cases b <;> norm_num [faceSign]

/-- An active tuple cannot contain the two opposite faces of one coordinate.
The empty tuple and tuples of size greater than the dimension are handled by
the same definition (the latter have no inhabitants). -/
structure CompatibleFaceTuple (p q : ℕ) where
  face : Fin q → Face p
  coordinate_injective : Function.Injective (fun i => (face i).1)

namespace CompatibleFaceTuple

variable {p q : ℕ} (S : CompatibleFaceTuple p q)

def gram (Q : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => faceSign (S.face i) * faceSign (S.face j) * Q (S.face i).1 (S.face j).1

/-- Extension of signed active coefficients by zero to the original coordinates. -/
def lift (u : Fin q → ℝ) : Fin p → ℝ :=
  fun j => ∑ i, if (S.face i).1 = j then faceSign (S.face i) * u i else 0

theorem lift_at (u : Fin q → ℝ) (i : Fin q) :
    S.lift u (S.face i).1 = faceSign (S.face i) * u i := by
  classical
  unfold lift
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp only [if_neg (fun h => hji (S.coordinate_injective h))]
  · simp

theorem lift_off (u : Fin q → ℝ) (j : Fin p)
    (hj : j ∉ Finset.univ.image (fun i => (S.face i).1)) : S.lift u j = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun hi => hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))

theorem support_lift (u : Fin q → ℝ) :
    coordinateSupport (S.lift u) ⊆ Finset.univ.image (fun i => (S.face i).1) := by
  classical
  intro j hj
  by_contra hn
  have hz := S.lift_off u j hn
  simp only [coordinateSupport, Finset.mem_filter, Finset.mem_univ, true_and, hz,
    ne_eq, not_true_eq_false] at hj

theorem support_lift_card (u : Fin q → ℝ) :
    (coordinateSupport (S.lift u)).card ≤ q := by
  exact (Finset.card_le_card (S.support_lift u)).trans
    ((Finset.card_image_le).trans (by simp))

theorem sum_lift (u : Fin q → ℝ) (g : Fin p → ℝ) :
    (∑ j, S.lift u j * g j) = ∑ i, faceSign (S.face i) * u i * g (S.face i).1 := by
  classical
  simp only [lift, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

theorem normSq_lift (u : Fin q → ℝ) :
    vectorNormSq (S.lift u) = vectorNormSq u := by
  classical
  unfold vectorNormSq
  calc
    _ = ∑ j ∈ Finset.univ.image (fun i => (S.face i).1), S.lift u j ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [S.lift_off u j hj]
    _ = ∑ i, S.lift u (S.face i).1 ^ 2 :=
      Finset.sum_image (fun i _ j _ hij => S.coordinate_injective hij)
    _ = ∑ i, u i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [S.lift_at, mul_pow, faceSign_sq, one_mul]

theorem quadratic_lift (Q : Matrix (Fin p) (Fin p) ℝ) (u : Fin q → ℝ) :
    matrixQuadratic Q (S.lift u) = matrixQuadratic (S.gram Q) u := by
  unfold matrixQuadratic
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [S.sum_lift]
  apply Finset.sum_congr rfl
  intro i _
  have hi := S.sum_lift u (fun k => Q (S.face i).1 k)
  simp_rw [mul_comm (Q (S.face i).1 _) (S.lift u _)]
  rw [hi]
  simp only [Finset.mul_sum, gram]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Sparse lower bounds pass to every compatible signed principal Gram matrix.
This works for singular full covariance matrices. -/
theorem gram_lower {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (hQ : LocalCovarianceLower Q q a) (u : Fin q → ℝ) :
    a * vectorNormSq u ≤ matrixQuadratic (S.gram Q) u := by
  simpa only [S.normSq_lift, S.quadratic_lift] using hQ (S.lift u) (S.support_lift_card u)

theorem gram_diagonal {Q : Matrix (Fin p) (Fin p) ℝ}
    (hdiag : ∀ j, Q j j = 1) (i : Fin q) : S.gram Q i i = 1 := by
  simp only [gram, hdiag, mul_one, ← pow_two, faceSign_sq, one_pow]

theorem gram_symmetric {Q : Matrix (Fin p) (Fin p) ℝ}
    (hsym : ∀ i j, Q i j = Q j i) (i j : Fin q) : S.gram Q i j = S.gram Q j i := by
  unfold gram
  rw [hsym (S.face i).1 (S.face j).1]
  ring

theorem abs_gram_offDiagonal {Q : Matrix (Fin p) (Fin p) ℝ}
    (i j : Fin q) (hij : i ≠ j) : |S.gram Q i j| ≤ 1 - pairGap Q := by
  simpa only [gram, abs_mul, abs_faceSign, one_mul] using
    abs_offDiagonal_le Q (S.face i).1 (S.face j).1
      (fun h => hij (S.coordinate_injective h))

end CompatibleFaceTuple

namespace FaceWeights

theorem abs_directionalMean_le_norm {p : ℕ} (w : FaceWeights p) (y : Fin p → ℝ) :
    |w.directionalMean y| ≤ ‖y‖ := by
  rw [w.directionalMean_eq]
  calc
    _ ≤ ∑ j, |w.v j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w.v j| * ‖y‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y j) (abs_nonneg _)
    _ = (∑ j, |w.v j|) * ‖y‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right w.sum_abs_v_le_one (norm_nonneg _)
    _ = _ := one_mul _

end FaceWeights

private theorem hasDerivAt_prod_scaled {ι : Type*} (S : Finset ι)
    (f : ι → ℝ → ℝ) (r : ι → ℝ) (t : ℝ)
    (hf : ∀ i ∈ S, HasDerivAt (f i) (f i t * r i) t) :
    HasDerivAt (fun a => ∏ i ∈ S, f i a)
      ((∏ i ∈ S, f i t) * ∑ i ∈ S, r i) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hasDerivAt_const t (1 : ℝ)
  | @insert i S hi ih =>
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hprod := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    convert hfi.mul hprod using 1
    · ext a
      simp only [Finset.prod_insert hi]
    · simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      ring

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- A positive soft active-face weight. Its Gaussian integral is the smooth
analogue of the corresponding Gaussian face density. -/
def softFaceWeight (S : Finset (Face p)) (x : Fin p → ℝ) : ℝ :=
  s.F x * ∏ f ∈ S, (s.weights x).pi f

theorem softFaceWeight_nonneg (S : Finset (Face p)) (x : Fin p → ℝ) :
    0 ≤ s.softFaceWeight S x :=
  mul_nonneg (s.weights x).F_pos.le
    (Finset.prod_nonneg (fun f _ => (s.weights x).pi_nonneg f))

theorem hasDerivAt_softFaceWeight_line (S : Finset (Face p))
    (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun a => s.softFaceWeight S (line x y a))
      (s.softFaceWeight S (line x y t) / s.bandwidth *
        ((∑ f ∈ S, normalDot f y) -
          ((S.card : ℝ) + 1) * (s.weights (line x y t)).directionalMean y)) t := by
  have hpi (f : Face p) (_hf : f ∈ S) :
      HasDerivAt (fun a => (s.weights (line x y a)).pi f)
        ((s.weights (line x y t)).pi f *
          ((normalDot f y - (s.weights (line x y t)).directionalMean y) / s.bandwidth)) t := by
    convert s.hasDerivAt_pi_line f x y t using 1
    simp only [pi]
    ring
  have hp := hasDerivAt_prod_scaled S
    (fun f a => (s.weights (line x y a)).pi f)
    (fun f => (normalDot f y - (s.weights (line x y t)).directionalMean y) / s.bandwidth) t hpi
  convert (s.hasDerivAt_F_line x y t).mul hp using 1
  simp only [softFaceWeight, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

@[fun_prop] theorem continuous_softFaceWeight (S : Finset (Face p)) :
    Continuous (s.softFaceWeight S) :=
  s.continuous_F.mul (continuous_finset_prod S (fun f _ => s.continuous_pi f))

theorem softFaceWeight_le_one (S : Finset (Face p)) (x : Fin p → ℝ) :
    s.softFaceWeight S x ≤ 1 := by
  have hp : (∏ f ∈ S, (s.weights x).pi f) ≤ 1 := by
    apply Finset.prod_le_one
    · exact fun f _ => (s.weights x).pi_nonneg f
    · exact fun f _ => ((s.weights x).pi_le_theta f).trans (s.weights x).theta_lt_one.le
  exact (mul_le_mul_of_nonneg_left hp (s.F_pos x).le).trans (by simpa using s.F_le_one x)

theorem normalDot_coordinate_eq (f : Face p) (j : Fin p) :
    normalDot f (coordinateDirection j) = if f.1 = j then faceSign f else 0 := by
  cases f with | mk k b => cases b <;> by_cases h : k = j <;>
    simp [normalDot, coordinateDirection, faceSign, h]

theorem softFaceWeight_insert (S : Finset (Face p)) (x : Fin p → ℝ)
    (f : Face p) (hf : f ∉ S) :
    s.softFaceWeight (insert f S) x = s.softFaceWeight S x * (s.weights x).pi f := by
  classical
  simp only [softFaceWeight, Finset.prod_insert hf]
  ring

/-- A derivative in an inactive coordinate creates the two signed enlarged
active faces with opposite signs. This is an actual derivative identity and
handles both finite endpoints without assigning mass to incompatible faces. -/
theorem hasDerivAt_softFaceWeight_inactive_coordinate (S : Finset (Face p))
    (j : Fin p) (hj : ∀ f ∈ S, f.1 ≠ j) (x : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun a => s.softFaceWeight S (line x (coordinateDirection j) a))
      (-(((S.card : ℝ) + 1) / s.bandwidth) *
        (s.softFaceWeight (insert (j, true) S) (line x (coordinateDirection j) t) -
          s.softFaceWeight (insert (j, false) S) (line x (coordinateDirection j) t))) t := by
  classical
  have hp : (j, true) ∉ S := fun h => hj _ h rfl
  have hm : (j, false) ∉ S := fun h => hj _ h rfl
  have hnormal : (∑ f ∈ S, normalDot f (coordinateDirection j)) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    simp only [normalDot_coordinate_eq, if_neg (hj f hf)]
  convert s.hasDerivAt_softFaceWeight_line S x (coordinateDirection j) t using 1
  rw [hnormal, directionalMean_coordinate, s.softFaceWeight_insert S _ _ hp,
    s.softFaceWeight_insert S _ _ hm]
  simp only [FaceWeights.v]
  ring

end FaceSmoother

/-- Explicit dot product, keeping the geometry independent of a choice between
the maximum norm and the Euclidean norm on finite real products. -/
def faceDot {p : ℕ} (x y : Fin p → ℝ) : ℝ := ∑ j, x j * y j

theorem faceDot_comm {p : ℕ} (x y : Fin p → ℝ) : faceDot x y = faceDot y x := by
  simp only [faceDot, mul_comm]

/-- A polyhedron described by a finite family of arbitrary real normals. -/
def facePolyhedron {p : ℕ} {ι : Type*} (faces : Finset ι)
    (normal : ι → Fin p → ℝ) (offset : ι → ℝ) : Set (Fin p → ℝ) :=
  {x | ∀ a ∈ faces, faceDot (normal a) x ≤ offset a}

/-- Points whose complete active set is exactly `active`. This excludes the
lower-dimensional boundaries shared with faces of larger active order. -/
def exactActiveFace {p : ℕ} {ι : Type*} (faces active : Finset ι)
    (normal : ι → Fin p → ℝ) (offset : ι → ℝ) : Set (Fin p → ℝ) :=
  {x | x ∈ facePolyhedron faces normal offset ∧
    ∀ a ∈ faces, faceDot (normal a) x = offset a ↔ a ∈ active}

def outwardDisplacement {p : ℕ} {ι : Type*} (active : Finset ι)
    (normal : ι → Fin p → ℝ) (u : ι → ℝ) : Fin p → ℝ :=
  fun j => ∑ a ∈ active, u a * normal a j

theorem outwardDisplacement_variational {p : ℕ} {ι : Type*}
    {faces active : Finset ι} {normal : ι → Fin p → ℝ} {offset : ι → ℝ}
    {z w : Fin p → ℝ} {u : ι → ℝ} (hsub : active ⊆ faces)
    (hz : z ∈ exactActiveFace faces active normal offset)
    (hw : w ∈ facePolyhedron faces normal offset)
    (hu : ∀ a ∈ active, 0 ≤ u a) :
    faceDot (outwardDisplacement active normal u) (w - z) ≤ 0 := by
  classical
  unfold faceDot outwardDisplacement
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_nonpos
  intro a ha
  have hza : faceDot (normal a) z = offset a := (hz.2 a (hsub ha)).mpr ha
  have hwa := hw a (hsub ha)
  have hinner : (∑ j, normal a j * (w - z) j) ≤ 0 := by
    simpa only [faceDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] using
      sub_nonpos.mpr (hwa.trans_eq hza.symm)
  simpa only [mul_assoc, ← Finset.mul_sum] using mul_nonpos_of_nonneg_of_nonpos (hu a ha) hinner

/-- An outward normal representation determines its base point uniquely.
This is the metric projection argument, proved directly as a finite sum of
squares, without assuming any projection or Gaussian integration oracle. -/
theorem outward_base_unique {p : ℕ} {ι : Type*}
    {faces active other : Finset ι} {normal : ι → Fin p → ℝ} {offset : ι → ℝ}
    {z w : Fin p → ℝ} {u v : ι → ℝ}
    (ha : active ⊆ faces) (hb : other ⊆ faces)
    (hz : z ∈ exactActiveFace faces active normal offset)
    (hw : w ∈ exactActiveFace faces other normal offset)
    (hu : ∀ a ∈ active, 0 ≤ u a) (hv : ∀ a ∈ other, 0 ≤ v a)
    (heq : z + outwardDisplacement active normal u =
      w + outwardDisplacement other normal v) : z = w := by
  have h₁ := outwardDisplacement_variational ha hz hw.1 hu
  have h₂ := outwardDisplacement_variational hb hw hz.1 hv
  have heach (j : Fin p) :
      (z j - w j) ^ 2 =
        outwardDisplacement active normal u j * (w j - z j) +
        outwardDisplacement other normal v j * (z j - w j) := by
    have hj := congrFun heq j
    simp only [Pi.add_apply] at hj
    have hd : outwardDisplacement active normal u j =
        outwardDisplacement other normal v j + (w j - z j) := by linarith
    rw [hd]
    ring
  have hsum : vectorNormSq (z - w) ≤ 0 := by
    simpa only [vectorNormSq, Pi.sub_apply, heach, Finset.sum_add_distrib,
      faceDot] using add_nonpos h₁ h₂
  have hzero : vectorNormSq (z - w) = 0 := le_antisymm hsum (vectorNormSq_nonneg _)
  have hzw : z - w = 0 := by
    apply Classical.byContradiction
    intro hn
    exact (ne_of_gt (vectorNormSq_pos hn)) hzero
  exact sub_eq_zero.mp hzw

def outwardTube {p : ℕ} {ι : Type*} (faces active : Finset ι)
    (normal : ι → Fin p → ℝ) (offset : ι → ℝ) (width : ℝ) : Set (Fin p → ℝ) :=
  {y | ∃ z ∈ exactActiveFace faces active normal offset, ∃ u : ι → ℝ,
    (∀ a ∈ active, 0 < u a ∧ u a < width) ∧ y = z + outwardDisplacement active normal u}

/-- Distinct exact active faces have disjoint positive outward tubes, for every
width. The Gaussian lower bound for each tube is a separate analytic step. -/
theorem outwardTube_disjoint {p : ℕ} {ι : Type*}
    {faces active other : Finset ι} {normal : ι → Fin p → ℝ} {offset : ι → ℝ}
    {width : ℝ} (ha : active ⊆ faces) (hb : other ⊆ faces) (hne : active ≠ other) :
    Disjoint (outwardTube faces active normal offset width)
      (outwardTube faces other normal offset width) := by
  rw [Set.disjoint_left]
  rintro y ⟨z, hz, u, hu, hy⟩ ⟨w, hw, v, hv, hy'⟩
  have hzw := outward_base_unique ha hb hz hw
    (fun a ha => (hu a ha).1.le) (fun a ha => (hv a ha).1.le) (hy.symm.trans hy')
  apply hne
  ext a
  by_cases haf : a ∈ faces
  · exact (hz.2 a haf).symm.trans (hzw ▸ hw.2 a haf)
  · exact iff_of_false (fun h => haf (ha h)) (fun h => haf (hb h))

/-- Standard Gaussian density with its dimension-dependent normalizing constant
omitted. This constant cancels in every tube/base density ratio. -/
def gaussianKernel {p : ℕ} (x : Fin p → ℝ) : ℝ := Real.exp (-vectorNormSq x / 2)

theorem gaussianKernel_pos {p : ℕ} (x : Fin p → ℝ) : 0 < gaussianKernel x :=
  Real.exp_pos _

theorem gaussianKernel_translate {p : ℕ} (z d : Fin p → ℝ) :
    gaussianKernel (z + d) = gaussianKernel z *
      Real.exp (-faceDot d z - vectorNormSq d / 2) := by
  have hn : vectorNormSq (z + d) =
      vectorNormSq z + 2 * faceDot d z + vectorNormSq d := by
    calc
      _ = ∑ j, (z j ^ 2 + 2 * (d j * z j) + d j ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.add_apply]
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        vectorNormSq, faceDot]
  unfold gaussianKernel
  rw [hn, ← Real.exp_add]
  congr 1
  ring

theorem gaussianKernel_translate_lower {p : ℕ} (z d : Fin p → ℝ)
    (hlinear : faceDot d z ≤ 1) (hquadratic : vectorNormSq d ≤ 1) :
    Real.exp (-(3 / 2 : ℝ)) * gaussianKernel z ≤ gaussianKernel (z + d) := by
  rw [gaussianKernel_translate, mul_comm (Real.exp _)]
  apply mul_le_mul_of_nonneg_left _ (gaussianKernel_pos z).le
  exact Real.exp_le_exp.mpr (by linarith)

/-- Signed coordinate rows of an actual Gaussian factor. -/
def signedRowNormal {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Face p) : Fin p → ℝ := fun j => faceSign f * A f.1 j

theorem signedRowNormal_gram {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f g : Face p) :
    faceDot (signedRowNormal A f) (signedRowNormal A g) =
      faceSign f * faceSign g * (A * A.transpose) f.1 g.1 := by
  simp only [faceDot, signedRowNormal, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

namespace CompatibleFaceTuple

variable {p q : ℕ} (S : CompatibleFaceTuple p q)

/-- The normal vector with prescribed active dual coefficients. -/
def normalCombination (A : Matrix (Fin p) (Fin p) ℝ) (u : Fin q → ℝ) : Fin p → ℝ :=
  fun j => ∑ i, u i * signedRowNormal A (S.face i) j

def activeScores (A : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ) : Fin q → ℝ :=
  fun i => faceDot (signedRowNormal A (S.face i)) x

/-- The usual Gaussian regression mean on the active equality plane. -/
def regressionMean (A : Matrix (Fin p) (Fin p) ℝ) (b : Fin q → ℝ) : Fin p → ℝ :=
  S.normalCombination A ((S.gram (A * A.transpose))⁻¹.mulVec b)

/-- Orthogonal residual expressed directly as a linear map of a standard
Gaussian vector. Its probabilistic law is concrete even when the full
covariance is singular. -/
def regressionResidual (A : Matrix (Fin p) (Fin p) ℝ) (z : Fin p → ℝ) : Fin p → ℝ :=
  z - S.regressionMean A (S.activeScores A z)

def radiusSq (A : Matrix (Fin p) (Fin p) ℝ) (b : Fin q → ℝ) : ℝ :=
  faceDot b ((S.gram (A * A.transpose))⁻¹.mulVec b)

theorem normalCombination_dot (A : Matrix (Fin p) (Fin p) ℝ)
    (u : Fin q → ℝ) (x : Fin p → ℝ) :
    faceDot (S.normalCombination A u) x = faceDot u (S.activeScores A x) := by
  simp only [faceDot, normalCombination, activeScores, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem activeScores_normalCombination (A : Matrix (Fin p) (Fin p) ℝ)
    (u : Fin q → ℝ) :
    S.activeScores A (S.normalCombination A u) = (S.gram (A * A.transpose)).mulVec u := by
  funext i
  unfold activeScores normalCombination faceDot
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ k, ∑ j, signedRowNormal A (S.face i) j *
    (u k * signedRowNormal A (S.face k) j)) = _
  calc
    _ = ∑ k, u k * faceDot (signedRowNormal A (S.face i)) (signedRowNormal A (S.face k)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [faceDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [signedRowNormal_gram, Matrix.mulVec, dotProduct, gram, mul_comm (u _)]

theorem activeScores_regressionMean (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) (b : Fin q → ℝ) :
    S.activeScores A (S.regressionMean A b) = b := by
  unfold regressionMean
  rw [S.activeScores_normalCombination, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

theorem activeScores_regressionResidual (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) (z : Fin p → ℝ) :
    S.activeScores A (S.regressionResidual A z) = 0 := by
  have hmean := S.activeScores_regressionMean A hd (S.activeScores A z)
  funext i
  have hi := congrFun hmean i
  simpa only [activeScores, regressionResidual, faceDot, Pi.sub_apply,
    mul_sub, Finset.sum_sub_distrib, Pi.zero_apply, sub_eq_zero] using hi.symm

/-- The active radius is the actual squared Euclidean norm of the Gaussian
regression mean, rather than an unrelated formal matrix expression. -/
theorem regressionMean_normSq (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) (b : Fin q → ℝ) :
    vectorNormSq (S.regressionMean A b) = S.radiusSq A b := by
  rw [show vectorNormSq (S.regressionMean A b) =
    faceDot (S.regressionMean A b) (S.regressionMean A b) by
      simp only [vectorNormSq, faceDot, pow_two]]
  unfold regressionMean
  rw [S.normalCombination_dot]
  change faceDot ((S.gram (A * A.transpose))⁻¹.mulVec b)
    (S.activeScores A (S.regressionMean A b)) = _
  rw [S.activeScores_regressionMean A hd]
  exact faceDot_comm _ _

theorem radiusSq_nonneg (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) (b : Fin q → ℝ) :
    0 ≤ S.radiusSq A b := by
  rw [← S.regressionMean_normSq A hd]
  exact vectorNormSq_nonneg _

def marginalDensity (A : Matrix (Fin p) (Fin p) ℝ) (b : Fin q → ℝ) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ q * (S.gram (A * A.transpose)).det))⁻¹ *
    Real.exp (-S.radiusSq A b / 2)

theorem marginalDensity_nonneg (A : Matrix (Fin p) (Fin p) ℝ) (b : Fin q → ℝ) :
    0 ≤ S.marginalDensity A b :=
  mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_pos _).le

/-- Conditional Gaussian probability of all inactive face inequalities.
This is defined using an actual pushforward of the standard product Gaussian,
rather than an unspecified Gaussian-face integration functional. -/
def conditionalFaceMass (A : Matrix (Fin p) (Fin p) ℝ) (faces : Finset (Face p))
    (b : Fin q → ℝ) (t : Face p → ℝ) : ℝ :=
  (standardGaussian p).real {z | ∀ f ∈ faces, f ∉ Finset.univ.image S.face →
    faceDot (signedRowNormal A f) (S.regressionMean A b + S.regressionResidual A z) ≤ t f}

/-- The Gaussian regression representation of an active-face density.
Identification with mixed threshold derivatives and with Hausdorff face
integrals requires separate coarea/conditional-Gaussian theorems. -/
def density (A : Matrix (Fin p) (Fin p) ℝ) (faces : Finset (Face p))
    (b : Fin q → ℝ) (t : Face p → ℝ) : ℝ :=
  S.marginalDensity A b * S.conditionalFaceMass A faces b t

theorem conditionalFaceMass_nonneg (A : Matrix (Fin p) (Fin p) ℝ)
    (faces : Finset (Face p)) (b : Fin q → ℝ) (t : Face p → ℝ) :
    0 ≤ S.conditionalFaceMass A faces b t := MeasureTheory.measureReal_nonneg

theorem conditionalFaceMass_le_one (A : Matrix (Fin p) (Fin p) ℝ)
    (faces : Finset (Face p)) (b : Fin q → ℝ) (t : Face p → ℝ) :
    S.conditionalFaceMass A faces b t ≤ 1 := MeasureTheory.measureReal_le_one

theorem density_nonneg (A : Matrix (Fin p) (Fin p) ℝ)
    (faces : Finset (Face p)) (b : Fin q → ℝ) (t : Face p → ℝ) :
    0 ≤ S.density A faces b t :=
  mul_nonneg (S.marginalDensity_nonneg A b) (S.conditionalFaceMass_nonneg A faces b t)

/-- Dropping inactive inequalities gives the exact marginal density majorant. -/
theorem density_le_marginal (A : Matrix (Fin p) (Fin p) ℝ)
    (faces : Finset (Face p)) (b : Fin q → ℝ) (t : Face p → ℝ) :
    S.density A faces b t ≤ S.marginalDensity A b := by
  exact (mul_le_mul_of_nonneg_left (S.conditionalFaceMass_le_one A faces b t)
    (S.marginalDensity_nonneg A b)).trans_eq (mul_one _)

theorem conditionalFaceMass_mono (A : Matrix (Fin p) (Fin p) ℝ)
    (faces : Finset (Face p)) (b : Fin q → ℝ) {t t' : Face p → ℝ}
    (htt' : ∀ f ∈ faces, f ∉ Finset.univ.image S.face → t f ≤ t' f) :
    S.conditionalFaceMass A faces b t ≤ S.conditionalFaceMass A faces b t' := by
  apply MeasureTheory.measureReal_mono ?_ (MeasureTheory.measure_ne_top _ _)
  intro z hz f hf hfa
  exact (hz f hf hfa).trans (htt' f hf hfa)

theorem density_mono (A : Matrix (Fin p) (Fin p) ℝ)
    (faces : Finset (Face p)) (b : Fin q → ℝ) {t t' : Face p → ℝ}
    (htt' : ∀ f ∈ faces, f ∉ Finset.univ.image S.face → t f ≤ t' f) :
    S.density A faces b t ≤ S.density A faces b t' :=
  mul_le_mul_of_nonneg_left (S.conditionalFaceMass_mono A faces b htt')
    (S.marginalDensity_nonneg A b)

end CompatibleFaceTuple

end

end RectangleCLT
