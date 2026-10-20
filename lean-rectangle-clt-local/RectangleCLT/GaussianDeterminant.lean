import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Polynomial.Roots

/-! Rectangular determinant identities used in Gaussian normal-map estimates.
The Cauchy--Binet identity here is stated over ordered tuples; the permutation
factor avoids choosing an ordering on arbitrary finite subsets. -/

open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem det_mul_rectangular_expand {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (A : Matrix n m ℝ) (B : Matrix m n ℝ) :
    (A * B).det = ∑ f : n → m, (A.submatrix id f).det * ∏ i, B (f i) i := by
  classical
  calc
    (A * B).det = ∑ f : n → m, ∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) (f i) * B (f i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
        Finset.mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
        Finset.sum_mul, Finset.prod_mul_distrib, mul_assoc]

/-- Cauchy--Binet with ordered tuples. Repeated entries contribute zero, and
each unordered minor occurs once for every permutation of its columns. -/
theorem cauchyBinet_ordered {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (A : Matrix n m ℝ) (B : Matrix m n ℝ) :
    (Fintype.card (Equiv.Perm n) : ℝ) * (A * B).det =
      ∑ f : n → m, (A.submatrix id f).det * (B.submatrix f id).det := by
  classical
  have hperm (σ : Equiv.Perm n) :
      (∑ f : n → m, (A.submatrix id f).det *
        (((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, B (f (σ i)) i)) = (A * B).det := by
    let e : (n → m) ≃ (n → m) := Equiv.arrowCongr σ (Equiv.refl m)
    have he (f : n → m) (i : n) : e f i = f (σ.symm i) := rfl
    rw [← e.sum_comp]
    calc
      _ = ∑ f : n → m, (A.submatrix id f).det * ∏ i, B (f i) i := by
        apply Finset.sum_congr rfl
        intro f _
        have hA : (A.submatrix id (e f)).det =
            ((Equiv.Perm.sign σ : ℤ) : ℝ) * (A.submatrix id f).det := by
          have := Matrix.det_permute' σ.symm (A.submatrix id f)
          simpa only [Matrix.submatrix_submatrix, Function.comp_def, he,
            Equiv.Perm.sign_symm] using this
        rw [hA]
        simp only [he, Equiv.symm_apply_apply]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simp [hσ]
      _ = _ := (det_mul_rectangular_expand A B).symm
  calc
    _ = ∑ σ : Equiv.Perm n, (A * B).det := by simp
    _ = ∑ σ : Equiv.Perm n, ∑ f : n → m,
        (A.submatrix id f).det *
          (((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, B (f (σ i)) i) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (hperm σ).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq, Finset.mul_sum]

/-- The rectangular Gram determinant is a sum of squared minors, with the
ordered-tuple permutation factor. -/
theorem gram_det_ordered {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (A : Matrix n m ℝ) :
    (Fintype.card (Equiv.Perm n) : ℝ) * (A * A.transpose).det =
      ∑ f : n → m, ((A.submatrix id f).det) ^ 2 := by
  rw [cauchyBinet_ordered]
  apply Finset.sum_congr rfl
  intro f _
  have h : A.transpose.submatrix f id = (A.submatrix id f).transpose := rfl
  rw [h, Matrix.det_transpose]
  ring

/-- The weighted second moment of a finite family of column vectors. -/
def weightedGram {n m : Type*} [Fintype m] (X : Matrix n m ℝ) (w : m → ℝ) :
    Matrix n n ℝ := fun j k => ∑ i, w i * X j i * X k i

def weightedMean {n m : Type*} [Fintype m] (X : Matrix n m ℝ) (w : m → ℝ) :
    n → ℝ := fun j => ∑ i, w i * X j i

def weightedCovariance {n m : Type*} [Fintype m] (X : Matrix n m ℝ) (w : m → ℝ) :
    Matrix n n ℝ := fun j k => weightedGram X w j k - weightedMean X w j * weightedMean X w k

/-- Weighted Cauchy--Binet, valid without any positivity hypotheses. -/
theorem weightedGram_det_ordered {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (X : Matrix n m ℝ) (w : m → ℝ) :
    (Fintype.card (Equiv.Perm n) : ℝ) * (weightedGram X w).det =
      ∑ f : n → m, (∏ i, w (f i)) * ((X.submatrix id f).det) ^ 2 := by
  let B : Matrix m n ℝ := fun i j => w i * X j i
  have hGram : weightedGram X w = X * B := by
    ext j k
    simp only [weightedGram, Matrix.mul_apply, B]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hGram, cauchyBinet_ordered]
  apply Finset.sum_congr rfl
  intro f _
  have hB : B.submatrix f id =
      Matrix.of (fun i j => w (f i) * (X.submatrix id f).transpose i j) := rfl
  rw [hB, Matrix.det_mul_column, Matrix.det_transpose]
  ring

/-- Adjoin an affine coordinate of value one to every column. -/
def augmentedColumns {n m : Type*} (X : Matrix n m ℝ) : Matrix (Unit ⊕ n) m ℝ :=
  fun j i => match j with
    | .inl _ => 1
    | .inr k => X k i

/-- The Schur complement of the normalized affine Gram matrix is precisely
the finite weighted covariance. -/
theorem det_augmented_weightedGram {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (X : Matrix n m ℝ) (w : m → ℝ)
    (hw : ∑ i, w i = 1) :
    (weightedGram (augmentedColumns X) w).det = (weightedCovariance X w).det := by
  have hblock : weightedGram (augmentedColumns X) w =
      Matrix.fromBlocks (1 : Matrix Unit Unit ℝ)
        (fun _ k => weightedMean X w k : Matrix Unit n ℝ)
        (fun j _ => weightedMean X w j : Matrix n Unit ℝ)
        (weightedGram X w) := by
    ext i j
    cases i with
    | inl i => cases j <;> simp [weightedGram, augmentedColumns, weightedMean, hw]
    | inr i => cases j <;> simp [weightedGram, augmentedColumns, weightedMean]
  rw [hblock, Matrix.det_fromBlocks_one₁₁]
  congr 1
  ext j k
  simp [weightedCovariance, Matrix.mul_apply]

/-- An ordered sum-of-squares formula for every finite covariance determinant.
The weights need only sum to one; their nonnegativity is used separately when
discarding terms. -/
theorem weightedCovariance_det_ordered {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (X : Matrix n m ℝ) (w : m → ℝ)
    (hw : ∑ i, w i = 1) :
    (Fintype.card (Equiv.Perm (Unit ⊕ n)) : ℝ) * (weightedCovariance X w).det =
      ∑ f : (Unit ⊕ n) → m,
        (∏ i, w (f i)) * (((augmentedColumns X).submatrix id f).det) ^ 2 := by
  rw [← det_augmented_weightedGram X w hw, weightedGram_det_ordered]

/-- A distinguished zero point, in addition to the given columns. -/
def withZeroColumn {n m : Type*} (X : Matrix n m ℝ) : Matrix n (Option m) ℝ :=
  fun j i => match i with
    | none => 0
    | some k => X j k

private def nullTuple {n m : Type*} (f : n → m) : (Unit ⊕ n) → Option m :=
  Sum.elim (fun _ => none) (fun i => some (f i))

private theorem det_augmented_nullTuple {n m : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n m ℝ) (f : n → m) :
    (((augmentedColumns (withZeroColumn X)).submatrix id (nullTuple f)).det) =
      (X.submatrix id f).det := by
  have hm : (augmentedColumns (withZeroColumn X)).submatrix id (nullTuple f) =
      Matrix.fromBlocks (1 : Matrix Unit Unit ℝ) (fun _ _ => (1 : ℝ))
        (0 : Matrix n Unit ℝ) (X.submatrix id f) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.submatrix_apply, augmentedColumns, withZeroColumn, nullTuple]
  rw [hm, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

/-- Keep the terms that contain the distinguished zero point in one fixed
position. This loses only the factor `(q+1)!`; unlike a dimension-dependent
bound, this is useful for the three- and four-face estimates. -/
theorem null_minors_le_covariance_det {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (X : Matrix n m ℝ) (w : Option m → ℝ)
    (hw : ∑ i, w i = 1) (hw0 : ∀ i, 0 ≤ w i) :
    w none * (∑ f : n → m, (∏ i, w (some (f i))) * (X.submatrix id f).det ^ 2) ≤
      (Fintype.card (Equiv.Perm (Unit ⊕ n)) : ℝ) *
        (weightedCovariance (withZeroColumn X) w).det := by
  classical
  rw [weightedCovariance_det_ordered _ _ hw]
  let T : ((Unit ⊕ n) → Option m) → ℝ := fun f =>
    (∏ i, w (f i)) * (((augmentedColumns (withZeroColumn X)).submatrix id f).det) ^ 2
  have hinj : Function.Injective (nullTuple : (n → m) → (Unit ⊕ n) → Option m) := by
    intro f g hfg
    funext i
    exact Option.some.inj (congrFun hfg (.inr i))
  calc
    _ = ∑ f : n → m, T (nullTuple f) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      change w none * ((∏ i, w (some (f i))) * (X.submatrix id f).det ^ 2) =
        (∏ i, w (nullTuple f i)) *
          ((augmentedColumns (withZeroColumn X)).submatrix id (nullTuple f)).det ^ 2
      rw [det_augmented_nullTuple]
      simp only [Fintype.prod_sum_type,
        nullTuple, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique]
      ring
    _ = ∑ f ∈ Finset.univ.image nullTuple, T f := by
      rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    _ ≤ ∑ f, T f := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro f _ _
      exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw0 (f i))) (sq_nonneg _)
    _ = _ := rfl

/-- A principal submatrix, indexed directly by the finite subset. -/
def principalMatrix {n : Type*} [Fintype n] (A : Matrix n n ℝ) (S : Finset n) :
    Matrix S S ℝ := A.submatrix Subtype.val Subtype.val

private theorem det_piecewise_identity {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (S : Finset n) :
    Matrix.det (S.piecewise A (1 : Matrix n n ℝ)) = (principalMatrix A S).det := by
  classical
  let e := Equiv.sumCompl (fun i => i ∈ S)
  have hm : Matrix.submatrix (S.piecewise A (1 : Matrix n n ℝ)) e e =
      Matrix.fromBlocks (principalMatrix A S)
        (A.submatrix Subtype.val Subtype.val : Matrix S {i // i ∉ S} ℝ)
        (0 : Matrix {i // i ∉ S} S ℝ) (1 : Matrix {i // i ∉ S} {i // i ∉ S} ℝ) := by
    ext i j
    cases i with
    | inl i => cases j <;> simp [e, Finset.piecewise, principalMatrix]
    | inr i =>
      cases j with
      | inl j =>
        simp only [Matrix.submatrix_apply, e, Equiv.sumCompl_apply_inr,
          Equiv.sumCompl_apply_inl]
        simp only [Finset.piecewise, i.property, if_false,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
        exact Matrix.one_apply_ne (by intro hij; exact i.property (hij.symm ▸ j.property))
      | inr j => simp [e, Finset.piecewise, i.property, Matrix.one_apply, Subtype.ext_iff]
  rw [← Matrix.det_submatrix_equiv_self e, hm, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

/-- Expansion of `det(I+A)` in all principal minors. -/
theorem det_one_add_eq_sum_principal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    (1 + A).det = ∑ S : Finset n, (principalMatrix A S).det := by
  classical
  rw [add_comm]
  have h := Matrix.detRowAlternating.toMultilinearMap.map_add_univ A (1 : Matrix n n ℝ)
  change (A + 1).det = ∑ S : Finset n,
    Matrix.det (S.piecewise A (1 : Matrix n n ℝ)) at h
  change (A + 1).det = ∑ S : Finset n, (principalMatrix A S).det
  rw [h]
  exact Finset.sum_congr rfl (fun S _ => det_piecewise_identity A S)

theorem posSemidef_smul_nonneg {n : Type*} [Fintype n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) : (t • A).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · change (t • A).conjTranspose = t • A
    simp only [Matrix.conjTranspose_smul, star_trivial, hA.isHermitian.eq]
  · rw [Matrix.smul_mulVec_assoc, dotProduct_smul]
    exact mul_nonneg ht (hA.2 x)

theorem posSemidef_det_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) : 0 ≤ A.det := by
  rw [← hA.sqrt_mul_self, Matrix.det_mul]
  exact mul_self_nonneg _

/-- Every family of principal minors of one fixed size gives a lower bound
for the determinant of `I+tA` when `A` is positive semidefinite. -/
theorem principal_sum_le_det_one_add {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) (q : ℕ) :
    (∑ S : Finset n with S.card = q, (principalMatrix (t • A) S).det) ≤
      (1 + t • A).det := by
  classical
  rw [det_one_add_eq_sum_principal]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro S _ _
  exact posSemidef_det_nonneg ((posSemidef_smul_nonneg hA ht).submatrix Subtype.val)

private theorem principal_sum_one {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    (∑ S : Finset n with S.card = 1, (principalMatrix A S).det) = Matrix.trace A := by
  classical
  rw [← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.powersetCard_one,
    Finset.sum_map]
  change (∑ i, (principalMatrix A {i}).det) = ∑ i, A i i
  apply Finset.sum_congr rfl
  intro i _
  haveI : Subsingleton ({i} : Finset n) := by
    constructor
    intro a b
    apply Subtype.ext
    exact (Finset.mem_singleton.mp a.property).trans (Finset.mem_singleton.mp b.property).symm
  exact Matrix.det_eq_elem_of_subsingleton (principalMatrix A {i})
    (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset n))

/-- The trace term alone is controlled by the nonnegative normal-map
Jacobian. This includes zero-dimensional matrices. -/
theorem posSemidef_mul_trace_le_det_one_add {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    t * Matrix.trace A ≤ (1 + t • A).det := by
  have h := principal_sum_le_det_one_add hA ht 1
  rw [principal_sum_one] at h
  simpa only [Matrix.trace_smul, smul_eq_mul] using h

private def principalPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Polynomial ℝ :=
  ∑ S : Finset n, Polynomial.C (principalMatrix A S).det * Polynomial.X ^ S.card

private theorem eval_principalPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (t : ℝ) :
    (principalPolynomial A).eval t = (1 + t • A).det := by
  classical
  rw [det_one_add_eq_sum_principal]
  simp only [principalPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro S _
  change (principalMatrix A S).det * t ^ S.card = (t • principalMatrix A S).det
  rw [Matrix.det_smul]
  simp [mul_comm]

private theorem coeff_principalPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (q : ℕ) :
    (principalPolynomial A).coeff q =
      ∑ S : Finset n with S.card = q, (principalMatrix A S).det := by
  classical
  simp only [principalPolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  simp [eq_comm]

/-- The sum of principal minors of `AB` and `BA` agrees in every degree,
including when the two matrix sizes differ. -/
theorem principal_sum_mul_comm {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (A : Matrix n m ℝ) (B : Matrix m n ℝ) (q : ℕ) :
    (∑ S : Finset n with S.card = q, (principalMatrix (A * B) S).det) =
      ∑ S : Finset m with S.card = q, (principalMatrix (B * A) S).det := by
  have heq : principalPolynomial (A * B) = principalPolynomial (B * A) := by
    apply Polynomial.funext
    intro t
    rw [eval_principalPolynomial, eval_principalPolynomial]
    have h := Matrix.det_one_add_mul_comm (t • A) B
    simpa only [Matrix.smul_mul, Matrix.mul_smul] using h
  simpa only [coeff_principalPolynomial] using congrArg (fun P => P.coeff q) heq

/-- The exact finite-dimensional coefficient needed by the normal-map
argument, expressed as squared coordinate minors. The factor `(q+1)!` depends
only on the number of active faces, and not on the ambient dimension. -/
theorem null_principal_minors_le_normalMap_det {n m : Type*}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (X : Matrix n m ℝ) (w : Option m → ℝ)
    (hw : ∑ i, w i = 1) (hw0 : ∀ i, 0 ≤ w i)
    (hcov : (weightedCovariance (withZeroColumn X) w).PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) (q : ℕ) :
    t ^ q * w none *
      (∑ S : Finset n with S.card = q,
        ∑ f : S → m, (∏ i, w (some (f i))) *
          ((X.submatrix Subtype.val f).det) ^ 2) ≤
      ((q + 1).factorial : ℝ) *
        (1 + t • weightedCovariance (withZeroColumn X) w).det := by
  classical
  have hpoint (S : Finset n) (hS : S.card = q) :
      t ^ q * w none *
        (∑ f : S → m, (∏ i, w (some (f i))) *
          ((X.submatrix Subtype.val f).det) ^ 2) ≤
        ((q + 1).factorial : ℝ) *
          (principalMatrix (t • weightedCovariance (withZeroColumn X) w) S).det := by
    have h := null_minors_le_covariance_det (X.submatrix (fun j : S => (j : n)) id) w hw hw0
    have hc : weightedCovariance (withZeroColumn (X.submatrix (fun j : S => (j : n)) id)) w =
        principalMatrix (weightedCovariance (withZeroColumn X) w) S := rfl
    have hcard : Fintype.card (Unit ⊕ S) = q + 1 := by
      simp [Fintype.card_sum, hS, Nat.add_comm]
    rw [Fintype.card_perm, hcard, hc] at h
    have hscalar :
        (principalMatrix (t • weightedCovariance (withZeroColumn X) w) S).det =
          t ^ q * (principalMatrix (weightedCovariance (withZeroColumn X) w) S).det := by
      change (t • principalMatrix (weightedCovariance (withZeroColumn X) w) S).det = _
      rw [Matrix.det_smul]
      simp only [Fintype.card_coe, hS]
    rw [hscalar]
    have htq : 0 ≤ t ^ q := pow_nonneg ht q
    have hm := mul_le_mul_of_nonneg_left h htq
    simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp,
      mul_assoc, mul_comm, mul_left_comm] using hm
  calc
    _ = ∑ S : Finset n with S.card = q,
        t ^ q * w none * (∑ f : S → m, (∏ i, w (some (f i))) *
          ((X.submatrix Subtype.val f).det) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ ∑ S : Finset n with S.card = q, ((q + 1).factorial : ℝ) *
        (principalMatrix (t • weightedCovariance (withZeroColumn X) w) S).det := by
      apply Finset.sum_le_sum
      intro S hS
      exact hpoint S (Finset.mem_filter.mp hS).2
    _ = ((q + 1).factorial : ℝ) *
        ∑ S : Finset n with S.card = q,
          (principalMatrix (t • weightedCovariance (withZeroColumn X) w) S).det := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (principal_sum_le_det_one_add hcov ht q)
      (Nat.cast_nonneg _)

/-- Move a principal-minor sum from coordinate space to the finite family of
normal vectors. This is the rectangular determinant identity, degree by
degree, with the weights kept outside each minor. -/
theorem weightedGram_principal_sum_dual {n m : Type*}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (X : Matrix n m ℝ) (w : m → ℝ) (q : ℕ) :
    (∑ S : Finset n with S.card = q, (principalMatrix (weightedGram X w) S).det) =
      ∑ S : Finset m with S.card = q,
        (∏ i : S, w i) * (principalMatrix (X.transpose * X) S).det := by
  classical
  let B : Matrix m n ℝ := fun i j => w i * X j i
  have hGram : weightedGram X w = X * B := by
    ext j k
    simp only [weightedGram, Matrix.mul_apply, B]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hGram, principal_sum_mul_comm X B]
  apply Finset.sum_congr rfl
  intro S _
  have hm : principalMatrix (B * X) S =
      Matrix.of (fun i j : S => w i * principalMatrix (X.transpose * X) S i j) := by
    ext i j
    simp only [principalMatrix, Matrix.submatrix_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.of_apply, B, Finset.mul_sum]
    simp only [mul_assoc]
  rw [hm, Matrix.det_mul_column]

/-- The Gaussian normal-map Jacobian controls the sum of all weighted
`q`-face Gram determinants. The loss is at most `q+1`, and retains one power
of the distinguished null probability. Consequently local three- and
four-coordinate determinant bounds can be used without replacing them by a
global least-eigenvalue bound. -/
theorem faceGram_sum_le_normalMap_det {n m : Type*}
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (X : Matrix n m ℝ) (w : Option m → ℝ)
    (hw : ∑ i, w i = 1) (hw0 : ∀ i, 0 ≤ w i)
    (hcov : (weightedCovariance (withZeroColumn X) w).PosSemidef)
    {t : ℝ} (ht : 0 ≤ t) (q : ℕ) :
    t ^ q * w none *
      (∑ S : Finset m with S.card = q,
        (∏ i : S, w (some i)) * (principalMatrix (X.transpose * X) S).det) ≤
      (q + 1 : ℝ) * (1 + t • weightedCovariance (withZeroColumn X) w).det := by
  classical
  have hinner :
      (∑ S : Finset n with S.card = q,
        ∑ f : S → m, (∏ i, w (some (f i))) * ((X.submatrix Subtype.val f).det) ^ 2) =
      (q.factorial : ℝ) *
        ∑ S : Finset n with S.card = q,
          (principalMatrix (weightedGram X (fun i => w (some i))) S).det := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    have hSq : S.card = q := (Finset.mem_filter.mp hS).2
    have h := weightedGram_det_ordered (X.submatrix (fun i : S => (i : n)) id)
      (fun i => w (some i))
    rw [Fintype.card_perm, Fintype.card_coe, hSq] at h
    simpa only [weightedGram, principalMatrix, Matrix.submatrix_apply,
      Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] using h.symm
  have h := null_principal_minors_le_normalMap_det X w hw hw0 hcov ht q
  rw [hinner, weightedGram_principal_sum_dual] at h
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  have hpos : 0 < (q.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos q
  apply (mul_le_mul_right hpos).mp
  convert h using 1 <;> ring

end
end RectangleCLT
