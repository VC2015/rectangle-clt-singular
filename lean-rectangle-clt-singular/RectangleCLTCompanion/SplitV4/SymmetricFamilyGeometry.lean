import RectangleCLTCompanion.Statement
import RectangleCLTCompanion.SplitV4.SymmetricFamilyFinite
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Deterministic geometry of the common symmetric family

The covariance is indexed first by a genuine pair of finite indices.
A rectangular Gram factor exposes its one-dimensional coefficient kernel,
so the rank is proved without a nondegeneracy or rank premise.
-/

open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

def additiveGridFactor (m : ℕ) (a b : ℝ) :
    Matrix (Fin m × Fin m) (Fin m ⊕ Fin m) ℝ :=
  fun ju => Sum.elim (fun j => if ju.1 = j then a else 0)
    (fun u => if ju.2 = u then b else 0)

def additiveGridKernelVector (m : ℕ) (a b : ℝ) : (Fin m ⊕ Fin m) → ℝ :=
  Sum.elim (fun _ => -b) (fun _ => a)

def familyPairCovariance (m : ℕ) (v : ℝ) : Matrix (Fin m × Fin m) (Fin m × Fin m) ℝ :=
  fun ju ju' => (1 - v) * (if ju.1 = ju'.1 then 1 else 0) +
    v * (if ju.2 = ju'.2 then 1 else 0)

theorem additiveGridFactor_mulVec {m : ℕ} (a b : ℝ)
    (x : (Fin m ⊕ Fin m) → ℝ) (ju : Fin m × Fin m) :
    (additiveGridFactor m a b).mulVec x ju = a * x (Sum.inl ju.1) + b * x (Sum.inr ju.2) := by
  classical
  simp [additiveGridFactor, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, eq_comm]

theorem additiveGridFactor_gram {m : ℕ} (a b : ℝ) :
    additiveGridFactor m a b * (additiveGridFactor m a b).transpose =
      fun ju ju' => a ^ 2 * (if ju.1 = ju'.1 then 1 else 0) +
        b ^ 2 * (if ju.2 = ju'.2 then 1 else 0) := by
  classical
  ext ju ju'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, additiveGridFactor, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  by_cases hj : ju.1 = ju'.1 <;> by_cases hu : ju.2 = ju'.2 <;>
    simp [hj, hu, eq_comm, mul_ite, ite_mul, pow_two]

theorem additiveGridFactor_ker {m : ℕ} (hm : 1 ≤ m) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearMap.ker (additiveGridFactor m a b).mulVecLin =
      Submodule.span ℝ {additiveGridKernelVector m a b} := by
  classical
  let zeroIndex : Fin m := ⟨0, by omega⟩
  ext x
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hx
    have hx0 : (additiveGridFactor m a b).mulVec x = 0 := hx
    have he (j u : Fin m) : a * x (Sum.inl j) + b * x (Sum.inr u) = 0 := by
      simpa only [additiveGridFactor_mulVec, Pi.zero_apply] using congrFun hx0 (j, u)
    have hy (u : Fin m) : x (Sum.inr u) = x (Sum.inr zeroIndex) := by
      apply mul_left_cancel₀ hb
      linarith [he zeroIndex u, he zeroIndex zeroIndex]
    refine ⟨x (Sum.inr zeroIndex) / a, ?_⟩
    funext k
    cases k with
    | inl j =>
      change (x (Sum.inr zeroIndex) / a) * (-b) = x (Sum.inl j)
      field_simp [ha]
      nlinarith [he j zeroIndex]
    | inr u =>
      change (x (Sum.inr zeroIndex) / a) * a = x (Sum.inr u)
      rw [div_mul_cancel₀ _ ha, hy u]
  · rintro ⟨c, rfl⟩
    change (additiveGridFactor m a b).mulVec (c • additiveGridKernelVector m a b) = 0
    funext ju
    rw [additiveGridFactor_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, additiveGridKernelVector, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
    ring

theorem additiveGridFactor_rank {m : ℕ} (hm : 1 ≤ m) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (additiveGridFactor m a b).rank = 2 * m - 1 := by
  classical
  let zeroIndex : Fin m := ⟨0, by omega⟩
  have hw : additiveGridKernelVector m a b ≠ 0 := by
    intro hh
    have hval := congrFun hh (Sum.inr zeroIndex)
    exact ha hval
  have hn := LinearMap.finrank_range_add_finrank_ker (additiveGridFactor m a b).mulVecLin
  rw [additiveGridFactor_ker hm ha hb, finrank_span_singleton hw] at hn
  change (additiveGridFactor m a b).rank + 1 = _ at hn
  simp only [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin] at hn
  omega

theorem familyPairCovariance_gram {m : ℕ} {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    familyPairCovariance m v =
      additiveGridFactor m (Real.sqrt (1 - v)) (Real.sqrt v) *
        (additiveGridFactor m (Real.sqrt (1 - v)) (Real.sqrt v)).transpose := by
  rw [additiveGridFactor_gram]
  simp only [Real.sq_sqrt (sub_pos.mpr hv1).le, Real.sq_sqrt hv.le, familyPairCovariance]
  rfl

theorem familyPairCovariance_rank {m : ℕ} (hm : 1 ≤ m) {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    (familyPairCovariance m v).rank = 2 * m - 1 := by
  rw [familyPairCovariance_gram hv hv1, Matrix.rank_self_mul_transpose]
  exact additiveGridFactor_rank hm (Real.sqrt_pos.mpr (sub_pos.mpr hv1)).ne'
    (Real.sqrt_pos.mpr hv).ne'

theorem familyCovariance_eq_pair_submatrix (m : ℕ) (v : ℝ) :
    familyCovariance m v = (familyPairCovariance m v).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm := rfl

/-- Rank of the actual flattened covariance used by the finite family. -/
theorem familyCovariance_rank {m : ℕ} (hm : 1 ≤ m) {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    (familyCovariance m v).rank = 2 * m - 1 := by
  rw [familyCovariance_eq_pair_submatrix, Matrix.rank_submatrix]
  exact familyPairCovariance_rank hm hv hv1

theorem familyCovariance_unit_diagonal (m : ℕ) (v : ℝ) (j : Fin (m * m)) :
    familyCovariance m v j j = 1 := by
  simp only [familyCovariance, if_true, mul_one]
  ring

theorem familyCovariance_abs_offDiagonal_le {m : ℕ} {v : ℝ}
    (hv : 0 < v) (hvhalf : v < 1 / 2) (j k : Fin (m * m)) (hjk : j ≠ k) :
    |familyCovariance m v j k| ≤ 1 - v := by
  have hv1 : 0 < 1 - v := by linarith
  have hne : finProdFinEquiv.symm j ≠ (finProdFinEquiv.symm k : Fin m × Fin m) :=
    fun hh => hjk (finProdFinEquiv.symm.injective hh)
  change |(1 - v) * (if (finProdFinEquiv.symm j : Fin m × Fin m).1 =
      (finProdFinEquiv.symm k : Fin m × Fin m).1 then 1 else 0) +
    v * (if (finProdFinEquiv.symm j : Fin m × Fin m).2 =
      (finProdFinEquiv.symm k : Fin m × Fin m).2 then 1 else 0)| ≤ 1 - v
  by_cases hfirst : (finProdFinEquiv.symm j : Fin m × Fin m).1 =
      (finProdFinEquiv.symm k : Fin m × Fin m).1
  · have hsecond : (finProdFinEquiv.symm j : Fin m × Fin m).2 ≠
        (finProdFinEquiv.symm k : Fin m × Fin m).2 := fun hh => hne (Prod.ext hfirst hh)
    simp only [if_pos hfirst, if_neg hsecond, mul_one, mul_zero, add_zero, abs_of_pos hv1, le_refl]
  · by_cases hsecond : (finProdFinEquiv.symm j : Fin m × Fin m).2 =
        (finProdFinEquiv.symm k : Fin m × Fin m).2
    · simp only [if_neg hfirst, if_pos hsecond, mul_zero, mul_one, zero_add, abs_of_pos hv]
      linarith
    · simp only [if_neg hfirst, if_neg hsecond, mul_zero, zero_add, abs_zero]
      exact hv1.le

theorem familyCovariance_offDiagonal_attains {m : ℕ} (hm : 2 ≤ m) (v : ℝ) :
    ∃ j k : Fin (m * m), j ≠ k ∧ familyCovariance m v j k = 1 - v := by
  let z : Fin m := ⟨0, by omega⟩
  let o : Fin m := ⟨1, by omega⟩
  refine ⟨finProdFinEquiv (z, z), finProdFinEquiv (z, o), ?_, ?_⟩
  · intro hh
    have hp := finProdFinEquiv.injective hh
    have hv := congrArg (fun x : Fin m × Fin m => (x.2 : ℕ)) hp
    dsimp [z, o] at hv
    omega
  · have hzo : z ≠ o := by intro hh; have hv := congrArg Fin.val hh; dsimp [z, o] at hv; omega
    simp only [familyCovariance, Equiv.symm_apply_apply, if_true, if_neg hzo, mul_one, mul_zero, add_zero]

theorem familyCovariance_maxOffDiagonal {m : ℕ} (hm : 2 ≤ m) {v : ℝ}
    (hv : 0 < v) (hvhalf : v < 1 / 2) :
    maxOffDiagonal (familyCovariance m v) = 1 - v := by
  classical
  apply le_antisymm
  · apply (Finset.fold_max_le _).mpr
    refine ⟨by linarith, ?_⟩
    intro jk _
    by_cases hjk : jk.1 = jk.2
    · simp only [if_pos hjk]
      linarith
    · simpa only [if_neg hjk] using familyCovariance_abs_offDiagonal_le hv hvhalf jk.1 jk.2 hjk
  · obtain ⟨j, k, hjk, hval⟩ := familyCovariance_offDiagonal_attains hm v
    have hh : |familyCovariance m v j k| ≤ maxOffDiagonal (familyCovariance m v) := by
      apply (Finset.le_fold_max _).mpr
      exact Or.inr ⟨(j, k), Finset.mem_univ _, by simp [hjk]⟩
    rw [hval, abs_of_pos (by linarith : 0 < 1 - v)] at hh
    exact hh

theorem familyCovariance_pairGap {m : ℕ} (hm : 2 ≤ m) {v : ℝ}
    (hv : 0 < v) (hvhalf : v < 1 / 2) : pairGap (familyCovariance m v) = v := by
  rw [pairGap, familyCovariance_maxOffDiagonal hm hv hvhalf]
  ring

end

end RectangleCLT.Companion.SplitV4
