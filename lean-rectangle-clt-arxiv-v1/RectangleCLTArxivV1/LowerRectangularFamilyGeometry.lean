import RectangleCLTArxivV1.LowerRectangularFamilyProperties
import RectangleCLTCompanion.SplitV4.SymmetricFamilyGeometry

/-! Rank and exact correlation gap for the actual two-count covariance. -/
namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def lowerAdditiveGridFactor (r m : ℕ) (a b : ℝ) :
    Matrix (Fin r × Fin m) (Fin r ⊕ Fin m) ℝ :=
  fun ju => Sum.elim (fun j => if ju.1 = j then a else 0)
    (fun u => if ju.2 = u then b else 0)

def lowerAdditiveGridKernelVector (r m : ℕ) (a b : ℝ) : (Fin r ⊕ Fin m) → ℝ :=
  Sum.elim (fun _ => -b) (fun _ => a)

def lowerFamilyPairCovariance (r m : ℕ) (v : ℝ) : Matrix (Fin r × Fin m) (Fin r × Fin m) ℝ :=
  fun ju ju' => (1 - v) * (if ju.1 = ju'.1 then 1 else 0) +
    v * (if ju.2 = ju'.2 then 1 else 0)

theorem lowerAdditiveGridFactor_mulVec {r m : ℕ} (a b : ℝ)
    (x : (Fin r ⊕ Fin m) → ℝ) (ju : Fin r × Fin m) :
    (lowerAdditiveGridFactor r m a b).mulVec x ju = a * x (Sum.inl ju.1) + b * x (Sum.inr ju.2) := by
  classical
  simp [lowerAdditiveGridFactor, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, eq_comm]

theorem lowerAdditiveGridFactor_gram {r m : ℕ} (a b : ℝ) :
    lowerAdditiveGridFactor r m a b * (lowerAdditiveGridFactor r m a b).transpose =
      fun ju ju' => a ^ 2 * (if ju.1 = ju'.1 then 1 else 0) +
        b ^ 2 * (if ju.2 = ju'.2 then 1 else 0) := by
  classical
  ext ju ju'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, lowerAdditiveGridFactor, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  by_cases hj : ju.1 = ju'.1 <;> by_cases hu : ju.2 = ju'.2 <;>
    simp [hj, hu, eq_comm, mul_ite, ite_mul, pow_two]

theorem lowerAdditiveGridFactor_ker {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearMap.ker (lowerAdditiveGridFactor r m a b).mulVecLin =
      Submodule.span ℝ {lowerAdditiveGridKernelVector r m a b} := by
  classical
  let leadingZero : Fin r := ⟨0, by omega⟩
  let zeroIndex : Fin m := ⟨0, by omega⟩
  ext x
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hx
    have hx0 : (lowerAdditiveGridFactor r m a b).mulVec x = 0 := hx
    have he (j : Fin r) (u : Fin m) : a * x (Sum.inl j) + b * x (Sum.inr u) = 0 := by
      simpa only [lowerAdditiveGridFactor_mulVec, Pi.zero_apply] using congrFun hx0 (j, u)
    have hy (u : Fin m) : x (Sum.inr u) = x (Sum.inr zeroIndex) := by
      apply mul_left_cancel₀ hb
      linarith [he leadingZero u, he leadingZero zeroIndex]
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
    change (lowerAdditiveGridFactor r m a b).mulVec (c • lowerAdditiveGridKernelVector r m a b) = 0
    funext ju
    rw [lowerAdditiveGridFactor_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, lowerAdditiveGridKernelVector, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
    ring

theorem lowerAdditiveGridFactor_rank {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (lowerAdditiveGridFactor r m a b).rank = r + m - 1 := by
  classical
  let zeroIndex : Fin m := ⟨0, by omega⟩
  have hw : lowerAdditiveGridKernelVector r m a b ≠ 0 := by
    intro hh
    have hval := congrFun hh (Sum.inr zeroIndex)
    exact ha hval
  have hn := LinearMap.finrank_range_add_finrank_ker (lowerAdditiveGridFactor r m a b).mulVecLin
  rw [lowerAdditiveGridFactor_ker hr hm ha hb, finrank_span_singleton hw] at hn
  change (lowerAdditiveGridFactor r m a b).rank + 1 = _ at hn
  simp only [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin] at hn
  omega

theorem lowerFamilyPairCovariance_gram {r m : ℕ} {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    lowerFamilyPairCovariance r m v =
      lowerAdditiveGridFactor r m (Real.sqrt (1 - v)) (Real.sqrt v) *
        (lowerAdditiveGridFactor r m (Real.sqrt (1 - v)) (Real.sqrt v)).transpose := by
  rw [lowerAdditiveGridFactor_gram]
  simp only [Real.sq_sqrt (sub_pos.mpr hv1).le, Real.sq_sqrt hv.le, lowerFamilyPairCovariance]
  rfl

theorem lowerFamilyPairCovariance_rank {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    (lowerFamilyPairCovariance r m v).rank = r + m - 1 := by
  rw [lowerFamilyPairCovariance_gram hv hv1, Matrix.rank_self_mul_transpose]
  exact lowerAdditiveGridFactor_rank hr hm (Real.sqrt_pos.mpr (sub_pos.mpr hv1)).ne'
    (Real.sqrt_pos.mpr hv).ne'

theorem lowerFamilyCovariance_eq_pair_submatrix (r m : ℕ) (v : ℝ) :
    lowerFamilyCovariance r m v = (lowerFamilyPairCovariance r m v).submatrix
      finProdFinEquiv.symm finProdFinEquiv.symm := rfl

/-- Rank of the actual flattened covariance used by the finite family. -/
theorem lowerFamilyCovariance_rank {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    (lowerFamilyCovariance r m v).rank = r + m - 1 := by
  rw [lowerFamilyCovariance_eq_pair_submatrix, Matrix.rank_submatrix]
  exact lowerFamilyPairCovariance_rank hr hm hv hv1

theorem lowerFamilyCovariance_abs_offDiagonal_le {r m : ℕ} {v : ℝ}
    (hv : 0 < v) (hvhalf : v < 1 / 2) (j k : Fin (r * m)) (hjk : j ≠ k) :
    |lowerFamilyCovariance r m v j k| ≤ 1 - v := by
  have hv1 : 0 < 1 - v := by linarith
  have hne : finProdFinEquiv.symm j ≠ (finProdFinEquiv.symm k : Fin r × Fin m) :=
    fun hh => hjk (finProdFinEquiv.symm.injective hh)
  change |(1 - v) * (if (finProdFinEquiv.symm j : Fin r × Fin m).1 =
      (finProdFinEquiv.symm k : Fin r × Fin m).1 then 1 else 0) +
    v * (if (finProdFinEquiv.symm j : Fin r × Fin m).2 =
      (finProdFinEquiv.symm k : Fin r × Fin m).2 then 1 else 0)| ≤ 1 - v
  by_cases hfirst : (finProdFinEquiv.symm j : Fin r × Fin m).1 =
      (finProdFinEquiv.symm k : Fin r × Fin m).1
  · have hsecond : (finProdFinEquiv.symm j : Fin r × Fin m).2 ≠
        (finProdFinEquiv.symm k : Fin r × Fin m).2 := fun hh => hne (Prod.ext hfirst hh)
    simp only [if_pos hfirst, if_neg hsecond, mul_one, mul_zero, add_zero, abs_of_pos hv1, le_refl]
  · by_cases hsecond : (finProdFinEquiv.symm j : Fin r × Fin m).2 =
        (finProdFinEquiv.symm k : Fin r × Fin m).2
    · simp only [if_neg hfirst, if_pos hsecond, mul_zero, mul_one, zero_add, abs_of_pos hv]
      linarith
    · simp only [if_neg hfirst, if_neg hsecond, mul_zero, zero_add, abs_zero]
      exact hv1.le

theorem lowerFamilyCovariance_offDiagonal_attains {r m : ℕ} (hr : 1 ≤ r) (hm : 2 ≤ m) (v : ℝ) :
    ∃ j k : Fin (r * m), j ≠ k ∧ lowerFamilyCovariance r m v j k = 1 - v := by
  let leadingZero : Fin r := ⟨0, by omega⟩
  let z : Fin m := ⟨0, by omega⟩
  let o : Fin m := ⟨1, by omega⟩
  refine ⟨finProdFinEquiv (leadingZero, z), finProdFinEquiv (leadingZero, o), ?_, ?_⟩
  · intro hh
    have hp := finProdFinEquiv.injective hh
    have hv := congrArg (fun x : Fin r × Fin m => (x.2 : ℕ)) hp
    dsimp [z, o] at hv
    omega
  · have hzo : z ≠ o := by intro hh; have hv := congrArg Fin.val hh; dsimp [z, o] at hv; omega
    simp only [lowerFamilyCovariance, Equiv.symm_apply_apply, if_true, if_neg hzo, mul_one, mul_zero, add_zero]

theorem lowerFamilyCovariance_maxOffDiagonal {r m : ℕ} (hr : 1 ≤ r) (hm : 2 ≤ m) {v : ℝ}
    (hv : 0 < v) (hvhalf : v < 1 / 2) :
    maxOffDiagonal (lowerFamilyCovariance r m v) = 1 - v := by
  classical
  apply le_antisymm
  · apply (Finset.fold_max_le _).mpr
    refine ⟨by linarith, ?_⟩
    intro jk _
    by_cases hjk : jk.1 = jk.2
    · simp only [if_pos hjk]
      linarith
    · simpa only [if_neg hjk] using lowerFamilyCovariance_abs_offDiagonal_le hv hvhalf jk.1 jk.2 hjk
  · obtain ⟨j, k, hjk, hval⟩ := lowerFamilyCovariance_offDiagonal_attains hr hm v
    have hh : |lowerFamilyCovariance r m v j k| ≤ maxOffDiagonal (lowerFamilyCovariance r m v) := by
      apply (Finset.le_fold_max _).mpr
      exact Or.inr ⟨(j, k), Finset.mem_univ _, by simp [hjk]⟩
    rw [hval, abs_of_pos (by linarith : 0 < 1 - v)] at hh
    exact hh

theorem lowerFamilyCovariance_pairGap {r m : ℕ} (hr : 1 ≤ r) (hm : 2 ≤ m) {v : ℝ}
    (hv : 0 < v) (hvhalf : v < 1 / 2) : pairGap (lowerFamilyCovariance r m v) = v := by
  rw [pairGap, lowerFamilyCovariance_maxOffDiagonal hr hm hv hvhalf]
  ring

theorem lowerFamilyNormalizedObservations_rank (P : SymmetricFamilyParameters)
    {n r m : ℕ} (hn : 1≤n) (hr : 1≤r) (hm : 1≤m) :
    Matrix.rank (covariance (lowerFamilyArrayLaw P n r m)
      (sumVector (lowerFamilyNormalizedObservations P))) = r+m-1 := by
  rw [lowerFamilyNormalizedObservations_covariance P hn]
  exact lowerFamilyCovariance_rank hr hm P.variance_pos (lt_trans P.variance_lt_half (by norm_num))

theorem lowerFamilyNormalizedObservations_pairGap (P : SymmetricFamilyParameters)
    {n r m : ℕ} (hn : 1≤n) (hr : 1≤r) (hm : 2≤m) :
    pairGap (covariance (lowerFamilyArrayLaw P n r m)
      (sumVector (lowerFamilyNormalizedObservations P))) = P.variance := by
  rw [lowerFamilyNormalizedObservations_covariance P hn]
  exact lowerFamilyCovariance_pairGap hr hm P.variance_pos P.variance_lt_half

end
end RectangleCLTArxivV1
