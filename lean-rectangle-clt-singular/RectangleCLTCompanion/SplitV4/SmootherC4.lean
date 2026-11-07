import RectangleCLTCompanion.SplitV4.PairedSlepian
import RectangleCLTCompanion.SplitV4.CommonPointFourth
import RectangleCLT.TranslationTaylor

/-!
The actual rational logistic face smoother as a canonical C4 test.  All
regularity witnesses and global derivative bounds are proved from the
existing smoother derivatives; no comparison estimate is an input.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem vector_eq_sum_coordinate_directions {p : ℕ} (x : Vector p) :
    x = ∑ j, x j • FaceSmoother.coordinateDirection j := by
  ext k
  simp [FaceSmoother.coordinateDirection, Finset.sum_apply, eq_comm]

/-- In a finite maximum-norm product, bounded coordinate coefficients give
a genuine operator norm bound for the whole multilinear tensor. -/
theorem multilinear_norm_le_coordinate_bound {p k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Vector p) ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hM : ∀ α : Fin k → Fin p,
      ‖M (fun i => FaceSmoother.coordinateDirection (α i))‖ ≤ B) :
    ‖M‖ ≤ (p : ℝ) ^ k * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) hB)
  intro m
  have heq : M m = ∑ α : Fin k → Fin p,
      (∏ i, m i (α i)) * M (fun i => FaceSmoother.coordinateDirection (α i)) := by
    calc
      _ = M (fun i => ∑ j, m i j • FaceSmoother.coordinateDirection j) := by
        congr 1
        funext i
        exact vector_eq_sum_coordinate_directions (m i)
      _ = _ := by
        rw [M.map_sum]
        apply Finset.sum_congr rfl
        intro α _
        rw [M.map_smul_univ]
        rfl
  rw [heq]
  calc
    _ ≤ ∑ α : Fin k → Fin p,
        ‖(∏ i, m i (α i)) * M (fun i => FaceSmoother.coordinateDirection (α i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _α : Fin k → Fin p, (∏ i, ‖m i‖) * B := by
      apply Finset.sum_le_sum
      intro α _
      rw [norm_mul, norm_prod]
      apply mul_le_mul _ (hM α) (norm_nonneg _) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
      apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
      intro i _
      exact norm_le_pi_norm (m i) (α i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ring

/-- The canonical derivative of an arbitrary fixed tensor contraction along
a coordinate line.  This is obtained from actual Fréchet derivatives. -/
theorem hasDerivAt_iteratedFDeriv_coordinate {p k : ℕ}
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) (hk : k < 4)
    (x : Vector p) (j : Fin p) (v : Fin k → Vector p) :
    HasDerivAt (fun t => iteratedFDeriv ℝ k F
      (FaceSmoother.line x (FaceSmoother.coordinateDirection j) t) v)
      (iteratedFDeriv ℝ (k + 1) F x
        (Fin.cons (FaceSmoother.coordinateDirection j) v)) 0 := by
  let x₀ := FaceSmoother.line x (FaceSmoother.coordinateDirection j) 0
  have hd := ((hF.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast hk)) x₀).hasFDerivAt
  have he := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Vector p) ℝ v).hasFDerivAt.comp x₀ hd
  have hl : HasDerivAt (FaceSmoother.line x (FaceSmoother.coordinateDirection j))
      (FaceSmoother.coordinateDirection j) 0 := by
    simpa only [one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (FaceSmoother.coordinateDirection j)).const_add x
  have hh : HasDerivAt (fun t => iteratedFDeriv ℝ k F
      (FaceSmoother.line x (FaceSmoother.coordinateDirection j) t) v)
      (((fderiv ℝ (iteratedFDeriv ℝ k F) x) (FaceSmoother.coordinateDirection j)) v) 0 := by
    convert he.comp_hasDerivAt (𝕜 := ℝ) 0 hl using 1 <;>
      simp only [x₀, FaceSmoother.line_zero, ContinuousLinearMap.comp_apply,
        ContinuousMultilinearMap.apply_apply]
  simpa only [FaceSmoother.line_zero, ContinuousLinearMap.comp_apply,
    ContinuousMultilinearMap.apply_apply, iteratedFDeriv_succ_apply_left,
    Fin.cons_zero, Fin.tail_cons] using hh

theorem smoother_iteratedFDeriv_one_coordinate {p : ℕ} (s : FaceSmoother p)
    (x : Vector p) (α : Fin 1 → Fin p) :
    iteratedFDeriv ℝ 1 s.F x (fun i => FaceSmoother.coordinateDirection (α i)) =
      s.coordinateDerivativeF x (α 0) := by
  have hd := hasDerivAt_iteratedFDeriv_coordinate
    (s.contDiff_F_translation.of_le (by simp) : ContDiff ℝ 4 s.F)
    (k := 0) (by norm_num) x (α 0) (fun _ => 0)
  simp only [Nat.zero_add, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, Fin.cons_zero] at hd
  have he := hd.unique (s.hasDerivAt_F_coordinate_normalized x (α 0) 0)
  change iteratedFDeriv ℝ 1 s.F x
    (Fin.cons (FaceSmoother.coordinateDirection (α 0)) (fun _ : Fin 0 => 0)) = _ at he
  rw [iteratedFDeriv_one_apply] at he
  simpa only [FaceSmoother.line_zero, iteratedFDeriv_one_apply, Fin.cons_zero] using he

private theorem coordinate_cons_tail {p k : ℕ} (α : Fin (k + 1) → Fin p) :
    Fin.cons (FaceSmoother.coordinateDirection (α 0))
      (fun i : Fin k => FaceSmoother.coordinateDirection (α i.succ)) =
      (fun i => FaceSmoother.coordinateDirection (α i)) := by
  funext i
  exact Fin.cases rfl (fun j => rfl) i

theorem smoother_iteratedFDeriv_two_coordinate {p : ℕ} (s : FaceSmoother p)
    (x : Vector p) (α : Fin 2 → Fin p) :
    iteratedFDeriv ℝ 2 s.F x (fun i => FaceSmoother.coordinateDirection (α i)) =
      s.mixedSecondDerivativeF x (α 1) (α 0) := by
  have hd := hasDerivAt_iteratedFDeriv_coordinate
    (s.contDiff_F_translation.of_le (by simp) : ContDiff ℝ 4 s.F)
    (k := 1) (by norm_num) x (α 0)
    (fun i : Fin 1 => FaceSmoother.coordinateDirection (α i.succ))
  rw [coordinate_cons_tail α] at hd
  simp_rw [smoother_iteratedFDeriv_one_coordinate] at hd
  simpa only [FaceSmoother.line_zero] using
    hd.unique (s.hasDerivAt_firstDerivative_coordinate x (α 1) (α 0) 0)

theorem smoother_iteratedFDeriv_three_coordinate {p : ℕ} (s : FaceSmoother p)
    (x : Vector p) (α : Fin 3 → Fin p) :
    iteratedFDeriv ℝ 3 s.F x (fun i => FaceSmoother.coordinateDirection (α i)) =
      s.mixedThirdDerivativeF x (α 2) (α 1) (α 0) := by
  have hd := hasDerivAt_iteratedFDeriv_coordinate
    (s.contDiff_F_translation.of_le (by simp) : ContDiff ℝ 4 s.F)
    (k := 2) (by norm_num) x (α 0)
    (fun i : Fin 2 => FaceSmoother.coordinateDirection (α i.succ))
  rw [coordinate_cons_tail α] at hd
  simp_rw [smoother_iteratedFDeriv_two_coordinate] at hd
  simpa only [FaceSmoother.line_zero] using
    hd.unique (s.hasDerivAt_secondDerivative_coordinate x (α 2) (α 1) (α 0) 0)

theorem smoother_iteratedFDeriv_four_coordinate {p : ℕ} (s : FaceSmoother p)
    (x : Vector p) (α : Fin 4 → Fin p) :
    iteratedFDeriv ℝ 4 s.F x (fun i => FaceSmoother.coordinateDirection (α i)) =
      s.mixedFourthDerivativeF x (α 3) (α 2) (α 1) (α 0) := by
  have hd := hasDerivAt_iteratedFDeriv_coordinate
    (s.contDiff_F_translation.of_le (by simp) : ContDiff ℝ 4 s.F)
    (k := 3) (by norm_num) x (α 0)
    (fun i : Fin 3 => FaceSmoother.coordinateDirection (α i.succ))
  rw [coordinate_cons_tail α] at hd
  simp_rw [smoother_iteratedFDeriv_three_coordinate] at hd
  simpa only [FaceSmoother.line_zero] using
    hd.unique (s.hasDerivAt_thirdDerivative_coordinate x (α 3) (α 2) (α 1) (α 0) 0)

def smootherC4Bound {p : ℕ} (s : FaceSmoother p) : ℝ :=
  (p : ℝ) ^ 1 * (1 / s.bandwidth) +
  (p : ℝ) ^ 2 * (3 / s.bandwidth ^ 2) +
  (p : ℝ) ^ 3 * (13 / s.bandwidth ^ 3) +
  (p : ℝ) ^ 4 * (75 / s.bandwidth ^ 4)

theorem smootherC4Bound_nonneg {p : ℕ} (s : FaceSmoother p) :
    0 ≤ smootherC4Bound s := by
  have hb := s.bandwidth_pos
  unfold smootherC4Bound
  positivity

theorem smoother_iteratedFDeriv_norm_le {p : ℕ} (s : FaceSmoother p)
    (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ 4) (x : Vector p) :
    ‖iteratedFDeriv ℝ k s.F x‖ ≤ smootherC4Bound s := by
  have hb := s.bandwidth_pos
  have h1 : ‖iteratedFDeriv ℝ 1 s.F x‖ ≤ (p : ℝ) ^ 1 * (1 / s.bandwidth) := by
    apply multilinear_norm_le_coordinate_bound _ (by positivity)
    intro α
    rw [smoother_iteratedFDeriv_one_coordinate]
    exact s.norm_firstDerivative_le x (α 0)
  have h2 : ‖iteratedFDeriv ℝ 2 s.F x‖ ≤ (p : ℝ) ^ 2 * (3 / s.bandwidth ^ 2) := by
    apply multilinear_norm_le_coordinate_bound _ (by positivity)
    intro α
    rw [smoother_iteratedFDeriv_two_coordinate]
    exact s.norm_secondDerivative_le x (α 1) (α 0)
  have h3 : ‖iteratedFDeriv ℝ 3 s.F x‖ ≤ (p : ℝ) ^ 3 * (13 / s.bandwidth ^ 3) := by
    apply multilinear_norm_le_coordinate_bound _ (by positivity)
    intro α
    rw [smoother_iteratedFDeriv_three_coordinate]
    exact s.norm_thirdDerivative_le x (α 2) (α 1) (α 0)
  have h4 : ‖iteratedFDeriv ℝ 4 s.F x‖ ≤ (p : ℝ) ^ 4 * (75 / s.bandwidth ^ 4) := by
    apply multilinear_norm_le_coordinate_bound _ (by positivity)
    intro α
    rw [smoother_iteratedFDeriv_four_coordinate]
    exact s.norm_fourthDerivative_le x (α 3) (α 2) (α 1) (α 0)
  have hc1 : 0 ≤ (p : ℝ) ^ 1 * (1 / s.bandwidth) := by positivity
  have hc2 : 0 ≤ (p : ℝ) ^ 2 * (3 / s.bandwidth ^ 2) := by positivity
  have hc3 : 0 ≤ (p : ℝ) ^ 3 * (13 / s.bandwidth ^ 3) := by positivity
  have hc4 : 0 ≤ (p : ℝ) ^ 4 * (75 / s.bandwidth ^ 4) := by positivity
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by omega) with rfl | rfl | rfl | rfl <;>
    unfold smootherC4Bound <;> linarith

/-- The canonical, fully witnessed C4 test for the actual logistic smoother.
The dimension-dependent coarse bound is used only for integrability and
differentiation justifications, not as the sharp analytic comparison bound. -/
def smootherC4Test {p : ℕ} (s : FaceSmoother p) : C4Test p :=
  C4Test.ofContDiff s.F (s.contDiff_F_translation.of_le (by simp))
    (smootherC4Bound s) (smootherC4Bound_nonneg s) (smoother_iteratedFDeriv_norm_le s)

theorem smootherC4Test_value {p : ℕ} (s : FaceSmoother p) :
    (smootherC4Test s).value = s.F := rfl

theorem smootherC4Test_gradient_eq_translationD1 {p : ℕ} (s : FaceSmoother p)
    (x y : Vector p) : (smootherC4Test s).gradient x y = s.translationD1 x y := by
  have hl : HasDerivAt (FaceSmoother.line x y) y 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add x
  have hd := ((s.contDiff_F_translation.differentiable (by simp))
    (FaceSmoother.line x y 0)).hasFDerivAt.comp_hasDerivAt 0 hl
  have he := hd.unique (s.hasDerivAt_F_line_sum_translation x y 0)
  change (fderiv ℝ s.F x) y = _
  simpa only [FaceSmoother.line_zero, FaceSmoother.translationD1] using he

theorem smootherC4Test_secondDiagonal_eq_translationD2 {p : ℕ} (s : FaceSmoother p)
    (x y : Vector p) : (smootherC4Test s).secondDiagonal x y = s.translationD2 x y := by
  have hd := (smootherC4Test s).hasDerivAt_gradient_segment x y 1 0
  simp only [one_mul, zero_smul, add_zero] at hd
  simp_rw [smootherC4Test_gradient_eq_translationD1] at hd
  simpa only [FaceSmoother.line_zero] using hd.unique (s.hasDerivAt_translationD1 x y 0)

theorem smootherC4Test_thirdDiagonal_eq_translationD3 {p : ℕ} (s : FaceSmoother p)
    (x y : Vector p) : (smootherC4Test s).thirdDiagonal x y = s.translationD3 x y := by
  have hd := (smootherC4Test s).hasDerivAt_hessian_segment x y 1 0
  simp only [one_mul, zero_smul, add_zero] at hd
  simp_rw [smootherC4Test_secondDiagonal_eq_translationD2] at hd
  simpa only [FaceSmoother.line_zero] using hd.unique (s.hasDerivAt_translationD2 x y 0)

theorem smootherC4Test_fourthDiagonal_eq_translationD4 {p : ℕ} (s : FaceSmoother p)
    (x y : Vector p) : (smootherC4Test s).fourthDiagonal x y = s.translationD4 x y := by
  have hd := (smootherC4Test s).hasDerivAt_third_segment x y 1 0
  simp only [one_mul, zero_smul, add_zero] at hd
  simp_rw [smootherC4Test_thirdDiagonal_eq_translationD3] at hd
  simpa only [FaceSmoother.line_zero] using hd.unique (s.hasDerivAt_translationD3 x y 0)

/-- The tensor contraction in the paired Slepian identity is precisely the
coordinate fourth derivative controlled by the common-point estimate. -/
theorem smootherC4Test_fourthDiagonal_eq_diagonalFourth {p : ℕ} (s : FaceSmoother p)
    (x y : Vector p) : (smootherC4Test s).fourthDiagonal x y = diagonalFourth s x y := by
  rw [smootherC4Test_fourthDiagonal_eq_translationD4, diagonalFourth_eq_translationD4]

end
end RectangleCLT.Companion.SplitV4
