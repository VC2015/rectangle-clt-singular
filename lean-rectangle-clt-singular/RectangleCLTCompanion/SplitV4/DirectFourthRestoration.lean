import RectangleCLTCompanion.SplitV4.DirectFourthProducts

/-! Direct fourth-order restoration at one actual common base. Arbitrary
measurable copy-dependent displacements are allowed within the bandwidth.
The positive coordinate majorants are fixed before the copies are averaged. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def directCopyVector {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (i : Fin n) (b : Bool) (z : Ω × Ω) : Vector p :=
  fun j => directCopyCoordinate ξ i j b z

theorem measurable_directCopyVector
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (i : Fin n) (b : Bool) :
    Measurable (directCopyVector ξ i b) := by
  cases b
  · exact (hξ i).comp measurable_fst
  · exact (hξ i).comp measurable_snd

theorem RelativeMomentBounds.integrable_directCopyCoordinate_fourth
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (h : RelativeMomentBounds μ ξ s₃ s₄) (i : Fin n) (j : Fin p) (b : Bool) :
    Integrable (fun z : Ω × Ω => directCopyCoordinate ξ i j b z^4) (μ.prod μ) := by
  cases b
  · simpa only [directCopyCoordinate, Bool.false_eq_true, if_false, mul_one] using
      (h.integrable_coordinate_fourth i j).mul_prod (integrable_const (1 : ℝ))
  · simpa only [directCopyCoordinate, if_true, one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).mul_prod
        (h.integrable_coordinate_fourth i j)

theorem multilinear_norm_le_weighted_coordinate_bounds {p q : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin q => Vector p) ℝ)
    (B : (Fin q → Fin p) → ℝ)
    (hB : ∀ α, ‖M (fun i => FaceSmoother.coordinateDirection (α i))‖ ≤ B α)
    (z : Fin q → Vector p) :
    ‖M z‖ ≤ ∑ α : Fin q → Fin p, B α*(∏ i, |z i (α i)|) := by
  rw [multilinear_eq_sum_coordinate_directions]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro α _
  rw [norm_mul, norm_prod]
  have hp : 0 ≤ ∏ i, |z i (α i)| := Finset.prod_nonneg (fun i _ => abs_nonneg _)
  simpa only [Real.norm_eq_abs, mul_comm] using
    mul_le_mul_of_nonneg_left (hB α) hp

private theorem sum_fin_succ_functions {α : Type*} [Fintype α] {k : ℕ}
    (f : (Fin (k+1) → α) → ℝ) :
    (∑ v : Fin (k+1) → α, f v) = ∑ a, ∑ v : Fin k → α, f (Fin.cons a v) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv] using
    ((Fin.consEquiv (fun _ : Fin (k+1) => α)).sum_comp f).symm

theorem sum_fourthLocalMajorant_coordinate_tuples {p : ℕ} (s : FaceSmoother p) (x : Vector p) :
    (∑ α : Fin 4 → Fin p, s.fourthLocalMajorant x (α 3) (α 2) (α 1) (α 0)) =
      ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m := by
  rw [sum_fin_succ_functions]
  simp_rw [sum_fin_succ_functions]
  simp only [Finset.univ_unique, Finset.sum_singleton, Fin.cons_zero, Fin.cons_succ]
  change (∑ m, ∑ l, ∑ k, ∑ j, s.fourthLocalMajorant x j k l m) = _
  calc
    _ = ∑ m, ∑ j, ∑ k, ∑ l, s.fourthLocalMajorant x j k l m := by
      apply Finset.sum_congr rfl
      intro m _
      calc
        _ = ∑ l, ∑ j, ∑ k, s.fourthLocalMajorant x j k l m :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = ∑ j, ∑ l, ∑ k, s.fourthLocalMajorant x j k l m := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ j, ∑ m, ∑ k, ∑ l, s.fourthLocalMajorant x j k l m := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = ∑ k, ∑ m, ∑ l, s.fourthLocalMajorant x j k l m := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

set_option maxHeartbeats 1000000 in
theorem sum_integral_norm_fourth_shift_copies_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {s₃ s₄ : ℝ} (h : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (s : FaceSmoother p) (x : Vector p)
    (v : Fin n → Ω × Ω → Vector p) (hv : ∀ i, Measurable (v i))
    (hvb : ∀ i, ∀ᵐ z ∂μ.prod μ, ‖v i z‖ ≤ s.bandwidth) (b : Fin 4 → Bool) :
    (∀ i, Integrable (fun z : Ω × Ω => iteratedFDeriv ℝ 4 s.F (x+v i z)
      (fun a => directCopyVector ξ i (b a) z)) (μ.prod μ)) ∧
    (∑ i, ∫ z : Ω × Ω, ‖iteratedFDeriv ℝ 4 s.F (x+v i z)
      (fun a => directCopyVector ξ i (b a) z)‖ ∂μ.prod μ) ≤
      fourthDerivativeEnvelopeConstant*s₄*s.F x*(1-s.F x)/s.bandwidth^4 := by
  let B : (Fin 4 → Fin p) → ℝ := fun α => s.fourthLocalMajorant x (α 3) (α 2) (α 1) (α 0)
  let P : Fin n → (Fin 4 → Fin p) → Ω × Ω → ℝ := fun i α z =>
    |directCopyCoordinate ξ i (α 0) (b 0) z*directCopyCoordinate ξ i (α 1) (b 1) z*
      directCopyCoordinate ξ i (α 2) (b 2) z*directCopyCoordinate ξ i (α 3) (b 3) z|
  let D : Fin n → Ω × Ω → ℝ := fun i z => iteratedFDeriv ℝ 4 s.F (x+v i z)
    (fun a => directCopyVector ξ i (b a) z)
  have hB (α : Fin 4 → Fin p) : 0 ≤ B α := s.fourthLocalMajorant_nonneg x _ _ _ _
  have hP (i : Fin n) (α : Fin 4 → Fin p) : Integrable (P i α) (μ.prod μ) := by
    exact integrable_abs_four_product (μ.prod μ) _ _ _ _
      ((measurable_pi_apply (α 0)).comp (measurable_directCopyVector ξ h.measurable i (b 0)))
      ((measurable_pi_apply (α 1)).comp (measurable_directCopyVector ξ h.measurable i (b 1)))
      ((measurable_pi_apply (α 2)).comp (measurable_directCopyVector ξ h.measurable i (b 2)))
      ((measurable_pi_apply (α 3)).comp (measurable_directCopyVector ξ h.measurable i (b 3)))
      (h.integrable_directCopyCoordinate_fourth i (α 0) (b 0))
      (h.integrable_directCopyCoordinate_fourth i (α 1) (b 1))
      (h.integrable_directCopyCoordinate_fourth i (α 2) (b 2))
      (h.integrable_directCopyCoordinate_fourth i (α 3) (b 3))
  have hmajor (i : Fin n) : Integrable (fun z => ∑ α, B α*P i α z) (μ.prod μ) :=
    integrable_finset_sum _ (fun α _ => (hP i α).const_mul (B α))
  have hpoint (i : Fin n) : ∀ᵐ z ∂μ.prod μ, ‖D i z‖ ≤ ∑ α, B α*P i α z := by
    filter_upwards [hvb i] with z hz
    have hm := multilinear_norm_le_weighted_coordinate_bounds (iteratedFDeriv ℝ 4 s.F (x+v i z)) B
      (fun α => by
        rw [smoother_iteratedFDeriv_four_coordinate, Real.norm_eq_abs]
        exact s.abs_mixedFourthDerivativeF_shift_le x hz _ _ _ _) (fun a => directCopyVector ξ i (b a) z)
    apply hm.trans_eq
    apply Finset.sum_congr rfl
    intro α _
    congr 1
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, directCopyVector, P, abs_mul]
    change (|directCopyCoordinate ξ i (α 0) (b 0) z| *
      (|directCopyCoordinate ξ i (α 1) (b 1) z| *
        (|directCopyCoordinate ξ i (α 2) (b 2) z| * |directCopyCoordinate ξ i (α 3) (b 3) z|))) = _
    ring
  have hmD (i : Fin n) : Measurable (D i) := by
    have hc : Continuous (fun y : Vector p × (Fin 4 → Vector p) => iteratedFDeriv ℝ 4 s.F y.1 y.2) :=
      ((s.contDiff_F_translation.continuous_iteratedFDeriv (by simp)).comp continuous_fst).eval continuous_snd
    exact hc.measurable.comp ((measurable_const.add (hv i)).prodMk
      (measurable_pi_lambda _ (fun a => measurable_directCopyVector ξ h.measurable i (b a))))
  have hiD (i : Fin n) : Integrable (D i) (μ.prod μ) := (hmajor i).mono' (hmD i).aestronglyMeasurable (hpoint i)
  refine ⟨hiD, ?_⟩
  calc
    _ ≤ ∑ i, ∫ z, ∑ α, B α*P i α z ∂μ.prod μ :=
      Finset.sum_le_sum (fun i _ => integral_mono_ae (hiD i).norm (hmajor i) (hpoint i))
    _ = ∑ α, B α*(∑ i, ∫ z, P i α z ∂μ.prod μ) := by
      simp_rw [integral_finset_sum _ (fun α _ => (hP _ α).const_mul (B α)), integral_const_mul]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ α, B α*s₄ := Finset.sum_le_sum (fun α _ =>
      mul_le_mul_of_nonneg_left (h.sum_integral_abs_copy_coordinate_four_product_le hunit α b) (hB α))
    _ = s₄*(∑ α, B α) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      ring
    _ ≤ s₄*(fourthDerivativeEnvelopeConstant*s.F x*(1-s.F x)/s.bandwidth^4) := by
      apply mul_le_mul_of_nonneg_left _ h.s₄_nonneg
      rw [show (∑ α, B α) = ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m from
        sum_fourthLocalMajorant_coordinate_tuples s x]
      exact s.sum_fourthLocalMajorant_le_variance x
    _ = _ := by ring

end
end RectangleCLT.Companion.SplitV4
