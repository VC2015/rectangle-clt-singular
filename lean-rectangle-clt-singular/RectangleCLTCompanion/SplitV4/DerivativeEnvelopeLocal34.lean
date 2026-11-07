import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeSupremum
import RectangleCLTCompanion.SplitV4.RestorationDerivativeIdentification

/-! Actual canonical third and fourth derivative envelopes for arbitrary
finite face maps. Every direction is measured in the face seminorm. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem iteratedFDeriv_logisticNullWeight_eq {m r q : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h)
    (x : Vector r) (z : Fin q → Vector r) :
    iteratedFDeriv ℝ q (logisticNullWeight U a h) x z =
      iteratedFDeriv ℝ q (upperFaceSmoother a h hh).F (U.mulVec x) (fun i => U.mulVec (z i)) := by
  let L : Vector r →L[ℝ] Vector m := (Matrix.toLin' U).toContinuousLinearMap
  have hf : ContDiff ℝ q (upperFaceSmoother a h hh).F :=
    (upperFaceSmoother a h hh).contDiff_F_translation.of_le (by simp)
  have he := congrArg (fun M => M z) (L.iteratedFDeriv_comp_right hf x le_rfl)
  have hfun : (upperFaceSmoother a h hh).F ∘ L = logisticNullWeight U a h := by
    funext y
    exact upperFaceSmoother_F U a h hh y
  rw [hfun] at he
  exact he

theorem contDiff_logisticNullWeight {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ ⊤ (logisticNullWeight U a h) := by
  let L : Vector r →L[ℝ] Vector m := (Matrix.toLin' U).toContinuousLinearMap
  have hc := (upperFaceSmoother a h hh).contDiff_F_translation.comp L.contDiff
  change ContDiff ℝ ⊤ (fun y => (upperFaceSmoother a h hh).F (U.mulVec y)) at hc
  simpa only [upperFaceSmoother_F] using hc

theorem multilinear_norm_le_sum_coordinate_bounds {p q : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin q => Vector p) ℝ)
    (B : (Fin q → Fin p) → ℝ)
    (hB : ∀ α, ‖M (fun i => FaceSmoother.coordinateDirection (α i))‖ ≤ B α)
    (z : Fin q → Vector p) :
    ‖M z‖ ≤ (∑ α, B α)*(∏ i, ‖z i‖) := by
  rw [multilinear_eq_sum_coordinate_directions]
  calc
    _ ≤ ∑ α : Fin q → Fin p,
        ‖(∏ i, z i (α i))*M (fun i => FaceSmoother.coordinateDirection (α i))‖ := norm_sum_le _ _
    _ ≤ ∑ α : Fin q → Fin p, (∏ i, ‖z i‖)*B α := by
      apply Finset.sum_le_sum
      intro α _
      rw [norm_mul, norm_prod]
      apply mul_le_mul _ (hB α) (norm_nonneg _) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => norm_le_pi_norm (z i) (α i))
    _ = _ := by rw [← Finset.mul_sum]; ring

private theorem sum_fin_succ_functions {α : Type*} [Fintype α] {k : ℕ}
    (f : (Fin (k+1) → α) → ℝ) :
    (∑ v : Fin (k+1) → α, f v) = ∑ a, ∑ v : Fin k → α, f (Fin.cons a v) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv] using
    ((Fin.consEquiv (fun _ : Fin (k+1) => α)).sum_comp f).symm

private theorem sum_three_reverse {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

private theorem sum_four_reverse {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ d, ∑ c, ∑ b, ∑ a, f a b c d := by
  calc
    _ = ∑ a, ∑ d, ∑ c, ∑ b, f a b c d := Finset.sum_congr rfl (fun a _ => sum_three_reverse (f a))
    _ = ∑ d, ∑ a, ∑ c, ∑ b, f a b c d := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      calc
        _ = ∑ c, ∑ a, ∑ b, f a b c d := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

def thirdDerivativeEnvelopeConstant : ℝ := 13*(Real.exp 2)^4
def fourthDerivativeEnvelopeConstant : ℝ := 75*(Real.exp 2)^5

theorem smoother_iteratedFDeriv_three_shift_envelope {m : ℕ}
    (s : FaceSmoother m) (x : Vector m) {v : Vector m} (hv : ‖v‖ ≤ s.bandwidth)
    (z : Fin 3 → Vector m) :
    ‖iteratedFDeriv ℝ 3 s.F (x+v) z‖ ≤
      (thirdDerivativeEnvelopeConstant*s.F x*(1-s.F x)/s.bandwidth^3)*(∏ i, ‖z i‖) := by
  have hb := multilinear_norm_le_sum_coordinate_bounds (iteratedFDeriv ℝ 3 s.F (x+v))
    (fun α => s.thirdLocalMajorant x (α 2) (α 1) (α 0))
    (fun α => by
      rw [smoother_iteratedFDeriv_three_coordinate, Real.norm_eq_abs]
      exact s.abs_mixedThirdDerivativeF_shift_le x hv _ _ _) z
  have hsum : (∑ α : Fin 3 → Fin m, s.thirdLocalMajorant x (α 2) (α 1) (α 0)) =
      ∑ j, ∑ k, ∑ l, s.thirdLocalMajorant x j k l := by
    rw [sum_fin_succ_functions]
    simp_rw [sum_fin_succ_functions]
    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.cons_zero, Fin.cons_succ]
    change (∑ l, ∑ k, ∑ j, s.thirdLocalMajorant x j k l) = _
    exact sum_three_reverse _
  rw [hsum] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (s.sum_thirdLocalMajorant_le_variance x)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem smoother_iteratedFDeriv_four_shift_envelope {m : ℕ}
    (s : FaceSmoother m) (x : Vector m) {v : Vector m} (hv : ‖v‖ ≤ s.bandwidth)
    (z : Fin 4 → Vector m) :
    ‖iteratedFDeriv ℝ 4 s.F (x+v) z‖ ≤
      (fourthDerivativeEnvelopeConstant*s.F x*(1-s.F x)/s.bandwidth^4)*(∏ i, ‖z i‖) := by
  have hb := multilinear_norm_le_sum_coordinate_bounds (iteratedFDeriv ℝ 4 s.F (x+v))
    (fun α => s.fourthLocalMajorant x (α 3) (α 2) (α 1) (α 0))
    (fun α => by
      rw [smoother_iteratedFDeriv_four_coordinate, Real.norm_eq_abs]
      exact s.abs_mixedFourthDerivativeF_shift_le x hv _ _ _ _) z
  have hsum : (∑ α : Fin 4 → Fin m, s.fourthLocalMajorant x (α 3) (α 2) (α 1) (α 0)) =
      ∑ j, ∑ k, ∑ l, ∑ k', s.fourthLocalMajorant x j k l k' := by
    rw [sum_fin_succ_functions]
    simp_rw [sum_fin_succ_functions]
    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.cons_zero, Fin.cons_succ]
    change (∑ k', ∑ l, ∑ k, ∑ j, s.fourthLocalMajorant x j k l k') = _
    exact sum_four_reverse _
  rw [hsum] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (s.sum_fourthLocalMajorant_le_variance x)
    (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))

theorem logistic_iteratedFDeriv_three_shift_envelope {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h)
    (x : Vector r) {v : Vector r} (hv : faceProjectionNorm U v ≤ h) (z : Fin 3 → Vector r) :
    ‖iteratedFDeriv ℝ 3 (logisticNullWeight U a h) (x+v) z‖ ≤
      (thirdDerivativeEnvelopeConstant*logisticNullWeight U a h x*(1-logisticNullWeight U a h x)/h^3)*
        (∏ i, faceProjectionNorm U (z i)) := by
  rw [iteratedFDeriv_logisticNullWeight_eq U a hh, Matrix.mulVec_add]
  simpa only [upperFaceSmoother_F, faceProjectionNorm] using
    smoother_iteratedFDeriv_three_shift_envelope (upperFaceSmoother a h hh) (U.mulVec x) hv
      (fun i => U.mulVec (z i))

theorem logistic_iteratedFDeriv_four_shift_envelope {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h)
    (x : Vector r) {v : Vector r} (hv : faceProjectionNorm U v ≤ h) (z : Fin 4 → Vector r) :
    ‖iteratedFDeriv ℝ 4 (logisticNullWeight U a h) (x+v) z‖ ≤
      (fourthDerivativeEnvelopeConstant*logisticNullWeight U a h x*(1-logisticNullWeight U a h x)/h^4)*
        (∏ i, faceProjectionNorm U (z i)) := by
  rw [iteratedFDeriv_logisticNullWeight_eq U a hh, Matrix.mulVec_add]
  simpa only [upperFaceSmoother_F, faceProjectionNorm] using
    smoother_iteratedFDeriv_four_shift_envelope (upperFaceSmoother a h hh) (U.mulVec x) hv
      (fun i => U.mulVec (z i))

end
end RectangleCLT.Companion.SplitV4
