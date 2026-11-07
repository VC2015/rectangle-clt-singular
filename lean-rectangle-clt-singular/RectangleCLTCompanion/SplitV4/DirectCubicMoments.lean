import RectangleCLTCompanion.SplitV4.DirectRelativeDerivatives

/-! The signed coefficient contraction equals the actual canonical cubic
fresh-copy integral. Every finite interchange uses genuine third moments. -/

open MeasureTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem smoother_canonical_third_diagonal_coordinates {p : ℕ}
    (s : FaceSmoother p) (x y : Vector p) :
    iteratedFDeriv ℝ 3 s.F x (fun _ => y) =
      ∑ j, ∑ k, ∑ l, s.mixedThirdDerivativeF x j k l*(y j*(y k*y l)) := by
  have hc : (![y, y, y] : Fin 3 → Vector p) = (fun _ => y) := by
    funext i
    fin_cases i <;> rfl
  have hh := restorationThirdDerivative_eq_coordinate s x y y
  unfold restorationThirdDerivative at hh
  rw [hc] at hh
  rw [hh]
  simp only [matrixQuadratic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem RelativeMomentBounds.integrable_canonical_third_diagonal
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (h : RelativeMomentBounds μ ξ s₃ s₄) (s : FaceSmoother p) (x : Vector p) (i : Fin n) :
    Integrable (fun ω => iteratedFDeriv ℝ 3 s.F x (fun _ => ξ i ω)) μ := by
  have hi : Integrable (fun ω => ∑ j, ∑ k, ∑ l,
      s.mixedThirdDerivativeF x j k l*(ξ i ω j*(ξ i ω k*ξ i ω l))) μ :=
    integrable_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ =>
      integrable_finset_sum _ (fun l _ => (h.third_integrable i j k l).const_mul _)))
  exact hi.congr (ae_of_all _ (fun ω => (smoother_canonical_third_diagonal_coordinates s x (ξ i ω)).symm))

theorem relativeCubicContraction_eq_sum_integral_canonical_third
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (s : FaceSmoother p) (h : RelativeMomentBounds μ ξ s₃ s₄) (x : Vector p) :
    relativeCubicContraction s μ ξ x =
      ∑ i, ∫ ω, iteratedFDeriv ℝ 3 s.F x (fun _ => ξ i ω) ∂μ := by
  symm
  simp_rw [smoother_canonical_third_diagonal_coordinates]
  have hi (i : Fin n) (j k l : Fin p) := (h.third_integrable i j k l).const_mul
    (s.mixedThirdDerivativeF x j k l)
  simp_rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ =>
    integrable_finset_sum _ (fun l _ => hi _ j k l))),
    integral_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => hi _ _ k l)),
    integral_finset_sum _ (fun l _ => hi _ _ _ l), integral_const_mul]
  calc
    _ = ∑ j, ∑ i, ∑ k, ∑ l, s.mixedThirdDerivativeF x j k l*
        (∫ ω, ξ i ω j*(ξ i ω k*ξ i ω l) ∂μ) := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ∑ l, s.mixedThirdDerivativeF x j k l*
        (∫ ω, ξ i ω j*(ξ i ω k*ξ i ω l) ∂μ) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ j, ∑ k, ∑ l, ∑ i, s.mixedThirdDerivativeF x j k l*
        (∫ ω, ξ i ω j*(ξ i ω k*ξ i ω l) ∂μ) :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
    _ = _ := by
      unfold relativeCubicContraction relativeThirdMatrix restorationCoefficient
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro i _
      ring

end
end RectangleCLT.Companion.SplitV4
