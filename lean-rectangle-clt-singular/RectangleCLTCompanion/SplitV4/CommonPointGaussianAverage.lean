import RectangleCLTCompanion.SplitV4.CommonPointFourth
import Mathlib.MeasureTheory.Integral.Prod

/-! Gaussian averaging with actual independent, random common centers,
increments and local shifts. Dependence between those data is allowed. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem continuous_diagonalFourth_joint {p : ℕ} (s : FaceSmoother p) :
    Continuous (fun q : Vector p × Vector p => diagonalFourth s q.1 q.2) := by
  unfold diagonalFourth
  apply continuous_finset_sum; intro j _
  apply continuous_finset_sum; intro k _
  apply continuous_finset_sum; intro l _
  apply continuous_finset_sum; intro m _
  exact ((s.continuous_fourthDerivative j k l m).comp continuous_fst).mul
    (by fun_prop)

theorem sum_fourthLocalMajorant_le_constant {p : ℕ} (s : FaceSmoother p) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant x j k l m) ≤
      (75 * (Real.exp 2)^5) / s.bandwidth^4 := by
  apply (s.sum_fourthLocalMajorant_le_variance x).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hF : s.F x * (1 - s.F x) ≤ 1 := by
    nlinarith [s.F_pos x, s.F_le_one x, sq_nonneg (s.F x)]
  have hm := mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ 75 * (Real.exp 2)^5)
  nlinarith

theorem gaussian_common_point_fourth_random_data
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (R : Ω → Vector p) (hR : Measurable R)
    (Y Z : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i))
    (hZ : ∀ i, Measurable (Z i))
    (hz : ∀ i, ∀ᵐ ω ∂μ, ‖Z i ω‖ ≤ s.bandwidth)
    (hQ : Integrable (fun ω => coordinateFourthBudget (fun i => Y i ω)) μ) :
    (∫ q : Vector p × Ω, ∑ i,
      |diagonalFourth s ((q.1 + R q.2) + Z i q.2) (Y i q.2)|
      ∂(gaussianLaw A).prod μ) ≤
      ((75 * (Real.exp 2)^5 * Real.exp (3 / 2 : ℝ)) *
        Real.sqrt (dimensionLog p / v) / s.bandwidth^3) *
          (∫ ω, coordinateFourthBudget (fun i => Y i ω) ∂μ) := by
  let F : Vector p × Ω → ℝ := fun q => ∑ i,
    |diagonalFourth s ((q.1 + R q.2) + Z i q.2) (Y i q.2)|
  let Q : Ω → ℝ := fun ω => coordinateFourthBudget (fun i => Y i ω)
  let C := (75 * (Real.exp 2)^5) / s.bandwidth^4
  have hFm : Measurable F := by
    apply Finset.measurable_sum; intro i _
    exact ((continuous_diagonalFourth_joint s).measurable.comp
      (((measurable_fst.add (hR.comp measurable_snd)).add (hZ i |>.comp measurable_snd)).prodMk
        (hY i |>.comp measurable_snd))).abs
  have hsnd : MeasurePreserving (Prod.snd : Vector p × Ω → Ω)
      ((gaussianLaw A).prod μ) μ := ⟨measurable_snd, by simp⟩
  have hQp : Integrable (fun q : Vector p × Ω => Q q.2) ((gaussianLaw A).prod μ) :=
    (hsnd.integrable_comp hQ.aestronglyMeasurable).mpr hQ
  have hhz : ∀ᵐ q : Vector p × Ω ∂(gaussianLaw A).prod μ,
      ∀ i, ‖Z i q.2‖ ≤ s.bandwidth := by
    exact hsnd.quasiMeasurePreserving.ae (ae_all_iff.mpr hz)
  have hFi : Integrable F ((gaussianLaw A).prod μ) := by
    apply (hQp.mul_const C).mono' hFm.aestronglyMeasurable
    filter_upwards [hhz] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
    exact (common_point_fourth_contraction_majorant s (q.1 + R q.2)
      (fun i => Y i q.2) (fun i => Z i q.2) hq).trans
      (mul_le_mul_of_nonneg_left (sum_fourthLocalMajorant_le_constant s _)
        (coordinateFourthBudget_nonneg _))
  rw [show (∫ q : Vector p × Ω, ∑ i,
      |diagonalFourth s ((q.1 + R q.2) + Z i q.2) (Y i q.2)|
      ∂(gaussianLaw A).prod μ) = ∫ q, F q ∂(gaussianLaw A).prod μ from rfl,
    integral_prod_symm F hFi]
  have hupper := hQ.const_mul
    ((75 * (Real.exp 2)^5 * Real.exp (3 / 2 : ℝ)) *
      Real.sqrt (dimensionLog p / v) / s.bandwidth^3)
  have hcomp := integral_mono_ae hFi.integral_prod_right hupper (by
    filter_upwards [ae_all_iff.mpr hz] with ω hω
    simpa only [F, mul_comm] using gaussian_common_point_fourth_contraction hp s A hv hdiag
      (R ω) (fun i => Y i ω) (fun i => Z i ω) hω)
  exact hcomp.trans_eq (integral_const_mul _ _)

end
end RectangleCLT.Companion.SplitV4
