import RectangleCLTArxivV1.PairedGaussianContractions
import RectangleCLTCompanion.SplitV4.CommonPointGaussianAverage

/-! The common-point fourth contraction with the actual Gaussian width.
The sum of coordinate fourth moments is retained before averaging; no
independence between original centers, increments, and shifts is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

theorem gaussian_integral_sum_fourthLocalMajorant_intrinsic {p : ℕ} (_hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p) :
    (∫ g, ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (g+r) j k l m ∂gaussianLaw A) ≤
      (75 * (Real.exp 2)^5 * Real.exp (3/2 : ℝ)) *
        (gaussianMaximumMean A / v) / s.bandwidth^3 := by
  have hM : Integrable (fun g => ∑ j, ∑ k, ∑ l, ∑ m,
      s.fourthLocalMajorant (g+r) j k l m) (gaussianLaw A) := by
    apply integrable_finset_sum; intro j _
    apply integrable_finset_sum; intro k _
    apply integrable_finset_sum; intro l _
    apply integrable_finset_sum; intro m _
    exact s.integrable_fourthLocalMajorant_comp (gaussianLaw A) (fun g => g+r)
      (measurable_id.add_const r) j k l m
  have hΨ := s.integrable_smallerEnvelope (fun g : Vector p => g+r) (measurable_id.add_const r)
    (μ := gaussianLaw A)
  let C := 75 * (Real.exp 2)^5 / s.bandwidth^4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb := integral_mono hM (hΨ.const_mul C) (fun g => by
    convert s.sum_fourthLocalMajorant_le_variance (g+r) using 1
    dsimp [C]
    ring)
  rw [integral_const_mul] at hb
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left (gaussian_smallerEnvelope_intrinsic s A hv hdiag r) hC
  convert hh using 1
  dsimp [C]
  field_simp [s.bandwidth_pos.ne']
  ring

theorem intrinsic_gaussian_common_point_fourth_contraction {p n : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p)
    (y z : Fin n → Vector p) (hz : ∀ i, ‖z i‖ ≤ s.bandwidth) :
    (∫ g : Vector p, ∑ i, |diagonalFourth s ((g + r) + z i) (y i)| ∂gaussianLaw A) ≤
      coordinateFourthBudget y *
        ((75 * (Real.exp 2)^5 * Real.exp (3 / 2 : ℝ)) *
          (gaussianMaximumMean A / v) / s.bandwidth^3) := by
  let M : Vector p → ℝ := fun g => ∑ j, ∑ k, ∑ l, ∑ m,
    s.fourthLocalMajorant (g + r) j k l m
  have hM : Integrable M (gaussianLaw A) := by
    apply integrable_finset_sum; intro j _
    apply integrable_finset_sum; intro k _
    apply integrable_finset_sum; intro l _
    apply integrable_finset_sum; intro m _
    exact s.integrable_fourthLocalMajorant_comp (gaussianLaw A) (fun g => g + r)
      (measurable_id.add measurable_const) j k l m
  have hupper := hM.const_mul (coordinateFourthBudget y)
  have hcont : Continuous (fun g : Vector p =>
      ∑ i, |diagonalFourth s ((g + r) + z i) (y i)|) := by
    apply continuous_finset_sum; intro i _
    exact ((continuous_diagonalFourth s (y i)).comp
      ((continuous_id.add continuous_const).add continuous_const)).abs
  have hbound (g : Vector p) := common_point_fourth_contraction_majorant s (g + r) y z hz
  have hlo : Integrable (fun g : Vector p =>
      ∑ i, |diagonalFourth s ((g + r) + z i) (y i)|) (gaussianLaw A) :=
    hupper.mono' hcont.aestronglyMeasurable (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
      exact hbound g)
  calc
    _ ≤ ∫ g, coordinateFourthBudget y * M g ∂gaussianLaw A :=
      integral_mono hlo hupper (fun g => hbound g)
    _ = coordinateFourthBudget y * ∫ g, M g ∂gaussianLaw A := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (gaussian_integral_sum_fourthLocalMajorant_intrinsic hp s A hv hdiag r)
      (coordinateFourthBudget_nonneg y)

theorem intrinsic_gaussian_common_point_fourth_random_data
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
        (gaussianMaximumMean A / v) / s.bandwidth^3) *
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
      (gaussianMaximumMean A / v) / s.bandwidth^3)
  have hcomp := integral_mono_ae hFi.integral_prod_right hupper (by
    filter_upwards [ae_all_iff.mpr hz] with ω hω
    simpa only [F, mul_comm] using intrinsic_gaussian_common_point_fourth_contraction hp s A hv hdiag
      (R ω) (fun i => Y i ω) (fun i => Z i ω) hω)
  exact hcomp.trans_eq (integral_const_mul _ _)

end
end RectangleCLTArxivV1
