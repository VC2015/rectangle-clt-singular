import RectangleCLTCompanion.SplitV4.SmootherC4
import RectangleCLTCompanion.SplitV4.SlepianDerivative
import RectangleCLTCompanion.SplitV4.ConditionalMatrixFluctuation
import RectangleCLT.GaussianEnvelope
import Mathlib.Tactic.FinCases

/-! Gaussian averaged first and second derivative contractions. The random
center and coefficients may depend arbitrarily on the same original sample;
only the Gaussian sample is independent. Matrix coefficients use the actual
maximum-entry norm, with no rank or eigenvalue loss. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem matrix_entry_abs_le_maxEntryNorm {p : ℕ}
    (M : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) : |M j k| ≤ matrixMaxEntryNorm M :=
  (norm_le_pi_norm (M j) k).trans (norm_le_pi_norm M j)

theorem smootherC4Test_hessianCoordinate {p : ℕ} (s : FaceSmoother p)
    (x : Vector p) (j k : Fin p) :
    (smootherC4Test s).hessianCoordinate x j k = s.mixedSecondDerivativeF x j k := by
  change iteratedFDeriv ℝ 2 s.F x
    (Function.update (fun _ : Fin 2 => C4Test.coordinateVector j) 0 (C4Test.coordinateVector k)) = _
  have ht : Function.update (fun _ : Fin 2 => C4Test.coordinateVector j) 0 (C4Test.coordinateVector k) =
      (fun i : Fin 2 => FaceSmoother.coordinateDirection ((![k, j] : Fin 2 → Fin p) i)) := by
    ext i l
    fin_cases i <;> simp [C4Test.coordinateVector, FaceSmoother.coordinateDirection, Pi.single_apply]
  rw [ht]
  simpa using smoother_iteratedFDeriv_two_coordinate s x (![k, j] : Fin 2 → Fin p)

theorem abs_smoother_gradient_le_envelope {p : ℕ} (s : FaceSmoother p) (x b : Vector p) :
    |(smootherC4Test s).gradient x b| ≤
      (‖b‖ / s.bandwidth) * (s.F x * (1 - s.F x)) := by
  rw [smootherC4Test_gradient_eq_translationD1]
  unfold FaceSmoother.translationD1
  calc
    _ ≤ ∑ j, |s.coordinateDerivativeF x j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |s.coordinateDerivativeF x j| * ‖b‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm b j) (abs_nonneg _)
    _ = ‖b‖ * ∑ j, |s.coordinateDerivativeF x j| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ ‖b‖ * (s.F x * (1 - s.F x) / s.bandwidth) :=
      mul_le_mul_of_nonneg_left (s.sum_abs_deriv_F_coordinate_le_variance x) (norm_nonneg b)
    _ = _ := by ring

theorem abs_smoother_hessianTrace_le_envelope {p : ℕ} (s : FaceSmoother p)
    (x : Vector p) (M : Matrix (Fin p) (Fin p) ℝ) :
    |(smootherC4Test s).hessianTrace M x| ≤
      (3 * matrixMaxEntryNorm M / s.bandwidth ^ 2) * (s.F x * (1 - s.F x)) := by
  simp only [C4Test.hessianTrace, smootherC4Test_hessianCoordinate]
  calc
    _ ≤ ∑ j, ∑ k, |M j k * s.mixedSecondDerivativeF x j k| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j, ∑ k, matrixMaxEntryNorm M * |s.mixedSecondDerivativeF x j k| := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (matrix_entry_abs_le_maxEntryNorm M j k) (abs_nonneg _)
    _ = matrixMaxEntryNorm M * ∑ j, ∑ k, |s.mixedSecondDerivativeF x j k| := by
      simp only [Finset.mul_sum]
    _ ≤ matrixMaxEntryNorm M * (3 * s.F x * (1 - s.F x) / s.bandwidth ^ 2) :=
      mul_le_mul_of_nonneg_left (s.sum_abs_mixedSecondDerivativeF_le_variance x) (norm_nonneg (fun j : Fin p => fun k : Fin p => M j k))
    _ = _ := by ring

theorem gaussian_gradient_contraction {p : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r b : Vector p) :
    (∫ g, |(smootherC4Test s).gradient (g + r) b| ∂gaussianLaw A) ≤
      Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p / v) * ‖b‖ := by
  have hi := (smootherC4Test s).integrable_gradient_eval (gaussianLaw A)
    (fun g => g + r) (fun _ => b) (measurable_id.add_const r) measurable_const ‖b‖ (fun _ => le_rfl)
  have hΨ := s.integrable_smallerEnvelope (fun g : Vector p => g + r) (measurable_id.add_const r)
    (μ := gaussianLaw A)
  calc
    _ ≤ ∫ g, (‖b‖ / s.bandwidth) * (s.F (g + r) * (1 - s.F (g + r))) ∂gaussianLaw A :=
      integral_mono_ae hi.abs (hΨ.const_mul _) (ae_of_all _ (fun g => abs_smoother_gradient_le_envelope s _ b))
    _ = (‖b‖ / s.bandwidth) * ∫ g, s.F (g + r) * (1 - s.F (g + r)) ∂gaussianLaw A :=
      integral_const_mul _ _
    _ ≤ (‖b‖ / s.bandwidth) *
        (Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p / v)) :=
      mul_le_mul_of_nonneg_left (s.gaussian_expected_variance_le_of_diagonal hp A hv hdiag r)
        (div_nonneg (norm_nonneg b) s.bandwidth_pos.le)
    _ = _ := by field_simp [ne_of_gt s.bandwidth_pos]; ring

theorem gaussian_hessian_contraction {p : ℕ} (hp : 1 ≤ p) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p)
    (M : Matrix (Fin p) (Fin p) ℝ) :
    (∫ g, |(smootherC4Test s).hessianTrace M (g + r)| ∂gaussianLaw A) ≤
      (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth) * Real.sqrt (dimensionLog p / v) * matrixMaxEntryNorm M := by
  have hi := (smootherC4Test s).integrable_hessianTrace (gaussianLaw A)
    (fun g => g + r) (measurable_id.add_const r) M
  have hΨ := s.integrable_smallerEnvelope (fun g : Vector p => g + r) (measurable_id.add_const r)
    (μ := gaussianLaw A)
  calc
    _ ≤ ∫ g, (3 * matrixMaxEntryNorm M / s.bandwidth ^ 2) *
        (s.F (g + r) * (1 - s.F (g + r))) ∂gaussianLaw A :=
      integral_mono_ae hi.abs (hΨ.const_mul _) (ae_of_all _ (fun g => abs_smoother_hessianTrace_le_envelope s _ M))
    _ = (3 * matrixMaxEntryNorm M / s.bandwidth ^ 2) *
        ∫ g, s.F (g + r) * (1 - s.F (g + r)) ∂gaussianLaw A := integral_const_mul _ _
    _ ≤ (3 * matrixMaxEntryNorm M / s.bandwidth ^ 2) *
        (Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p / v)) :=
      mul_le_mul_of_nonneg_left (s.gaussian_expected_variance_le_of_diagonal hp A hv hdiag r)
        (by unfold matrixMaxEntryNorm; positivity)
    _ = _ := by field_simp [ne_of_gt s.bandwidth_pos]; ring

theorem integrable_weighted_gaussian_gradient
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (R b : Ω → Vector p)
    (hR : Measurable R) (hb : Measurable b) (hbi : Integrable (fun ω => ‖b ω‖) μ) :
    Integrable (fun z : Ω × Vector p => (smootherC4Test s).gradient (z.2 + R z.1) (b z.1))
      (μ.prod (gaussianLaw A)) := by
  have hn : Integrable (fun z : Ω × Vector p => ‖b z.1‖) (μ.prod (gaussianLaw A)) := by
    simpa only [mul_one] using hbi.mul_prod (integrable_const (1 : ℝ))
  exact (smootherC4Test s).integrable_gradient_eval_of_integrable_norm _ _ _
    (measurable_snd.add (hR.comp measurable_fst)) (hb.comp measurable_fst) hn

theorem weighted_gaussian_gradient_contraction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (R b : Ω → Vector p)
    (hR : Measurable R) (hb : Measurable b) (hbi : Integrable (fun ω => ‖b ω‖) μ) :
    (∫ z : Ω × Vector p, |(smootherC4Test s).gradient (z.2 + R z.1) (b z.1)|
      ∂μ.prod (gaussianLaw A)) ≤
      (Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p / v)) * ∫ ω, ‖b ω‖ ∂μ := by
  have hi := integrable_weighted_gaussian_gradient s μ A R b hR hb hbi
  calc
    _ = ∫ ω, ∫ g, |(smootherC4Test s).gradient (g + R ω) (b ω)| ∂gaussianLaw A ∂μ :=
      integral_prod _ hi.abs
    _ ≤ ∫ ω, (Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p / v)) * ‖b ω‖ ∂μ :=
      integral_mono_ae hi.abs.integral_prod_left (hbi.const_mul _)
        (ae_of_all _ (fun ω => gaussian_gradient_contraction hp s A hv hdiag (R ω) (b ω)))
    _ = _ := integral_const_mul _ _

theorem integrable_weighted_gaussian_hessian
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (R : Ω → Vector p)
    (M : Ω → Matrix (Fin p) (Fin p) ℝ) (hR : Measurable R)
    (hM : ∀ j k, Measurable (fun ω => M ω j k))
    (hMi : Integrable (fun ω => matrixMaxEntryNorm (M ω)) μ) :
    Integrable (fun z : Ω × Vector p => (smootherC4Test s).hessianTrace (M z.1) (z.2 + R z.1))
      (μ.prod (gaussianLaw A)) := by
  have hQ : Measurable (fun z : Ω × Vector p => z.2 + R z.1) :=
    measurable_snd.add (hR.comp measurable_fst)
  have hF : Measurable (fun z : Ω × Vector p =>
      (smootherC4Test s).hessianTrace (M z.1) (z.2 + R z.1)) := by
    apply Finset.measurable_sum
    intro j _
    apply Finset.measurable_sum
    intro k _
    exact (((hM j k).comp measurable_fst).mul
      (((smootherC4Test s).continuous_hessianCoordinate j k).measurable.comp hQ))
  have hn : Integrable (fun z : Ω × Vector p => matrixMaxEntryNorm (M z.1))
      (μ.prod (gaussianLaw A)) := by
    simpa only [mul_one] using hMi.mul_prod (integrable_const (1 : ℝ))
  apply (hn.const_mul (3 / s.bandwidth ^ 2)).mono' hF.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs]
  calc
    _ ≤ (3 * matrixMaxEntryNorm (M z.1) / s.bandwidth ^ 2) *
        (s.F (z.2 + R z.1) * (1 - s.F (z.2 + R z.1))) :=
      abs_smoother_hessianTrace_le_envelope s _ _
    _ ≤ (3 * matrixMaxEntryNorm (M z.1) / s.bandwidth ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left (s.variance_le_one _)
        (by unfold matrixMaxEntryNorm; positivity)
    _ = _ := by ring

theorem weighted_gaussian_hessian_contraction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (R : Ω → Vector p)
    (M : Ω → Matrix (Fin p) (Fin p) ℝ) (hR : Measurable R)
    (hM : ∀ j k, Measurable (fun ω => M ω j k))
    (hMi : Integrable (fun ω => matrixMaxEntryNorm (M ω)) μ) :
    (∫ z : Ω × Vector p, |(smootherC4Test s).hessianTrace (M z.1) (z.2 + R z.1)|
      ∂μ.prod (gaussianLaw A)) ≤
      (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth * Real.sqrt (dimensionLog p / v)) *
        ∫ ω, matrixMaxEntryNorm (M ω) ∂μ := by
  have hi := integrable_weighted_gaussian_hessian s μ A R M hR hM hMi
  calc
    _ = ∫ ω, ∫ g, |(smootherC4Test s).hessianTrace (M ω) (g + R ω)| ∂gaussianLaw A ∂μ :=
      integral_prod _ hi.abs
    _ ≤ ∫ ω, (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth * Real.sqrt (dimensionLog p / v)) *
        matrixMaxEntryNorm (M ω) ∂μ :=
      integral_mono_ae hi.abs.integral_prod_left (hMi.const_mul _)
        (ae_of_all _ (fun ω => gaussian_hessian_contraction hp s A hv hdiag (R ω) (M ω)))
    _ = _ := integral_const_mul _ _

theorem gaussianLaw_map_scalar {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) :
    (gaussianLaw A).map (fun g => c • g) = gaussianLaw (c • A) := by
  unfold gaussianLaw
  have hsmul : Measurable (fun g : Vector p => c • g) := measurable_const.smul measurable_id
  rw [Measure.map_map hsmul (measurable_mulVec A)]
  congr 1
  funext g
  exact (Matrix.smul_mulVec_assoc c A g).symm

theorem scaled_gaussian_product_preserving
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [SFinite μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) :
    MeasurePreserving (fun z : Ω × Vector p => (z.1, c • z.2))
      (μ.prod (gaussianLaw A)) (μ.prod (gaussianLaw (c • A))) := by
  exact (MeasurePreserving.id μ).prod
    ⟨measurable_const.smul measurable_id, gaussianLaw_map_scalar A c⟩

theorem integrable_scaled_gaussian_product
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [SFinite μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) (F : Ω × Vector p → ℝ)
    (hi : Integrable F (μ.prod (gaussianLaw (c • A)))) :
    Integrable (fun z : Ω × Vector p => F (z.1, c • z.2)) (μ.prod (gaussianLaw A)) :=
  ((scaled_gaussian_product_preserving μ A c).integrable_comp hi.aestronglyMeasurable).mpr hi

theorem integral_scaled_gaussian_product
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [SFinite μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) (F : Ω × Vector p → ℝ)
    (hi : Integrable F (μ.prod (gaussianLaw (c • A)))) :
    (∫ z : Ω × Vector p, F (z.1, c • z.2) ∂μ.prod (gaussianLaw A)) =
      ∫ z, F z ∂μ.prod (gaussianLaw (c • A)) := by
  have hmp := scaled_gaussian_product_preserving μ A c
  have hm : AEStronglyMeasurable F ((μ.prod (gaussianLaw A)).map
      (fun z : Ω × Vector p => (z.1, c • z.2))) := by
    rw [hmp.map_eq]
    exact hi.aestronglyMeasurable
  rw [← integral_map hmp.measurable.aemeasurable hm, hmp.map_eq]

theorem slepian_scaled_factor_diagonal {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) {t : ℝ} (ht : t ≤ 1) :
    ∀ j, ((Real.sqrt (1 - t) • A) * (Real.sqrt (1 - t) • A).transpose) j j = 1 - t := by
  intro j
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_apply, smul_eq_mul, hdiag, mul_one]
  simpa only [pow_two] using Real.sq_sqrt (sub_nonneg.mpr ht)

theorem integrable_slepian_weighted_gradient
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (W b : Ω → Vector p)
    (hW : Measurable W) (hb : Measurable b) (hbi : Integrable (fun ω => ‖b ω‖) μ) (t : ℝ) :
    Integrable (fun z => (smootherC4Test s).gradient (C4Test.slepianPoint W t z) (b z.1))
      (μ.prod (gaussianLaw A)) := by
  have hi := integrable_weighted_gaussian_gradient s μ (Real.sqrt (1 - t) • A)
    (fun ω => Real.sqrt t • W ω) b (measurable_const.smul hW) hb hbi
  have hs := integrable_scaled_gaussian_product μ A (Real.sqrt (1 - t)) _ hi
  simpa only [C4Test.slepianPoint, add_comm] using hs

theorem slepian_weighted_gradient_contraction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (W b : Ω → Vector p) (hW : Measurable W) (hb : Measurable b)
    (hbi : Integrable (fun ω => ‖b ω‖) μ) {t : ℝ} (ht : t < 1) :
    (∫ z, |(smootherC4Test s).gradient (C4Test.slepianPoint W t z) (b z.1)|
      ∂μ.prod (gaussianLaw A)) ≤
      (Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p / (1 - t))) * ∫ ω, ‖b ω‖ ∂μ := by
  have hi := integrable_weighted_gaussian_gradient s μ (Real.sqrt (1 - t) • A)
    (fun ω => Real.sqrt t • W ω) b (measurable_const.smul hW) hb hbi
  have he := integral_scaled_gaussian_product μ A (Real.sqrt (1 - t)) _ hi.abs
  have hbnd := weighted_gaussian_gradient_contraction hp s μ (Real.sqrt (1 - t) • A)
    (sub_pos.mpr ht) (slepian_scaled_factor_diagonal A hdiag ht.le)
    (fun ω => Real.sqrt t • W ω) b (measurable_const.smul hW) hb hbi
  simpa only [C4Test.slepianPoint, add_comm] using he.trans_le hbnd

theorem integrable_slepian_weighted_hessian
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (W : Ω → Vector p)
    (M : Ω → Matrix (Fin p) (Fin p) ℝ) (hW : Measurable W)
    (hM : ∀ j k, Measurable (fun ω => M ω j k))
    (hMi : Integrable (fun ω => matrixMaxEntryNorm (M ω)) μ) (t : ℝ) :
    Integrable (fun z => (smootherC4Test s).hessianTrace (M z.1) (C4Test.slepianPoint W t z))
      (μ.prod (gaussianLaw A)) := by
  have hi := integrable_weighted_gaussian_hessian s μ (Real.sqrt (1 - t) • A)
    (fun ω => Real.sqrt t • W ω) M (measurable_const.smul hW) hM hMi
  have hs := integrable_scaled_gaussian_product μ A (Real.sqrt (1 - t)) _ hi
  simpa only [C4Test.slepianPoint, add_comm] using hs

theorem slepian_weighted_hessian_contraction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (W : Ω → Vector p) (M : Ω → Matrix (Fin p) (Fin p) ℝ) (hW : Measurable W)
    (hM : ∀ j k, Measurable (fun ω => M ω j k))
    (hMi : Integrable (fun ω => matrixMaxEntryNorm (M ω)) μ) {t : ℝ} (ht : t < 1) :
    (∫ z, |(smootherC4Test s).hessianTrace (M z.1) (C4Test.slepianPoint W t z)|
      ∂μ.prod (gaussianLaw A)) ≤
      (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth * Real.sqrt (dimensionLog p / (1 - t))) *
        ∫ ω, matrixMaxEntryNorm (M ω) ∂μ := by
  have hi := integrable_weighted_gaussian_hessian s μ (Real.sqrt (1 - t) • A)
    (fun ω => Real.sqrt t • W ω) M (measurable_const.smul hW) hM hMi
  have he := integral_scaled_gaussian_product μ A (Real.sqrt (1 - t)) _ hi.abs
  have hbnd := weighted_gaussian_hessian_contraction hp s μ (Real.sqrt (1 - t) • A)
    (sub_pos.mpr ht) (slepian_scaled_factor_diagonal A hdiag ht.le)
    (fun ω => Real.sqrt t • W ω) M (measurable_const.smul hW) hM hMi
  simpa only [C4Test.slepianPoint, add_comm] using he.trans_le hbnd

end

end RectangleCLT.Companion.SplitV4
