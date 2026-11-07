import RectangleCLTCompanion.SplitV4.SlepianDerivative
import RectangleCLTCompanion.SplitV4.ProductConditional
import Mathlib.Tactic.FinCases

/-! Coordinate contractions of the genuine paired-copy conditional
coefficients in Lemma G.3. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

namespace C4Test

variable {p : ℕ} (f : C4Test p)

private theorem paired_linear_coordinates (L : Vector p →L[ℝ] ℝ) (v : Vector p) :
    L v = ∑ j, v j * L (coordinateVector j) := by
  classical
  have hv : v = ∑ j : Fin p, v j • coordinateVector j := by
    ext k
    simp [coordinateVector, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul]

private theorem paired_update_two (u v : Vector p) :
    Function.update (fun _ : Fin 2 => u) 1 v =
      Function.update (fun _ : Fin 2 => v) 0 u := by
  ext i
  fin_cases i <;> simp

/-- The actual Hessian quadratic contraction is the coordinate trace of
the rank-one matrix. The coordinate order matches the Gaussian Stein API. -/
theorem secondDiagonal_eq_rankOne_hessianTrace (x y : Vector p) :
    f.secondDiagonal x y = f.hessianTrace (fun j k => y j * y k) x := by
  have hfirst := paired_linear_coordinates
    ((f.hessian x).toContinuousLinearMap (fun _ => y) 0) y
  simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply,
    Function.update_eq_self] at hfirst
  have hsecond (k : Fin p) :
      f.hessian x (Function.update (fun _ => y) 0 (coordinateVector k)) =
        ∑ j, y j * f.hessianCoordinate x j k := by
    have hh := paired_linear_coordinates
      ((f.hessian x).toContinuousLinearMap (fun _ => coordinateVector k) 1) y
    simp only [ContinuousMultilinearMap.toContinuousLinearMap_apply,
      paired_update_two, hessianCoordinate] at hh
    exact hh
  change f.hessian x (fun _ => y) = _
  rw [hfirst]
  simp_rw [hsecond]
  unfold hessianTrace
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem hessianTrace_sub (A B : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    f.hessianTrace (A - B) x = f.hessianTrace A x - f.hessianTrace B x := by
  simp only [hessianTrace, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem hessianTrace_smul (a : ℝ) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    f.hessianTrace (a • A) x = a * f.hessianTrace A x := by
  simp only [hessianTrace, Matrix.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Subtracting the truncated increment leaves exactly the manuscript's
strict large-increment cutoff, including the boundary case. -/
theorem paired_large_increment_eq_cutoff (x y : Vector p) (h : ℝ) :
    y - x - pairedTruncatedIncrement x y h =
      if h < ‖y - x‖ then y - x else 0 := by
  by_cases he : ‖y - x‖ ≤ h
  · simp only [pairedTruncatedIncrement, if_pos he, not_lt.mpr he, ↓reduceIte, sub_self]
  · have ht : h < ‖y - x‖ := lt_of_not_ge he
    simp only [pairedTruncatedIncrement, if_neg he, if_pos ht, sub_zero]

theorem measurable_truncated_copy_at {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → Vector p) (hX : Measurable X) (x : Vector p) (h : ℝ) :
    Measurable (fun ω => pairedTruncatedIncrement x (X ω) h) :=
  Measurable.ite (measurableSet_le (hX.sub_const x).norm measurable_const)
    (hX.sub_const x) measurable_const

theorem integrable_truncated_copy_at {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Vector p)
    (hX : Measurable X) (x : Vector p) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun ω => pairedTruncatedIncrement x (X ω) h) μ := by
  apply (integrable_const h).mono'
    (measurable_truncated_copy_at X hX x h).aestronglyMeasurable
  exact ae_of_all _ (fun ω => norm_pairedTruncatedIncrement_le x (X ω) hh)

theorem integrable_truncated_copy_coordinate_product
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Vector p) (hX : Measurable X) (x : Vector p) {h : ℝ} (hh : 0 ≤ h)
    (j k : Fin p) :
    Integrable (fun ω => pairedTruncatedIncrement x (X ω) h j *
      pairedTruncatedIncrement x (X ω) h k) μ := by
  have hY := measurable_truncated_copy_at X hX x h
  apply (integrable_const (h ^ 2)).mono'
    ((((measurable_pi_apply j).comp hY).mul
      ((measurable_pi_apply k).comp hY)).aestronglyMeasurable)
  apply ae_of_all
  intro ω
  have hb := norm_pairedTruncatedIncrement_le x (X ω) hh
  have hj : ‖pairedTruncatedIncrement x (X ω) h j‖ ≤ h :=
    (norm_le_pi_norm _ j).trans hb
  have hk : ‖pairedTruncatedIncrement x (X ω) h k‖ ≤ h :=
    (norm_le_pi_norm _ k).trans hb
  rw [norm_mul, pow_two]
  exact mul_le_mul hj hk (norm_nonneg _) hh

/-- The conditional copy second-moment matrix contracts to the actual
Hessian directional expectation. No matrix coefficient is postulated. -/
theorem hessianTrace_copyTruncatedCovariance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Vector p) (hX : Measurable X) (x z : Vector p) {h : ℝ} (hh : 0 ≤ h) :
    f.hessianTrace (copyTruncatedCovariance μ X x h) z =
      (1 / 2 : ℝ) * ∫ ω, f.secondDiagonal z (pairedTruncatedIncrement x (X ω) h) ∂μ := by
  have hi (j k : Fin p) := integrable_truncated_copy_coordinate_product μ X hX x hh j k
  have heq : (∫ ω, f.secondDiagonal z (pairedTruncatedIncrement x (X ω) h) ∂μ) =
      ∑ j, ∑ k, (∫ ω, pairedTruncatedIncrement x (X ω) h j *
        pairedTruncatedIncrement x (X ω) h k ∂μ) * f.hessianCoordinate z j k := by
    simp_rw [f.secondDiagonal_eq_rankOne_hessianTrace, hessianTrace]
    rw [integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum _ (fun k _ => (hi j k).mul_const _))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum Finset.univ (fun k _ => (hi j k).mul_const _)]
    simp only [integral_mul_const]
  rw [heq]
  simp only [hessianTrace, copyTruncatedCovariance, Finset.mul_sum, mul_assoc]

/-- The conditional large-increment vector contracts to the actual gradient
expectation. Genuine integrability follows from the original first moment
and the bounded truncated increment. -/
theorem gradient_copyLargeIncrementMean
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Vector p) (hX : Measurable X) (hXi : Integrable X μ)
    (x z : Vector p) {h : ℝ} (hh : 0 ≤ h) :
    f.gradient z (copyLargeIncrementMean μ X x h) =
      ∫ ω, f.gradient z (X ω - x - pairedTruncatedIncrement x (X ω) h) ∂μ := by
  have hi : Integrable (fun ω => X ω - x - pairedTruncatedIncrement x (X ω) h) μ :=
    (hXi.sub (integrable_const x)).sub (integrable_truncated_copy_at μ X hX x hh)
  exact ((f.gradient z).integral_comp_comm hi).symm

theorem integral_hessianTrace_copyTruncatedCovariance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X W : Ω → Vector p) (hX : Measurable X) (hW : Measurable W)
    {h : ℝ} (hh : 0 ≤ h) :
    (∫ ω, f.hessianTrace (copyTruncatedCovariance μ X (X ω) h) (W ω) ∂μ) =
      (1 / 2 : ℝ) * ∫ z : Ω × Ω,
        f.secondDiagonal (W z.1) (pairedTruncatedIncrement (X z.1) (X z.2) h) ∂μ.prod μ := by
  let Y := fun z : Ω × Ω => pairedTruncatedIncrement (X z.1) (X z.2) h
  let H := fun z : Ω × Ω => f.secondDiagonal (W z.1) (Y z)
  have hY : Measurable Y := measurable_pairedTruncatedIncrement X hX h
  have hi : Integrable H (μ.prod μ) := f.integrable_secondDiagonal (μ.prod μ)
    (fun z => W z.1) Y (hW.comp measurable_fst) hY h
    (fun z => norm_pairedTruncatedIncrement_le _ _ hh)
  calc
    _ = ∫ ω, (1 / 2 : ℝ) * ∫ ω', H (ω, ω') ∂μ ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => f.hessianTrace_copyTruncatedCovariance μ X hX (X ω) (W ω) hh)
    _ = _ := by rw [integral_const_mul, ← integral_prod _ hi]

theorem integral_gradient_copyLargeIncrementMean
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X W : Ω → Vector p) (hX : Measurable X) (hXi : Integrable X μ)
    (hW : Measurable W) {h : ℝ} (hh : 0 ≤ h) :
    (∫ ω, f.gradient (W ω) (copyLargeIncrementMean μ X (X ω) h) ∂μ) =
      ∫ z : Ω × Ω, f.gradient (W z.1)
        (X z.2 - X z.1 - pairedTruncatedIncrement (X z.1) (X z.2) h) ∂μ.prod μ := by
  have hi := f.integrable_gradient_eval_of_integrable_norm (μ.prod μ)
    (fun z => W z.1) (copyLargeIncrementIntegrand X h) (hW.comp measurable_fst)
    (measurable_copyLargeIncrementIntegrand X hX h)
    (integrable_copyLargeIncrementIntegrand μ X hX hXi hh).norm
  calc
    _ = ∫ ω, ∫ ω', f.gradient (W ω)
        (X ω' - X ω - pairedTruncatedIncrement (X ω) (X ω') h) ∂μ ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => f.gradient_copyLargeIncrementMean μ X hX hXi (X ω) (W ω) hh)
    _ = _ := (integral_prod _ hi).symm

theorem integrable_shifted_hessianTrace_copyTruncatedCovariance
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (X : Ω → Vector p) (W : Ω × Γ → Vector p) (hX : Measurable X) (hW : Measurable W)
    {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun z => f.hessianTrace (copyTruncatedCovariance μ X (X z.1) h) (W z))
      (μ.prod ν) := by
  let Y := fun z : (Ω × Γ) × Ω => pairedTruncatedIncrement (X z.1.1) (X z.2) h
  have hY : Measurable Y := by
    have hd : Measurable (fun z : (Ω × Γ) × Ω => X z.2 - X z.1.1) := (hX.comp measurable_snd).sub
      (hX.comp (measurable_fst.comp measurable_fst))
    exact Measurable.ite (measurableSet_le hd.norm measurable_const) hd measurable_const
  have hi := f.integrable_secondDiagonal ((μ.prod ν).prod μ)
    (fun z => W z.1) Y (hW.comp measurable_fst) hY h
    (fun z => norm_pairedTruncatedIncrement_le _ _ hh)
  apply (hi.integral_prod_left.const_mul (1 / 2 : ℝ)).congr
  exact ae_of_all _ (fun z =>
    (f.hessianTrace_copyTruncatedCovariance μ X hX (X z.1) (W z) hh).symm)

theorem shifted_hessianTrace_copyTruncatedCovariance
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (X : Ω → Vector p) (W : Ω × Γ → Vector p) (hX : Measurable X) (hW : Measurable W)
    {h : ℝ} (hh : 0 ≤ h) :
    (∫ z, f.hessianTrace (copyTruncatedCovariance μ X (X z.1) h) (W z) ∂μ.prod ν) =
      (1 / 2 : ℝ) * ∫ z : Γ × (Ω × Ω),
        f.secondDiagonal (W (z.2.1, z.1))
          (pairedTruncatedIncrement (X z.2.1) (X z.2.2) h) ∂ν.prod (μ.prod μ) := by
  let H := fun z : Γ × (Ω × Ω) => f.secondDiagonal (W (z.2.1, z.1))
    (pairedTruncatedIncrement (X z.2.1) (X z.2.2) h)
  have hW' : Measurable (fun z : Γ × (Ω × Ω) => W (z.2.1, z.1)) :=
    hW.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have hY : Measurable (fun z : Γ × (Ω × Ω) =>
      pairedTruncatedIncrement (X z.2.1) (X z.2.2) h) :=
    (measurable_pairedTruncatedIncrement X hX h).comp measurable_snd
  have hiH : Integrable H (ν.prod (μ.prod μ)) := f.integrable_secondDiagonal _ _ _ hW' hY h
    (fun z => norm_pairedTruncatedIncrement_le _ _ hh)
  have hi := f.integrable_shifted_hessianTrace_copyTruncatedCovariance μ ν X W hX hW hh
  calc
    _ = ∫ γ, ∫ ω, f.hessianTrace (copyTruncatedCovariance μ X (X ω) h) (W (ω, γ)) ∂μ ∂ν :=
      integral_prod_symm _ hi
    _ = ∫ γ, (1 / 2 : ℝ) * ∫ z, H (γ, z) ∂μ.prod μ ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ (fun γ => f.integral_hessianTrace_copyTruncatedCovariance μ X
        (fun ω => W (ω, γ)) hX (hW.comp (measurable_id.prodMk measurable_const)) hh)
    _ = _ := by rw [integral_const_mul, ← integral_prod _ hiH]

theorem integrable_shifted_gradient_copyLargeIncrementMean
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (X : Ω → Vector p) (W : Ω × Γ → Vector p) (hX : Measurable X) (hXi : Integrable X μ)
    (hW : Measurable W) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun z => f.gradient (W z) (copyLargeIncrementMean μ X (X z.1) h))
      (μ.prod ν) := by
  have hb : Integrable (fun ω => copyLargeIncrementMean μ X (X ω) h) μ :=
    (integrable_copyLargeIncrementIntegrand μ X hX hXi hh).integral_prod_left
  have hbm : Measurable (fun ω => copyLargeIncrementMean μ X (X ω) h) :=
    ((measurable_copyLargeIncrementIntegrand X hX h).stronglyMeasurable.integral_prod_right').measurable
  have hn : Integrable (fun z : Ω × Γ => ‖copyLargeIncrementMean μ X (X z.1) h‖) (μ.prod ν) := by
    simpa only [mul_one] using hb.norm.mul_prod (integrable_const (1 : ℝ))
  exact f.integrable_gradient_eval_of_integrable_norm _ W _ hW (hbm.comp measurable_fst) hn

theorem shifted_gradient_copyLargeIncrementMean
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (X : Ω → Vector p) (W : Ω × Γ → Vector p) (hX : Measurable X) (hXi : Integrable X μ)
    (hW : Measurable W) {h : ℝ} (hh : 0 ≤ h) :
    (∫ z, f.gradient (W z) (copyLargeIncrementMean μ X (X z.1) h) ∂μ.prod ν) =
      ∫ z : Γ × (Ω × Ω), f.gradient (W (z.2.1, z.1))
        (X z.2.2 - X z.2.1 - pairedTruncatedIncrement (X z.2.1) (X z.2.2) h)
          ∂ν.prod (μ.prod μ) := by
  let T := fun z : Γ × (Ω × Ω) => f.gradient (W (z.2.1, z.1))
    (copyLargeIncrementIntegrand X h z.2)
  have hN : Integrable (fun z : Γ × (Ω × Ω) => ‖copyLargeIncrementIntegrand X h z.2‖)
      (ν.prod (μ.prod μ)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod
      (integrable_copyLargeIncrementIntegrand μ X hX hXi hh).norm
  have hW' : Measurable (fun z : Γ × (Ω × Ω) => W (z.2.1, z.1)) :=
    hW.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have hiT : Integrable T (ν.prod (μ.prod μ)) :=
    f.integrable_gradient_eval_of_integrable_norm _ _ _ hW'
      ((measurable_copyLargeIncrementIntegrand X hX h).comp measurable_snd) hN
  have hi := f.integrable_shifted_gradient_copyLargeIncrementMean μ ν X W hX hXi hW hh
  calc
    _ = ∫ γ, ∫ ω, f.gradient (W (ω, γ)) (copyLargeIncrementMean μ X (X ω) h) ∂μ ∂ν :=
      integral_prod_symm _ hi
    _ = ∫ γ, ∫ z, T (γ, z) ∂μ.prod μ ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ (fun γ => f.integral_gradient_copyLargeIncrementMean μ X
        (fun ω => W (ω, γ)) hX hXi (hW.comp (measurable_id.prodMk measurable_const)) hh)
    _ = _ := (integral_prod _ hiT).symm

theorem hessianTrace_copyArrayTruncatedCovariance
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (ξ : Fin n → Ω → Vector p) (ω : Ω) (h : ℝ) (x : Vector p) :
    f.hessianTrace (copyArrayTruncatedCovariance μ ξ ω h) x =
      ∑ i, f.hessianTrace (copyTruncatedCovariance μ (ξ i) (ξ i ω) h) x := by
  simp only [hessianTrace, copyArrayTruncatedCovariance, Finset.sum_mul]
  let g := fun i j k => copyTruncatedCovariance μ (ξ i) (ξ i ω) h j k * f.hessianCoordinate x j k
  change (∑ j, ∑ k, ∑ i, g i j k) = ∑ i, ∑ j, ∑ k, g i j k
  calc
    _ = ∑ j, ∑ i, ∑ k, g i j k :=
      Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem integrable_shifted_hessianTrace_copyArrayTruncatedCovariance
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) (W : Ω × Γ → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hW : Measurable W) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun z => f.hessianTrace (copyArrayTruncatedCovariance μ ξ z.1 h) (W z))
      (μ.prod ν) := by
  simp_rw [f.hessianTrace_copyArrayTruncatedCovariance]
  exact integrable_finset_sum _ (fun i _ =>
    f.integrable_shifted_hessianTrace_copyTruncatedCovariance μ ν (ξ i) W (hξ i) hW hh)

theorem integrable_shifted_hessianTrace_copyArray_sub
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) (W : Ω × Γ → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hW : Measurable W) (cov : Matrix (Fin p) (Fin p) ℝ)
    {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun z => f.hessianTrace (copyArrayTruncatedCovariance μ ξ z.1 h - cov) (W z))
      (μ.prod ν) := by
  simp_rw [f.hessianTrace_sub]
  exact (f.integrable_shifted_hessianTrace_copyArrayTruncatedCovariance μ ν ξ W hξ hW hh).sub
    (f.integrable_hessianTrace (μ.prod ν) W hW cov)

/-- Full-array conditional covariance contraction, including an arbitrary
independent shift. Its right-hand side uses the actual array/copy experiment
in the order needed by the paired Slepian identity. -/
theorem shifted_hessianTrace_copyArrayTruncatedCovariance
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) (W : Ω × Γ → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hW : Measurable W) {h : ℝ} (hh : 0 ≤ h) :
    (∫ z, f.hessianTrace (copyArrayTruncatedCovariance μ ξ z.1 h) (W z) ∂μ.prod ν) =
      (1 / 2 : ℝ) * ∑ i, ∫ z : Γ × (Ω × Ω), f.secondDiagonal (W (z.2.1, z.1))
        (pairedTruncatedIncrement (ξ i z.2.1) (ξ i z.2.2) h) ∂ν.prod (μ.prod μ) := by
  simp_rw [f.hessianTrace_copyArrayTruncatedCovariance]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    f.integrable_shifted_hessianTrace_copyTruncatedCovariance μ ν (ξ i) W (hξ i) hW hh)]
  calc
    _ = ∑ i, (1 / 2 : ℝ) * ∫ z : Γ × (Ω × Ω), f.secondDiagonal (W (z.2.1, z.1))
        (pairedTruncatedIncrement (ξ i z.2.1) (ξ i z.2.2) h) ∂ν.prod (μ.prod μ) :=
      Finset.sum_congr rfl (fun i _ =>
        f.shifted_hessianTrace_copyTruncatedCovariance μ ν (ξ i) W (hξ i) hW hh)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem integrable_shifted_gradient_copyArrayLargeMean
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) (W : Ω × Γ → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hξi : ∀ i, Integrable (ξ i) μ)
    (hW : Measurable W) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun z => f.gradient (W z) (copyArrayLargeMean μ ξ z.1 h)) (μ.prod ν) := by
  simp only [copyArrayLargeMean, map_sum]
  exact integrable_finset_sum _ (fun i _ =>
    f.integrable_shifted_gradient_copyLargeIncrementMean μ ν (ξ i) W (hξ i) (hξi i) hW hh)

/-- Full-array large-increment mean contraction, with all summands retained.
Neither symmetry nor independence of the summands is needed for this
conditional-expectation conversion. -/
theorem shifted_gradient_copyArrayLargeMean
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) (W : Ω × Γ → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hξi : ∀ i, Integrable (ξ i) μ)
    (hW : Measurable W) {h : ℝ} (hh : 0 ≤ h) :
    (∫ z, f.gradient (W z) (copyArrayLargeMean μ ξ z.1 h) ∂μ.prod ν) =
      ∑ i, ∫ z : Γ × (Ω × Ω), f.gradient (W (z.2.1, z.1))
        (ξ i z.2.2 - ξ i z.2.1 - pairedTruncatedIncrement (ξ i z.2.1) (ξ i z.2.2) h)
          ∂ν.prod (μ.prod μ) := by
  simp only [copyArrayLargeMean, map_sum]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    f.integrable_shifted_gradient_copyLargeIncrementMean μ ν (ξ i) W (hξ i) (hξi i) hW hh)]
  exact Finset.sum_congr rfl (fun i _ =>
    f.shifted_gradient_copyLargeIncrementMean μ ν (ξ i) W (hξ i) (hξi i) hW hh)

end C4Test

end

end RectangleCLT.Companion.SplitV4
