import RectangleCLTCompanion.SplitV4.RelativeMoments
import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeAverage34

/-! Direct derivative estimates preserve the signed aggregate cubic
coefficient before taking absolute values. Singular covariance directions
are handled by symmetric polarization, without an inverse covariance. -/

open MeasureTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem matrixQuadratic_smul_eq {p : ℕ} (c : ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (u : Vector p) :
    matrixQuadratic (c • A) u = c*matrixQuadratic A u := by
  simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem matrixQuadratic_single_add_sub {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) :
    matrixQuadratic A (Pi.single j 1+Pi.single k 1) -
      matrixQuadratic A (Pi.single j 1-Pi.single k 1) = 2*(A j k+A k j) ∧
    matrixQuadratic A (Pi.single j 1+Pi.single k 1) +
      matrixQuadratic A (Pi.single j 1-Pi.single k 1) = 2*(A j j+A k k) := by
  simp only [matrixQuadratic, Pi.add_apply, Pi.sub_apply, add_mul, sub_mul,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Pi.single_apply, ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  constructor <;> ring

theorem abs_entry_le_of_relative_quadratic_bound {p : ℕ}
    (A S : Matrix (Fin p) (Fin p) ℝ) (hA : A.transpose = A)
    {s : ℝ} (hbound : ∀ u, |matrixQuadratic A u| ≤ s*matrixQuadratic S u)
    (hunit : ∀ j, S j j = 1) (j k : Fin p) : |A j k| ≤ s := by
  have hp := abs_le.mp (hbound (Pi.single j 1+Pi.single k 1))
  have hm := abs_le.mp (hbound (Pi.single j 1-Pi.single k 1))
  have hAp := (matrixQuadratic_single_add_sub A j k).1
  have hSp := (matrixQuadratic_single_add_sub S j k).2
  have hsym : A k j = A j k := by simpa only [Matrix.transpose_apply] using congrFun (congrFun hA j) k
  rw [hsym] at hAp
  rw [hunit j, hunit k] at hSp
  have hs := congrArg (fun x => s*x) hSp
  dsimp only at hs
  simp only [mul_add] at hs
  apply abs_le.mpr
  constructor <;> nlinarith only [hp.1, hp.2, hm.1, hm.2, hAp, hs]

theorem RelativeMomentBounds.abs_third_entry_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (h : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (j k l : Fin p) :
    |relativeThirdMatrix μ ξ j k l| ≤ s₃ := by
  apply abs_entry_le_of_relative_quadratic_bound (relativeThirdMatrix μ ξ j) (covariance μ (sumVector ξ))
    (restorationCoefficient_symmetric μ ξ (fun i ω => ξ i ω j)) _ hunit
  intro u
  apply abs_le.mpr
  have hlo := h.third_lower j u
  have hup := h.third_upper j u
  rw [matrixQuadratic_smul_eq] at hlo hup
  exact ⟨by linarith, hup⟩

/-- The actual third moment is summed with its sign before contraction. -/
def relativeCubicContraction {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) : ℝ :=
  ∑ j, ∑ k, ∑ l, relativeThirdMatrix μ ξ j k l*s.mixedThirdDerivativeF x j k l

theorem abs_relativeCubicContraction_le_envelope
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (s : FaceSmoother p) (h : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (x : Vector p) :
    |relativeCubicContraction s μ ξ x| ≤ 13*s₃*s.F x*(1-s.F x)/s.bandwidth^3 := by
  have hn : 0 ≤ s.F x*(1-s.F x) := mul_nonneg (s.F_pos x).le (sub_nonneg.mpr (s.F_le_one x))
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, |relativeThirdMatrix μ ξ j k l*s.mixedThirdDerivativeF x j k l| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j, ∑ k, ∑ l, s₃*|s.mixedThirdDerivativeF x j k l| := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (h.abs_third_entry_le hunit j k l) (abs_nonneg _)
    _ = s₃*(∑ j, ∑ k, ∑ l, |s.mixedThirdDerivativeF x j k l|) := by simp only [Finset.mul_sum]
    _ ≤ s₃*(13*s.F x*(1-s.F x)/s.bandwidth^3) :=
      mul_le_mul_of_nonneg_left (s.sum_abs_mixedThirdDerivativeF_le_variance x) h.s₃_nonneg
    _ = _ := by ring

theorem integrable_relativeCubicContraction_and_integral_bound
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {p n : ℕ}
    (μ : Measure Ω) (ν : Measure Γ) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) {s₃ s₄ : ℝ}
    (s : FaceSmoother p) (h : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (X : Γ → Vector p) (hX : Measurable X) :
    Integrable (fun ω => relativeCubicContraction s μ ξ (X ω)) ν ∧
      |∫ ω, relativeCubicContraction s μ ξ (X ω) ∂ν| ≤
        (13*s₃/s.bandwidth^3)*(∫ ω, s.F (X ω)*(1-s.F (X ω)) ∂ν) := by
  let E : Γ → ℝ := fun ω => s.F (X ω)*(1-s.F (X ω))
  have hiE : Integrable E ν := by
    apply (integrable_const (1 : ℝ)).mono'
      (((s.continuous_F.mul (continuous_const.sub s.continuous_F)).measurable.comp hX).aestronglyMeasurable)
    filter_upwards [] with ω
    simp only [E, Function.comp_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (s.F_pos _).le (sub_nonneg.mpr (s.F_le_one _)))]
    nlinarith [s.F_le_one (X ω), (s.F_pos (X ω)).le, sq_nonneg (s.F (X ω))]
  have hm : Measurable (fun ω => relativeCubicContraction s μ ξ (X ω)) := by
    unfold relativeCubicContraction
    exact Finset.measurable_sum _ (fun j _ => Finset.measurable_sum _ (fun k _ =>
      Finset.measurable_sum _ (fun l _ => measurable_const.mul
        ((s.continuous_thirdDerivative j k l).measurable.comp hX))))
  have hp (ω : Γ) : |relativeCubicContraction s μ ξ (X ω)| ≤ (13*s₃/s.bandwidth^3)*E ω :=
    (abs_relativeCubicContraction_le_envelope s h hunit (X ω)).trans_eq (by dsimp only [E]; ring)
  have hiC : Integrable (fun ω => relativeCubicContraction s μ ξ (X ω)) ν := by
    apply (hiE.const_mul (13*s₃/s.bandwidth^3)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hp ω)
  refine ⟨hiC, ?_⟩
  have hi := integral_mono_ae hiC.abs (hiE.const_mul (13*s₃/s.bandwidth^3)) (ae_of_all _ hp)
  exact abs_integral_le_integral_abs.trans (hi.trans_eq (integral_const_mul _ _))

end
end RectangleCLT.Companion.SplitV4
