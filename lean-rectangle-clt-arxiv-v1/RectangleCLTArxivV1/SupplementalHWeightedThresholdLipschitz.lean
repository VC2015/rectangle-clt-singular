import RectangleCLTArxivV1.SupplementalHWeightedThresholdDerivative

/-! Uniform finite domination for exchanging the actual Gamma derivative. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem gaussian_exp_sq_polynomial_bound (t a : ℝ) (ha : 0<a) :
    t^2*Real.exp (-(t^2/a)) ≤ a := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (t^2/a))
    (Real.exp_nonneg (-(t^2/a)))
  rw [show Real.exp (t^2/a)*Real.exp (-(t^2/a))=1 by
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]] at hh
  have hm := mul_le_mul_of_nonneg_left hh ha.le
  have he : a*((t^2/a+1)*Real.exp (-(t^2/a)))=
      t^2*Real.exp (-(t^2/a))+a*Real.exp (-(t^2/a)) := by
    field_simp
    ring
  rw [he] at hm
  nlinarith [Real.exp_pos (-(t^2/a))]

def gaussianAbsoluteFaceDensityBudget (r : ℕ) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹*(9+3*(r:ℝ))

theorem gaussianAbsoluteFaceDensityBudget_nonneg (r : ℕ) :
    0≤gaussianAbsoluteFaceDensityBudget r := by
  unfold gaussianAbsoluteFaceDensityBudget
  positivity

theorem gaussianPDFReal_mul_abs_sq_add_dimension_le (r : ℕ) (t : ℝ) :
    gaussianPDFReal 0 1 t*(|t| *(t^2+2*(r:ℝ)))≤gaussianAbsoluteFaceDensityBudget r := by
  let e := Real.exp (-(t^2/2))
  have he0 : 0≤e := Real.exp_nonneg _
  have he1 : e≤1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])
  have h2 : t^2*e≤2 := gaussian_exp_sq_polynomial_bound t 2 (by norm_num)
  have h4 : t^4*e≤16 := by
    have hh := pow_le_pow_left₀
      (mul_nonneg (sq_nonneg t) (Real.exp_nonneg (-(t^2/4))))
      (gaussian_exp_sq_polynomial_bound t 4 (by norm_num)) 2
    have heq : Real.exp (-(t^2/4))^2=e := by
      rw [←Real.exp_nat_mul]
      dsimp [e]
      congr 1
      norm_num
      ring
    rw [mul_pow,heq] at hh
    convert hh using 1 <;> ring
  have ht : |t|≤(t^2+1)/2 := by nlinarith [sq_nonneg (|t|-1),sq_abs t]
  have hr : 0≤(r:ℝ) := Nat.cast_nonneg r
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right ht (by positivity : 0≤t^2+2*(r:ℝ))) he0
  have hscalar : e*(|t| *(t^2+2*(r:ℝ)))≤9+3*(r:ℝ) := by
    have h22 := mul_le_mul_of_nonneg_left h2 (by positivity : 0≤1+2*(r:ℝ))
    have hr0 := mul_le_mul_of_nonneg_left he1 (by positivity : 0≤2*(r:ℝ))
    nlinarith [sq_nonneg t]
  have hpdf : gaussianPDFReal 0 1 t=(Real.sqrt (2*Real.pi))⁻¹*e := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,neg_div,e]
  rw [hpdf,mul_assoc]
  exact mul_le_mul_of_nonneg_left hscalar (by positivity)

theorem norm_gaussianAbsoluteFace_section_density_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1) (t : ℝ) :
    ‖gaussianPDFReal 0 1 t*(|t| * Printed.thresholdSignedSection u b j t)‖≤
      gaussianAbsoluteFaceDensityBudget r := by
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),abs_mul,abs_abs]
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Printed.abs_thresholdSignedSection_le u b j hu t) (abs_nonneg t))
    (gaussianPDFReal_nonneg _ _ _)).trans (gaussianPDFReal_mul_abs_sq_add_dimension_le r t)

theorem gaussianThresholdAbsoluteFaceTrace_update_increment_bound {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1)
    (c d : ℝ) :
    ‖gaussianThresholdAbsoluteFaceTrace u (Function.update b j c) j-
      gaussianThresholdAbsoluteFaceTrace u (Function.update b j d) j‖≤
      gaussianAbsoluteFaceDensityBudget (n+1)*|c-d| := by
  have hi := standardRealGaussian_integrable_density_mul (integrable_abs_mul_thresholdSignedSection u b j hu)
  rw [gaussianThresholdAbsoluteFaceTrace_update_eq_section_integral u b j hu c,
    gaussianThresholdAbsoluteFaceTrace_update_eq_section_integral u b j hu d,
    intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ =>
    norm_gaussianAbsoluteFace_section_density_le u b j hu t)

theorem lipschitzWith_gaussianThresholdAbsoluteFaceTrace_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hu : vectorNormSq (u j)=1) :
    LipschitzWith ⟨gaussianAbsoluteFaceDensityBudget (n+1),gaussianAbsoluteFaceDensityBudget_nonneg _⟩
      (fun t => gaussianThresholdAbsoluteFaceTrace u (Function.update b j t) j) := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  simpa only [dist_eq_norm,Real.norm_eq_abs] using
    gaussianThresholdAbsoluteFaceTrace_update_increment_bound u b j hu c d

end
end RectangleCLTArxivV1
