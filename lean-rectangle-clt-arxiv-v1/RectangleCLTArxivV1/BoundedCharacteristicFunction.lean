import RectangleCLT.GaussianComparisonLaw
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Probability.Independence.Basic

/-! The actual bounded-phase characteristic-function estimate used in G.2. -/
namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

set_option autoImplicit false
noncomputable section

def unitPhase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

@[simp] theorem norm_unitPhase (x : ℝ) : ‖unitPhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

@[simp] theorem re_unitPhase (x : ℝ) : (unitPhase x).re = Real.cos x := by
  simp [unitPhase, Complex.exp_re]

theorem unitPhase_sub (x y : ℝ) : unitPhase (x-y) = unitPhase x * conj (unitPhase y) := by
  unfold unitPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub]
  ring

theorem unitPhase_sum {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    unitPhase (∑ i, x i) = ∏ i, unitPhase (x i) := by
  unfold unitPhase
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Finset.sum_mul]

theorem integrable_unitPhase {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : Measurable X) :
    Integrable (fun ω => unitPhase (X ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · have hm : Measurable (fun ω => unitPhase (X ω)) := by
      unfold unitPhase
      fun_prop
    exact hm.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω => by simp)

/-- Symmetrization is an identity for the actual independent-copy product
measure, before applying any trigonometric bound. -/
theorem norm_integral_unitPhase_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) :
    ‖∫ ω, unitPhase (X ω) ∂μ‖ ^ 2 =
      ∫ z : Ω × Ω, Real.cos (X z.1-X z.2) ∂μ.prod μ := by
  have hd := integrable_unitPhase (μ.prod μ) (fun z : Ω × Ω => X z.1-X z.2)
    ((hX.comp measurable_fst).sub (hX.comp measurable_snd))
  have he : (∫ z : Ω × Ω, unitPhase (X z.1-X z.2) ∂μ.prod μ) =
      (∫ ω, unitPhase (X ω) ∂μ) * conj (∫ ω, unitPhase (X ω) ∂μ) := by
    simp_rw [unitPhase_sub]
    calc
      _ = (∫ ω, unitPhase (X ω) ∂μ) * (∫ ω, conj (unitPhase (X ω)) ∂μ) :=
        integral_prod_mul (fun ω => unitPhase (X ω)) (fun ω => conj (unitPhase (X ω)))
      _ = _ := by rw [integral_conj]
  have hr : (∫ z : Ω × Ω, Real.cos (X z.1-X z.2) ∂μ.prod μ) =
      ((∫ ω, unitPhase (X ω) ∂μ) * conj (∫ ω, unitPhase (X ω) ∂μ)).re := by
    calc
      _ = ∫ z : Ω × Ω, (unitPhase (X z.1-X z.2)).re ∂μ.prod μ := by simp only [re_unitPhase]
      _ = (∫ z : Ω × Ω, unitPhase (X z.1-X z.2) ∂μ.prod μ).re := integral_re hd
      _ = _ := congrArg Complex.re he
  simpa only [re_unitPhase, Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.ofReal_re] using hr.symm

theorem integrable_bounded_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1/2) : Integrable X μ := by
  apply (integrable_const (1/2 : ℝ)).mono' hX.aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using hb

theorem integrable_sq_bounded_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1/2) : Integrable (fun ω => X ω ^ 2) μ := by
  apply (integrable_const ((1/2 : ℝ)^2)).mono' (hX.pow_const 2).aestronglyMeasurable
  filter_upwards [hb] with ω hω
  have hs := (sq_le_sq₀ (abs_nonneg (X ω)) (by norm_num : (0 : ℝ) ≤ 1/2)).mpr hω
  simpa only [Real.norm_eq_abs, sq_abs, abs_of_nonneg (sq_nonneg (X ω))] using hs

theorem integral_independent_copy_contrast_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hi : Integrable X μ) (hi₂ : Integrable (fun ω => X ω ^ 2) μ)
    (hmean : (∫ ω, X ω ∂μ) = 0) :
    (∫ z : Ω × Ω, (X z.1-X z.2)^2 ∂μ.prod μ) = 2 * ∫ ω, X ω^2 ∂μ := by
  have hfst : Integrable (fun z : Ω × Ω => X z.1 ^ 2) (μ.prod μ) := by
    simpa only [mul_one] using hi₂.mul_prod (integrable_const (1 : ℝ))
  have hsnd : Integrable (fun z : Ω × Ω => X z.2 ^ 2) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hi₂
  have hcross := hi.mul_prod hi
  calc
    _ = ∫ z : Ω × Ω, (X z.1^2+X z.2^2)-2*(X z.1*X z.2) ∂μ.prod μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)
    _ = _ := by
      rw [integral_sub (f := fun z : Ω × Ω => X z.1^2+X z.2^2)
          (g := fun z => 2*(X z.1*X z.2)) (hfst.add hsnd) (hcross.const_mul 2),
        integral_add (f := fun z : Ω × Ω => X z.1^2) (g := fun z => X z.2^2) hfst hsnd,
        integral_const_mul, integral_fun_fst (fun ω => X ω^2),
        integral_fun_snd (fun ω => X ω^2), integral_prod_mul X X]
      simp [hmean, two_mul]

/-- The scalar characteristic function has Gaussian decay on the actual
bounded-phase range. The independent-copy identity handles its imaginary part. -/
theorem norm_integral_unitPhase_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hmean : (∫ ω, X ω ∂μ) = 0) (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1/2) :
    ‖∫ ω, unitPhase (X ω) ∂μ‖ ≤
      Real.exp (-(2/Real.pi^2) * (∫ ω, X ω^2 ∂μ)) := by
  have hi := integrable_bounded_half μ X hX hb
  have hi₂ := integrable_sq_bounded_half μ X hX hb
  have hfst : Integrable (fun z : Ω × Ω => X z.1 ^ 2) (μ.prod μ) := by
    simpa only [mul_one] using hi₂.mul_prod (integrable_const (1 : ℝ))
  have hsnd : Integrable (fun z : Ω × Ω => X z.2 ^ 2) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hi₂
  have hdiff : Integrable (fun z : Ω × Ω => (X z.1-X z.2)^2) (μ.prod μ) := by
    convert (hfst.add hsnd).sub ((hi.mul_prod hi).const_mul 2) using 1
    ext z
    dsimp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hcos : Integrable (fun z : Ω × Ω => Real.cos (X z.1-X z.2)) (μ.prod μ) := by
    have hh := (integrable_unitPhase (μ.prod μ) (fun z : Ω × Ω => X z.1-X z.2)
      ((hX.comp measurable_fst).sub (hX.comp measurable_snd))).re
    change Integrable (fun z : Ω × Ω => (unitPhase (X z.1-X z.2)).re) (μ.prod μ) at hh
    simpa only [re_unitPhase] using hh
  have hbpair : ∀ᵐ z : Ω × Ω ∂μ.prod μ, |X z.1| ≤ 1/2 ∧ |X z.2| ≤ 1/2 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_le (hX.comp measurable_fst).abs measurable_const).inter
      (measurableSet_le (hX.comp measurable_snd).abs measurable_const))).mpr
    filter_upwards [hb] with x hx
    exact hb.mono (fun y hy => ⟨hx, hy⟩)
  have hpoint : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      Real.cos (X z.1-X z.2) ≤ 1 - (2/Real.pi^2)*(X z.1-X z.2)^2 := by
    filter_upwards [hbpair] with z hz
    have habs : |X z.1-X z.2| ≤ 1 := by
      have ht := abs_sub (X z.1) (X z.2)
      linarith [hz.1, hz.2]
    exact Real.cos_le_one_sub_mul_cos_sq (habs.trans (by linarith [Real.two_le_pi]))
  have hineq := integral_mono_ae hcos
    ((integrable_const (1 : ℝ)).sub (hdiff.const_mul (2/Real.pi^2))) hpoint
  have hid : (∫ z : Ω × Ω, 1-(2/Real.pi^2)*(X z.1-X z.2)^2 ∂μ.prod μ) =
      1-(2/Real.pi^2)*(2*(∫ ω, X ω^2 ∂μ)) := by
    calc
      _ = (∫ _ : Ω × Ω, (1 : ℝ) ∂μ.prod μ) -
          ∫ z : Ω × Ω, (2/Real.pi^2)*(X z.1-X z.2)^2 ∂μ.prod μ :=
        integral_sub (f := fun _ : Ω × Ω => (1 : ℝ))
          (g := fun z => (2/Real.pi^2)*(X z.1-X z.2)^2)
          (integrable_const (1 : ℝ)) (hdiff.const_mul (2/Real.pi^2))
      _ = _ := by
        rw [integral_const_mul, integral_independent_copy_contrast_sq μ X hi hi₂ hmean]
        simp
  have hbound : (∫ z : Ω × Ω, Real.cos (X z.1-X z.2) ∂μ.prod μ) ≤
      1-(2/Real.pi^2)*(2*(∫ ω, X ω^2 ∂μ)) := hineq.trans_eq hid
  have hsq : ‖∫ ω, unitPhase (X ω) ∂μ‖ ^ 2 ≤
      (Real.exp (-(2/Real.pi^2)*(∫ ω, X ω^2 ∂μ))) ^ 2 := by
    rw [norm_integral_unitPhase_sq μ X hX]
    calc
      _ ≤ 1-(2/Real.pi^2)*(2*(∫ ω, X ω^2 ∂μ)) := hbound
      _ ≤ Real.exp (-(4/Real.pi^2)*(∫ ω, X ω^2 ∂μ)) := by
        have he := Real.add_one_le_exp (-(4/Real.pi^2)*(∫ ω, X ω^2 ∂μ))
        convert he using 1 <;> ring
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp hsq

/-- Independence is applied to the actual joint pushforward law, so the
complex-valued product integral requires no additional factorization premise. -/
theorem integral_unitPhase_sum_eq_prod {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) :
    (∫ ω, unitPhase (∑ i, X i ω) ∂μ) = ∏ i, ∫ ω, unitPhase (X i ω) ∂μ := by
  let ν : Fin n → Measure ℝ := fun i => μ.map (X i)
  have hνprob (i : Fin n) : IsProbabilityMeasure (ν i) :=
    isProbabilityMeasure_map (hX i).aemeasurable
  have hpi : (∫ y : Fin n → ℝ, ∏ i, unitPhase (y i) ∂Measure.pi ν) =
      ∏ i, ∫ x : ℝ, unitPhase x ∂ν i := by
    exact @integral_fintype_prod_eq_prod ℂ inferInstance (Fin n) inferInstance
      (fun _ => ℝ) (fun _ x => unitPhase x) (fun i => ⟨ν i⟩)
      (fun i => by
        change SigmaFinite (ν i)
        letI := hνprob i
        infer_instance)
  have hj : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ hX
  have hF : Measurable (fun y : Fin n → ℝ => ∏ i, unitPhase (y i)) := by
    apply Finset.measurable_prod
    intro i _
    unfold unitPhase
    fun_prop
  have hlaw := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mp hind
  calc
    _ = ∫ ω, ∏ i, unitPhase (X i ω) ∂μ := by simp_rw [unitPhase_sum]
    _ = ∫ y : Fin n → ℝ, ∏ i, unitPhase (y i) ∂μ.map (fun ω i => X i ω) :=
      (integral_map hj.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∏ i, ∫ x : ℝ, unitPhase x ∂ν i := by rw [hlaw]; exact hpi
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      have hm : Measurable unitPhase := by unfold unitPhase; fun_prop
      exact integral_map (hX i).aemeasurable hm.aestronglyMeasurable

theorem norm_integral_unitPhase_sum_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1/2) :
    ‖∫ ω, unitPhase (∑ i, X i ω) ∂μ‖ ≤
      Real.exp (-(2/Real.pi^2)*(∑ i, ∫ ω, X i ω^2 ∂μ)) := by
  rw [integral_unitPhase_sum_eq_prod μ X hX hind, norm_prod]
  calc
    _ ≤ ∏ i, Real.exp (-(2/Real.pi^2)*(∫ ω, X i ω^2 ∂μ)) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _)
        (fun i _ => norm_integral_unitPhase_le μ (X i) (hX i) (hmean i) (hb i))
    _ = _ := by
      rw [← Real.exp_sum, Finset.mul_sum]

/-- The independent Gaussian phase has its exact variance exponent, also
for rectangular or singular coefficient matrices. -/
theorem norm_integral_unitPhase_gaussian_linear {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (w : Fin p → ℝ) :
    ‖∫ g, unitPhase (dotProduct w (A.mulVec g)) ∂RectangleCLT.standardGaussian r‖ =
      Real.exp (-(∑ j, (A.transpose.mulVec w j)^2)/2) := by
  have hdot (g : Fin r → ℝ) : dotProduct w (A.mulVec g) =
      dotProduct g (A.transpose.mulVec w) := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]
  simp_rw [hdot]
  change ‖RectangleCLT.vectorFourier (RectangleCLT.standardGaussian r) (A.transpose.mulVec w)‖ = _
  rw [RectangleCLT.vectorFourier_standardGaussian, Complex.norm_exp]
  congr 1
  simp
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]

theorem two_div_pi_sq_le_half : (2 : ℝ)/Real.pi^2 ≤ 1/2 := by
  apply (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
  nlinarith [Real.two_le_pi]

theorem norm_integral_unitPhase_gaussian_linear_le {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (w : Fin p → ℝ) :
    ‖∫ g, unitPhase (dotProduct w (A.mulVec g)) ∂RectangleCLT.standardGaussian r‖ ≤
      Real.exp (-(2/Real.pi^2)*(∑ j, (A.transpose.mulVec w j)^2)) := by
  rw [norm_integral_unitPhase_gaussian_linear]
  apply Real.exp_le_exp.mpr
  have hs : 0 ≤ ∑ j, (A.transpose.mulVec w j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_right two_div_pi_sq_le_half hs
  linarith

end
end RectangleCLTArxivV1
