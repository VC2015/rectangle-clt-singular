import RectangleCLT.GaussianMaximum
import RectangleCLT.GaussianFaces
import RectangleCLT.GaussianCurvature
import RectangleCLT.GaussianDeterminant
import RectangleCLT.TranslationTaylor
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Pi

/-! Gaussian density and injective changes of variables for the convex
potential normal map. Bounds concern the actual product Gaussian law. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal

namespace RectangleCLT

/-- Lebesgue density of the concrete finite product of standard Gaussians. -/
noncomputable def standardGaussianDensity (p : ℕ) (x : Vector p) : ℝ :=
  ∏ j, gaussianPDFReal 0 1 (x j)

theorem standardGaussianDensity_pos (p : ℕ) (x : Vector p) :
    0 < standardGaussianDensity p x :=
  Finset.prod_pos (fun j _ => gaussianPDFReal_pos 0 1 (x j) (by simp))

theorem standardGaussianDensity_measurable (p : ℕ) :
    Measurable (standardGaussianDensity p) :=
  Finset.measurable_prod _ (fun j _ => (measurable_gaussianPDFReal 0 1).comp
    (measurable_pi_apply j))

theorem standardGaussianDensity_integrable (p : ℕ) :
    Integrable (standardGaussianDensity p) :=
  Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 1)

theorem standardGaussianDensity_integral (p : ℕ) :
    (∫ x : Vector p, standardGaussianDensity p x) = 1 := by
  unfold standardGaussianDensity
  rw [integral_fintype_prod_eq_prod]
  simp only [integral_gaussianPDFReal_eq_one 0 (by simp : (1 : NNReal) ≠ 0),
    Finset.prod_const_one]

theorem standardGaussianDensity_setIntegral (p : ℕ) (S : Fin p → Set ℝ)
    (hS : ∀ j, MeasurableSet (S j)) :
    (∫ x in Set.pi Set.univ S, standardGaussianDensity p x) =
      ∏ j, ∫ t in S j, gaussianPDFReal 0 1 t := by
  classical
  have hpi : MeasurableSet (Set.pi Set.univ S) := MeasurableSet.univ_pi hS
  rw [← integral_indicator hpi]
  have hfun : (Set.pi Set.univ S).indicator (standardGaussianDensity p) =
      (fun x : Vector p => ∏ j, (S j).indicator (gaussianPDFReal 0 1) (x j)) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ S
    · rw [Set.indicator_of_mem hx]
      apply Finset.prod_congr rfl
      intro j _
      rw [Set.indicator_of_mem (hx j (Set.mem_univ j))]
    · rw [Set.indicator_of_not_mem hx]
      obtain ⟨j, hj⟩ : ∃ j, x j ∉ S j := by simpa only [Set.mem_pi, Set.mem_univ,
        true_implies, not_forall] using hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_not_mem hj _)
  rw [hfun, integral_fintype_prod_eq_prod]
  simp only [integral_indicator (hS _)]

/-- Identification with the concrete product law, proved on all measurable
coordinate rectangles. No abstract Gaussian-density predicate is used. -/
theorem standardGaussian_eq_withDensity (p : ℕ) :
    standardGaussian p = volume.withDensity
      (fun x : Vector p => ENNReal.ofReal (standardGaussianDensity p x)) := by
  apply Measure.pi_eq
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS),
    ← ofReal_integral_eq_lintegral_ofReal (standardGaussianDensity_integrable p).restrict
      (ae_of_all _ (fun x => (standardGaussianDensity_pos p x).le)),
    standardGaussianDensity_setIntegral p S hS,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => integral_nonneg
      (fun t => gaussianPDFReal_nonneg 0 1 t))]
  exact Finset.prod_congr rfl (fun j _ =>
    (gaussianReal_apply_eq_integral 0 (by simp : (1 : NNReal) ≠ 0) (S j)).symm)

theorem standardGaussian_integral_density_mul {p : ℕ} (g : Vector p → ℝ) :
    (∫ x, g x ∂standardGaussian p) =
      ∫ x : Vector p, standardGaussianDensity p x * g x := by
  rw [standardGaussian_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      (standardGaussianDensity_measurable p).ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (standardGaussianDensity_pos p _).le, smul_eq_mul]

theorem standardGaussian_integrable_density_mul_iff {p : ℕ} (g : Vector p → ℝ) :
    Integrable g (standardGaussian p) ↔
      Integrable (fun x : Vector p => standardGaussianDensity p x * g x) := by
  rw [standardGaussian_eq_withDensity,
    integrable_withDensity_iff_integrable_smul'
      (standardGaussianDensity_measurable p).ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (standardGaussianDensity_pos p _).le, smul_eq_mul]

/-- Gaussian weighted change of variables for a genuinely differentiable,
injective map. The pointwise density comparison is explicit. Integrability of
the weighted Jacobian is part of the conclusion. -/
theorem standardGaussian_weighted_jacobian_le {p : ℕ}
    {T : Vector p → Vector p} {DT : Vector p → Vector p →L[ℝ] Vector p}
    (hT : ∀ x, HasFDerivAt T (DT x) x) (hinj : Function.Injective T)
    (hDT : Measurable DT) {W G : Vector p → ℝ}
    (hW : Measurable W) (hW₀ : ∀ x, 0 ≤ W x) (hG₀ : ∀ x, 0 ≤ G x)
    (hGi : Integrable G (standardGaussian p))
    (hbound : ∀ x, standardGaussianDensity p x * W x ≤
      standardGaussianDensity p (T x) * G (T x)) :
    Integrable (fun x => |(DT x).det| * W x) (standardGaussian p) ∧
      (∫ x, |(DT x).det| * W x ∂standardGaussian p) ≤
        ∫ x, G x ∂standardGaussian p := by
  let ρ := standardGaussianDensity p
  have hρ : ∀ x, 0 ≤ ρ x := fun x => (standardGaussianDensity_pos p x).le
  have hvol : Integrable (fun x => ρ x * G x) :=
    (standardGaussian_integrable_density_mul_iff G).mp hGi
  have hwithin : ∀ x ∈ (Set.univ : Set (Vector p)), HasFDerivWithinAt T (DT x) Set.univ x :=
    fun x _ => (hT x).hasFDerivWithinAt
  have htrans : Integrable (fun x => |(DT x).det| * (ρ (T x) * G (T x))) := by
    have hh := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      MeasurableSet.univ hwithin hinj.injOn (fun x => ρ x * G x)).mp hvol.integrableOn
    simpa only [IntegrableOn, Measure.restrict_univ, smul_eq_mul] using hh
  have hJ : Measurable (fun x => |(DT x).det|) :=
    (ContinuousLinearMap.continuous_det.measurable.comp hDT).abs
  have hsource : Integrable (fun x => ρ x * (|(DT x).det| * W x)) := by
    apply htrans.mono'
      ((standardGaussianDensity_measurable p).mul (hJ.mul hW)).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ x)
        (mul_nonneg (abs_nonneg _) (hW₀ x)))]
      calc
        _ = |(DT x).det| * (ρ x * W x) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _)
  refine ⟨(standardGaussian_integrable_density_mul_iff _).mpr hsource, ?_⟩
  rw [standardGaussian_integral_density_mul, standardGaussian_integral_density_mul]
  calc
    _ ≤ ∫ x : Vector p, |(DT x).det| * (ρ (T x) * G (T x)) :=
      integral_mono hsource htrans (fun x => by
        calc
          _ = |(DT x).det| * (ρ x * W x) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _))
    _ = ∫ x in T '' Set.univ, ρ x * G x := by
      symm
      simpa only [Measure.restrict_univ, smul_eq_mul] using
        integral_image_eq_integral_abs_det_fderiv_smul volume
          MeasurableSet.univ hwithin hinj.injOn (fun x => ρ x * G x)
    _ ≤ _ := setIntegral_le_integral hvol (ae_of_all _ fun x => mul_nonneg (hρ x) (hG₀ x))

/-- In particular, the true Gaussian density ratio times the Jacobian has
integral at most one, with no surjectivity requirement. -/
theorem standardGaussian_jacobian_density_ratio_le {p : ℕ}
    {T : Vector p → Vector p} {DT : Vector p → Vector p →L[ℝ] Vector p}
    (hT : ∀ x, HasFDerivAt T (DT x) x) (hinj : Function.Injective T)
    (hDT : Measurable DT) :
    Integrable (fun x => |(DT x).det| *
      (standardGaussianDensity p (T x) / standardGaussianDensity p x)) (standardGaussian p) ∧
    (∫ x, |(DT x).det| *
      (standardGaussianDensity p (T x) / standardGaussianDensity p x)
        ∂standardGaussian p) ≤ 1 := by
  have hTm : Measurable T := (continuous_iff_continuousAt.mpr
    (fun x => (hT x).continuousAt)).measurable
  have hρm := standardGaussianDensity_measurable p
  have hh := standardGaussian_weighted_jacobian_le hT hinj hDT
    ((hρm.comp hTm).div hρm)
    (fun x => div_nonneg (standardGaussianDensity_pos p (T x)).le
      (standardGaussianDensity_pos p x).le)
    (fun _ => by norm_num : ∀ _x : Vector p, (0 : ℝ) ≤ 1)
    (integrable_const (1 : ℝ)) (fun x => by
      rw [mul_div_cancel₀ _ (ne_of_gt (standardGaussianDensity_pos p x)), mul_one]
      exact le_rfl)
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hh

/-- Exponential-moment interpolation with the exponent shifted by its known
upper bound. This gives the dimension-free finite-maximum envelope below. -/
theorem integral_exp_scale_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {a c : ℝ}
    (hf : Measurable f) (hfi : Integrable (fun x => Real.exp (f x)) μ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hc : (∫ x, Real.exp (f x) ∂μ) ≤ Real.exp c) :
    Integrable (fun x => Real.exp (a * f x)) μ ∧
      (∫ x, Real.exp (a * f x) ∂μ) ≤ Real.exp (a * c) := by
  have hpoint (x : Ω) : Real.exp (a * f x) ≤ Real.exp (a * c) *
      ((1 - a) + (a * Real.exp (-c)) * Real.exp (f x)) := by
    have hh := convexOn_exp.2 (Set.mem_univ (f x - c)) (Set.mem_univ (0 : ℝ))
      ha (sub_nonneg.mpr ha1) (by ring : a + (1 - a) = 1)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hh
    calc
      _ = Real.exp (a * c) * Real.exp (a * (f x - c)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (a * c) * (a * Real.exp (f x - c) + (1 - a)) :=
        mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
      _ = _ := by rw [Real.exp_sub, Real.exp_neg]; ring
  have hright : Integrable (fun x => Real.exp (a * c) *
      ((1 - a) + (a * Real.exp (-c)) * Real.exp (f x))) μ :=
    ((integrable_const (1 - a)).add (hfi.const_mul _)).const_mul _
  have hlow : Integrable (fun x => Real.exp (a * f x)) μ := by
    apply hright.mono' (hf.const_mul a).exp.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hpoint x
  refine ⟨hlow, ?_⟩
  calc
    _ ≤ ∫ x, Real.exp (a * c) *
        ((1 - a) + (a * Real.exp (-c)) * Real.exp (f x)) ∂μ := integral_mono hlow hright hpoint
    _ = Real.exp (a * c) * ((1 - a) + (a * Real.exp (-c)) *
        (∫ x, Real.exp (f x) ∂μ)) := by
      rw [integral_const_mul,
        integral_add (integrable_const (1 - a)) (hfi.const_mul (a * Real.exp (-c)))]
      simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul]
    _ ≤ Real.exp (a * c) * ((1 - a) + (a * Real.exp (-c)) * Real.exp c) :=
      mul_le_mul_of_nonneg_left
        (add_le_add_left (mul_le_mul_of_nonneg_left hc (mul_nonneg ha (Real.exp_nonneg _))) _)
        (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc a, ← Real.exp_add, neg_add_cancel, Real.exp_zero]; ring

/-- A dimension-free exponential moment of the standardized finite maximum.
This is an estimate for the actual concrete Gaussian law. -/
theorem gaussianLaw_integral_exp_norm_scaled_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (b : ℝ) :
    (∫ x : Vector p, Real.exp ((b / Real.sqrt (dimensionLog p)) * ‖x‖)
      ∂gaussianLaw A) ≤ Real.exp (1 + b ^ 2 / 2) := by
  let L := dimensionLog p
  let s := Real.sqrt L
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hLpos : 0 < L := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr hLpos
  have hs2 : s ^ 2 = L := Real.sq_sqrt hLpos.le
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hcard : 2 * (p : ℝ) ≤ Real.exp L := by
    rw [show L = Real.log (Real.exp 1 * (p : ℝ)) from rfl,
      Real.exp_log (mul_pos (Real.exp_pos _) hpR)]
    exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (1 : ℝ)]) hpR.le
  have hhigh : (∫ x : Vector p, Real.exp ((b * s) * ‖x‖) ∂gaussianLaw A) ≤
      Real.exp ((1 + b ^ 2 / 2) * L) := by
    calc
      _ ≤ (2 * (p : ℝ)) * Real.exp ((b * s) ^ 2 / 2) :=
        gaussianLaw_integral_exp_norm_le hp A hdiag (b * s)
      _ ≤ Real.exp L * Real.exp ((b * s) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; nlinarith [hs2]
  have hh := (integral_exp_scale_le
    (measurable_norm.const_mul (b * s)) (gaussianLaw_integrable_exp_norm hp A (b * s))
    (inv_nonneg.mpr hLpos.le) ((inv_le_one₀ hLpos).mpr hL) hhigh).2
  have hcoeff : L⁻¹ * (b * s) = b / s := by
    field_simp [ne_of_gt hLpos, ne_of_gt hs]
    nlinarith only [congrArg (fun u : ℝ => b * u) hs2]
  have hexponent : L⁻¹ * ((1 + b ^ 2 / 2) * L) = 1 + b ^ 2 / 2 := by
    field_simp
  simpa only [← mul_assoc, hcoeff, hexponent] using hh

theorem standardGaussianDensity_eq_kernel {p : ℕ} (x : Vector p) :
    standardGaussianDensity p x =
      ((Real.sqrt (2 * Real.pi))⁻¹) ^ p * gaussianKernel x := by
  unfold standardGaussianDensity gaussianKernel vectorNormSq
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  congr 2
  simp only [Finset.sum_div, ← Finset.sum_neg_distrib]

theorem standardGaussianDensity_translate {p : ℕ} (x d : Vector p) :
    standardGaussianDensity p (x + d) = standardGaussianDensity p x *
      Real.exp (-faceDot d x - vectorNormSq d / 2) := by
  rw [standardGaussianDensity_eq_kernel, standardGaussianDensity_eq_kernel,
    gaussianKernel_translate]
  ring

/-- The gradient of the actual potential pulled back through a Gaussian
matrix factor, expressed in the ambient standard Gaussian coordinates. -/
noncomputable def normalGradient {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r z : Vector p) : Vector p :=
  A.transpose.mulVec (s.v (A.mulVec z + r))

/-- The convex potential's normal map. -/
noncomputable def normalMap {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (ε : ℝ) (z : Vector p) : Vector p :=
  z + ε • normalGradient s A r z

theorem faceDot_transpose_mulVec {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (x y : Vector p) : faceDot (A.transpose.mulVec x) y = faceDot x (A.mulVec y) := by
  simp only [faceDot, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem normalGradient_dot_le_norm {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r z y : Vector p) :
    faceDot (normalGradient s A r z) y ≤ ‖A.mulVec y‖ := by
  rw [normalGradient, faceDot_transpose_mulVec]
  have hh := (s.weights (A.mulVec z + r)).abs_directionalMean_le_norm (A.mulVec y)
  rw [FaceWeights.directionalMean_eq] at hh
  exact (le_abs_self _).trans hh

theorem contDiff_mulVec {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    ContDiff ℝ ⊤ A.mulVec := by
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ ⊤ (fun z : Vector p => ∑ i, A j i * z i)
  exact ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i))

theorem contDiff_normalGradient {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) :
    ContDiff ℝ ⊤ (normalGradient s A r) := by
  have hv : ContDiff ℝ ⊤ (fun x : Vector p => s.v x) :=
    contDiff_pi.mpr (fun j => s.contDiff_v_translation j)
  exact (contDiff_mulVec A.transpose).comp
    (hv.comp ((contDiff_mulVec A).add contDiff_const))

theorem contDiff_normalMap {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (ε : ℝ) :
    ContDiff ℝ ⊤ (normalMap s A r ε) :=
  contDiff_id.add (contDiff_const.smul (contDiff_normalGradient s A r))

/-- Monotonicity of the actual pulled-back potential gradient follows from
its nonnegative directional second derivatives. -/
theorem normalGradient_monotone {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r z w : Vector p) :
    0 ≤ faceDot (normalGradient s A r z - normalGradient s A r w) (z - w) := by
  let y := A.mulVec (z - w)
  let x := A.mulVec w + r
  have hm : Monotone (fun t => (s.weights (FaceSmoother.line x y t)).directionalMean y) :=
    monotone_of_hasDerivAt_nonneg (s.hasDerivAt_directionalMean_line x y)
      (fun t => div_nonneg ((s.weights _).directionalCovariance_nonneg y) s.bandwidth_pos.le)
  have h01 := hm (by norm_num : (0 : ℝ) ≤ 1)
  change (s.weights (FaceSmoother.line x y 0)).directionalMean y ≤
    (s.weights (FaceSmoother.line x y 1)).directionalMean y at h01
  have hzero : FaceSmoother.line x y 0 = A.mulVec w + r := FaceSmoother.line_zero _ _
  have hone : FaceSmoother.line x y 1 = A.mulVec z + r := by
    ext j
    simp only [FaceSmoother.line, one_mul, x, y, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply]
    ring
  rw [hzero, hone, FaceWeights.directionalMean_eq, FaceWeights.directionalMean_eq] at h01
  have hd : faceDot (normalGradient s A r z - normalGradient s A r w) (z - w) =
      (∑ j, s.v (A.mulVec z + r) j * y j) - ∑ j, s.v (A.mulVec w + r) j * y j := by
    rw [show normalGradient s A r z - normalGradient s A r w =
      A.transpose.mulVec (s.v (A.mulVec z + r) - s.v (A.mulVec w + r)) from
        (Matrix.mulVec_sub A.transpose _ _).symm, faceDot_transpose_mulVec]
    simp only [faceDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, y]
  rw [hd]
  exact sub_nonneg.mpr h01

theorem normalMap_injective {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) {ε : ℝ} (hε : 0 ≤ ε) :
    Function.Injective (normalMap s A r ε) := by
  classical
  intro z w heq
  have hmono := normalGradient_monotone s A r z w
  have hsum : vectorNormSq (z - w) +
      ε * faceDot (normalGradient s A r z - normalGradient s A r w) (z - w) = 0 := by
    have hcoord (j : Fin p) := congrFun heq j
    unfold vectorNormSq faceDot
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    have hj := hcoord j
    change z j + ε * normalGradient s A r z j = w j + ε * normalGradient s A r w j at hj
    simp only [Pi.sub_apply]
    have hm := congrArg (fun a : ℝ => a * (z j - w j)) hj
    dsimp only at hm
    linear_combination hm
  have hzero : vectorNormSq (z - w) = 0 := by
    nlinarith [vectorNormSq_nonneg (z - w), mul_nonneg hε hmono]
  exact sub_eq_zero.mp (by
    by_contra hne
    exact (ne_of_gt (vectorNormSq_pos hne)) hzero)

/-- The Gaussian density comparison uses the finite maximum of row-normal
projections at the image point, with no dimension-dependent Euclidean norm. -/
theorem normalMap_density_le {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) {ε : ℝ} (hε : 0 ≤ ε)
    (z : Vector p) :
    standardGaussianDensity p z ≤ standardGaussianDensity p (normalMap s A r ε z) *
      Real.exp (ε * ‖A.mulVec (normalMap s A r ε z)‖) := by
  let Tz := normalMap s A r ε z
  let d := -ε • normalGradient s A r z
  have hd : Tz + d = z := by
    dsimp [Tz, d, normalMap]
    rw [neg_smul]
    exact add_neg_cancel_right _ _
  have hdot : faceDot d Tz = -ε * faceDot (normalGradient s A r z) Tz := by
    simp only [d, faceDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hexponent : -faceDot d Tz - vectorNormSq d / 2 ≤ ε * ‖A.mulVec Tz‖ := by
    rw [hdot]
    have hh := mul_le_mul_of_nonneg_left (normalGradient_dot_le_norm s A r z Tz) hε
    nlinarith [vectorNormSq_nonneg d]
  calc
    _ = standardGaussianDensity p (Tz + d) := congrArg _ hd.symm
    _ = standardGaussianDensity p Tz * Real.exp (-faceDot d Tz - vectorNormSq d / 2) :=
      standardGaussianDensity_translate Tz d
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
      (standardGaussianDensity_pos p Tz).le

/-- The injective change of variables is applied to the actual smooth normal
map, and its Jacobian is its actual Fréchet derivative. -/
theorem normalMap_integral_abs_det_le_exp_norm {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (r : Vector p) {ε : ℝ} (hε : 0 ≤ ε) :
    Integrable (fun z => |(fderiv ℝ (normalMap s A r ε) z).det|) (standardGaussian p) ∧
      (∫ z, |(fderiv ℝ (normalMap s A r ε) z).det| ∂standardGaussian p) ≤
        ∫ x : Vector p, Real.exp (ε * ‖x‖) ∂gaussianLaw A := by
  have hdiff := (contDiff_normalMap s A r ε).differentiable (by simp)
  have hG : Integrable (fun z : Vector p => Real.exp (ε * ‖A.mulVec z‖))
      (standardGaussian p) := by
    exact (integrable_map_measure (measurable_norm.const_mul ε).exp.aestronglyMeasurable
      (measurable_mulVec A).aemeasurable).mp (gaussianLaw_integrable_exp_norm hp A ε)
  have hh := standardGaussian_weighted_jacobian_le (fun z => (hdiff z).hasFDerivAt)
    (normalMap_injective s A r hε)
    ((contDiff_normalMap s A r ε).continuous_fderiv (by simp)).measurable
    (measurable_const : Measurable (fun _z : Vector p => (1 : ℝ)))
    (fun _ => zero_le_one) (fun _ => Real.exp_nonneg _) hG
    (fun z => by simpa only [mul_one] using normalMap_density_le s A r hε z)
  have hmap : (∫ z : Vector p, Real.exp (ε * ‖A.mulVec z‖) ∂standardGaussian p) =
      ∫ x : Vector p, Real.exp (ε * ‖x‖) ∂gaussianLaw A := by
    symm
    exact integral_map (measurable_mulVec A).aemeasurable
      (measurable_norm.const_mul ε).exp.aestronglyMeasurable
  simpa only [mul_one, hmap] using hh

/-- A dimension-free Gaussian Jacobian bound at the normal-map scale.
Every analytic hypothesis on the map has been discharged for the actual
rectangle potential. The matrix factor may be singular. -/
theorem normalMap_integral_abs_det_le {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (r : Vector p)
    {b : ℝ} (hb : 0 ≤ b) :
    (∫ z, |(fderiv ℝ
      (normalMap s A r (b / Real.sqrt (dimensionLog p))) z).det|
        ∂standardGaussian p) ≤ Real.exp (1 + b ^ 2 / 2) :=
  (normalMap_integral_abs_det_le_exp_norm hp s A r (div_nonneg hb (Real.sqrt_nonneg _))).2.trans
    (gaussianLaw_integral_exp_norm_scaled_le hp A hdiag b)

/-- The concrete pulled-back potential Hessian. -/
noncomputable def normalHessian {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r z : Vector p) : Matrix (Fin p) (Fin p) ℝ :=
  A.transpose * s.potentialCoordinateHessian (A.mulVec z + r) * A

theorem normalGradient_fderiv_apply {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r z y : Vector p) :
    fderiv ℝ (normalGradient s A r) z y = (normalHessian s A r z).mulVec y := by
  have hline : HasDerivAt (fun t : ℝ => z + t • y) y 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add z
  have hdiff : Differentiable ℝ (normalGradient s A r) :=
    (contDiff_normalGradient s A r).differentiable (by simp)
  have hactual : HasDerivAt (fun t : ℝ => normalGradient s A r (z + t • y))
      (fderiv ℝ (normalGradient s A r) z y) 0 := by
    have hh := (hdiff (z + (0 : ℝ) • y)).hasFDerivAt.comp_hasDerivAt 0 hline
    simpa only [zero_smul, add_zero] using hh
  have hd (j : Fin p) : HasDerivAt
      (fun t : ℝ => s.v (A.mulVec (z + t • y) + r) j)
      (∑ k, (A.mulVec y) k * s.potentialCoordinateHessian (A.mulVec z + r) j k) 0 := by
    convert s.hasDerivAt_v_line_hessian (A.mulVec z + r) (A.mulVec y) j using 1
    funext t
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    congr 1
    exact add_right_comm _ _ _
  have hsum : HasDerivAt (fun t : ℝ => normalGradient s A r (z + t • y))
      ((normalHessian s A r z).mulVec y) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have hh := HasDerivAt.sum (u := Finset.univ) (fun j _ => (hd j).const_mul (A j i))
    convert hh using 1
    simp only [normalHessian, ← Matrix.mulVec_mulVec]
    change (∑ j, A j i * (∑ k,
      s.potentialCoordinateHessian (A.mulVec z + r) j k * (A.mulVec y) k)) = _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  exact hactual.unique hsum

theorem normalMap_fderiv_apply {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r z y : Vector p) (ε : ℝ) :
    fderiv ℝ (normalMap s A r ε) z y =
      (1 + ε • normalHessian s A r z).mulVec y := by
  have hh := (hasFDerivAt_id z).add
    (((contDiff_normalGradient s A r).differentiable (by simp) z).hasFDerivAt.const_smul ε)
  have hderiv : fderiv ℝ (normalMap s A r ε) z =
      ContinuousLinearMap.id ℝ (Vector p) + ε • fderiv ℝ (normalGradient s A r) z := hh.fderiv
  rw [hderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, normalGradient_fderiv_apply,
    Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]

/-- The Jacobian determinant is the determinant of the concrete positive
identity-plus-Hessian matrix used in the finite determinant estimates. -/
theorem normalMap_fderiv_det {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r z : Vector p) (ε : ℝ) :
    (fderiv ℝ (normalMap s A r ε) z).det = (1 + ε • normalHessian s A r z).det := by
  classical
  change LinearMap.det ((fderiv ℝ (normalMap s A r ε) z).toLinearMap) = _
  rw [← LinearMap.det_toMatrix']
  congr 1
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix'_apply]
  change fderiv ℝ (normalMap s A r ε) z (fun k => if k = j then 1 else 0) i = _
  rw [normalMap_fderiv_apply]
  simp [Matrix.mulVec, dotProduct]

namespace FaceWeights

theorem covarianceEntry_quadratic {p : ℕ} (w : FaceWeights p) (y : Vector p) :
    dotProduct y (Matrix.mulVec (fun j k => w.covarianceEntry j k) y) =
      w.directionalCovariance y := by
  change (∑ j, y j * ∑ k, w.covarianceEntry j k * y k) = _
  have hrow (j : Fin p) : (∑ k, w.covarianceEntry j k * y k) =
      w.coordinateMass j * y j - w.v j * w.directionalMean y := by
    simpa only [mul_comm] using w.covarianceEntry_mul_sum j y
  simp_rw [hrow]
  have hpoint (j : Fin p) : y j *
      (w.coordinateMass j * y j - w.v j * w.directionalMean y) =
        w.coordinateMass j * y j ^ 2 - (w.v j * y j) * w.directionalMean y := by ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← w.directionalMean_eq]
  simp only [directionalCovariance, w.directionalSecondMoment_eq, coordinateMass]
  ring

theorem covarianceEntry_posSemidef {p : ℕ} (w : FaceWeights p) :
    Matrix.PosSemidef (fun j k => w.covarianceEntry j k) := by
  constructor
  · change Matrix.conjTranspose (fun j k => w.covarianceEntry j k) = _
    ext j k
    simpa only [Matrix.conjTranspose_apply, star_trivial] using w.covarianceEntry_symm k j
  · intro y
    simpa only [star_trivial, w.covarianceEntry_quadratic] using w.directionalCovariance_nonneg y

/-- A unit-diagonal correlation matrix preserves the full null-face times
non-null-face curvature budget, with no inverse pair-gap loss. -/
theorem covarianceContraction_ge_F_theta {p : ℕ} (w : FaceWeights p)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, Q j j = 1)
    (habs : ∀ j k, |Q j k| ≤ 1) :
    w.F * w.theta ≤ w.covarianceContraction Q := by
  have hdiagSum : (∑ j, ∑ k, Q j k * w.diagonalMass j k) = w.theta := by
    simp only [diagonalMass, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, hdiag, one_mul, w.sum_coordinateMass]
  have hquad : (∑ j, ∑ k, Q j k * (w.v j * w.v k)) ≤ (∑ j, |w.v j|) ^ 2 := by
    calc
      _ ≤ ∑ j, ∑ k, |w.v j| * |w.v k| := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        calc
          _ ≤ |Q j k * (w.v j * w.v k)| := le_abs_self _
          _ = |Q j k| * (|w.v j| * |w.v k|) := by simp only [abs_mul]
          _ ≤ _ := by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (habs j k) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]; ring
  have hsquare : (∑ j, |w.v j|) ^ 2 ≤ w.theta ^ 2 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => abs_nonneg _)) w.sum_abs_v_le_theta 2
  unfold covarianceContraction covarianceEntry
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hdiagSum]
  unfold theta at *
  nlinarith

end FaceWeights

theorem rowGram_abs_le_one {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (j k : Fin p) :
    |(A * A.transpose) j k| ≤ 1 := by
  have hrow (i : Fin p) : (∑ r, A i r ^ 2) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hdiag i
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r => A j r) (fun r => A k r)
  rw [hrow, hrow, one_mul] at hcs
  have heq : (A * A.transpose) j k = ∑ r, A j r * A k r := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [heq]
  nlinarith [sq_abs (∑ r, A j r * A k r), abs_nonneg (∑ r, A j r * A k r)]

theorem FaceSmoother.potentialHessian_posSemidef {p : ℕ}
    (s : FaceSmoother p) (x : Vector p) : (s.potentialCoordinateHessian x).PosSemidef := by
  have heq : s.potentialCoordinateHessian x =
      s.bandwidth⁻¹ • (fun j k => (s.weights x).covarianceEntry j k) := by
    ext j k
    change s.potentialCoordinateHessian x j k = s.bandwidth⁻¹ * (s.weights x).covarianceEntry j k
    rw [s.potentialCoordinateHessian_eq]
    ring
  rw [heq]
  exact posSemidef_smul_nonneg (s.weights x).covarianceEntry_posSemidef
    (inv_nonneg.mpr s.bandwidth_pos.le)

theorem normalHessian_posSemidef {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r z : Vector p) :
    (normalHessian s A r z).PosSemidef := by
  simpa only [normalHessian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (s.potentialHessian_posSemidef (A.mulVec z + r)).conjTranspose_mul_mul_same A

/-- The trace of the pulled-back Hessian controls `F(1-F)` directly, without
any local eigenvalue or pair-gap parameter. -/
theorem normalHessian_trace_ge_variance {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (r z : Vector p) :
    s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r)) / s.bandwidth ≤
      Matrix.trace (normalHessian s A r z) := by
  rw [normalHessian, Matrix.trace_mul_cycle, s.potentialCoordinateHessian_contraction]
  exact div_le_div_of_nonneg_right
    ((s.weights (A.mulVec z + r)).covarianceContraction_ge_F_theta (A * A.transpose)
      hdiag (rowGram_abs_le_one A hdiag)) s.bandwidth_pos.le

/-- Direct Gaussian short-cap/envelope bound from the actual convex normal
map. This avoids a Gaussian polyhedral surface-area estimate and has no
pair-gap or full-covariance inverse factor. -/
theorem FaceSmoother.gaussian_expected_variance_le {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (r : Vector p) :
    (∫ x : Vector p, s.F (x + r) * (1 - s.F (x + r)) ∂gaussianLaw A) ≤
      Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p) := by
  let a := Real.sqrt (dimensionLog p)
  let t := 1 / a
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have ht : 0 ≤ t := (div_pos zero_lt_one ha).le
  have hden : 0 < s.bandwidth * a := mul_pos s.bandwidth_pos ha
  have hvarint : Integrable
      (fun z : Vector p => s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r)))
      (standardGaussian p) := by
    have hF : Measurable (fun z : Vector p => s.F (A.mulVec z + r)) :=
      s.continuous_F.measurable.comp ((measurable_mulVec A).add measurable_const)
    apply (integrable_const (1 : ℝ)).mono'
      (hF.mul (measurable_const.sub hF)).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (s.F_pos _).le
        (sub_nonneg.mpr (s.F_le_one _)))]
      exact s.variance_le_one _
  have hJint := (normalMap_integral_abs_det_le_exp_norm hp s A r ht).1
  have hpwise (z : Vector p) :
      s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r)) ≤
        (s.bandwidth * a) * |(fderiv ℝ (normalMap s A r t) z).det| := by
    rw [mul_comm (s.bandwidth * a)]
    apply (div_le_iff₀ hden).mp
    calc
      _ = t * (s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r)) / s.bandwidth) := by
        dsimp [t]
        ring
      _ ≤ t * Matrix.trace (normalHessian s A r z) :=
        mul_le_mul_of_nonneg_left (normalHessian_trace_ge_variance s A hdiag r z) ht
      _ ≤ (1 + t • normalHessian s A r z).det :=
        posSemidef_mul_trace_le_det_one_add (normalHessian_posSemidef s A r z) ht
      _ ≤ _ := by rw [normalMap_fderiv_det]; exact le_abs_self _
  have hmap : (∫ x : Vector p, s.F (x + r) * (1 - s.F (x + r)) ∂gaussianLaw A) =
      ∫ z : Vector p, s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r))
        ∂standardGaussian p := by
    apply integral_map (measurable_mulVec A).aemeasurable
    have hF : Measurable (fun x : Vector p => s.F (x + r)) :=
      s.continuous_F.measurable.comp (measurable_id.add measurable_const)
    exact (hF.mul (measurable_const.sub hF)).aestronglyMeasurable
  rw [hmap]
  calc
    _ ≤ ∫ z : Vector p, (s.bandwidth * a) *
        |(fderiv ℝ (normalMap s A r t) z).det| ∂standardGaussian p :=
      integral_mono hvarint (hJint.const_mul _) hpwise
    _ = (s.bandwidth * a) *
        (∫ z, |(fderiv ℝ (normalMap s A r t) z).det| ∂standardGaussian p) := integral_const_mul _ _
    _ ≤ (s.bandwidth * a) * Real.exp (3 / 2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hden.le
      convert normalMap_integral_abs_det_le hp s A hdiag r (by norm_num : (0 : ℝ) ≤ 1) using 1
      norm_num [t, a]
    _ = _ := by ring

end RectangleCLT
