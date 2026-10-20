import RectangleCLTCompanion.SignedSurfaceKernel
import RectangleCLTCompanion.SelectorMatrixReduction
import Mathlib.Data.Nat.Choose.Sum

/-! Finite binomial reduction of the actual signed selector score.  All
Gaussian integral interchanges below follow from bounded weights and actual
Gaussian second moments; no quantitative trace estimate is assumed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

set_option maxRecDepth 2048

variable {p r : ℕ}

def gaussianPowerTrace (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (v : Vector p) (a : ℕ) : ℝ :=
  ∫ g, (vectorNormSq g - (r : ℝ)) *
    (s.F (A.mulVec g + v) ^ (a + 1) * s.theta (A.mulVec g + v)) ∂standardGaussian r

def gaussianSelectorTrace (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (v : Vector p) (k : ℕ) : ℝ :=
  ∫ g, (vectorNormSq g - (r : ℝ)) *
    (s.F (A.mulVec g + v) * s.theta (A.mulVec g + v) ^ k) ∂standardGaussian r

theorem continuous_smoother_theta (s : FaceSmoother p) : Continuous s.theta := by
  change Continuous (fun x => 1 - s.F x)
  exact continuous_const.sub s.continuous_F

theorem smoother_power_weight_bounds (s : FaceSmoother p) (a : ℕ) (x : Vector p) :
    0 ≤ s.F x ^ (a + 1) * s.theta x ∧ s.F x ^ (a + 1) * s.theta x ≤ 1 := by
  have hθ0 : 0 ≤ s.theta x := (s.weights x).theta_nonneg
  have hθ1 : s.theta x ≤ 1 := (s.weights x).theta_lt_one.le
  constructor
  · exact mul_nonneg (pow_nonneg (s.F_pos x).le _) hθ0
  · exact (mul_le_mul (pow_le_one₀ (s.F_pos x).le (s.F_le_one x)) hθ1 hθ0 zero_le_one).trans_eq
      (one_mul _)

theorem smoother_selector_weight_bounds (s : FaceSmoother p) (k : ℕ) (x : Vector p) :
    0 ≤ s.F x * s.theta x ^ k ∧ s.F x * s.theta x ^ k ≤ 1 := by
  have hθ0 : 0 ≤ s.theta x := (s.weights x).theta_nonneg
  have hθ1 : s.theta x ≤ 1 := (s.weights x).theta_lt_one.le
  constructor
  · exact mul_nonneg (s.F_pos x).le (pow_nonneg hθ0 _)
  · exact (mul_le_mul (s.F_le_one x) (pow_le_one₀ hθ0 hθ1) (pow_nonneg hθ0 _)
      zero_le_one).trans_eq (one_mul _)

theorem integrable_gaussian_score_weight (w : Vector p → ℝ) (hw : Continuous w)
    (hb : ∀ x, |w x| ≤ 1) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    Integrable (fun g => (vectorNormSq g - (r : ℝ)) * w (A.mulVec g + v))
      (standardGaussian r) := by
  apply integrable_gaussian_bounded_mul (hw.comp (by fun_prop))
    ⟨1, fun g => by simpa only [Real.norm_eq_abs] using hb (A.mulVec g + v)⟩
  exact (standardGaussian_integrable_vectorNormSq r).sub (integrable_const _)

theorem integrable_gaussian_power_trace (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (a : ℕ) :
    Integrable (fun g => (vectorNormSq g - (r : ℝ)) *
      (s.F (A.mulVec g + v) ^ (a + 1) * s.theta (A.mulVec g + v))) (standardGaussian r) := by
  apply integrable_gaussian_score_weight _
    ((s.continuous_F.pow _).mul (continuous_smoother_theta s)) _ A v
  intro x
  rw [abs_of_nonneg (smoother_power_weight_bounds s a x).1]
  exact (smoother_power_weight_bounds s a x).2

theorem integrable_gaussian_selector_trace (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (k : ℕ) :
    Integrable (fun g => (vectorNormSq g - (r : ℝ)) *
      (s.F (A.mulVec g + v) * s.theta (A.mulVec g + v) ^ k)) (standardGaussian r) := by
  apply integrable_gaussian_score_weight _
    (s.continuous_F.mul ((continuous_smoother_theta s).pow _)) _ A v
  intro x
  rw [abs_of_nonneg (smoother_selector_weight_bounds s k x).1]
  exact (smoother_selector_weight_bounds s k x).2

/-- Pointwise binomial identity, with no Gaussian or covariance hypothesis. -/
theorem selector_weight_binomial_succ (s : FaceSmoother p) (x : Vector p) (n : ℕ) :
    s.F x * s.theta x ^ (n + 1) =
      ∑ a ∈ Finset.range (n + 1), (-1 : ℝ) ^ a * (n.choose a : ℝ) *
        (s.F x ^ (a + 1) * s.theta x) := by
  have hbin : s.theta x ^ n = ∑ a ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ a * s.F x ^ a * (n.choose a : ℝ) := by
    calc
      _ = (-s.F x + 1) ^ n := by
        congr 1
        change 1 - s.F x = -s.F x + 1
        ring
      _ = _ := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro a _
        rw [one_pow, mul_one, neg_pow]
  calc
    _ = (s.F x * s.theta x) * s.theta x ^ n := by rw [pow_succ]; ring
    _ = (s.F x * s.theta x) * ∑ a ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ a * s.F x ^ a * (n.choose a : ℝ) := by rw [hbin]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [pow_succ]
      ring

theorem gaussianSelectorTrace_binomial_succ (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (n : ℕ) :
    gaussianSelectorTrace s A v (n + 1) =
      ∑ a ∈ Finset.range (n + 1), (-1 : ℝ) ^ a * (n.choose a : ℝ) *
        gaussianPowerTrace s A v a := by
  unfold gaussianSelectorTrace gaussianPowerTrace
  simp_rw [selector_weight_binomial_succ, Finset.mul_sum]
  rw [integral_finset_sum (Finset.range (n + 1)) (fun a _ => by
    simpa only [mul_assoc, mul_left_comm] using
      (integrable_gaussian_power_trace s A v a).const_mul ((-1 : ℝ) ^ a * (n.choose a : ℝ)))]
  apply Finset.sum_congr rfl
  intro a _
  have heq (g : Vector r) :
      (vectorNormSq g - (r : ℝ)) * ((-1 : ℝ) ^ a * (n.choose a : ℝ) *
        (s.F (A.mulVec g + v) ^ (a + 1) * s.theta (A.mulVec g + v))) =
      ((-1 : ℝ) ^ a * (n.choose a : ℝ)) * ((vectorNormSq g - (r : ℝ)) *
        (s.F (A.mulVec g + v) ^ (a + 1) * s.theta (A.mulVec g + v))) := by ring
  simp_rw [heq]
  rw [integral_const_mul]

theorem gaussianSelectorTrace_binomial (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) {k : ℕ} (hk : 1 ≤ k) :
    gaussianSelectorTrace s A v k =
      ∑ a ∈ Finset.range k, (-1 : ℝ) ^ a * ((k - 1).choose a : ℝ) *
        gaussianPowerTrace s A v a := by
  have hh := gaussianSelectorTrace_binomial_succ s A v (k - 1)
  simpa only [Nat.sub_add_cancel hk] using hh

/-- Scalar assembly of quantitative power estimates, retaining the stronger
factor `2^n` for an order-`n+1` selector. -/
theorem abs_binomial_sum_le {T : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (n : ℕ)
    (hT : ∀ a ∈ Finset.range (n + 1), |T a| ≤ B / ((a : ℝ) + 1)) :
    |∑ a ∈ Finset.range (n + 1), (-1 : ℝ) ^ a * (n.choose a : ℝ) * T a| ≤
      (2 : ℝ) ^ n * B := by
  have hsum : (∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ)) = (2 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ ≤ ∑ a ∈ Finset.range (n + 1),
        |(-1 : ℝ) ^ a * (n.choose a : ℝ) * T a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.range (n + 1), (n.choose a : ℝ) * B := by
      apply Finset.sum_le_sum
      intro a ha
      have hdiv : B / ((a : ℝ) + 1) ≤ B := by
        apply (div_le_iff₀ (by positivity : 0 < (a : ℝ) + 1)).mpr
        have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
        nlinarith
      have hc : (0 : ℝ) ≤ (n.choose a : ℝ) := by positivity
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left ((hT a ha).trans hdiv) hc
    _ = _ := by rw [← Finset.sum_mul, hsum]

theorem abs_gaussianSelectorTrace_le_of_power_bounds (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) {k : ℕ} (hk : 1 ≤ k)
    {B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ a ∈ Finset.range k, |gaussianPowerTrace s A v a| ≤ B / ((a : ℝ) + 1)) :
    |gaussianSelectorTrace s A v k| ≤ (2 : ℝ) ^ (k - 1) * B := by
  rw [gaussianSelectorTrace_binomial s A v hk]
  have hh := abs_binomial_sum_le (T := gaussianPowerTrace s A v) hB (k - 1)
    (by simpa only [Nat.sub_add_cancel hk] using hT)
  simpa only [Nat.sub_add_cancel hk] using hh

/-- Identification of the actual matrix trace with its scalar Gaussian
score integral; finite second moments justify the diagonal sum. -/
theorem trace_weightedScore_eq_gaussian_score {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1) :
    Matrix.trace (weightedScore (standardGaussian r) id w) =
      ∫ z, (vectorNormSq z - (r : ℝ)) * w z ∂standardGaussian r := by
  have hi (j : Fin r) : Integrable (fun z : Vector r => (z j * z j - 1) * w z)
      (standardGaussian r) := by
    convert (standardGaussian_integrable_weighted_product w hw hb j j).sub
      (standardGaussian_integrable_bounded_weight w hw hb) using 1
    funext z
    simp only [Pi.sub_apply]
    ring
  unfold Matrix.trace weightedScore
  simp only [Matrix.diag_apply, id_eq, ↓reduceIte]
  rw [← integral_finset_sum Finset.univ (fun j _ => hi j)]
  apply integral_congr_ae
  refine ae_of_all _ (fun z => ?_)
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, vectorNormSq, sq]
  ring

/-- The signed trace retained by `sum_selectorWeight_trace_reduction` is
exactly the scalar selector score used in the binomial reduction. -/
theorem sum_selectorWeight_trace_eq_gaussianSelectorTrace (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (k : ℕ) :
    (∑ α : Fin k → Face p, Matrix.trace (weightedScore (standardGaussian r) id
      (fun g => selectorWeight s α (A.mulVec g + v)))) = gaussianSelectorTrace s A v k := by
  have hw (α : Fin k → Face p) : Measurable (fun g => selectorWeight s α (A.mulVec g + v)) :=
    (continuous_selectorWeight_affine s α A v).measurable
  have hb (α : Fin k → Face p) (g : Vector r) : |selectorWeight s α (A.mulVec g + v)| ≤ 1 := by
    rw [abs_of_nonneg (selectorWeight_nonneg s α _)]
    exact selectorWeight_le_one s α _
  have hi (α : Fin k → Face p) : Integrable
      (fun g => (vectorNormSq g - (r : ℝ)) * selectorWeight s α (A.mulVec g + v))
      (standardGaussian r) := by
    simpa only [mul_comm, Pi.sub_apply] using
      ((standardGaussian_integrable_vectorNormSq r).sub (integrable_const (r : ℝ))).bdd_mul
        (hw α).aestronglyMeasurable ⟨1, fun g => by simpa only [Real.norm_eq_abs] using hb α g⟩
  simp_rw [trace_weightedScore_eq_gaussian_score _ (hw _) (hb _)]
  rw [← integral_finset_sum Finset.univ (fun α _ => hi α)]
  unfold gaussianSelectorTrace
  apply integral_congr_ae
  refine ae_of_all _ (fun g => ?_)
  change (∑ α : Fin k → Face p,
    (vectorNormSq g - (r : ℝ)) * selectorWeight s α (A.mulVec g + v)) = _
  rw [← Finset.mul_sum, sum_selectorWeight_eq]


/-- Actual soft-power integrability against any integrable Gaussian scalar
factor. This also covers the signed facet and score polynomials. -/
theorem integrable_gaussian_softFacePower_mul (s : FaceSmoother p) (a : ℕ)
    (f : Face p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    {P : Vector r → ℝ} (hP : Integrable P (standardGaussian r)) :
    Integrable (fun g => P g * softFacePower s a f (A.mulVec g + v)) (standardGaussian r) := by
  apply integrable_gaussian_bounded_mul ((continuous_softFacePower s a f).comp (by fun_prop))
    ⟨1, fun g => ?_⟩ hP
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (softFacePower_nonneg _ _ _ _)]
  exact softFacePower_le_one _ _ _ _

theorem integrable_gaussian_softFacePower_pair_mul (s : FaceSmoother p) (a : ℕ)
    (f k : Face p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    {P : Vector r → ℝ} (hP : Integrable P (standardGaussian r)) :
    Integrable (fun g => P g *
      (softFacePower s a f (A.mulVec g + v) * (s.weights (A.mulVec g + v)).pi k))
        (standardGaussian r) := by
  have hin : Continuous (fun g : Vector r => A.mulVec g + v) := by fun_prop
  apply integrable_gaussian_bounded_mul
    (((continuous_softFacePower s a f).comp hin).mul ((s.continuous_pi k).comp hin))
    ⟨1, fun g => ?_⟩ hP
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (softFacePower_nonneg _ _ _ _)
    ((s.weights _).pi_nonneg _))]
  have hpi : (s.weights (A.mulVec g + v)).pi k ≤ 1 :=
    ((s.weights _).pi_le_theta _).trans (s.weights _).theta_lt_one.le
  exact (mul_le_mul (softFacePower_le_one _ _ _ _) hpi ((s.weights _).pi_nonneg _)
    zero_le_one).trans_eq (one_mul _)

/-- Exact signed facet/ridge decomposition of one scalar power score.
The ridge terms have already been paired; all moment and finite-integral
interchanges are proved from the concrete Gaussian law. -/
theorem gaussianPowerTrace_eq_paired_facet_ridge (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (v : Vector p)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) :
    gaussianPowerTrace s (σ • A) v a =
      (∫ g, ∑ f : Face p, (faceDot (signedRowNormal A f) g ^ 2 - 1) *
        softFacePower s a f ((σ • A).mulVec g + v) ∂standardGaussian p) -
      ((((a : ℝ) + 2) * σ / s.bandwidth) / 2) *
        (∫ g, ∑ f : Face p, ∑ k : Face p,
          softFacePower s a f ((σ • A).mulVec g + v) *
            (s.weights ((σ • A).mulVec g + v)).pi k *
              (1 - faceDot (signedRowNormal A f) (signedRowNormal A k)) *
                (faceDot (signedRowNormal A f) g + faceDot (signedRowNormal A k) g)
                  ∂standardGaussian p) := by
  let Y := fun g => (σ • A).mulVec g + v
  let P := fun f g => softFacePower s a f (Y g)
  let Facet := fun f g => (faceDot (signedRowNormal A f) g ^ 2 - 1) * P f g
  let Ridge := fun f k g => P f g * (s.weights (Y g)).pi k *
    (faceDot (signedRowNormal A k) g -
      faceDot (signedRowNormal A k) (signedRowNormal A f) * faceDot (signedRowNormal A f) g)
  let C := ((a : ℝ) + 2) * σ / s.bandwidth
  have hscore (f : Face p) : Integrable
      (fun g => (vectorNormSq g - (p : ℝ)) * P f g) (standardGaussian p) :=
    integrable_gaussian_softFacePower_mul s a f (σ • A) v
      ((standardGaussian_integrable_vectorNormSq p).sub (integrable_const _))
  have hfacet (f : Face p) : Integrable (Facet f) (standardGaussian p) :=
    integrable_gaussian_softFacePower_mul s a f (σ • A) v
      ((standardGaussian_integrable_faceDot_sq _).sub (integrable_const _))
  have hridge (f k : Face p) : Integrable (Ridge f k) (standardGaussian p) := by
    have hlin : Integrable (fun g => faceDot (signedRowNormal A k) g -
        faceDot (signedRowNormal A k) (signedRowNormal A f) * faceDot (signedRowNormal A f) g)
        (standardGaussian p) :=
      (standardGaussian_integrable_faceDot _).sub ((standardGaussian_integrable_faceDot _).const_mul _)
    simpa only [Ridge, P, Y, mul_comm] using
      integrable_gaussian_softFacePower_pair_mul s a f k (σ • A) v hlin
  have htrace : gaussianPowerTrace s (σ • A) v a =
      ∑ f : Face p, ∫ g, (vectorNormSq g - (p : ℝ)) * P f g ∂standardGaussian p := by
    unfold gaussianPowerTrace
    change (∫ g, (vectorNormSq g - (p : ℝ)) *
      (s.F (Y g) ^ (a + 1) * (s.weights (Y g)).theta) ∂standardGaussian p) = _
    simp_rw [← sum_softFacePower, Finset.mul_sum]
    exact integral_finset_sum Finset.univ (fun f _ => hscore f)
  have hsum : (∑ f : Face p, ∫ g, (vectorNormSq g - (p : ℝ)) * P f g ∂standardGaussian p) =
      (∑ f : Face p, ∫ g, Facet f g ∂standardGaussian p) -
        C * ∑ f : Face p, ∑ k : Face p, ∫ g, Ridge f k g ∂standardGaussian p := by
    calc
      _ = ∑ f : Face p, ((∫ g, Facet f g ∂standardGaussian p) -
          C * ∑ k : Face p, ∫ g, Ridge f k g ∂standardGaussian p) := by
        apply Finset.sum_congr rfl
        intro f _
        exact softFacePower_gaussian_tangent_identity s a f A σ v (signedRowNormal_unit_normSq A hdiag f)
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hfacetInt : (∫ g, ∑ f : Face p, Facet f g ∂standardGaussian p) =
      ∑ f : Face p, ∫ g, Facet f g ∂standardGaussian p :=
    integral_finset_sum Finset.univ (fun f _ => hfacet f)
  have hridgeInt : (∫ g, ∑ f : Face p, ∑ k : Face p, Ridge f k g ∂standardGaussian p) =
      ∑ f : Face p, ∑ k : Face p, ∫ g, Ridge f k g ∂standardGaussian p := by
    rw [integral_finset_sum Finset.univ (fun f _ =>
      integrable_finset_sum Finset.univ (fun k _ => hridge f k))]
    apply Finset.sum_congr rfl
    intro f _
    exact integral_finset_sum Finset.univ (fun k _ => hridge f k)
  have hpairInt :
      (∫ g, ∑ f : Face p, ∑ k : Face p, P f g * (s.weights (Y g)).pi k *
        (1 - faceDot (signedRowNormal A f) (signedRowNormal A k)) *
          (faceDot (signedRowNormal A f) g + faceDot (signedRowNormal A k) g)
            ∂standardGaussian p) =
      2 * ∑ f : Face p, ∑ k : Face p, ∫ g, Ridge f k g ∂standardGaussian p := by
    calc
      _ = ∫ g, 2 * (∑ f : Face p, ∑ k : Face p, Ridge f k g) ∂standardGaussian p := by
        apply integral_congr_ae
        exact ae_of_all _ (fun g => (softFacePower_sum_ridge_pairing s a A (Y g) g).symm)
      _ = _ := by rw [integral_const_mul, hridgeInt]
  change gaussianPowerTrace s (σ • A) v a =
    (∫ g, ∑ f : Face p, Facet f g ∂standardGaussian p) - (C / 2) *
      (∫ g, ∑ f : Face p, ∑ k : Face p, P f g * (s.weights (Y g)).pi k *
        (1 - faceDot (signedRowNormal A f) (signedRowNormal A k)) *
          (faceDot (signedRowNormal A f) g + faceDot (signedRowNormal A k) g)
            ∂standardGaussian p)
  rw [htrace, hsum, hfacetInt, hpairInt]
  ring


section Averaged

variable (μ : Measure (Vector p)) [IsProbabilityMeasure μ]

/-- An arbitrary base probability law, independent of the actual Gaussian
factor. No moment assumption on the base point is needed. -/
def averagedGaussianPowerTrace (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (a : ℕ) : ℝ :=
  ∫ z : Vector p × Vector r, (vectorNormSq z.2 - (r : ℝ)) *
    (s.F (A.mulVec z.2 + z.1) ^ (a + 1) * s.theta (A.mulVec z.2 + z.1))
      ∂μ.prod (standardGaussian r)

def averagedGaussianSelectorTrace (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (k : ℕ) : ℝ :=
  ∫ z : Vector p × Vector r, (vectorNormSq z.2 - (r : ℝ)) *
    (s.F (A.mulVec z.2 + z.1) * s.theta (A.mulVec z.2 + z.1) ^ k)
      ∂μ.prod (standardGaussian r)

theorem integrable_averaged_gaussian_score_weight (w : Vector p → ℝ) (hw : Continuous w)
    (hb : ∀ x, |w x| ≤ 1) (A : Matrix (Fin p) (Fin r) ℝ) :
    Integrable (fun z : Vector p × Vector r => (vectorNormSq z.2 - (r : ℝ)) *
      w (A.mulVec z.2 + z.1)) (μ.prod (standardGaussian r)) := by
  have hscore : Integrable (fun g : Vector r => vectorNormSq g - (r : ℝ))
      (standardGaussian r) :=
    (standardGaussian_integrable_vectorNormSq r).sub (integrable_const _)
  have hprod : Integrable (fun z : Vector p × Vector r => vectorNormSq z.2 - (r : ℝ))
      (μ.prod (standardGaussian r)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Vector p => (1 : ℝ)) μ).mul_prod hscore
  have hweight : Continuous (fun z : Vector p × Vector r => w (A.mulVec z.2 + z.1)) :=
    hw.comp (by fun_prop)
  simpa only [mul_comm] using hprod.bdd_mul hweight.aestronglyMeasurable
    ⟨1, fun z => by simpa only [Real.norm_eq_abs] using hb (A.mulVec z.2 + z.1)⟩

theorem integrable_averaged_gaussian_power_trace (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (a : ℕ) :
    Integrable (fun z : Vector p × Vector r => (vectorNormSq z.2 - (r : ℝ)) *
      (s.F (A.mulVec z.2 + z.1) ^ (a + 1) * s.theta (A.mulVec z.2 + z.1)))
        (μ.prod (standardGaussian r)) := by
  apply integrable_averaged_gaussian_score_weight μ _
    ((s.continuous_F.pow _).mul (continuous_smoother_theta s)) _ A
  intro x
  rw [abs_of_nonneg (smoother_power_weight_bounds s a x).1]
  exact (smoother_power_weight_bounds s a x).2

theorem integrable_averaged_gaussian_selector_trace (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (k : ℕ) :
    Integrable (fun z : Vector p × Vector r => (vectorNormSq z.2 - (r : ℝ)) *
      (s.F (A.mulVec z.2 + z.1) * s.theta (A.mulVec z.2 + z.1) ^ k))
        (μ.prod (standardGaussian r)) := by
  apply integrable_averaged_gaussian_score_weight μ _
    (s.continuous_F.mul ((continuous_smoother_theta s).pow _)) _ A
  intro x
  rw [abs_of_nonneg (smoother_selector_weight_bounds s k x).1]
  exact (smoother_selector_weight_bounds s k x).2

theorem averagedGaussianPowerTrace_eq_integral (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (a : ℕ) :
    averagedGaussianPowerTrace μ s A a = ∫ v, gaussianPowerTrace s A v a ∂μ := by
  unfold averagedGaussianPowerTrace gaussianPowerTrace
  exact integral_prod _ (integrable_averaged_gaussian_power_trace μ s A a)

theorem averagedGaussianSelectorTrace_eq_integral (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (k : ℕ) :
    averagedGaussianSelectorTrace μ s A k = ∫ v, gaussianSelectorTrace s A v k ∂μ := by
  unfold averagedGaussianSelectorTrace gaussianSelectorTrace
  exact integral_prod _ (integrable_averaged_gaussian_selector_trace μ s A k)

theorem integrable_gaussianPowerTrace_base (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (a : ℕ) :
    Integrable (fun v => gaussianPowerTrace s A v a) μ :=
  (integrable_averaged_gaussian_power_trace μ s A a).integral_prod_left

theorem integrable_gaussianSelectorTrace_base (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (k : ℕ) :
    Integrable (fun v => gaussianSelectorTrace s A v k) μ :=
  (integrable_averaged_gaussian_selector_trace μ s A k).integral_prod_left

theorem averagedGaussianSelectorTrace_binomial_succ (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (n : ℕ) :
    averagedGaussianSelectorTrace μ s A (n + 1) =
      ∑ a ∈ Finset.range (n + 1), (-1 : ℝ) ^ a * (n.choose a : ℝ) *
        averagedGaussianPowerTrace μ s A a := by
  rw [averagedGaussianSelectorTrace_eq_integral]
  simp_rw [gaussianSelectorTrace_binomial_succ]
  rw [integral_finset_sum (Finset.range (n + 1)) (fun a _ =>
    (integrable_gaussianPowerTrace_base μ s A a).const_mul _)]
  simp_rw [integral_const_mul, ← averagedGaussianPowerTrace_eq_integral]

theorem averagedGaussianSelectorTrace_binomial (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) {k : ℕ} (hk : 1 ≤ k) :
    averagedGaussianSelectorTrace μ s A k =
      ∑ a ∈ Finset.range k, (-1 : ℝ) ^ a * ((k - 1).choose a : ℝ) *
        averagedGaussianPowerTrace μ s A a := by
  have hh := averagedGaussianSelectorTrace_binomial_succ μ s A (k - 1)
  simpa only [Nat.sub_add_cancel hk] using hh

theorem abs_averagedGaussianSelectorTrace_le_of_power_bounds (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) {k : ℕ} (hk : 1 ≤ k) {B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ a ∈ Finset.range k,
      |averagedGaussianPowerTrace μ s A a| ≤ B / ((a : ℝ) + 1)) :
    |averagedGaussianSelectorTrace μ s A k| ≤ (2 : ℝ) ^ (k - 1) * B := by
  rw [averagedGaussianSelectorTrace_binomial μ s A hk]
  have hh := abs_binomial_sum_le (T := averagedGaussianPowerTrace μ s A) hB (k - 1)
    (by simpa only [Nat.sub_add_cancel hk] using hT)
  simpa only [Nat.sub_add_cancel hk] using hh

/-- Direct bridge to the signed matrix trace remaining in the actual
selector-family covariance restoration inequality. -/
theorem integral_sum_selectorWeight_trace_eq_averagedGaussianSelectorTrace
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (k : ℕ) :
    (∫ v, ∑ α : Fin k → Face p, Matrix.trace (weightedScore (standardGaussian r) id
      (fun g => selectorWeight s α (A.mulVec g + v))) ∂μ) =
        averagedGaussianSelectorTrace μ s A k := by
  simp_rw [sum_selectorWeight_trace_eq_gaussianSelectorTrace]
  exact (averagedGaussianSelectorTrace_eq_integral μ s A k).symm


/-- Gaussian polynomial moments remain integrable after multiplication by
an actual shifted soft face, under an arbitrary independent base law. -/
theorem integrable_averaged_gaussian_softFacePower_mul (s : FaceSmoother p) (a : ℕ)
    (f : Face p) (A : Matrix (Fin p) (Fin r) ℝ)
    {P : Vector r → ℝ} (hP : Integrable P (standardGaussian r)) :
    Integrable (fun z : Vector p × Vector r => P z.2 *
      softFacePower s a f (A.mulVec z.2 + z.1)) (μ.prod (standardGaussian r)) := by
  have hprod : Integrable (fun z : Vector p × Vector r => P z.2)
      (μ.prod (standardGaussian r)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Vector p => (1 : ℝ)) μ).mul_prod hP
  have hw : Continuous (fun z : Vector p × Vector r => softFacePower s a f (A.mulVec z.2 + z.1)) :=
    (continuous_softFacePower s a f).comp (by fun_prop)
  simpa only [mul_comm] using hprod.bdd_mul hw.aestronglyMeasurable
    ⟨1, fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (softFacePower_nonneg _ _ _ _)]
      exact softFacePower_le_one _ _ _ _⟩

theorem integrable_averaged_gaussian_softFacePower_pair_mul (s : FaceSmoother p) (a : ℕ)
    (f k : Face p) (A : Matrix (Fin p) (Fin r) ℝ)
    {P : Vector r → ℝ} (hP : Integrable P (standardGaussian r)) :
    Integrable (fun z : Vector p × Vector r => P z.2 *
      (softFacePower s a f (A.mulVec z.2 + z.1) * (s.weights (A.mulVec z.2 + z.1)).pi k))
        (μ.prod (standardGaussian r)) := by
  have hprod : Integrable (fun z : Vector p × Vector r => P z.2)
      (μ.prod (standardGaussian r)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Vector p => (1 : ℝ)) μ).mul_prod hP
  have hin : Continuous (fun z : Vector p × Vector r => A.mulVec z.2 + z.1) := by fun_prop
  have hw : Continuous (fun z : Vector p × Vector r =>
      softFacePower s a f (A.mulVec z.2 + z.1) * (s.weights (A.mulVec z.2 + z.1)).pi k) :=
    ((continuous_softFacePower s a f).comp hin).mul ((s.continuous_pi k).comp hin)
  simpa only [mul_comm] using hprod.bdd_mul hw.aestronglyMeasurable
    ⟨1, fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (softFacePower_nonneg _ _ _ _)
        ((s.weights _).pi_nonneg _))]
      have hpi : (s.weights (A.mulVec z.2 + z.1)).pi k ≤ 1 :=
        ((s.weights _).pi_le_theta _).trans (s.weights _).theta_lt_one.le
      exact (mul_le_mul (softFacePower_le_one _ _ _ _) hpi ((s.weights _).pi_nonneg _)
        zero_le_one).trans_eq (one_mul _)⟩

/-- The fully averaged signed decomposition, with actual product probability
law and all polynomial/kernel integrability and Fubini conditions discharged. -/
theorem averagedGaussianPowerTrace_eq_paired_facet_ridge (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) :
    averagedGaussianPowerTrace μ s (σ • A) a =
      (∫ z : Vector p × Vector p, ∑ f : Face p,
        (faceDot (signedRowNormal A f) z.2 ^ 2 - 1) *
          softFacePower s a f ((σ • A).mulVec z.2 + z.1) ∂μ.prod (standardGaussian p)) -
      ((((a : ℝ) + 2) * σ / s.bandwidth) / 2) *
        (∫ z : Vector p × Vector p, ∑ f : Face p, ∑ k : Face p,
          softFacePower s a f ((σ • A).mulVec z.2 + z.1) *
            (s.weights ((σ • A).mulVec z.2 + z.1)).pi k *
              (1 - faceDot (signedRowNormal A f) (signedRowNormal A k)) *
                (faceDot (signedRowNormal A f) z.2 + faceDot (signedRowNormal A k) z.2)
                  ∂μ.prod (standardGaussian p)) := by
  let Facet := fun z : Vector p × Vector p => ∑ f : Face p,
    (faceDot (signedRowNormal A f) z.2 ^ 2 - 1) *
      softFacePower s a f ((σ • A).mulVec z.2 + z.1)
  let Ridge := fun z : Vector p × Vector p => ∑ f : Face p, ∑ k : Face p,
    softFacePower s a f ((σ • A).mulVec z.2 + z.1) *
      (s.weights ((σ • A).mulVec z.2 + z.1)).pi k *
        (1 - faceDot (signedRowNormal A f) (signedRowNormal A k)) *
          (faceDot (signedRowNormal A f) z.2 + faceDot (signedRowNormal A k) z.2)
  let C := (((a : ℝ) + 2) * σ / s.bandwidth) / 2
  have hFacet : Integrable Facet (μ.prod (standardGaussian p)) := by
    apply integrable_finset_sum Finset.univ
    intro f _
    exact integrable_averaged_gaussian_softFacePower_mul μ s a f (σ • A)
      ((standardGaussian_integrable_faceDot_sq _).sub (integrable_const _))
  have hRidge : Integrable Ridge (μ.prod (standardGaussian p)) := by
    apply integrable_finset_sum Finset.univ
    intro f _
    apply integrable_finset_sum Finset.univ
    intro k _
    have hlin : Integrable (fun g =>
        (1 - faceDot (signedRowNormal A f) (signedRowNormal A k)) *
          (faceDot (signedRowNormal A f) g + faceDot (signedRowNormal A k) g))
        (standardGaussian p) :=
      ((standardGaussian_integrable_faceDot _).add (standardGaussian_integrable_faceDot _)).const_mul _
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      integrable_averaged_gaussian_softFacePower_pair_mul μ s a f k (σ • A) hlin
  change averagedGaussianPowerTrace μ s (σ • A) a =
    (∫ z, Facet z ∂μ.prod (standardGaussian p)) - C * (∫ z, Ridge z ∂μ.prod (standardGaussian p))
  rw [averagedGaussianPowerTrace_eq_integral]
  calc
    _ = ∫ v, ((∫ g, Facet (v, g) ∂standardGaussian p) -
        C * (∫ g, Ridge (v, g) ∂standardGaussian p)) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun v => gaussianPowerTrace_eq_paired_facet_ridge s a A σ v hdiag)
    _ = (∫ v, ∫ g, Facet (v, g) ∂standardGaussian p ∂μ) -
        C * (∫ v, ∫ g, Ridge (v, g) ∂standardGaussian p ∂μ) := by
      rw [integral_sub hFacet.integral_prod_left (hRidge.integral_prod_left.const_mul C),
        integral_const_mul]
    _ = _ := by rw [← integral_prod _ hFacet, ← integral_prod _ hRidge]

end Averaged

end
end RectangleCLT.Companion.SignedSurface
