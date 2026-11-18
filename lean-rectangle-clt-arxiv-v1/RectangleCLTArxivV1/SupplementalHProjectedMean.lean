import RectangleCLTArxivV1.SmoothingGaussianMean
import RectangleCLTCompanion.SplitV4.Printed.MatrixNuclearReduction

/-! The projected-reference Gaussian mean estimate of Supplemental H.
The bounded-weight case is proved here for an arbitrary orthogonal
projection, rather than only one face. This does not assert the separate
localized Hausdorff surface estimates or the linear-growth extension of
covariance contraction. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion
open scoped BigOperators
noncomputable section

theorem projection_complement_mem_kernel {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (hPP : P*P=P) (x : Vector r) :
    P.mulVec (x-P.mulVec x)=0 := by
  rw [Matrix.mulVec_sub,Matrix.mulVec_mulVec,hPP,sub_self]

theorem symmetric_projection_dot {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (hPt : P.transpose=P) (x y : Vector r) :
    faceDot (P.mulVec x) y = faceDot x (P.mulVec y) := by
  change dotProduct (P.mulVec x) y = dotProduct x (P.mulVec y)
  rw [Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose,hPt]

theorem projection_complement_orthogonal {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (hPt : P.transpose=P) (hPP : P*P=P) (x : Vector r) :
    faceDot (P.mulVec x) (x-P.mulVec x)=0 := by
  rw [symmetric_projection_dot P hPt,projection_complement_mem_kernel P hPP]
  simp [faceDot]

theorem projection_complement_dot {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (hPt : P.transpose=P) (hPP : P*P=P) (x : Vector r) :
    faceDot (x-P.mulVec x) x = vectorNormSq (x-P.mulVec x) := by
  have ho := projection_complement_orthogonal P hPt hPP x
  unfold faceDot at ho ⊢
  unfold vectorNormSq
  have he (j : Fin r) : (x-P.mulVec x) j*x j =
      ((x-P.mulVec x) j)^2+P.mulVec x j*(x-P.mulVec x) j := by
    simp only [Pi.sub_apply]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,ho,add_zero]

theorem projection_normSq_decomposition {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (hPt : P.transpose=P) (hPP : P*P=P) (x : Vector r) :
    vectorNormSq x = vectorNormSq (P.mulVec x)+vectorNormSq (x-P.mulVec x) := by
  have ho := projection_complement_orthogonal P hPt hPP x
  unfold faceDot at ho
  unfold vectorNormSq
  have he (j : Fin r) : x j^2 =
      (P.mulVec x j)^2+((x-P.mulVec x) j)^2+2*(P.mulVec x j*(x-P.mulVec x) j) := by
    simp only [Pi.sub_apply]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,ho,mul_zero,add_zero]

/-- A reference depending on an actual projection is invariant under a
Gaussian exponential tilt orthogonal to that projection. -/
theorem gaussian_projection_exponential {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (β : Vector r → ℝ) (t : Vector r)
    (ht : P.mulVec t=0) :
    (∫ g, β (P.mulVec g)*Real.exp (faceDot t g) ∂standardGaussian r) =
      Real.exp (vectorNormSq t/2)*(∫ g, β (P.mulVec g) ∂standardGaussian r) := by
  rw [gaussian_exponential_translation]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    change β (P.mulVec (g+t))=β (P.mulVec g)
    rw [Matrix.mulVec_add,ht,add_zero])

/-- Weighted Cauchy--Schwarz controls the mean component in the projected
coordinates by its genuine weighted second moment. -/
theorem gaussian_projected_mean_sq_le_second {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (w : Vector r → ℝ)
    (hw : Measurable w) (hw0 : ∀ g, 0 ≤ w g) (hw1 : ∀ g, w g ≤ 1)
    (hp : 0 < weightMass (standardGaussian r) w) :
    weightMass (standardGaussian r) w *
      vectorNormSq (P.mulVec (weightMean (standardGaussian r) id w)) ≤
      ∫ g, w g*vectorNormSq (P.mulVec g) ∂standardGaussian r := by
  have hbound : ∀ g, |w g| ≤ 1 := fun g => by
    rw [abs_of_nonneg (hw0 g)]
    exact hw1 g
  have hi := standardGaussian_integrable_bounded_weight w hw hbound
  have hsq (j : Fin r) := gaussian_integrable_weighted_linear_sq w hw hbound (P j)
  have hc (j : Fin r) := weighted_mean_sq_le_second (standardGaussian r) w (faceDot (P j))
    hw0 hi (gaussian_integrable_weighted_linear w hw hbound (P j)) (hsq j) hp
  have hb (j : Fin r) : weightMass (standardGaussian r) w *
      (faceDot (P j) (weightMean (standardGaussian r) id w))^2 ≤
      ∫ g, w g*(faceDot (P j) g)^2 ∂standardGaussian r := by
    have hh := hc j
    rw [weighted_linear_integral_eq_mean w hw hbound hp.ne'] at hh
    change weightMass (standardGaussian r) w *
      ((weightMass (standardGaussian r) w *
        faceDot (P j) (weightMean (standardGaussian r) id w))/weightMass (standardGaussian r) w)^2 ≤ _ at hh
    rw [mul_div_cancel_left₀ _ hp.ne'] at hh
    exact hh
  calc
    _ = ∑ j, weightMass (standardGaussian r) w *
        (faceDot (P j) (weightMean (standardGaussian r) id w))^2 := by
      simp only [vectorNormSq,Finset.mul_sum]
      rfl
    _ ≤ ∑ j, ∫ g, w g*(faceDot (P j) g)^2 ∂standardGaussian r :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by
      rw [←integral_finset_sum Finset.univ (fun j _ => hsq j)]
      apply integral_congr_ae
      exact ae_of_all _ (fun g => by simp only [vectorNormSq,Finset.mul_sum]; rfl)

/-- Supplemental H's projected-reference mean inequality for actual
bounded weights. All Gaussian moments and tilt factorizations are proved
from the displayed weight and projection data. -/
theorem gaussian_mean_relative_to_projection {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (hPt : P.transpose=P) (hPP : P*P=P)
    (β : Vector r → ℝ) (hβ : Measurable β) (hβb : ∀ x, 0 ≤ β x ∧ β x ≤ 1)
    (w : Vector r → ℝ) (hw : Measurable w)
    (hwb : ∀ g, 0 ≤ w g ∧ w g ≤ β (P.mulVec g))
    (hpw : 0 < weightMass (standardGaussian r) w) :
    weightMass (standardGaussian r) w * vectorNormSq (weightMean (standardGaussian r) id w) ≤
      (∫ g, w g*vectorNormSq (P.mulVec g) ∂standardGaussian r)+
      2*weightMass (standardGaussian r) w *
        Real.log ((∫ g, β (P.mulVec g) ∂standardGaussian r)/weightMass (standardGaussian r) w) := by
  let μ := weightMean (standardGaussian r) id w
  let t := μ-P.mulVec μ
  let p := weightMass (standardGaussian r) w
  let b : Vector r → ℝ := fun g => β (P.mulVec g)
  let pb := ∫ g, b g ∂standardGaussian r
  have hw0 : ∀ g, 0 ≤ w g := fun g => (hwb g).1
  have hw1 : ∀ g, w g ≤ 1 := fun g => (hwb g).2.trans (hβb _).2
  have hbound : ∀ g, |w g| ≤ 1 := fun g => by rw [abs_of_nonneg (hw0 g)]; exact hw1 g
  have hb : Measurable b := hβ.comp (measurable_mulVec P)
  have hbb : ∀ g, |b g| ≤ 1 := fun g => by rw [abs_of_nonneg (hβb _).1]; exact (hβb _).2
  have hwi := standardGaussian_integrable_bounded_weight w hw hbound
  have hbi := standardGaussian_integrable_bounded_weight b hb hbb
  have hppb : p ≤ pb := integral_mono hwi hbi (fun g => (hwb g).2)
  have hpb : 0 < pb := hpw.trans_le hppb
  have hexp : Integrable (fun g => Real.exp (faceDot t g)) (standardGaussian r) := by
    simpa only [one_mul,faceDot] using integrable_exp_linearProjection t 1
  have hwexp := hexp.bdd_mul hw.aestronglyMeasurable
    ⟨1,fun g => by simpa only [Real.norm_eq_abs] using hbound g⟩
  have hbexp := hexp.bdd_mul hb.aestronglyMeasurable
    ⟨1,fun g => by simpa only [Real.norm_eq_abs] using hbb g⟩
  have hJ := weighted_exp_mean_le (standardGaussian r) w (faceDot t) hw0 hwi
    (gaussian_integrable_weighted_linear w hw hbound t) hwexp hpw
  rw [weighted_linear_integral_eq_mean w hw hbound hpw.ne'] at hJ
  change p*Real.exp ((p*faceDot t μ)/p) ≤ _ at hJ
  rw [mul_div_cancel_left₀ _ hpw.ne'] at hJ
  have hnormal : faceDot t μ = vectorNormSq t := projection_complement_dot P hPt hPP μ
  have hI : p*Real.exp (vectorNormSq t) ≤ pb*Real.exp (vectorNormSq t/2) := by
    calc
      _ = p*Real.exp (faceDot t μ) := by rw [hnormal]
      _ ≤ ∫ g, w g*Real.exp (faceDot t g) ∂standardGaussian r := hJ
      _ ≤ ∫ g, b g*Real.exp (faceDot t g) ∂standardGaussian r :=
        integral_mono hwexp hbexp (fun g =>
          mul_le_mul_of_nonneg_right (hwb g).2 (Real.exp_nonneg _))
      _ = _ := by
        rw [gaussian_projection_exponential P β t (projection_complement_mem_kernel P hPP μ)]
        ring
  have hexpHalf : Real.exp (vectorNormSq t/2) ≤ pb/p := by
    apply (le_div_iff₀ hpw).mpr
    apply (mul_le_mul_right (Real.exp_pos (vectorNormSq t/2))).mp
    have heq : Real.exp (vectorNormSq t) =
        Real.exp (vectorNormSq t/2)*Real.exp (vectorNormSq t/2) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [heq] at hI
    convert hI using 1; ring
  have hlog : vectorNormSq t ≤ 2*Real.log (pb/p) := by
    have hh := (Real.le_log_iff_exp_le (div_pos hpb hpw)).mpr hexpHalf
    linarith
  have hsecond := gaussian_projected_mean_sq_le_second P w hw hw0 hw1 hpw
  have hdecomp := projection_normSq_decomposition P hPt hPP μ
  have hplog := mul_le_mul_of_nonneg_left hlog hpw.le
  change p*vectorNormSq μ ≤ _
  change p*vectorNormSq (P.mulVec μ) ≤ _ at hsecond
  dsimp only [p,pb,b] at hplog
  dsimp only [p,pb,b] at hsecond ⊢
  nlinarith

/-- The matrix reduction of H.lemmaGaussian for bounded nonnegative
log-concave weights. The checked Prékopa covariance contraction is inside
the proof, including weights that vanish on part of the Gaussian space. -/
theorem gaussian_bounded_logConcave_matrix_reduction {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w)
    (hw0 : ∀ g, 0 ≤ w g) (hw1 : ∀ g, w g ≤ 1)
    (hp : 0 < weightMass (standardGaussian r) w)
    (hc : RectangleCLT.Companion.SplitV4.Printed.NonnegativeLogConcave w) :
    RectangleCLT.Companion.SplitV4.symmetricNuclearNorm
      (weightedScore (standardGaussian r) id w) ≤
      2*weightMass (standardGaussian r) w *
        vectorNormSq (weightMean (standardGaussian r) id w)-
      ∫ g, (vectorNormSq g-(r:ℝ))*w g ∂standardGaussian r :=
  RectangleCLT.Companion.SplitV4.Printed.nonnegative_logConcave_weight_nuclear_reduction
    w hw hw0 hw1 hp hc

/-- An actual affine logistic selector matrix satisfies the projected
reference reduction used later in H. Repeated selected faces, arbitrary
singular factors and arbitrary projection rank are allowed. -/
theorem gaussian_selector_projected_matrix_bound {p k r : ℕ}
    (s : FaceSmoother p) (α : Fin k → Face p) (hactive : ∀ i, α i ∈ s.faces)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (P : Matrix (Fin r) (Fin r) ℝ) (hPt : P.transpose=P) (hPP : P*P=P)
    (β : Vector r → ℝ) (hβ : Measurable β) (hβb : ∀ x, 0 ≤ β x ∧ β x ≤ 1)
    (hdom : ∀ g, selectorWeight s α (A.mulVec g+v) ≤ β (P.mulVec g)) :
    RectangleCLT.Companion.SplitV4.symmetricNuclearNorm
      (weightedScore (standardGaussian r) id (fun g => selectorWeight s α (A.mulVec g+v))) ≤
      2*(∫ g, selectorWeight s α (A.mulVec g+v)*vectorNormSq (P.mulVec g) ∂standardGaussian r)+
      4*weightMass (standardGaussian r) (fun g => selectorWeight s α (A.mulVec g+v))*
        Real.log ((∫ g, β (P.mulVec g) ∂standardGaussian r)/
          weightMass (standardGaussian r) (fun g => selectorWeight s α (A.mulVec g+v)))-
      ∫ g, (vectorNormSq g-(r:ℝ))*selectorWeight s α (A.mulVec g+v) ∂standardGaussian r := by
  have hw := (continuous_selectorWeight_affine s α A v).measurable
  have hp := selectorWeight_affine_mass_pos s α hactive A v
  have hmean := gaussian_mean_relative_to_projection P hPt hPP β hβ hβb
    (fun g => selectorWeight s α (A.mulVec g+v)) hw
    (fun g => ⟨selectorWeight_nonneg s α _,hdom g⟩) hp
  have hmatrix := RectangleCLT.Companion.SplitV4.selectorWeight_nuclear_reduction s α A v
  rw [SignedSurface.trace_weightedScore_eq_gaussian_score _ hw (fun g => by
    rw [abs_of_nonneg (selectorWeight_nonneg s α _)]
    exact selectorWeight_le_one s α _)] at hmatrix
  nlinarith

end
end RectangleCLTArxivV1
