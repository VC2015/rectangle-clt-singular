import RectangleCLT.GaussianMoments
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Integration by parts for the concrete standard real and product Gaussian measures.
The whole-line boundary terms are discharged by integrability, rather than
being assumed to vanish. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace RectangleCLT

theorem hasDerivAt_standardRealGaussian_density (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1)
      (-x * gaussianPDFReal 0 1 x) x := by
  have hpdf : gaussianPDFReal 0 1 = (fun x : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [hpdf]
  convert (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp.const_mul
    (Real.sqrt (2 * Real.pi))⁻¹) using 1
  dsimp
  ring

/-- Integrability under the Gaussian law transfers to its Lebesgue density. -/
theorem standardRealGaussian_integrable_density_mul {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x * g x) := by
  rw [gaussianReal_of_var_ne_zero 0 (by simp : (1 : NNReal) ≠ 0)] at hg
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1)
    (ae_of_all _ (fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mp hg
  simpa only [toReal_gaussianPDF, smul_eq_mul] using h

/-- Gaussian integration by parts with explicit integrability hypotheses.
No boundary limit or integration-by-parts identity is assumed. -/
theorem standardRealGaussian_stein_of_integrable {g g' : ℝ → ℝ}
    (hgderiv : ∀ x, HasDerivAt g (g' x) x)
    (hg : Integrable g (gaussianReal 0 1))
    (hg' : Integrable g' (gaussianReal 0 1))
    (hxg : Integrable (fun x => x * g x) (gaussianReal 0 1)) :
    (∫ x, x * g x ∂gaussianReal 0 1) = ∫ x, g' x ∂gaussianReal 0 1 := by
  have huvg := standardRealGaussian_integrable_density_mul hg
  have huvg' := standardRealGaussian_integrable_density_mul hg'
  have hu'vg : Integrable
      (fun x => (-x * gaussianPDFReal 0 1 x) * g x) := by
    simpa only [Pi.neg_apply, mul_neg, neg_mul, mul_assoc, mul_left_comm] using
      (standardRealGaussian_integrable_density_mul hxg).neg
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    hasDerivAt_standardRealGaussian_density hgderiv huvg' hu'vg huvg
  have hneg :
      (∫ x, (-x * gaussianPDFReal 0 1 x) * g x) =
        -(∫ x, gaussianPDFReal 0 1 x * (x * g x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by ring)
  rw [hneg, neg_neg] at hibp
  calc
    _ = ∫ x, gaussianPDFReal 0 1 x * (x * g x) := by
      simpa only [smul_eq_mul] using
        (integral_gaussianReal_eq_integral_smul
          (f := fun x => x * g x) (by simp : (1 : NNReal) ≠ 0))
    _ = ∫ x, gaussianPDFReal 0 1 x * g' x := hibp.symm
    _ = _ := by
      symm
      simpa only [smul_eq_mul] using
        (integral_gaussianReal_eq_integral_smul
          (f := g') (by simp : (1 : NNReal) ≠ 0))

/-- Bounded differentiable tests with bounded derivative satisfy the Stein
identity; all measurability, integrability and boundary conditions are proved. -/
theorem standardRealGaussian_stein {g g' : ℝ → ℝ}
    (hgderiv : ∀ x, HasDerivAt g (g' x) x)
    (hgbounded : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hg'bounded : ∃ C : ℝ, ∀ x, |g' x| ≤ C) :
    (∫ x, x * g x ∂gaussianReal 0 1) = ∫ x, g' x ∂gaussianReal 0 1 := by
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr
    (fun x => (hgderiv x).continuousAt)
  have hg'meas : Measurable g' := by
    have hderiv : g' = deriv g := funext (fun x => (hgderiv x).deriv.symm)
    rw [hderiv]
    exact measurable_deriv g
  obtain ⟨C, hC⟩ := hgbounded
  obtain ⟨D, hD⟩ := hg'bounded
  have hgint : Integrable g (gaussianReal 0 1) := by
    apply (integrable_const C).mono' hgcont.measurable.aestronglyMeasurable
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hC x)
  have hg'int : Integrable g' (gaussianReal 0 1) := by
    apply (integrable_const D).mono' hg'meas.aestronglyMeasurable
    exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hD x)
  have hxint : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) := by
    simpa only [pow_one, id_eq] using standardRealGaussian_integrable_pow 1
  have hxg : Integrable (fun x => x * g x) (gaussianReal 0 1) := by
    have h := hxint.bdd_mul hgcont.measurable.aestronglyMeasurable
      ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x⟩
    simpa only [id_eq, mul_comm] using h
  exact standardRealGaussian_stein_of_integrable hgderiv hgint hg'int hxg

/-- The coordinate Stein identity for the actual finite product Gaussian law.
The prescribed coordinate derivative is checked on coordinate slices. -/
theorem standardGaussian_coordinate_stein {p : ℕ} (j : Fin p)
    {g g' : Vector p → ℝ}
    (hgderiv : ∀ x, HasDerivAt (fun t => g (Function.update x j t)) (g' x) (x j))
    (hgmeas : Measurable g) (hg'meas : Measurable g')
    (hgbounded : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hg'bounded : ∃ C : ℝ, ∀ x, |g' x| ≤ C) :
    (∫ x, x j * g x ∂standardGaussian p) = ∫ x, g' x ∂standardGaussian p := by
  cases p with
  | zero => exact Fin.elim0 j
  | succ n =>
    obtain ⟨C, hC⟩ := hgbounded
    obtain ⟨D, hD⟩ := hg'bounded
    have hxg : Integrable (fun x : Vector (n + 1) => x j * g x)
        (standardGaussian (n + 1)) := by
      have h := (standardGaussian_integrable_coordinate (n + 1) j).bdd_mul
        hgmeas.aestronglyMeasurable
        ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x⟩
      simpa only [mul_comm] using h
    have hg'int : Integrable g' (standardGaussian (n + 1)) := by
      apply (integrable_const D).mono' hg'meas.aestronglyMeasurable
      exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hD x)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
    have hmp : MeasurePreserving e (standardGaussian (n + 1))
        ((gaussianReal 0 1).prod (standardGaussian n)) :=
      measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) j
    have hinv := MeasurePreserving.symm e hmp
    have hleft : Integrable
        (fun z : ℝ × Vector n => (e.symm z) j * g (e.symm z))
        ((gaussianReal 0 1).prod (standardGaussian n)) :=
      (hinv.integrable_comp_emb e.symm.measurableEmbedding).mpr hxg
    have hright : Integrable
        (fun z : ℝ × Vector n => g' (e.symm z))
        ((gaussianReal 0 1).prod (standardGaussian n)) :=
      (hinv.integrable_comp_emb e.symm.measurableEmbedding).mpr hg'int
    have hscalar (y : Vector n) :
        (∫ t, t * g (j.insertNth t y) ∂gaussianReal 0 1) =
          ∫ t, g' (j.insertNth t y) ∂gaussianReal 0 1 := by
      apply standardRealGaussian_stein
      · intro t
        simpa only [Fin.insertNth_apply_same, Fin.update_insertNth] using
          hgderiv (j.insertNth t y)
      · exact ⟨C, fun t => hC (j.insertNth t y)⟩
      · exact ⟨D, fun t => hD (j.insertNth t y)⟩
    calc
      _ = ∫ z : ℝ × Vector n, (e.symm z) j * g (e.symm z)
          ∂(gaussianReal 0 1).prod (standardGaussian n) :=
        (hinv.integral_comp' (fun x => x j * g x)).symm
      _ = ∫ y : Vector n, ∫ t, (e.symm (t, y)) j * g (e.symm (t, y))
          ∂gaussianReal 0 1 ∂standardGaussian n := integral_prod_symm _ hleft
      _ = ∫ y : Vector n, ∫ t, g' (e.symm (t, y))
          ∂gaussianReal 0 1 ∂standardGaussian n := by
        apply integral_congr_ae
        exact ae_of_all _ (fun y => by
          simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv] using hscalar y)
      _ = ∫ z : ℝ × Vector n, g' (e.symm z)
          ∂(gaussianReal 0 1).prod (standardGaussian n) :=
        (integral_prod_symm _ hright).symm
      _ = ∫ x, g' x ∂standardGaussian (n + 1) := hinv.integral_comp' g'


private theorem mulVec_update {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (z : Vector p) (r : Fin p) (t : ℝ) :
    A.mulVec (Function.update z r t) =
      A.mulVec z + (t - z r) • (fun k => A k r) := by
  classical
  have hupdate : Function.update z r t = z + (t - z r) • (Pi.single r (1 : ℝ) : Vector p) := by
    funext i
    by_cases hi : i = r
    · subst i
      simp
    · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]
  rw [hupdate, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

/-- Covariance-form Stein identity for the concrete Gaussian image, including
singular factors. The analytic hypothesis specifies actual derivatives along
matrix columns; no integration identity is assumed. -/
theorem gaussianLaw_stein {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p)
    {g : Vector p → ℝ} {dg : Vector p → Vector p}
    (hgderiv : ∀ x r, HasDerivAt
      (fun t : ℝ => g (x + t • (fun k => A k r)))
      (∑ k, A k r * dg x k) 0)
    (hgmeas : Measurable g) (hdgmeas : ∀ k, Measurable (fun x => dg x k))
    (hgbounded : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hdgbounded : ∃ D : ℝ, ∀ x k, |dg x k| ≤ D) :
    (∫ x, x j * g x ∂gaussianLaw A) =
      ∑ k, (A * A.transpose) j k * ∫ x, dg x k ∂gaussianLaw A := by
  classical
  obtain ⟨C, hC⟩ := hgbounded
  obtain ⟨D, hD⟩ := hdgbounded
  have hgcompmeas : Measurable (fun z => g (A.mulVec z)) :=
    hgmeas.comp (measurable_mulVec A)
  have hdgcompmeas (k : Fin p) : Measurable (fun z => dg (A.mulVec z) k) :=
    (hdgmeas k).comp (measurable_mulVec A)
  have hdgcompint (k : Fin p) :
      Integrable (fun z : Vector p => dg (A.mulVec z) k) (standardGaussian p) := by
    apply (integrable_const D).mono' (hdgcompmeas k).aestronglyMeasurable
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hD (A.mulVec z) k)
  have hxgint (r : Fin p) :
      Integrable (fun z : Vector p => z r * g (A.mulVec z)) (standardGaussian p) := by
    have hi := (standardGaussian_integrable_coordinate p r).bdd_mul
      hgcompmeas.aestronglyMeasurable
      ⟨C, fun z => by simpa only [Real.norm_eq_abs] using hC (A.mulVec z)⟩
    simpa only [mul_comm] using hi
  have hstein (r : Fin p) :
      (∫ z : Vector p, z r * g (A.mulVec z) ∂standardGaussian p) =
        ∑ k, A k r * ∫ z : Vector p, dg (A.mulVec z) k ∂standardGaussian p := by
    have hh : (∫ z : Vector p, z r * g (A.mulVec z) ∂standardGaussian p) =
        ∫ z : Vector p, ∑ k, A k r * dg (A.mulVec z) k ∂standardGaussian p := by
      apply standardGaussian_coordinate_stein
      · intro z
        have hgd : HasDerivAt
            (fun u : ℝ => g (A.mulVec z + u • (fun k => A k r)))
            (∑ k, A k r * dg (A.mulVec z) k) (z r - z r) := by
          simpa only [sub_self] using hgderiv (A.mulVec z) r
        have hcomp := hgd.comp (h := fun t : ℝ => t - z r) (z r) ((hasDerivAt_id (z r)).sub_const (z r))
        simpa only [mulVec_update, Function.comp_apply, one_mul, mul_one] using hcomp
      · exact hgcompmeas
      · exact Finset.measurable_sum Finset.univ
          (fun k _ => (hdgcompmeas k).const_mul (A k r))
      · exact ⟨C, fun z => hC (A.mulVec z)⟩
      · refine ⟨(∑ k, |A k r|) * D, fun z => ?_⟩
        calc
          _ ≤ ∑ k, |A k r * dg (A.mulVec z) k| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k, |A k r| * D := Finset.sum_le_sum (fun k _ => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hD (A.mulVec z) k) (abs_nonneg _))
          _ = _ := by rw [Finset.sum_mul]
    rw [hh, integral_finset_sum Finset.univ
      (fun k _ => (hdgcompint k).const_mul (A k r))]
    simp only [integral_const_mul]
  have hprod (z : Vector p) : A.mulVec z j * g (A.mulVec z) =
      ∑ r, A j r * (z r * g (A.mulVec z)) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  have hleftmap :
      (∫ x, x j * g x ∂gaussianLaw A) =
        ∫ z : Vector p, A.mulVec z j * g (A.mulVec z) ∂standardGaussian p := by
    exact integral_map (measurable_mulVec A).aemeasurable
      ((measurable_pi_apply j).mul hgmeas).aestronglyMeasurable
  have hrightmap (k : Fin p) :
      (∫ x, dg x k ∂gaussianLaw A) =
        ∫ z : Vector p, dg (A.mulVec z) k ∂standardGaussian p :=
    integral_map (measurable_mulVec A).aemeasurable (hdgmeas k).aestronglyMeasurable
  rw [hleftmap]
  simp_rw [hrightmap]
  calc
    _ = ∫ z : Vector p, ∑ r, A j r * (z r * g (A.mulVec z))
        ∂standardGaussian p := integral_congr_ae (ae_of_all _ hprod)
    _ = ∑ r, A j r * ∫ z : Vector p, z r * g (A.mulVec z)
        ∂standardGaussian p := by
      rw [integral_finset_sum Finset.univ (fun r _ => (hxgint r).const_mul (A j r))]
      simp only [integral_const_mul]
    _ = ∑ r, A j r * (∑ k, A k r * ∫ z : Vector p,
        dg (A.mulVec z) k ∂standardGaussian p) := by simp_rw [hstein]
    _ = _ := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro r _
      ring

end RectangleCLT
