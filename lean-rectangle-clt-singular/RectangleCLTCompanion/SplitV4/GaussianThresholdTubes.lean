import RectangleCLTCompanion.SplitV4.AveragedThreshold
import RectangleCLTCompanion.SplitV4.GaussianThresholdSections
import RectangleCLTCompanion.SplitV4.GaussianThresholdDerivatives

/-! Genuine ambient Gaussian transport for the hard adaptive threshold
tubes. Orthogonal Gaussian section maps are measure preserving, so their
use extends from bounded tests to actual integrable cubic radius weights. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace NNReal ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def gaussianNormalSectionMap {r : ℕ} (u : Vector r) (z : ℝ × Vector r) : Vector r :=
  SignedSurface.gaussianSectionPoint u z.1 z.2

theorem measurable_gaussianNormalSectionMap {r : ℕ} (u : Vector r) :
    Measurable (gaussianNormalSectionMap u) := by
  apply measurable_pi_lambda
  intro j
  change Measurable (fun z : ℝ × Vector r =>
    z.1 * u j + (z.2 j - faceDot u z.2 * u j))
  exact (measurable_fst.mul_const _).add
    (((measurable_pi_apply j).comp measurable_snd).sub
      (((measurable_thresholdDot u).comp measurable_snd).mul_const _))

/-- A true Gaussian pushforward identity, proved on all measurable sets
using the concrete orthogonal-section disintegration. -/
theorem gaussianNormalSectionMap_measurePreserving {n : ℕ}
    (u : Vector (n + 1)) (hu : vectorNormSq u = 1) :
    MeasurePreserving (gaussianNormalSectionMap u)
      ((gaussianReal 0 1).prod (standardGaussian (n + 1))) (standardGaussian (n + 1)) := by
  refine ⟨measurable_gaussianNormalSectionMap u, ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_gaussianNormalSectionMap u) hA]
  apply (ENNReal.toReal_eq_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  let f : Vector (n + 1) → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hA
  have hb : ∀ g, |f g| ≤ (1 : ℝ) := by
    intro g
    by_cases hg : g ∈ A <;> simp [f, hg]
  have hi : Integrable (fun z : ℝ × Vector (n + 1) => f (gaussianNormalSectionMap u z))
      ((gaussianReal 0 1).prod (standardGaussian (n + 1))) := by
    apply (integrable_const (1 : ℝ)).mono'
      (hf.comp (measurable_gaussianNormalSectionMap u)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb _)
  have hh := standardGaussian_integral_section_product (0 : Fin (n + 1)) u hu f hf 1 hb
  have hprod := integral_prod (fun z : ℝ × Vector (n + 1) => f (gaussianNormalSectionMap u z)) hi
  have hleft : (∫ z : ℝ × Vector (n + 1), f (gaussianNormalSectionMap u z)
      ∂((gaussianReal 0 1).prod (standardGaussian (n + 1)))) =
      ((gaussianReal 0 1).prod (standardGaussian (n + 1))).real
        ((gaussianNormalSectionMap u) ⁻¹' A) := by
    change (∫ z, ((gaussianNormalSectionMap u) ⁻¹' A).indicator (fun _ => (1 : ℝ)) z
      ∂((gaussianReal 0 1).prod (standardGaussian (n + 1)))) = _
    rw [integral_indicator_const _ (hA.preimage (measurable_gaussianNormalSectionMap u)),
      smul_eq_mul, mul_one]
  have hright : (∫ z, f z ∂standardGaussian (n + 1)) = (standardGaussian (n + 1)).real A := by
    rw [integral_indicator_const _ hA, smul_eq_mul, mul_one]
  exact hleft.symm.trans (hprod.trans (hh.symm.trans hright))

/-- Actual integrability transport through the normal/residual Gaussian
product. This is available for unbounded cubic-radius-weighted tube tests. -/
theorem integrable_gaussianNormalSectionMap_iff {n : ℕ}
    (u : Vector (n + 1)) (hu : vectorNormSq u = 1)
    (F : Vector (n + 1) → ℝ) (hF : Measurable F) :
    Integrable (fun z : ℝ × Vector (n + 1) => F (gaussianNormalSectionMap u z))
      ((gaussianReal 0 1).prod (standardGaussian (n + 1))) ↔
      Integrable F (standardGaussian (n + 1)) :=
  (gaussianNormalSectionMap_measurePreserving u hu).integrable_comp hF.aestronglyMeasurable

theorem integral_gaussianNormalSectionMap {n : ℕ}
    (u : Vector (n + 1)) (hu : vectorNormSq u = 1)
    (F : Vector (n + 1) → ℝ) (hF : Measurable F) :
    (∫ z : ℝ × Vector (n + 1), F (gaussianNormalSectionMap u z)
      ∂((gaussianReal 0 1).prod (standardGaussian (n + 1)))) =
      ∫ g, F g ∂standardGaussian (n + 1) := by
  have hh := integral_map
    (μ := (gaussianReal 0 1).prod (standardGaussian (n + 1)))
    (measurable_gaussianNormalSectionMap u).aemeasurable hF.aestronglyMeasurable
  rw [(gaussianNormalSectionMap_measurePreserving u hu).map_eq] at hh
  exact hh.symm

def euclideanThresholdRadius {m r : ℕ} (u : Fin m → Vector r)
    (x : EuclideanSpace ℝ (Fin r)) : ℝ := thresholdProjectionRadius u (fun j => x j)

theorem continuous_euclideanThresholdRadius {m r : ℕ} (u : Fin m → Vector r) :
    Continuous (euclideanThresholdRadius u) :=
  (continuous_thresholdProjectionRadius u).comp (PiLp.continuous_equiv 2 _)

theorem euclideanThresholdRadius_ge_one {m r : ℕ} (u : Fin m → Vector r)
    (x : EuclideanSpace ℝ (Fin r)) : 1 ≤ euclideanThresholdRadius u x :=
  thresholdProjectionRadius_ge_one u _

theorem euclideanThresholdRadius_add_le {m r : ℕ} (u : Fin m → Vector r)
    (x d : EuclideanSpace ℝ (Fin r)) :
    euclideanThresholdRadius u (x + d) ≤ euclideanThresholdRadius u x + ‖d‖ := by
  have hd : projectionEuclideanVector (fun j => d j) = d := by ext j; rfl
  simpa only [euclideanThresholdRadius, hd] using
    thresholdProjectionRadius_add_le u (fun j => x j) (fun j => d j)

theorem thresholdEuclideanNormal_unit {r : ℕ} (v : Vector r) (hv : vectorNormSq v = 1) :
    ‖projectionEuclideanVector v‖ = 1 := by
  have hs := SignedSurface.vectorNormSq_eq_euclidean_norm_sq v
  rw [hv] at hs
  change 1 = ‖projectionEuclideanVector v‖ ^ 2 at hs
  nlinarith [norm_nonneg (projectionEuclideanVector v)]

/-- A normal-fiber bound using the actual standard-normal density and
the actual threshold radius at the full section point. -/
theorem thresholdFacet_fiber_lower {m r : ℕ}
    (u : Fin m → Vector r) (j : Fin m) (hu : vectorNormSq (u j) = 1)
    (b : ℝ) (x : Vector r) (hx : faceDot (u j) x = b) :
    Real.exp (-(3 : ℝ) / 2) * (1 + b ^ 2) * gaussianPDFReal 0 1 b / 32 ≤
      ∫ t in Set.Icc (0 : ℝ) (1 / (4 * thresholdProjectionRadius u x)),
        thresholdProjectionRadius u (x + t • u j) ^ 3 * gaussianPDFReal 0 1 (b + t) := by
  let v := projectionEuclideanVector (u j)
  let X := projectionEuclideanVector x
  have hv : ‖v‖ = 1 := thresholdEuclideanNormal_unit _ hu
  have hR : euclideanThresholdRadius u X = thresholdProjectionRadius u x := rfl
  have hb : |b| ≤ thresholdProjectionRadius u x - 1 := by
    simpa only [hx] using thresholdProjectionRadius_face_le u j hv x
  have hRx := thresholdProjectionRadius_ge_one u x
  have hsq : 1 + b ^ 2 ≤ thresholdProjectionRadius u x ^ 2 := by
    nlinarith [abs_nonneg b, sq_abs b]
  have hz : |⟪b • v, v⟫_ℝ| ≤ euclideanThresholdRadius u X := by
    simpa only [inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq, hv,
      one_pow, mul_one, hR] using hb.trans (by linarith)
  have hh := adaptive_facet_gaussian_integral_lower (euclideanThresholdRadius u)
    (continuous_euclideanThresholdRadius u) (euclideanThresholdRadius_ge_one u)
    (euclideanThresholdRadius_add_le u) X v (b • v) hv hz
  let c := (Real.sqrt (2 * Real.pi))⁻¹
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hpdf (t : ℝ) : gaussianPDFReal 0 1 t = c * SignedSurface.gaussianKernel (t • v) := by
    simp only [SignedSurface.gaussianKernel, norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs]
    simp only [gaussianPDFReal, c, NNReal.coe_one, mul_one, sub_zero]
  have hint : (∫ t in Set.Icc (0 : ℝ) (1 / (4 * thresholdProjectionRadius u x)),
      thresholdProjectionRadius u (x + t • u j) ^ 3 * gaussianPDFReal 0 1 (b + t)) =
      c * ∫ t in Set.Icc (0 : ℝ) (1 / (4 * euclideanThresholdRadius u X)),
        euclideanThresholdRadius u (X + t • v) ^ 3 *
          SignedSurface.gaussianKernel (b • v + t • v) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by
      dsimp only
      rw [hpdf, ← add_smul]
      change thresholdProjectionRadius u (x + t • u j) ^ 3 *
          (c * SignedSurface.gaussianKernel ((b + t) • v)) =
        c * (thresholdProjectionRadius u (x + t • u j) ^ 3 *
          SignedSurface.gaussianKernel ((b + t) • v))
      ring)
  rw [hint, hpdf]
  have h0 := mul_le_mul_of_nonneg_left hh hc
  calc
    _ ≤ c * (Real.exp (-(3 : ℝ) / 2) * SignedSurface.gaussianKernel (b • v) *
        (euclideanThresholdRadius u X ^ 2 / 32)) := by
      rw [hR]
      have hn : 0 ≤ Real.exp (-(3 : ℝ) / 2) * c * SignedSurface.gaussianKernel (b • v) :=
        mul_nonneg (mul_nonneg (Real.exp_pos _).le hc) (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left hsq hn]
    _ ≤ _ := h0

/-- Strict inactive faces have the same true section probability as closed
inactive faces, because all remaining residual hyperplanes have zero mass. -/
theorem gaussianThresholdSectionProbability_eq_strict {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hi : LinearIndependent ℝ u) (t : ℝ) :
    gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) t =
      (standardGaussian r).real {z | ∀ l, l ≠ j →
        faceDot (u l) (SignedSurface.gaussianSectionPoint (u j) t z) < b l} := by
  classical
  have hn := gaussianFiniteThresholdEvent_ae_no_boundary (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l))
    (fun l hl => gaussianNormalProjection_ne_zero_of_independent u hi j l (Finset.mem_erase.mp hl).1)
    (fun l => b l - t * faceDot (u l) (u j))
  rw [gaussianThresholdSectionProbability_eq_section]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hn] with z hz
  simp only [Set.mem_setOf_eq, Finset.mem_erase, Finset.mem_univ, and_true]
  apply propext
  apply forall_congr'
  intro l
  by_cases hlj : l = j
  · simp [hlj]
  · have hne := hz l (Finset.mem_erase.mpr ⟨hlj, Finset.mem_univ _⟩)
    rw [gaussianSectionPoint_faceDot]
    constructor <;> intro h hlj'
    · have hle := h hlj'
      exact lt_of_le_of_ne hle (by intro he; apply hne; linarith)
    · exact (h hlj').le

theorem gaussianSectionPoint_comp {r : ℕ} (u : Vector r) (hu : vectorNormSq u = 1)
    (a b : ℝ) (z : Vector r) :
    SignedSurface.gaussianSectionPoint u a (SignedSurface.gaussianSectionPoint u b z) =
      SignedSurface.gaussianSectionPoint u a z := by
  rw [SignedSurface.gaussianSectionPoint_eq,
    SignedSurface.gaussianSectionPoint_on_hyperplane u b hu,
    SignedSurface.gaussianSectionPoint_eq, SignedSurface.gaussianSectionPoint_eq]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem gaussianSectionPoint_add_parameter {r : ℕ} (u : Vector r) (b t : ℝ) (z : Vector r) :
    SignedSurface.gaussianSectionPoint u (b + t) z =
      SignedSurface.gaussianSectionPoint u b z + t • u := by
  ext j
  simp only [SignedSurface.gaussianSectionPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A genuine normal integral dominates any matching nonnegative short
fiber, with the density and translation retained explicitly. -/
theorem normal_integral_dominates_translated_fiber
    (F W : ℝ → ℝ) (hFi : Integrable F (gaussianReal 0 1))
    (hF0 : ∀ t, 0 ≤ F t) (b ε : ℝ)
    (hmatch : ∀ t ∈ Set.Ioc (0 : ℝ) ε, F (b + t) = W t) :
    (∫ t in Set.Icc (0 : ℝ) ε, W t * gaussianPDFReal 0 1 (b + t)) ≤
      ∫ t, F t ∂gaussianReal 0 1 := by
  have hiD : Integrable (fun t => gaussianPDFReal 0 1 t * F t) := by
    have hi := hFi
    rw [gaussianReal_of_var_ne_zero 0 (by simp : (1 : ℝ≥0) ≠ 0)] at hi
    have hh := (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ))
      (measurable_gaussianPDF 0 1) (ae_of_all _ (fun _ => gaussianPDF_lt_top)) (g := F)).mp hi
    simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul] using hh
  have his := hiD.comp_add_left b
  calc
    _ = ∫ t in Set.Ioc (0 : ℝ) ε, W t * gaussianPDFReal 0 1 (b + t) := integral_Icc_eq_integral_Ioc
    _ = ∫ t in Set.Ioc (0 : ℝ) ε, gaussianPDFReal 0 1 (b + t) * F (b + t) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      rw [hmatch t ht, mul_comm]
    _ ≤ ∫ t : ℝ, gaussianPDFReal 0 1 (b + t) * F (b + t) :=
      setIntegral_le_integral his (ae_of_all _ (fun t =>
        mul_nonneg (gaussianPDFReal_nonneg _ _ _) (hF0 _)))
    _ = ∫ t : ℝ, gaussianPDFReal 0 1 t * F t :=
      integral_add_left_eq_self (μ := volume) (fun t : ℝ => gaussianPDFReal 0 1 t * F t) b
    _ = _ := by
      rw [integral_gaussianReal_eq_integral_smul (by simp : (1 : ℝ≥0) ≠ 0)]
      rfl

def gaussianFacetBase {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (g : Vector r) : Vector r := SignedSurface.gaussianSectionPoint (u j) (b j) g

def gaussianFacetEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j : Fin m) :
    Set (Vector r) :=
  {g | (∀ l, l ≠ j → faceDot (u l) (gaussianFacetBase u b j g) < b l) ∧
    0 < faceDot (u j) g - b j ∧
    faceDot (u j) g - b j ≤ 1 / (4 * thresholdProjectionRadius u (gaussianFacetBase u b j g))}

theorem measurableSet_gaussianFacetEvent {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) :
    MeasurableSet (gaussianFacetEvent u b j) := by
  have hx : Measurable (gaussianFacetBase u b j) := SignedSurface.measurable_gaussianSectionPoint _ _
  have ht : Measurable (fun g => faceDot (u j) g - b j) :=
    (measurable_thresholdDot _).sub_const _
  have hr : Measurable (fun g => 1 / (4 * thresholdProjectionRadius u (gaussianFacetBase u b j g))) :=
    measurable_const.div (measurable_const.mul ((measurable_thresholdProjectionRadius u).comp hx))
  unfold gaussianFacetEvent
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (MeasurableSet.iInter (fun l => MeasurableSet.iInter (fun _ =>
    measurableSet_lt ((measurable_thresholdDot _).comp hx) measurable_const))).inter
      ((measurableSet_lt measurable_const ht).inter (measurableSet_le ht hr))

theorem gaussianFacetEvent_section {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (z : Vector r) (t : ℝ) :
    SignedSurface.gaussianSectionPoint (u j) t z ∈ gaussianFacetEvent u b j ↔
      (∀ l, l ≠ j → faceDot (u l) (gaussianFacetBase u b j z) < b l) ∧
      0 < t - b j ∧ t - b j ≤ 1 / (4 * thresholdProjectionRadius u (gaussianFacetBase u b j z)) := by
  simp only [gaussianFacetEvent, Set.mem_setOf_eq, gaussianFacetBase,
    gaussianSectionPoint_comp (u j) hu, SignedSurface.gaussianSectionPoint_on_hyperplane (u j) t hu]

/-- Each actual one-face derivative term is controlled by the mass of its
genuine adaptive outward event, weighted by the actual common radius cubed. -/
theorem gaussianThresholdFirst_le_weighted_facet_event {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Real.exp (-(3 : ℝ) / 2) * (1 + b j ^ 2) * gaussianThresholdFirst u b j / 32 ≤
      ∫ g, (gaussianFacetEvent u b j).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  let F : Vector (n + 1) → ℝ :=
    (gaussianFacetEvent u b j).indicator (fun g => thresholdProjectionRadius u g ^ 3)
  have hF : Measurable F := ((measurable_thresholdProjectionRadius u).pow_const 3).indicator
    (measurableSet_gaussianFacetEvent u b j)
  have hFi : Integrable F (standardGaussian (n + 1)) :=
    (thresholdProjectionRadius_moment hm u 3).1.indicator (measurableSet_gaussianFacetEvent u b j)
  have hF0 (g) : 0 ≤ F g := Set.indicator_nonneg (fun x _ =>
    pow_nonneg (zero_le_one.trans (thresholdProjectionRadius_ge_one u x)) 3) g
  have hprod := (integrable_gaussianNormalSectionMap_iff (u j) hu F hF).mpr hFi
  let V : Set (Vector (n + 1)) := {z | ∀ l, l ≠ j → faceDot (u l) (gaussianFacetBase u b j z) < b l}
  have hV : MeasurableSet V := by
    unfold V
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun l => MeasurableSet.iInter (fun _ =>
      measurableSet_lt ((measurable_thresholdDot _).comp
        (SignedSurface.measurable_gaussianSectionPoint _ _)) measurable_const))
  let c := Real.exp (-(3 : ℝ) / 2) * (1 + b j ^ 2) * gaussianPDFReal 0 1 (b j) / 32
  have hpoint : ∀ᵐ z ∂standardGaussian (n + 1),
      V.indicator (fun _ => c) z ≤ ∫ t, F (SignedSurface.gaussianSectionPoint (u j) t z)
        ∂gaussianReal 0 1 := by
    filter_upwards [hprod.prod_left_ae] with z hz
    by_cases hv : z ∈ V
    · rw [Set.indicator_of_mem hv]
      have hbnd := thresholdFacet_fiber_lower u j hu (b j) (gaussianFacetBase u b j z)
        (SignedSurface.gaussianSectionPoint_on_hyperplane _ _ hu z)
      apply hbnd.trans
      apply normal_integral_dominates_translated_fiber
        (fun t => F (SignedSurface.gaussianSectionPoint (u j) t z))
        (fun t => thresholdProjectionRadius u (gaussianFacetBase u b j z + t • u j) ^ 3)
        hz (fun t => hF0 _) (b j) (1 / (4 * thresholdProjectionRadius u (gaussianFacetBase u b j z)))
      intro t ht
      have he : SignedSurface.gaussianSectionPoint (u j) (b j + t) z ∈ gaussianFacetEvent u b j := by
        rw [gaussianFacetEvent_section u b j hu]
        exact ⟨hv, by simpa only [add_sub_cancel_left] using ht⟩
      dsimp only [F]
      rw [Set.indicator_of_mem he, gaussianSectionPoint_add_parameter]
      rfl
    · rw [Set.indicator_of_not_mem hv]
      exact integral_nonneg (fun t => hF0 _)
  have hmineq := integral_mono_ae
    ((integrable_const c).indicator hV) hprod.integral_prod_right hpoint
  have hmass : (∫ z, V.indicator (fun _ => c) z ∂standardGaussian (n + 1)) =
      Real.exp (-(3 : ℝ) / 2) * (1 + b j ^ 2) * gaussianThresholdFirst u b j / 32 := by
    rw [integral_indicator_const _ hV, gaussianThresholdFirst_eq_section u b j hu hi,
      gaussianThresholdSectionProbability_eq_strict u b j hi]
    change (standardGaussian (n + 1)).real V * c = _
    dsimp only [c, V, gaussianFacetBase]
    ring
  rw [hmass] at hmineq
  apply hmineq.trans_eq
  rw [← integral_prod_symm _ hprod]
  exact integral_gaussianNormalSectionMap (u j) hu F hF

end
end RectangleCLT.Companion.SplitV4
