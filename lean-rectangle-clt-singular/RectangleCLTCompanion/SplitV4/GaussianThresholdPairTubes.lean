import RectangleCLTCompanion.SplitV4.GaussianThresholdPairData
import RectangleCLTCompanion.SplitV4.GaussianThresholdTubeGeometry
import RectangleCLTCompanion.SplitV4.GaussianPairSections
import RectangleCLTCompanion.SplitV4.GaussianThresholdPairCoarea

/-! Actual two-dimensional normal fibers for the adaptive hard Gaussian
ridge tubes. All densities, translations and integrability are genuine. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace NNReal ENNReal

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem normalPair_eq_withDensity :
    (gaussianReal 0 1).prod (gaussianReal 0 1) =
      ((volume : Measure ℝ).prod volume).withDensity
        (fun st : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal 0 1 st.1 * gaussianPDFReal 0 1 st.2)) := by
  rw [gaussianReal_of_var_ne_zero 0 (by simp : (1 : ℝ≥0) ≠ 0),
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
  congr 1
  funext st
  exact (ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)).symm

theorem normalPair_integral_density (F : ℝ × ℝ → ℝ) :
    (∫ st, F st ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ st : ℝ × ℝ, (gaussianPDFReal 0 1 st.1 * gaussianPDFReal 0 1 st.2) * F st
        ∂((volume : Measure ℝ).prod volume) := by
  have hm : Measurable (fun st : ℝ × ℝ => ENNReal.ofReal
      (gaussianPDFReal 0 1 st.1 * gaussianPDFReal 0 1 st.2)) :=
    (((measurable_gaussianPDFReal 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDFReal 0 1).comp measurable_snd)).ennreal_ofReal
  rw [normalPair_eq_withDensity, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (mul_nonneg (gaussianPDFReal_nonneg _ _ _)
    (gaussianPDFReal_nonneg _ _ _)), smul_eq_mul]

theorem normalPair_integrable_density_iff (F : ℝ × ℝ → ℝ) :
    Integrable F ((gaussianReal 0 1).prod (gaussianReal 0 1)) ↔
      Integrable (fun st : ℝ × ℝ => (gaussianPDFReal 0 1 st.1 * gaussianPDFReal 0 1 st.2) * F st)
        ((volume : Measure ℝ).prod volume) := by
  rw [normalPair_eq_withDensity]
  have hm : Measurable (fun st : ℝ × ℝ => ENNReal.ofReal
      (gaussianPDFReal 0 1 st.1 * gaussianPDFReal 0 1 st.2)) :=
    (((measurable_gaussianPDFReal 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDFReal 0 1).comp measurable_snd)).ennreal_ofReal
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (gaussianPDFReal_nonneg _ _ _)
    (gaussianPDFReal_nonneg _ _ _)), smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure ℝ).prod volume) hm
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (g := F))

/-- An actual two-normal integral dominates any matching nonnegative
measurable finite fiber, with both normal densities retained. -/
theorem normalPair_integral_dominates_translated_fiber
    (F W : ℝ × ℝ → ℝ) (hFi : Integrable F ((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (hF0 : ∀ st, 0 ≤ F st) (a : ℝ × ℝ) (D : Set (ℝ × ℝ)) (hD : MeasurableSet D)
    (hmatch : ∀ st ∈ D, F (a + st) = W st) :
    (∫ st in D, W st * gaussianPDFReal 0 1 (a.1 + st.1) * gaussianPDFReal 0 1 (a.2 + st.2)
      ∂((volume : Measure ℝ).prod volume)) ≤
      ∫ st, F st ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have hiD := (normalPair_integrable_density_iff F).mp hFi
  have his := hiD.comp_add_left a
  calc
    _ = ∫ st in D, (gaussianPDFReal 0 1 (a.1 + st.1) * gaussianPDFReal 0 1 (a.2 + st.2)) *
        F (a + st) ∂((volume : Measure ℝ).prod volume) := by
      apply setIntegral_congr_fun hD
      intro st hst
      dsimp only
      rw [hmatch st hst]
      ring
    _ ≤ ∫ st : ℝ × ℝ,
        (gaussianPDFReal 0 1 (a.1 + st.1) * gaussianPDFReal 0 1 (a.2 + st.2)) * F (a + st)
        ∂((volume : Measure ℝ).prod volume) :=
      setIntegral_le_integral his (ae_of_all _ (fun st => mul_nonneg
        (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)) (hF0 _)))
    _ = ∫ st : ℝ × ℝ, (gaussianPDFReal 0 1 st.1 * gaussianPDFReal 0 1 st.2) * F st
        ∂((volume : Measure ℝ).prod volume) :=
      integral_add_left_eq_self (μ := (volume : Measure ℝ).prod volume)
        (fun st : ℝ × ℝ => (gaussianPDFReal 0 1 st.1 * gaussianPDFReal 0 1 st.2) * F st) a
    _ = _ := (normalPair_integral_density F).symm

/-- Weighted ridge-fiber mass in genuine standard-normal plane coordinates.
The radius is evaluated at the full ambient section point. -/
theorem thresholdRidge_fiber_lower {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (a c : ℝ) (x : Vector r)
    (hx : faceDot (thresholdPairBisector u j l) x = a)
    (hy : faceDot (thresholdPairDifference u j l) x = c) :
    Real.exp (-(3 : ℝ) / 2) * thresholdProjectionRadius u x *
        ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ *
        gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c / 2048 ≤
      ∫ st in SignedSurface.ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
          (1 / (4 * thresholdProjectionRadius u x)),
        thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l +
          st.2 • thresholdPairDifference u j l) ^ 3 * gaussianPDFReal 0 1 (a + st.1) *
          gaussianPDFReal 0 1 (c + st.2) ∂((volume : Measure ℝ).prod volume) := by
  let U := projectionEuclideanVector (u j)
  let V := projectionEuclideanVector (u l)
  let e := SignedSurface.bisector U V
  let f := SignedSurface.differenceDirection U V
  let X := projectionEuclideanVector x
  have hU : ‖U‖ = 1 := thresholdEuclideanNormal_unit _ hu
  have hV : ‖V‖ = 1 := thresholdEuclideanNormal_unit _ hv
  have he : ‖e‖ = 1 := SignedSurface.norm_bisector _ _ hp
  have hf : ‖f‖ = 1 := SignedSurface.norm_differenceDirection _ _ hm
  have hef : ⟪e, f⟫_ℝ = 0 := SignedSurface.inner_bisector_differenceDirection _ _ (hU.trans hV.symm)
  have hfe : ⟪f, e⟫_ℝ = 0 := by rw [real_inner_comm]; exact hef
  have hUmem : U ∈ thresholdPairSpan u (j, l) := by
    apply Submodule.subset_span
    exact ⟨0, by simp [U]⟩
  have hVmem : V ∈ thresholdPairSpan u (j, l) := by
    apply Submodule.subset_span
    exact ⟨1, by simp [V]⟩
  have hemem : e ∈ thresholdPairSpan u (j, l) :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ hUmem hVmem)
  have hfmem : f ∈ thresholdPairSpan u (j, l) :=
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hUmem hVmem)
  have ha : |a| ≤ thresholdProjectionRadius u x := by
    have hh := thresholdProjectionRadius_abs_inner_le u (j, l) hemem x
    have heq : ⟪e, X⟫_ℝ = faceDot (thresholdPairBisector u j l) x := by
      simp [X, thresholdPairBisector, e, U, V, projectionEuclideanVector, faceDot, PiLp.inner_apply, mul_comm]
    rw [heq, hx, he, one_mul] at hh
    exact hh.trans (by linarith)
  have hc : |c| ≤ thresholdProjectionRadius u x := by
    have hh := thresholdProjectionRadius_abs_inner_le u (j, l) hfmem x
    have heq : ⟪f, X⟫_ℝ = faceDot (thresholdPairDifference u j l) x := by
      simp [X, thresholdPairDifference, f, U, V, projectionEuclideanVector, faceDot, PiLp.inner_apply, mul_comm]
    rw [heq, hy, hf, one_mul] at hh
    exact hh.trans (by linarith)
  have hza : |⟪a • e + c • f, e⟫_ℝ| ≤ euclideanThresholdRadius u X := by
    simpa only [inner_add_left, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq,
      he, one_pow, hfe, mul_one, mul_zero, add_zero] using ha
  have hzc : |⟪a • e + c • f, f⟫_ℝ| ≤ euclideanThresholdRadius u X := by
    simpa only [inner_add_left, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq,
      hf, one_pow, hef, mul_one, mul_zero, zero_add] using hc
  have hh := adaptive_ridge_gaussian_integral_lower (euclideanThresholdRadius u)
    (continuous_euclideanThresholdRadius u) (euclideanThresholdRadius_ge_one u)
    (euclideanThresholdRadius_add_le u) X U V (a • e + c • f) hU hV hp hm hza hzc
  let d := (Real.sqrt (2 * Real.pi))⁻¹ ^ 2
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hnorm (s t : ℝ) : ‖s • e + t • f‖ ^ 2 = s ^ 2 + t ^ 2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, he, hf, mul_one, sq_abs,
      inner_smul_left, inner_smul_right, conj_trivial, hef, mul_zero, zero_mul, add_zero]
  have hpdf (s t : ℝ) : gaussianPDFReal 0 1 s * gaussianPDFReal 0 1 t =
      d * SignedSurface.gaussianKernel (s • e + t • f) := by
    rw [SignedSurface.gaussianKernel, hnorm]
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, d]
    rw [mul_mul_mul_comm, ← Real.exp_add]
    congr 1
    · exact (pow_two _).symm
    · congr 1
      ring
  have hint : (∫ st in SignedSurface.ridgeRectangle U V (1 / (4 * thresholdProjectionRadius u x)),
      thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l + st.2 • thresholdPairDifference u j l) ^ 3 *
        gaussianPDFReal 0 1 (a + st.1) * gaussianPDFReal 0 1 (c + st.2)
        ∂((volume : Measure ℝ).prod volume)) =
      d * ∫ st in SignedSurface.ridgeRectangle U V (1 / (4 * euclideanThresholdRadius u X)),
        euclideanThresholdRadius u (X + SignedSurface.ridgeDisplacement U V st) ^ 3 *
          SignedSurface.gaussianKernel (a • e + c • f + SignedSurface.ridgeDisplacement U V st)
          ∂((volume : Measure ℝ).prod volume) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with st
    have hplane : a • e + c • f + SignedSurface.ridgeDisplacement U V st =
        (a + st.1) • e + (c + st.2) • f := by
      dsimp only [SignedSurface.ridgeDisplacement, e, f]
      module
    rw [hplane]
    have hr : euclideanThresholdRadius u (X + SignedSurface.ridgeDisplacement U V st) =
        thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l + st.2 • thresholdPairDifference u j l) := by
      change thresholdProjectionRadius u (fun k => (X + SignedSurface.ridgeDisplacement U V st) k) = _
      congr 1
      funext k
      simp only [X, SignedSurface.ridgeDisplacement, PiLp.add_apply, PiLp.smul_apply,
        U, V, e, f, thresholdPairBisector, thresholdPairDifference, projectionEuclideanVector,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      change x k + (st.1 * e k + st.2 * f k) = (x k + st.1 * e k) + st.2 * f k
      ring
    rw [hr]
    rw [show thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l + st.2 • thresholdPairDifference u j l) ^ 3 *
        gaussianPDFReal 0 1 (a + st.1) * gaussianPDFReal 0 1 (c + st.2) =
      thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l + st.2 • thresholdPairDifference u j l) ^ 3 *
        (gaussianPDFReal 0 1 (a + st.1) * gaussianPDFReal 0 1 (c + st.2)) by ring, hpdf]
    ring
  rw [hint]
  have hRbase : euclideanThresholdRadius u X = thresholdProjectionRadius u x := rfl
  rw [hRbase] at hh
  have hmul := mul_le_mul_of_nonneg_left hh hd
  calc
    _ = Real.exp (-(3 : ℝ) / 2) * thresholdProjectionRadius u x * ‖U - V‖ *
        (gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c) / 2048 := by ring
    _ = d * (Real.exp (-(3 : ℝ) / 2) * SignedSurface.gaussianKernel (a • e + c • f) *
        (thresholdProjectionRadius u x * ‖U - V‖ / 2048)) := by rw [hpdf]; ring
    _ ≤ _ := hmul

theorem thresholdPairBisector_abs_le_radius {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0) (x : Vector r) :
    |faceDot (thresholdPairBisector u j l) x| ≤ thresholdProjectionRadius u x - 1 := by
  let U := projectionEuclideanVector (u j)
  let V := projectionEuclideanVector (u l)
  have hU : U ∈ thresholdPairSpan u (j, l) := by apply Submodule.subset_span; exact ⟨0, by simp [U]⟩
  have hV : V ∈ thresholdPairSpan u (j, l) := by apply Submodule.subset_span; exact ⟨1, by simp [V]⟩
  have hm : SignedSurface.bisector U V ∈ thresholdPairSpan u (j, l) :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ hU hV)
  have hh := thresholdProjectionRadius_abs_inner_le u (j, l) hm x
  rw [SignedSurface.norm_bisector _ _ hp, one_mul] at hh
  simpa only [SignedSurface.faceDot_eq_euclidean_inner, thresholdPairBisector_euclidean] using hh

theorem gaussianPairSectionPoint_comp {r : ℕ} (e f : Vector r)
    (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1) (hef : faceDot e f = 0)
    (a c s t : ℝ) (g : Vector r) :
    gaussianPairSectionPoint e f a c (gaussianPairSectionPoint e f s t g) =
      gaussianPairSectionPoint e f a c g := by
  have hl := gaussianPairSectionPoint_levels e f s t g he hf hef
  rw [gaussianPairSectionPoint_orthogonal_formula e f hef a c,
    hl.1, hl.2, gaussianPairSectionPoint_orthogonal_formula e f hef s t,
    gaussianPairSectionPoint_orthogonal_formula e f hef a c]
  module

theorem gaussianPairSectionPoint_add_parameters {r : ℕ} (e f : Vector r)
    (hef : faceDot e f = 0) (a c s t : ℝ) (g : Vector r) :
    gaussianPairSectionPoint e f (a + s) (c + t) g =
      gaussianPairSectionPoint e f a c g + s • e + t • f := by
  rw [gaussianPairSectionPoint_orthogonal_formula e f hef,
    gaussianPairSectionPoint_orthogonal_formula e f hef]
  module

theorem gaussianPairEvent_section {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (z : Vector r) (s t : ℝ) :
    gaussianPairSectionPoint (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairFirstLevel u b j l + s) (thresholdPairSecondLevel u b j l + t) z ∈
        gaussianPairEvent u b j l ↔
      (∀ k, k ≠ j → k ≠ l → faceDot (u k) (gaussianPairBase u b j l z) < b k) ∧
      (s, t) ∈ SignedSurface.ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l z))) := by
  have he := thresholdPairBisector_unit u j l hp
  have hf := thresholdPairDifference_unit u j l hm
  have hef := thresholdPair_frame_orthogonal u j l hu hv
  have hl := gaussianPairSectionPoint_levels (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l + s) (thresholdPairSecondLevel u b j l + t) z he hf hef
  simp only [gaussianPairEvent, Set.mem_setOf_eq, gaussianPairBase,
    gaussianPairSectionPoint_comp _ _ he hf hef, hl.1, hl.2, add_sub_cancel_left]

/-- Actual pair-event mass, before identifying its section probability with
the mixed CDF derivative. The coefficient is the true bisector level. -/
theorem gaussianPairEvent_weighted_mass {m n : ℕ}
    (hmfaces : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    (Real.exp (-(3 : ℝ) / 2) *
      ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ *
      |thresholdPairFirstLevel u b j l| * gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) / 2048) *
        (standardGaussian (n + 1)).real {z | ∀ k, k ≠ j → k ≠ l →
          faceDot (u k) (gaussianPairBase u b j l z) < b k} ≤
      ∫ g, (gaussianPairEvent u b j l).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  let F : Vector (n + 1) → ℝ :=
    (gaussianPairEvent u b j l).indicator (fun g => thresholdProjectionRadius u g ^ 3)
  have hF : Measurable F := ((measurable_thresholdProjectionRadius u).pow_const 3).indicator
    (measurableSet_gaussianPairEvent u b j l)
  have hFi : Integrable F (standardGaussian (n + 1)) :=
    (thresholdProjectionRadius_moment hmfaces u 3).1.indicator (measurableSet_gaussianPairEvent u b j l)
  have hF0 (g) : 0 ≤ F g := Set.indicator_nonneg (fun x _ =>
    pow_nonneg (zero_le_one.trans (thresholdProjectionRadius_ge_one u x)) 3) g
  let e := thresholdPairBisector u j l
  let f := thresholdPairDifference u j l
  let a := thresholdPairFirstLevel u b j l
  let c := thresholdPairSecondLevel u b j l
  have he : vectorNormSq e = 1 := thresholdPairBisector_unit u j l hp
  have hf : vectorNormSq f = 1 := thresholdPairDifference_unit u j l hm
  have hef : faceDot e f = 0 := thresholdPair_frame_orthogonal u j l hu hv
  have hprod := (integrable_gaussianPairSectionMap_iff e f he hf F hF).mpr hFi
  let V : Set (Vector (n + 1)) := {z | ∀ k, k ≠ j → k ≠ l →
    faceDot (u k) (gaussianPairBase u b j l z) < b k}
  have hV : MeasurableSet V := by
    unfold V
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
      measurableSet_lt ((measurable_thresholdDot _).comp (measurable_gaussianPairBase u b j l)) measurable_const)))
  let d := Real.exp (-(3 : ℝ) / 2) *
    ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ * |a| *
      gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c / 2048
  have hpoint : ∀ᵐ z ∂standardGaussian (n + 1),
      V.indicator (fun _ => d) z ≤ ∫ st, F (gaussianPairSectionPoint e f st.1 st.2 z)
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
    filter_upwards [hprod.prod_left_ae] with z hz
    by_cases hzV : z ∈ V
    · rw [Set.indicator_of_mem hzV]
      have hl := gaussianPairBase_frame_levels u b j l hu hv hp hm z
      have hbnd := thresholdRidge_fiber_lower u j l hu hv hp hm a c (gaussianPairBase u b j l z) hl.1 hl.2
      have ha : |a| ≤ thresholdProjectionRadius u (gaussianPairBase u b j l z) := by
        have hh := thresholdPairBisector_abs_le_radius u j l hp (gaussianPairBase u b j l z)
        rw [hl.1] at hh
        exact hh.trans (by linarith)
      have hcoef : d ≤ Real.exp (-(3 : ℝ) / 2) * thresholdProjectionRadius u (gaussianPairBase u b j l z) *
          ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ *
          gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c / 2048 := by
        have hc0 : 0 ≤ Real.exp (-(3 : ℝ) / 2) *
            ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ *
            gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c / 2048 := by
          exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
            (gaussianPDFReal_nonneg _ _ _)) (gaussianPDFReal_nonneg _ _ _)) (by norm_num)
        have hh := mul_le_mul_of_nonneg_right ha hc0
        convert hh using 1 <;> dsimp only [d] <;> ring
      apply hcoef.trans (hbnd.trans ?_)
      apply normalPair_integral_dominates_translated_fiber
        (fun st => F (gaussianPairSectionPoint e f st.1 st.2 z))
        (fun st => thresholdProjectionRadius u (gaussianPairBase u b j l z + st.1 • e + st.2 • f) ^ 3)
        hz (fun st => hF0 _) (a, c)
        (SignedSurface.ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
          (1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l z))))
        (isCompact_Icc.prod isCompact_Icc).measurableSet
      intro st hst
      have hmem : gaussianPairSectionPoint e f (a + st.1) (c + st.2) z ∈ gaussianPairEvent u b j l :=
        (gaussianPairEvent_section u b j l hu hv hp hm z st.1 st.2).mpr ⟨hzV, hst⟩
      dsimp only [Prod.fst_add, Prod.snd_add, F]
      rw [Set.indicator_of_mem hmem, gaussianPairSectionPoint_add_parameters e f hef]
      rfl
    · rw [Set.indicator_of_not_mem hzV]
      exact integral_nonneg (fun st => hF0 _)
  have hh := integral_mono_ae ((integrable_const d).indicator hV) hprod.integral_prod_right hpoint
  rw [integral_indicator_const _ hV, smul_eq_mul, mul_comm] at hh
  apply hh.trans_eq
  rw [← integral_prod_symm _ hprod]
  exact integral_gaussianPairSectionMap e f he hf F hF

/-- Exact cancellation of the pair angle in the actual mixed-derivative
coefficient, expressed in the bisector frame. -/
theorem thresholdPair_coefficient_identity {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ *
        |thresholdPairFirstLevel u b j l| =
      (1 - faceDot (u j) (u l)) * |b j + b l| /
        Real.sqrt (1 - faceDot (u j) (u l) ^ 2) := by
  let U := projectionEuclideanVector (u j)
  let V := projectionEuclideanVector (u l)
  have hU : ‖U‖ = 1 := thresholdEuclideanNormal_unit _ hu
  have hV : ‖V‖ = 1 := thresholdEuclideanNormal_unit _ hv
  have ha : 0 < ‖U + V‖ := norm_pos_iff.mpr hp
  have hd : 0 < ‖U - V‖ := norm_pos_iff.mpr hm
  have hdot : ⟪U, V⟫_ℝ = faceDot (u j) (u l) := by
    simpa only [U, V] using (SignedSurface.faceDot_eq_euclidean_inner (u j) (u l)).symm
  have hprod := SignedSurface.norm_sum_mul_norm_sub U V hU hV hp hm
  rw [hdot] at hprod
  have hs : 0 < Real.sqrt (1 - faceDot (u j) (u l) ^ 2) := by nlinarith [mul_pos ha hd]
  have hdq : ‖U - V‖ ^ 2 = 2 - 2 * faceDot (u j) (u l) := by
    have hh := norm_sub_sq_real U V
    rw [hU, hV, hdot] at hh
    nlinarith
  have hcoef : ‖U - V‖ / ‖U + V‖ =
      (1 - faceDot (u j) (u l)) / Real.sqrt (1 - faceDot (u j) (u l) ^ 2) := by
    apply (div_eq_div_iff ha.ne' hs.ne').mpr
    nlinarith
  rw [thresholdPairFirstLevel, abs_div, abs_of_pos ha]
  calc
    _ = (‖U - V‖ / ‖U + V‖) * |b j + b l| := by ring
    _ = _ := by rw [hcoef]; ring

/-- The actual paired mixed-derivative term is controlled by the genuine
weighted adaptive pair event, with no inverse correlation-gap constant. -/
theorem gaussianThresholdMixed_le_weighted_pair_event {m n : ℕ}
    (hmfaces : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m) (hjl : j ≠ l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1) (hi : LinearIndependent ℝ u) :
    Real.exp (-(3 : ℝ) / 2) * (1 - faceDot (u j) (u l)) * |b j + b l| *
        gaussianThresholdMixed u b j l / 2048 ≤
      ∫ g, (gaussianPairEvent u b j l).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  obtain ⟨hp, hm⟩ := thresholdPair_sum_sub_ne_zero_of_independent u hi j l hjl
  have hh := gaussianPairEvent_weighted_mass hmfaces u b j l hu hv hp hm
  rw [gaussianThresholdMixed_eq_pairBase u b j l hjl hu hv hi]
  have hcoef := thresholdPair_coefficient_identity u b j l hu hv hp hm
  have heq : Real.exp (-(3 : ℝ) / 2) * (1 - faceDot (u j) (u l)) * |b j + b l| *
      ((gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) /
          Real.sqrt (1 - faceDot (u j) (u l) ^ 2)) *
        (standardGaussian (n + 1)).real {z | ∀ k, k ≠ j → k ≠ l →
          faceDot (u k) (gaussianPairBase u b j l z) < b k}) / 2048 =
      (Real.exp (-(3 : ℝ) / 2) *
        ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ *
        |thresholdPairFirstLevel u b j l| * gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l) *
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) / 2048) *
        (standardGaussian (n + 1)).real {z | ∀ k, k ≠ j → k ≠ l →
          faceDot (u k) (gaussianPairBase u b j l z) < b k} := by
    rw [show Real.exp (-(3 : ℝ) / 2) *
        ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ *
        |thresholdPairFirstLevel u b j l| =
      Real.exp (-(3 : ℝ) / 2) *
        (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ *
          |thresholdPairFirstLevel u b j l|) by ring, hcoef]
    ring
  rwa [heq]

end
end RectangleCLT.Companion.SplitV4
