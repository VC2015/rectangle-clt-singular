import RectangleCLT.GaussianTubeEvents
import RectangleCLT.GaussianTubeDifferential
import RectangleCLT.GaussianTubeGamma
import RectangleCLT.GaussianNormalMap

/-! Actual exponential-mixture and augmented-tube integration. The inactive
inequalities are strict; their exact exponential tails agree with the closed
tails. All normalizing factors refer to the concrete probability laws. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology NNReal

namespace RectangleCLT

theorem unitExponential_integral_eq_Ioi (f : ℝ → ℝ) :
    (∫ r, f r ∂unitExponential) = ∫ r in Ioi 0, Real.exp (-r) * f r := by
  change (∫ r, f r ∂volume.withDensity (exponentialPDF 1)) = _
  have hm : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul
    hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have heq : (fun r => (exponentialPDF 1 r).toReal • f r) =
      (Ici (0 : ℝ)).indicator (fun r => Real.exp (-r) * f r) := by
    funext r
    have hreal : (exponentialPDF 1 r).toReal = exponentialPDFReal 1 r :=
      ENNReal.toReal_ofReal (exponentialPDFReal_nonneg (by norm_num) r)
    rw [hreal]
    simp only [exponentialPDFReal_formula, smul_eq_mul, one_mul, neg_mul,
      mul_one, Set.indicator, mem_Ici]
    split_ifs <;> simp
  rw [heq, integral_indicator measurableSet_Ici]
  exact setIntegral_congr_set Ioi_ae_eq_Ici.symm

theorem unitExponential_integrable_iff_Ioi (f : ℝ → ℝ) :
    Integrable f unitExponential ↔
      IntegrableOn (fun r => Real.exp (-r) * f r) (Ioi 0) := by
  change Integrable f (volume.withDensity (exponentialPDF 1)) ↔ _
  have hm : Measurable (exponentialPDF 1) := (measurable_exponentialPDFReal 1).ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul'
    hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have heq : (fun r => (exponentialPDF 1 r).toReal • f r) =
      (Ici (0 : ℝ)).indicator (fun r => Real.exp (-r) * f r) := by
    funext r
    have hreal : (exponentialPDF 1 r).toReal = exponentialPDFReal 1 r :=
      ENNReal.toReal_ofReal (exponentialPDFReal_nonneg (by norm_num) r)
    rw [hreal]
    simp only [exponentialPDFReal_formula, smul_eq_mul, one_mul, neg_mul,
      mul_one, Set.indicator, mem_Ici]
    split_ifs <;> simp
  rw [heq, integrable_indicator_iff measurableSet_Ici]
  exact ⟨fun h => h.congr_set_ae Ioi_ae_eq_Ici, fun h => h.congr_set_ae Ioi_ae_eq_Ici.symm⟩

theorem faceExponentialLaw_strict_tail {p : ℕ} (u : Face p → ℝ)
    (hu : ∀ f, 0 ≤ u f) :
    (faceExponentialLaw p).real {e | ∀ f, u f < e f} = Real.exp (-(∑ f, u f)) := by
  classical
  have hset : {e : Face p → ℝ | ∀ f, u f < e f} = Set.pi Set.univ (fun f => Ioi (u f)) := by
    ext e
    exact ⟨fun h f _ => h f, fun h f => h f (mem_univ f)⟩
  rw [hset, measureReal_def, faceExponentialLaw, Measure.pi_pi, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, unitExponential_Ioi (hu _)]
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

namespace GaussianTube

noncomputable section

def activeMass {p : ℕ} (w : FaceWeights p) (S : Finset (Face p)) : ℝ :=
  ∑ f ∈ S, w.weight f

def inactiveMass {p : ℕ} (w : FaceWeights p) (S : Finset (Face p)) : ℝ :=
  ∑ f, if f ∈ S then 0 else w.weight f

def inactiveEvent {p : ℕ} (w : FaceWeights p) (S : Finset (Face p)) (r : ℝ) :
    Set (Face p → ℝ) :=
  {e | ∀ f, (if f ∈ S then 0 else r * w.weight f) < e f}

/-- The active exponential factors before the null-clock average. -/
def sourceKernel {p : ℕ} (w : FaceWeights p) (S : Finset (Face p))
    (re : ℝ × (Face p → ℝ)) : ℝ :=
  (∏ f ∈ S, re.1 * w.weight f) * Real.exp (-(activeMass w S * re.1)) *
    (inactiveEvent w S re.1).indicator (fun _ => (1 : ℝ)) re.2

theorem activeMass_add_inactiveMass {p : ℕ} (w : FaceWeights p) (S : Finset (Face p)) :
    activeMass w S + inactiveMass w S = w.T := by
  classical
  unfold activeMass inactiveMass FaceWeights.T
  have hs : (∑ f ∈ S, w.weight f) = ∑ f, if f ∈ S then w.weight f else 0 := by
    simp only [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hs]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun f _ => by split_ifs <;> simp)

theorem inactiveMass_nonneg {p : ℕ} (w : FaceWeights p) (S : Finset (Face p)) :
    0 ≤ inactiveMass w S := by
  apply Finset.sum_nonneg
  intro f _
  split_ifs
  · exact le_rfl
  · exact w.nonneg f

theorem measurableSet_inactiveEvent {p : ℕ} (w : FaceWeights p)
    (S : Finset (Face p)) (r : ℝ) : MeasurableSet (inactiveEvent w S r) := by
  classical
  simp only [inactiveEvent, Set.setOf_forall]
  exact MeasurableSet.iInter fun f => measurableSet_lt measurable_const (measurable_pi_apply f)

theorem inactiveEvent_probability {p : ℕ} (w : FaceWeights p)
    (S : Finset (Face p)) {r : ℝ} (hr : 0 ≤ r) :
    (faceExponentialLaw p).real (inactiveEvent w S r) = Real.exp (-(r * inactiveMass w S)) := by
  classical
  have hnonneg (f : Face p) : 0 ≤ (if f ∈ S then 0 else r * w.weight f) := by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hr (w.nonneg f)
  rw [inactiveEvent, faceExponentialLaw_strict_tail _ hnonneg]
  apply congrArg (fun u : ℝ => Real.exp (-u))
  unfold inactiveMass
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun f _ => by split_ifs <;> simp)

theorem sourceKernel_integral_inner {p : ℕ} (w : FaceWeights p)
    (S : Finset (Face p)) {r : ℝ} (hr : 0 ≤ r) :
    (∫ e, sourceKernel w S (r, e) ∂faceExponentialLaw p) =
      (∏ f ∈ S, r * w.weight f) * Real.exp (-(w.T * r)) := by
  dsimp only [sourceKernel]
  rw [integral_const_mul, integral_indicator_const (1 : ℝ) (measurableSet_inactiveEvent w S r)]
  simp only [smul_eq_mul, mul_one]
  rw [inactiveEvent_probability w S hr, mul_assoc, ← Real.exp_add]
  congr 2
  have hh := activeMass_add_inactiveMass w S
  nlinarith

theorem sourceKernel_integral_iterated {p : ℕ} (w : FaceWeights p)
    (S : Finset (Face p)) :
    (∫ r, ∫ e, sourceKernel w S (r, e) ∂faceExponentialLaw p ∂unitExponential) =
      (S.card.factorial : ℝ) * (w.F * ∏ f ∈ S, w.pi f) := by
  rw [unitExponential_integral_eq_Ioi]
  calc
    _ = ∫ r : ℝ in Ioi 0,
        (∏ f ∈ S, r * w.weight f) * Real.exp (-((1 + w.T) * r)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [sourceKernel_integral_inner w S (mem_Ioi.mp hr).le]
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ = _ := integral_active_exponential_kernel w S

theorem sourceKernel_nonneg {p : ℕ} (w : FaceWeights p) (S : Finset (Face p))
    {r : ℝ} (hr : 0 ≤ r) (e : Face p → ℝ) : 0 ≤ sourceKernel w S (r, e) := by
  unfold sourceKernel
  apply mul_nonneg
  · exact mul_nonneg (Finset.prod_nonneg (fun f _ => mul_nonneg hr (w.nonneg f)))
      (Real.exp_nonneg _)
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem sourceKernel_measurable {p : ℕ} (w : FaceWeights p) (S : Finset (Face p)) :
    Measurable (sourceKernel w S) := by
  classical
  let D : Set (ℝ × (Face p → ℝ)) :=
    {re | ∀ f, (if f ∈ S then 0 else re.1 * w.weight f) < re.2 f}
  have hD : MeasurableSet D := by
    simp only [D, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro f
    by_cases hf : f ∈ S
    · simp only [hf, ↓reduceIte]
      exact measurableSet_lt measurable_const ((measurable_pi_apply f).comp measurable_snd)
    · simp only [hf, ↓reduceIte]
      exact measurableSet_lt (measurable_fst.mul_const _)
        ((measurable_pi_apply f).comp measurable_snd)
  have heq : sourceKernel w S = D.indicator
      (fun re => (∏ f ∈ S, re.1 * w.weight f) * Real.exp (-(activeMass w S * re.1))) := by
    funext re
    by_cases hd : re ∈ D <;> simp [sourceKernel, inactiveEvent, D, Set.indicator, hd]
  rw [heq]
  exact ((Finset.measurable_prod S (fun f _ => measurable_fst.mul_const _)).mul
    (measurable_fst.const_mul _).neg.exp).indicator hD

theorem sourceKernel_integrable_inner {p : ℕ} (w : FaceWeights p)
    (S : Finset (Face p)) (r : ℝ) :
    Integrable (fun e => sourceKernel w S (r, e)) (faceExponentialLaw p) := by
  have hi := (integrable_const ((∏ f ∈ S, r * w.weight f) *
    Real.exp (-(activeMass w S * r))) (μ := faceExponentialLaw p)).indicator
      (measurableSet_inactiveEvent w S r)
  convert hi using 1
  funext e
  by_cases he : e ∈ inactiveEvent w S r <;> simp [sourceKernel, Set.indicator, he]

theorem active_kernel_integrable_null {p : ℕ} (w : FaceWeights p) (S : Finset (Face p)) :
    Integrable (fun r => (∏ f ∈ S, r * w.weight f) * Real.exp (-(w.T * r))) unitExponential := by
  apply (unitExponential_integrable_iff_Ioi _).mpr
  have hh := (integrableOn_natPow_mul_exp_neg_mul_Ioi S.card w.denominator_pos).const_mul
    (∏ f ∈ S, w.weight f)
  apply hh.congr
  filter_upwards [] with r
  have he : Real.exp (-((1 + w.T) * r)) = Real.exp (-r) * Real.exp (-(w.T * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Finset.prod_mul_distrib, Finset.prod_const]
  rw [he]
  ring

theorem sourceKernel_integrable {p : ℕ} (w : FaceWeights p) (S : Finset (Face p)) :
    Integrable (sourceKernel w S) (exponentialRectangleLaw p) := by
  apply (integrable_prod_iff (sourceKernel_measurable w S).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (sourceKernel_integrable_inner w S), ?_⟩
  apply (active_kernel_integrable_null w S).congr
  filter_upwards [unitExponential_ae_pos] with r hr
  rw [← sourceKernel_integral_inner w S hr.le]
  apply integral_congr_ae
  exact ae_of_all _ fun e => by
    change sourceKernel w S (r, e) = ‖sourceKernel w S (r, e)‖
    rw [Real.norm_eq_abs, abs_of_nonneg (sourceKernel_nonneg w S hr.le e)]

/-- The complete actual null/inactive exponential experiment produces the
soft-face weight with its exact factorial. This includes the integrability
needed to use the identity inside later Gaussian/product integrals. -/
theorem sourceKernel_integral {p : ℕ} (w : FaceWeights p) (S : Finset (Face p)) :
    (∫ re, sourceKernel w S re ∂exponentialRectangleLaw p) =
      (S.card.factorial : ℝ) * (w.F * ∏ f ∈ S, w.pi f) := by
  rw [show exponentialRectangleLaw p = unitExponential.prod (faceExponentialLaw p) from rfl,
    integral_prod _ (sourceKernel_integrable w S)]
  exact sourceKernel_integral_iterated w S

theorem tuple_face_injective {p q : ℕ} (S : CompatibleFaceTuple p q) :
    Function.Injective S.face := by
  intro i j hij
  exact S.coordinate_injective (congrArg Prod.fst hij)

theorem activeFaces_card {p q : ℕ} (S : CompatibleFaceTuple p q) :
    (activeFaces S).card = q := by
  classical
  rw [activeFaces, Finset.card_image_of_injective _ (tuple_face_injective S)]
  exact Fintype.card_fin q

theorem activeFaces_sum {p q : ℕ} (S : CompatibleFaceTuple p q) (f : Face p → ℝ) :
    (∑ a ∈ activeFaces S, f a) = ∑ i, f (S.face i) := by
  classical
  exact Finset.sum_image (fun i _ j _ hij => tuple_face_injective S hij)

theorem activeFaces_prod {p q : ℕ} (S : CompatibleFaceTuple p q) (f : Face p → ℝ) :
    (∏ a ∈ activeFaces S, f a) = ∏ i, f (S.face i) := by
  classical
  exact Finset.prod_image (fun i _ j _ hij => tuple_face_injective S hij)

/-- The density on the image which remembers the Gaussian base point of the
augmented map. Its exponential factor is the actual joint density of the
new active exponential coordinates. -/
def pulledDensity {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (E₀ : ℝ)
    (y : Coordinates p q) : ℝ :=
  standardGaussianDensity p
      (base (inverse (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) y)) *
    Real.exp (-(∑ i, tube y i))

/-- The concrete augmented change of variables, including the active
exponential densities. No surface measure or face-integral premise appears
in this identity. -/
theorem lintegral_pulledDensity_image {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (e : Face p → ℝ) (width : ℝ)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ y in map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
        sourceDomain S s A r E₀ e width,
      ENNReal.ofReal (pulledDensity S s A r E₀ y)) =
      ∫⁻ w in sourceDomain S s A r E₀ e width,
        ENNReal.ofReal
          ((((∏ f ∈ activeFaces S, E₀ * (s.weights (A.mulVec (base w) + r)).weight f) /
              s.bandwidth ^ q) *
              ((normalMatrix S A).transpose * normalMatrix S A).det) *
            standardGaussianDensity p (base w) *
            Real.exp (-(E₀ * activeMass (s.weights (A.mulVec (base w) + r)) (activeFaces S)))) := by
  rw [lintegral_image_map _ s.bandwidth_pos hE₀ hd _ hgram
    (measurableSet_sourceDomain S s A r E₀ e width)]
  apply lintegral_congr_ae
  filter_upwards [] with w
  have hi := inverse_map (normalMatrix S A) s.bandwidth_pos.ne' hE₀.ne' hd
    (activeOffsets S s r) w
  have hp : (∏ i, tube (map (normalMatrix S A) s.bandwidth E₀
      (activeOffsets S s r) w) i) =
      ∏ f ∈ activeFaces S, E₀ * (s.weights (A.mulVec (base w) + r)).weight f := by
    rw [activeFaces_prod]
    exact Finset.prod_congr rfl (fun i _ => activeExponential_eq S s A r hactive E₀ w i)
  have hs : (∑ i, tube (map (normalMatrix S A) s.bandwidth E₀
      (activeOffsets S s r) w) i) =
      E₀ * activeMass (s.weights (A.mulVec (base w) + r)) (activeFaces S) := by
    simp only [activeMass, activeFaces_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => activeExponential_eq S s A r hactive E₀ w i)
  have hn : 0 ≤ ((∏ f ∈ activeFaces S,
      E₀ * (s.weights (A.mulVec (base w) + r)).weight f) / s.bandwidth ^ q) *
        ((normalMatrix S A).transpose * normalMatrix S A).det := by
    exact mul_nonneg (div_nonneg (Finset.prod_nonneg (fun f _ =>
      mul_nonneg hE₀.le ((s.weights _).nonneg f))) (pow_nonneg s.bandwidth_pos.le _)) hgram
  simp only [pulledDensity, hi, hp, hs]
  rw [← ENNReal.ofReal_mul hn]
  congr 1
  ring

def tubeBox (q : ℕ) (width : ℝ) : Set (Fin q → ℝ) :=
  {u | ∀ i, 0 < u i ∧ u i < width}

theorem sourceDomain_iff_inactiveEvent {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (he : ∀ f, 0 < e f) (width : ℝ)
    (w : Coordinates p q) :
    w ∈ sourceDomain S s A r E₀ e width ↔
      tube w ∈ tubeBox q width ∧
      e ∈ inactiveEvent (s.weights (A.mulVec (base w) + r)) (activeFaces S) E₀ := by
  classical
  constructor
  · rintro ⟨hu, hi⟩
    refine ⟨hu, fun f => ?_⟩
    by_cases hf : f ∈ activeFaces S
    · simpa [hf] using he f
    · simp only [hf, ↓reduceIte]
      by_cases hfaces : f ∈ s.faces
      · exact hi f hfaces hf
      · simpa [FaceSmoother.weights, hfaces] using he f
  · rintro ⟨hu, hi⟩
    refine ⟨hu, fun f _ hf => ?_⟩
    have hh := hi f
    simpa only [hf, ↓reduceIte] using hh

/-- The source density includes the actual Jacobian, the Gaussian base
density, the active exponential densities, and the inactive tube event. -/
def sourceDensity {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (width : ℝ)
    (w : Coordinates p q) (re : ℝ × (Face p → ℝ)) : ℝ :=
  ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
      standardGaussianDensity p (base w)) *
    (∏ f ∈ activeFaces S, re.1 * (s.weights (A.mulVec (base w) + r)).weight f) *
    Real.exp (-(activeMass (s.weights (A.mulVec (base w) + r)) (activeFaces S) * re.1)) *
    (sourceDomain S s A r re.1 re.2 width).indicator (fun _ => (1 : ℝ)) w

theorem sourceDensity_eq_sourceKernel {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (w : Coordinates p q) (re : ℝ × (Face p → ℝ))
    (he : ∀ f, 0 < re.2 f) :
    sourceDensity S s A r width w re =
      (tubeBox q width).indicator (fun _ => (1 : ℝ)) (tube w) *
        ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          standardGaussianDensity p (base w)) *
        sourceKernel (s.weights (A.mulVec (base w) + r)) (activeFaces S) re := by
  classical
  have hd := sourceDomain_iff_inactiveEvent S s A r re.1 re.2 he width w
  by_cases hu : tube w ∈ tubeBox q width
  · by_cases hi : re.2 ∈ inactiveEvent (s.weights (A.mulVec (base w) + r)) (activeFaces S) re.1
    · have hw := hd.mpr ⟨hu, hi⟩
      simp only [sourceDensity, sourceKernel, Set.indicator_of_mem hw,
        Set.indicator_of_mem hi, Set.indicator_of_mem hu, one_mul, mul_one]
      ring
    · have hw : w ∉ sourceDomain S s A r re.1 re.2 width := fun h => hi (hd.mp h).2
      simp [sourceDensity, sourceKernel, Set.indicator_of_not_mem hw,
        Set.indicator_of_not_mem hi]
  · have hw : w ∉ sourceDomain S s A r re.1 re.2 width := fun h => hu (hd.mp h).1
    simp [sourceDensity, Set.indicator_of_not_mem hw, Set.indicator_of_not_mem hu]

/-- Exact integration of the source density against the genuine null and
inactive exponential experiment. The only remaining tube factor is its
ordinary positive-cube indicator. -/
theorem sourceDensity_integral_exponentials {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (w : Coordinates p q) :
    (∫ re, sourceDensity S s A r width w re ∂exponentialRectangleLaw p) =
      (tubeBox q width).indicator (fun _ => (1 : ℝ)) (tube w) *
        ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          standardGaussianDensity p (base w)) *
        (q.factorial : ℝ) *
          ((s.weights (A.mulVec (base w) + r)).F *
            ∏ f ∈ activeFaces S, (s.weights (A.mulVec (base w) + r)).pi f) := by
  calc
    _ = ∫ re,
        (tubeBox q width).indicator (fun _ => (1 : ℝ)) (tube w) *
          ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
            standardGaussianDensity p (base w)) *
          sourceKernel (s.weights (A.mulVec (base w) + r)) (activeFaces S) re
        ∂exponentialRectangleLaw p := by
      apply integral_congr_ae
      filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
      exact sourceDensity_eq_sourceKernel S s A r width w re hre.2
    _ = _ := by
      rw [integral_const_mul, sourceKernel_integral, activeFaces_card]
      ring

theorem measurableSet_tubeBox (q : ℕ) (width : ℝ) :
    MeasurableSet (tubeBox q width) := by
  simp only [tubeBox, Set.setOf_forall]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const)

theorem integral_tubeBox_indicator (q : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    (∫ u : Fin q → ℝ, (tubeBox q width).indicator (fun _ => (1 : ℝ)) u) = width ^ q := by
  have hs : tubeBox q width = Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) width) := by
    ext u
    simp [tubeBox, Set.mem_pi]
  rw [integral_indicator_const _ (measurableSet_tubeBox q width), smul_eq_mul, mul_one,
    hs, measureReal_def, volume_pi, Measure.pi_pi, ENNReal.toReal_prod]
  simp [Real.volume_Ioo, ENNReal.toReal_ofReal hw]

theorem volume_tubeBox (q : ℕ) (width : ℝ) :
    volume (tubeBox q width) = (ENNReal.ofReal width) ^ q := by
  have hs : tubeBox q width = Set.pi Set.univ (fun _ : Fin q => Set.Ioo (0 : ℝ) width) := by
    ext u
    simp [tubeBox, Set.mem_pi]
  rw [hs, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

theorem integrable_tubeBox_mul {p q : ℕ} {g : Vector p → ℝ}
    (hg : Integrable g) (width : ℝ) :
    Integrable (fun w : Coordinates p q =>
      (tubeBox q width).indicator (fun _ => (1 : ℝ)) (tube w) * g (base w)) := by
  have hu : Integrable ((tubeBox q width).indicator (fun _ => (1 : ℝ))) := by
    apply (integrable_indicator_iff (measurableSet_tubeBox q width)).mpr
    apply integrableOn_const.mpr
    right
    rw [volume_tubeBox]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have hi := hg.mul_prod hu
  rw [← Measure.volume_eq_prod] at hi
  have hp := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ)
  have hi' := (hp.integrable_comp_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin p ⊕ Fin q => ℝ)).measurableEmbedding).mpr hi
  convert hi' using 1
  funext w
  change _ = g (base w) * (tubeBox q width).indicator (fun _ => (1 : ℝ)) (tube w)
  exact mul_comm _ _

/-- Splitting the actual Lebesgue coordinates of the augmented map leaves
exactly the volume of its positive tube cube. -/
theorem integral_tubeBox_mul {p q : ℕ} (g : Vector p → ℝ) {width : ℝ}
    (hw : 0 ≤ width) :
    (∫ w : Coordinates p q,
      (tubeBox q width).indicator (fun _ => (1 : ℝ)) (tube w) * g (base w)) =
      width ^ q * ∫ z, g z := by
  have hp := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin p ⊕ Fin q => ℝ)
  rw [← hp.integral_comp']
  change (∫ zu : Vector p × (Fin q → ℝ),
    (tubeBox q width).indicator (fun _ => (1 : ℝ)) zu.2 * g zu.1) = _
  simp_rw [mul_comm ((tubeBox q width).indicator _ _)]
  rw [Measure.volume_eq_prod, integral_prod_mul, integral_tubeBox_indicator q hw, mul_comm]

/-- The complete source-side tube integral is an actual Gaussian soft-face
expectation, with the precise Gram, bandwidth, tube-volume and factorial
normalizations. -/
theorem sourceDensity_integral_source {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {width : ℝ} (hw : 0 ≤ width) :
    (∫ w : Coordinates p q,
      ∫ re, sourceDensity S s A r width w re ∂exponentialRectangleLaw p) =
      width ^ q *
        (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
        (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) ∂standardGaussian p := by
  simp_rw [sourceDensity_integral_exponentials]
  calc
    _ = ∫ w : Coordinates p q,
        (tubeBox q width).indicator (fun _ => (1 : ℝ)) (tube w) *
          ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
            (q.factorial : ℝ) *
            (standardGaussianDensity p (base w) *
              s.softFaceWeight (activeFaces S) (A.mulVec (base w) + r))) := by
      apply integral_congr_ae
      filter_upwards [] with w
      unfold FaceSmoother.softFaceWeight FaceSmoother.F
      ring
    _ = _ := by
      rw [integral_tubeBox_mul (fun z : Vector p =>
        (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          (q.factorial : ℝ) *
          (standardGaussianDensity p z * s.softFaceWeight (activeFaces S) (A.mulVec z + r))) hw,
        integral_const_mul,
        ← standardGaussian_integral_density_mul]
      ring

theorem integral_pulledDensity_image_eq_sourceDensity {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (e : Face p → ℝ) (width : ℝ)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫ y in map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
        sourceDomain S s A r E₀ e width,
      pulledDensity S s A r E₀ y) =
      ∫ w, sourceDensity S s A r width w (E₀, e) := by
  rw [integral_image_map _ s.bandwidth_pos hE₀ hd _ hgram
    (measurableSet_sourceDomain S s A r E₀ e width)]
  rw [← integral_indicator (measurableSet_sourceDomain S s A r E₀ e width)]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : w ∈ sourceDomain S s A r E₀ e width
  · rw [Set.indicator_of_mem hw]
    have hi := inverse_map (normalMatrix S A) s.bandwidth_pos.ne' hE₀.ne' hd
      (activeOffsets S s r) w
    have hp : (∏ i, tube (map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) =
        ∏ f ∈ activeFaces S, E₀ * (s.weights (A.mulVec (base w) + r)).weight f := by
      rw [activeFaces_prod]
      exact Finset.prod_congr rfl (fun i _ => activeExponential_eq S s A r hactive E₀ w i)
    have hs : (∑ i, tube (map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) =
        activeMass (s.weights (A.mulVec (base w) + r)) (activeFaces S) * E₀ := by
      simp only [activeMass, activeFaces_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [activeExponential_eq S s A r hactive E₀ w i, mul_comm])
    simp only [pulledDensity, hi, hp, hs, sourceDensity, Set.indicator_of_mem hw, mul_one]
    ring
  · simp only [Set.indicator_of_not_mem hw, sourceDensity, mul_zero]

theorem sourceDensity_integrable_exponentials {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (w : Coordinates p q) :
    Integrable (sourceDensity S s A r width w) (exponentialRectangleLaw p) := by
  apply ((sourceKernel_integrable (s.weights (A.mulVec (base w) + r)) (activeFaces S)).const_mul
    ((tubeBox q width).indicator (fun _ => (1 : ℝ)) (tube w) *
      ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
        standardGaussianDensity p (base w)))).congr
  filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
  exact (sourceDensity_eq_sourceKernel S s A r width w re hre.2).symm

theorem sourceDensity_measurable {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) :
    Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      sourceDensity S s A r width z.1 z.2) := by
  classical
  let D : Set (Coordinates p q × (ℝ × (Face p → ℝ))) :=
    {z | z.1 ∈ sourceDomain S s A r z.2.1 z.2.2 width}
  have hb : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) => base z.1) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp measurable_fst)
  have hW := ((measurable_mulVec A).comp hb).add_const r
  have hclock : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) => z.2.1) := by fun_prop
  have hD : MeasurableSet D := by
    change MeasurableSet {z : Coordinates p q × (ℝ × (Face p → ℝ)) |
      (∀ i, 0 < tube z.1 i ∧ tube z.1 i < width) ∧
        ∀ f ∈ s.faces, f ∉ activeFaces S →
          z.2.1 * (s.weights (A.mulVec (base z.1) + r)).weight f < z.2.2 f}
    simp only [Set.setOf_and, Set.setOf_forall]
    refine MeasurableSet.inter (MeasurableSet.iInter (fun i => ?_))
      (MeasurableSet.iInter (fun f => MeasurableSet.iInter (fun _ =>
        MeasurableSet.iInter (fun _ => ?_))))
    · have ht : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) => tube z.1 i) :=
        (measurable_pi_apply (Sum.inr i : Fin p ⊕ Fin q)).comp measurable_fst
      exact (measurableSet_lt measurable_const ht).inter (measurableSet_lt ht measurable_const)
    · exact measurableSet_lt (hclock.mul ((s.continuous_weight f).measurable.comp hW)) (by fun_prop)
  have hweights (f : Face p) : Measurable
      (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
        (s.weights (A.mulVec (base z.1) + r)).weight f) :=
    (s.continuous_weight f).measurable.comp hW
  have hmass : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      activeMass (s.weights (A.mulVec (base z.1) + r)) (activeFaces S)) :=
    Finset.measurable_sum _ (fun f _ => hweights f)
  have hfun : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
        standardGaussianDensity p (base z.1)) *
      (∏ f ∈ activeFaces S, z.2.1 * (s.weights (A.mulVec (base z.1) + r)).weight f) *
      Real.exp (-(activeMass (s.weights (A.mulVec (base z.1) + r)) (activeFaces S) * z.2.1))) :=
    ((standardGaussianDensity_measurable p).comp hb).const_mul _ |>.mul
      (Finset.measurable_prod _ (fun f _ => hclock.mul (hweights f))) |>.mul
        (hmass.mul hclock).neg.exp
  convert hfun.indicator hD using 1
  funext z
  by_cases hz : z ∈ D
  · have hz' : z.1 ∈ sourceDomain S s A r z.2.1 z.2.2 width := hz
    simp only [sourceDensity, Set.indicator_of_mem hz, Set.indicator_of_mem hz', mul_one]
  · have hz' : z.1 ∉ sourceDomain S s A r z.2.1 z.2.2 width := hz
    simp only [sourceDensity, Set.indicator_of_not_mem hz, Set.indicator_of_not_mem hz', mul_zero]

theorem sourceDensity_nonneg {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (w : Coordinates p q) (re : ℝ × (Face p → ℝ)) (hr : 0 ≤ re.1)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    0 ≤ sourceDensity S s A r width w re := by
  unfold sourceDensity
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (div_nonneg hgram (pow_nonneg s.bandwidth_pos.le _))
      (standardGaussianDensity_pos p _).le)
    (Finset.prod_nonneg (fun f _ => mul_nonneg hr ((s.weights _).nonneg f))))
    (Real.exp_nonneg _)) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem sourceDensity_integrable {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    Integrable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      sourceDensity S s A r width z.1 z.2)
      (volume.prod (exponentialRectangleLaw p)) := by
  apply (integrable_prod_iff (sourceDensity_measurable S s A r width).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (sourceDensity_integrable_exponentials S s A r width), ?_⟩
  have hg : Integrable
      (fun z => s.softFaceWeight (activeFaces S) (A.mulVec z + r)) (standardGaussian p) := by
    apply (integrable_const (1 : ℝ)).mono'
      (((s.continuous_softFaceWeight _).comp
        ((continuous_const.matrix_mulVec continuous_id).add continuous_const)).measurable.aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,
        abs_of_nonneg (s.softFaceWeight_nonneg _ _)] using
          s.softFaceWeight_le_one (activeFaces S) (A.mulVec z + r))
  have hdens := (standardGaussian_integrable_density_mul_iff _).mp hg
  have hout := integrable_tubeBox_mul (q := q)
    (hdens.const_mul ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
      (q.factorial : ℝ))) width
  apply hout.congr
  filter_upwards [] with w
  have hn : (∫ re, ‖sourceDensity S s A r width w re‖ ∂exponentialRectangleLaw p) =
      ∫ re, sourceDensity S s A r width w re ∂exponentialRectangleLaw p := by
    apply integral_congr_ae
    filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
    rw [Real.norm_eq_abs, abs_of_nonneg (sourceDensity_nonneg S s A r width w re hre.1.le hgram)]
  rw [hn, sourceDensity_integral_exponentials]
  unfold FaceSmoother.softFaceWeight FaceSmoother.F
  ring

/-- Integrating the concrete tube images over all original null/inactive
exponential samples gives exactly the Gaussian soft-face expectation. The
actual Fubini and Jacobian hypotheses are discharged here. -/
theorem integral_pulledDensity_images {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces) {width : ℝ} (hw : 0 ≤ width)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫ re, ∫ y in map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
        sourceDomain S s A r re.1 re.2 width,
      pulledDensity S s A r re.1 y ∂volume ∂exponentialRectangleLaw p) =
      width ^ q *
        (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
        (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) ∂standardGaussian p := by
  calc
    _ = ∫ re, ∫ w, sourceDensity S s A r width w re ∂volume ∂exponentialRectangleLaw p := by
      apply integral_congr_ae
      filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
      exact integral_pulledDensity_image_eq_sourceDensity S s A r hactive hre.1 re.2 width hd hgram
    _ = ∫ w, ∫ re, sourceDensity S s A r width w re ∂exponentialRectangleLaw p :=
      (integral_integral_swap (sourceDensity_integrable S s A r width hgram)).symm
    _ = _ := sourceDensity_integral_source S s A r hw

theorem sourceDensity_integral_source_weighted {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (g : Vector p → ℝ) {width : ℝ} (hw : 0 ≤ width) :
    (∫ w : Coordinates p q,
      ∫ re, sourceDensity S s A r width w re * g (base w) ∂exponentialRectangleLaw p) =
      width ^ q *
        (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
        (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z ∂standardGaussian p := by
  simp_rw [integral_mul_const, sourceDensity_integral_exponentials]
  calc
    _ = ∫ w : Coordinates p q,
        (tubeBox q width).indicator (fun _ => (1 : ℝ)) (tube w) *
          ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
            (q.factorial : ℝ) *
            (standardGaussianDensity p (base w) *
              (s.softFaceWeight (activeFaces S) (A.mulVec (base w) + r) * g (base w)))) := by
      apply integral_congr_ae
      filter_upwards [] with w
      unfold FaceSmoother.softFaceWeight FaceSmoother.F
      ring
    _ = _ := by
      rw [integral_tubeBox_mul (fun z : Vector p =>
        (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
          (q.factorial : ℝ) *
          (standardGaussianDensity p z *
            (s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z))) hw,
        integral_const_mul, ← standardGaussian_integral_density_mul]
      ring

theorem sourceDensity_integrable_weighted {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (width : ℝ)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    Integrable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      sourceDensity S s A r width z.1 z.2 * g (base z.1))
      (volume.prod (exponentialRectangleLaw p)) := by
  have hb : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) => base z.1) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp measurable_fst)
  apply (integrable_prod_iff ((sourceDensity_measurable S s A r width).mul
    (hgm.comp hb)).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun w =>
    (sourceDensity_integrable_exponentials S s A r width w).mul_const (g (base w))), ?_⟩
  have hsoft : AEStronglyMeasurable
      (fun z => s.softFaceWeight (activeFaces S) (A.mulVec z + r)) (standardGaussian p) :=
    (((s.continuous_softFaceWeight _).comp
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const)).measurable.aestronglyMeasurable)
  have hgsoft := hgi.abs.bdd_mul hsoft ⟨1, fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg _ _)]
    exact s.softFaceWeight_le_one _ _⟩
  have hdens := (standardGaussian_integrable_density_mul_iff _).mp hgsoft
  have hout := integrable_tubeBox_mul (q := q)
    (hdens.const_mul ((((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
      (q.factorial : ℝ))) width
  apply hout.congr
  filter_upwards [] with w
  have hn : (∫ re, ‖sourceDensity S s A r width w re * g (base w)‖ ∂exponentialRectangleLaw p) =
      (∫ re, sourceDensity S s A r width w re ∂exponentialRectangleLaw p) * |g (base w)| := by
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sourceDensity_nonneg S s A r width w re hre.1.le hgram)]
  dsimp only [Function.comp_apply]
  rw [hn, sourceDensity_integral_exponentials]
  unfold FaceSmoother.softFaceWeight FaceSmoother.F
  ring

theorem integral_pulledDensity_weighted_image_eq_sourceDensity {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (g : Vector p → ℝ)
    (hactive : ∀ i, S.face i ∈ s.faces) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (e : Face p → ℝ) (width : ℝ)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫ y in map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
        sourceDomain S s A r E₀ e width,
      pulledDensity S s A r E₀ y *
        g (base (inverse (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) y))) =
      ∫ w, sourceDensity S s A r width w (E₀, e) * g (base w) := by
  rw [integral_image_map _ s.bandwidth_pos hE₀ hd _ hgram
    (measurableSet_sourceDomain S s A r E₀ e width)]
  rw [← integral_indicator (measurableSet_sourceDomain S s A r E₀ e width)]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : w ∈ sourceDomain S s A r E₀ e width
  · rw [Set.indicator_of_mem hw]
    have hi := inverse_map (normalMatrix S A) s.bandwidth_pos.ne' hE₀.ne' hd
      (activeOffsets S s r) w
    have hp : (∏ i, tube (map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) =
        ∏ f ∈ activeFaces S, E₀ * (s.weights (A.mulVec (base w) + r)).weight f := by
      rw [activeFaces_prod]
      exact Finset.prod_congr rfl (fun i _ => activeExponential_eq S s A r hactive E₀ w i)
    have hs : (∑ i, tube (map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) =
        activeMass (s.weights (A.mulVec (base w) + r)) (activeFaces S) * E₀ := by
      simp only [activeMass, activeFaces_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [activeExponential_eq S s A r hactive E₀ w i, mul_comm])
    simp only [pulledDensity, hi, hp, hs, sourceDensity, Set.indicator_of_mem hw, mul_one]
    ring
  · simp only [Set.indicator_of_not_mem hw, sourceDensity, mul_zero, zero_mul]

/-- Weighted version of the full actual tube identity. Any measurable
Gaussian-integrable weight may be attached to the recovered Gaussian base,
including the finite projection-radius moments used in higher face bounds. -/
theorem integral_pulledDensity_weighted_images {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (hactive : ∀ i, S.face i ∈ s.faces) {width : ℝ} (hw : 0 ≤ width)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫ re, ∫ y in map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
        sourceDomain S s A r re.1 re.2 width,
      pulledDensity S s A r re.1 y *
        g (base (inverse (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) y))
        ∂volume ∂exponentialRectangleLaw p) =
      width ^ q *
        (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
        (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z ∂standardGaussian p := by
  calc
    _ = ∫ re, ∫ w, sourceDensity S s A r width w re * g (base w)
        ∂volume ∂exponentialRectangleLaw p := by
      apply integral_congr_ae
      filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
      exact integral_pulledDensity_weighted_image_eq_sourceDensity S s A r g hactive hre.1 re.2 width hd hgram
    _ = ∫ w, ∫ re, sourceDensity S s A r width w re * g (base w) ∂exponentialRectangleLaw p :=
      (integral_integral_swap (sourceDensity_integrable_weighted S s A r g hgm hgi width hgram)).symm
    _ = _ := sourceDensity_integral_source_weighted S s A r g hw

theorem lintegral_pulledDensity_weighted_image_eq_sourceDensity {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (g : Vector p → ℝ)
    (hactive : ∀ i, S.face i ∈ s.faces) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (e : Face p → ℝ) (width : ℝ)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ y in map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) ''
        sourceDomain S s A r E₀ e width,
      ENNReal.ofReal (pulledDensity S s A r E₀ y *
        g (base (inverse (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) y)))) =
      ∫⁻ w, ENNReal.ofReal (sourceDensity S s A r width w (E₀, e) * g (base w)) := by
  rw [lintegral_image_map _ s.bandwidth_pos hE₀ hd _ hgram
    (measurableSet_sourceDomain S s A r E₀ e width)]
  rw [← lintegral_indicator (measurableSet_sourceDomain S s A r E₀ e width)]
  apply lintegral_congr_ae
  filter_upwards [] with w
  by_cases hw : w ∈ sourceDomain S s A r E₀ e width
  · rw [Set.indicator_of_mem hw]
    have hi := inverse_map (normalMatrix S A) s.bandwidth_pos.ne' hE₀.ne' hd
      (activeOffsets S s r) w
    have hp : (∏ i, tube (map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) =
        ∏ f ∈ activeFaces S, E₀ * (s.weights (A.mulVec (base w) + r)).weight f := by
      rw [activeFaces_prod]
      exact Finset.prod_congr rfl (fun i _ => activeExponential_eq S s A r hactive E₀ w i)
    have hs : (∑ i, tube (map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) =
        activeMass (s.weights (A.mulVec (base w) + r)) (activeFaces S) * E₀ := by
      simp only [activeMass, activeFaces_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [activeExponential_eq S s A r hactive E₀ w i, mul_comm])
    have hj : 0 ≤ ((∏ i, tube (map (normalMatrix S A) s.bandwidth E₀
        (activeOffsets S s r) w) i) / s.bandwidth ^ q) *
          ((normalMatrix S A).transpose * normalMatrix S A).det :=
      mul_nonneg (div_nonneg (Finset.prod_nonneg (fun i _ =>
        (tube_map_pos _ _ hE₀ _ _ _).le)) (pow_nonneg s.bandwidth_pos.le _)) hgram
    rw [← ENNReal.ofReal_mul hj]
    simp only [pulledDensity, hi, hp, hs, sourceDensity, Set.indicator_of_mem hw, mul_one]
    congr 1
    ring
  · simp only [Set.indicator_of_not_mem hw, sourceDensity, mul_zero, zero_mul,
      ENNReal.ofReal_zero]

/-- Nonnegative-integral form of the full weighted source identity, directly
usable with the common-experiment disintegration. -/
theorem lintegral_pulledDensity_weighted_images {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (hg0 : ∀ z, 0 ≤ g z)
    (hactive : ∀ i, S.face i ∈ s.faces) {width : ℝ} (hw : 0 ≤ width)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hgram : 0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ re, ∫⁻ y in map (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) ''
        sourceDomain S s A r re.1 re.2 width,
      ENNReal.ofReal (pulledDensity S s A r re.1 y *
        g (base (inverse (normalMatrix S A) s.bandwidth re.1 (activeOffsets S s r) y)))
        ∂volume ∂exponentialRectangleLaw p) =
      ENNReal.ofReal (width ^ q *
        (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
        (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z ∂standardGaussian p) := by
  have hm : Measurable
      (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
        sourceDensity S s A r width z.1 z.2 * g (base z.1)) := by
    exact (sourceDensity_measurable S s A r width).mul
      (hgm.comp (measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp measurable_fst)))
  have hnonneg : ∀ᵐ z ∂volume.prod (exponentialRectangleLaw p),
      0 ≤ sourceDensity S s A r width z.1 z.2 * g (base z.1) := by
    filter_upwards [((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Coordinates p q)))
      (ν := exponentialRectangleLaw p)).ae
        (exponentialRectangleLaw_ae_pos p))] with z hz
    exact mul_nonneg (sourceDensity_nonneg S s A r width z.1 z.2 hz.1.le hgram) (hg0 _)
  calc
    _ = ∫⁻ re, ∫⁻ w, ENNReal.ofReal
        (sourceDensity S s A r width w re * g (base w)) ∂volume ∂exponentialRectangleLaw p := by
      apply lintegral_congr_ae
      filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
      exact lintegral_pulledDensity_weighted_image_eq_sourceDensity S s A r g hactive hre.1 re.2 width hd hgram
    _ = ∫⁻ w, ∫⁻ re, ENNReal.ofReal
        (sourceDensity S s A r width w re * g (base w)) ∂exponentialRectangleLaw p :=
      (lintegral_lintegral_swap hm.ennreal_ofReal.aemeasurable).symm
    _ = ENNReal.ofReal (∫ w, ∫ re,
        sourceDensity S s A r width w re * g (base w) ∂exponentialRectangleLaw p) := by
      rw [lintegral_lintegral hm.ennreal_ofReal.aemeasurable,
        ← ofReal_integral_eq_lintegral_ofReal
          (sourceDensity_integrable_weighted S s A r g hgm hgi width hgram) hnonneg,
        integral_prod _ (sourceDensity_integrable_weighted S s A r g hgm hgi width hgram)]
    _ = _ := congrArg ENNReal.ofReal (sourceDensity_integral_source_weighted S s A r g hw)

end
end GaussianTube
end RectangleCLT
