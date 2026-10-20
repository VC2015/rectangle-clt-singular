import RectangleCLT.GaussianTubeEvents
import Mathlib.MeasureTheory.Integral.Pi

/-! Replacing the active exponential coordinates by fresh independent
exponentials preserves the actual common random-rectangle law. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.GaussianTube

noncomputable section

def activeIndexEquiv {p q : ℕ} (S : CompatibleFaceTuple p q) :
    Fin q ≃ {f : Face p // f ∈ activeFaces S} := by
  classical
  apply Equiv.ofBijective (fun i => ⟨S.face i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  constructor
  · intro i j hij
    exact S.coordinate_injective (congrArg (fun f : {f : Face p // f ∈ activeFaces S} => f.1.1) hij)
  · intro f
    rcases Finset.mem_image.mp f.2 with ⟨i, _, hi⟩
    exact ⟨i, Subtype.ext hi⟩

def faceSplit {p q : ℕ} (S : CompatibleFaceTuple p q) :
    (Face p → ℝ) ≃ᵐ
      ({f : Face p // f ∈ activeFaces S} → ℝ) ×
        ({f : Face p // f ∉ activeFaces S} → ℝ) := by
  classical
  exact MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Face p => ℝ) (fun f => f ∈ activeFaces S)

def replaceActive {p q : ℕ} (S : CompatibleFaceTuple p q)
    (e : Face p → ℝ) (a : Fin q → ℝ) : Face p → ℝ :=
  (faceSplit S).symm
    ((MeasurableEquiv.piCongrLeft (fun _ : {f : Face p // f ∈ activeFaces S} => ℝ)
      (activeIndexEquiv S)) a, fun f => e f)

theorem replaceActive_at {p q : ℕ} (S : CompatibleFaceTuple p q)
    (e : Face p → ℝ) (a : Fin q → ℝ) (i : Fin q) :
    replaceActive S e a (S.face i) = a i := by
  classical
  have hf : S.face i ∈ activeFaces S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  change (if h : S.face i ∈ activeFaces S then
    ((MeasurableEquiv.piCongrLeft
      (fun _ : {f : Face p // f ∈ activeFaces S} => ℝ) (activeIndexEquiv S)) a) ⟨S.face i, h⟩
    else e (S.face i)) = a i
  rw [dif_pos hf]
  have heq : (activeIndexEquiv S) i = ⟨S.face i, hf⟩ := rfl
  rw [← heq, MeasurableEquiv.piCongrLeft_apply_apply]

theorem replaceActive_off {p q : ℕ} (S : CompatibleFaceTuple p q)
    (e : Face p → ℝ) (a : Fin q → ℝ) (f : Face p) (hf : f ∉ activeFaces S) :
    replaceActive S e a f = e f := by
  classical
  change (if h : f ∈ activeFaces S then _ else e f) = e f
  rw [dif_neg hf]

theorem measurePreserving_replaceActive {p q : ℕ} (S : CompatibleFaceTuple p q) :
    MeasurePreserving (fun z : (Face p → ℝ) × (Fin q → ℝ) => replaceActive S z.1 z.2)
      ((faceExponentialLaw p).prod (Measure.pi (fun _ : Fin q => unitExponential)))
      (faceExponentialLaw p) := by
  classical
  letI : Fintype {f : Face p // f ∈ activeFaces S} :=
    Subtype.fintype (fun f : Face p => f ∈ activeFaces S)
  let μa : Measure ({f : Face p // f ∈ activeFaces S} → ℝ) := Measure.pi (fun _ => unitExponential)
  let μb : Measure ({f : Face p // f ∉ activeFaces S} → ℝ) := Measure.pi (fun _ => unitExponential)
  let μq : Measure (Fin q → ℝ) := Measure.pi (fun _ => unitExponential)
  have hs : MeasurePreserving (faceSplit S) (faceExponentialLaw p) (μa.prod μb) := by
    simpa only [faceSplit, faceExponentialLaw, μa, μb] using
      measurePreserving_piEquivPiSubtypeProd (fun _ : Face p => unitExponential)
        (fun f => f ∈ activeFaces S)
  have hcoord : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : {f : Face p // f ∈ activeFaces S} => ℝ)
        (activeIndexEquiv S)) μq μa :=
    measurePreserving_piCongrLeft (fun _ => unitExponential) (activeIndexEquiv S)
  have hsnd : MeasurePreserving Prod.snd (μa.prod μb) μb := by
    refine ⟨measurable_snd, ?_⟩
    exact Measure.snd_prod
  have hrest : MeasurePreserving (fun e : Face p → ℝ => fun f : {f : Face p // f ∉ activeFaces S} => e f)
      (faceExponentialLaw p) μb := hsnd.comp hs
  have hp := hrest.prod (MeasurePreserving.id μq)
  have hswap := (Measure.measurePreserving_swap (μ := μb) (ν := μq)).comp hp
  have hrebuild := (hs.symm (faceSplit S)).comp (hcoord.prod (MeasurePreserving.id μb))
  exact hrebuild.comp hswap

theorem unitExponentialPDFReal_eq_indicator :
    exponentialPDFReal 1 = (Set.Ici 0).indicator (fun x : ℝ => Real.exp (-x)) := by
  funext x
  simp [exponentialPDFReal, gammaPDFReal, Set.indicator]

theorem unitExponentialPDFReal_integrable : Integrable (exponentialPDFReal 1) := by
  rw [unitExponentialPDFReal_eq_indicator]
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  exact integrableOn_Ici_iff_integrableOn_Ioi.mpr (integrableOn_exp_neg_Ioi 0)

noncomputable def exponentialProductDensity (q : ℕ) (a : Fin q → ℝ) : ℝ :=
  ∏ i, exponentialPDFReal 1 (a i)

theorem exponentialProductDensity_nonneg (q : ℕ) (a : Fin q → ℝ) :
    0 ≤ exponentialProductDensity q a :=
  Finset.prod_nonneg (fun _ _ => exponentialPDFReal_nonneg (by norm_num) _)

theorem exponentialProductDensity_measurable (q : ℕ) :
    Measurable (exponentialProductDensity q) :=
  Finset.measurable_prod _ (fun i _ => (measurable_exponentialPDFReal 1).comp (measurable_pi_apply i))

theorem exponentialProductDensity_integrable (q : ℕ) : Integrable (exponentialProductDensity q) :=
  Integrable.fintype_prod (fun _ => unitExponentialPDFReal_integrable)

theorem exponentialProductDensity_setIntegral (q : ℕ) (s : Fin q → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) :
    (∫ a in Set.pi Set.univ s, exponentialProductDensity q a) =
      ∏ i, ∫ t in s i, exponentialPDFReal 1 t := by
  classical
  rw [← integral_indicator (MeasurableSet.univ_pi hs)]
  have hfun : (Set.pi Set.univ s).indicator (exponentialProductDensity q) =
      (fun a : Fin q → ℝ => ∏ i, (s i).indicator (exponentialPDFReal 1) (a i)) := by
    funext a
    by_cases ha : a ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem ha]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (ha i (Set.mem_univ i)) _).symm)
    · rw [Set.indicator_of_not_mem ha]
      obtain ⟨i, hi⟩ : ∃ i, a i ∉ s i := by
        simpa only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] using ha
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_not_mem hi _)
  rw [hfun, integral_fintype_prod_eq_prod]
  simp only [integral_indicator (hs _)]

theorem unitExponential_apply_setIntegral (s : Set ℝ) (hs : MeasurableSet s) :
    unitExponential s = ENNReal.ofReal (∫ t in s, exponentialPDFReal 1 t) := by
  change volume.withDensity (fun t => ENNReal.ofReal (exponentialPDFReal 1 t)) s = _
  rw [withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal unitExponentialPDFReal_integrable.restrict
      (Filter.Eventually.of_forall fun x => exponentialPDFReal_nonneg (by norm_num) x)]

theorem exponentialProductLaw_eq_withDensity (q : ℕ) :
    Measure.pi (fun _ : Fin q => unitExponential) =
      volume.withDensity (fun a : Fin q → ℝ => ENNReal.ofReal (exponentialProductDensity q a)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (exponentialProductDensity_integrable q).restrict
      (Filter.Eventually.of_forall (exponentialProductDensity_nonneg q)),
    exponentialProductDensity_setIntegral q s hs,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
      (fun t => exponentialPDFReal_nonneg (by norm_num) t))]
  exact Finset.prod_congr rfl (fun i _ => (unitExponential_apply_setIntegral (s i) (hs i)).symm)

theorem exponentialProductDensity_eq_exp {q : ℕ} (a : Fin q → ℝ) (ha : ∀ i, 0 < a i) :
    exponentialProductDensity q a = Real.exp (-(∑ i, a i)) := by
  unfold exponentialProductDensity
  have heq : (∏ i, exponentialPDFReal 1 (a i)) = ∏ i, Real.exp (-a i) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [unitExponentialPDFReal_eq_indicator,
      Set.indicator_of_mem (show a i ∈ Set.Ici (0 : ℝ) from (ha i).le)]
  rw [heq]
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

theorem exponentialProductDensity_ae_eq_indicator (q : ℕ) :
    exponentialProductDensity q =ᵐ[volume]
      {a : Fin q → ℝ | ∀ i, 0 < a i}.indicator (fun a => Real.exp (-(∑ i, a i))) := by
  classical
  have hne : ∀ᵐ a : Fin q → ℝ ∂volume, ∀ i, a i ≠ 0 := by
    apply ae_all_iff.mpr
    intro i
    simpa only [volume_pi] using
      Measure.ae_eval_ne (μ := fun _ : Fin q => (volume : Measure ℝ)) i (0 : ℝ)
  filter_upwards [hne] with a ha
  by_cases hp : ∀ i, 0 < a i
  · rw [Set.indicator_of_mem (show a ∈ {a : Fin q → ℝ | ∀ i, 0 < a i} from hp)]
    exact exponentialProductDensity_eq_exp a hp
  · rw [Set.indicator_of_not_mem (show a ∉ {a : Fin q → ℝ | ∀ i, 0 < a i} from hp)]
    obtain ⟨i, hi⟩ : ∃ i, a i < 0 := by
      obtain ⟨i, hi⟩ := not_forall.mp hp
      exact ⟨i, lt_of_le_of_ne (le_of_not_gt hi) (ha i)⟩
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [unitExponentialPDFReal_eq_indicator, Set.indicator, not_le.mpr hi]

/-- The concrete product-exponential law is exactly Lebesgue measure on the
positive orthant with density `exp(-sum a)`. Boundary coordinates have zero
Lebesgue measure, also in the zero-dimensional case. -/
theorem exponentialProductLaw_lintegral (q : ℕ) (H : (Fin q → ℝ) → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ a, H a ∂Measure.pi (fun _ : Fin q => unitExponential)) =
      ∫⁻ a in {a : Fin q → ℝ | ∀ i, 0 < a i},
        ENNReal.ofReal (Real.exp (-(∑ i, a i))) * H a := by
  rw [exponentialProductLaw_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul _ (exponentialProductDensity_measurable q).ennreal_ofReal hH]
  have hs : MeasurableSet {a : Fin q → ℝ | ∀ i, 0 < a i} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const (measurable_pi_apply i))
  rw [← lintegral_indicator hs]
  apply lintegral_congr_ae
  filter_upwards [exponentialProductDensity_ae_eq_indicator q] with a ha
  simp only [Pi.mul_apply]
  rw [ha]
  by_cases hp : ∀ i, 0 < a i <;> simp [Set.indicator, hp]

end

end RectangleCLT.GaussianTube
