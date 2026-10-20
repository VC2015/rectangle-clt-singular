import RectangleCLT.SmootherConvolution
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import RectangleCLT.ExponentialRescaling
import RectangleCLT.RandomResampling

/-! Exponential random rectangles for the logistic face smoother. All
probabilities below are taken against concrete exponential product laws. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RectangleCLT

noncomputable abbrev unitExponential : Measure ℝ := expMeasure 1

instance unitExponential_probability : IsProbabilityMeasure unitExponential :=
  isProbabilityMeasureExponential (by norm_num)

instance unitExponential_noAtoms : NoAtoms unitExponential := by
  unfold unitExponential expMeasure gammaMeasure
  exact ⟨fun x => withDensity_absolutelyContinuous _ _ (measure_singleton x)⟩

theorem unitExponential_Iic {t : ℝ} (ht : 0 ≤ t) :
    unitExponential.real (Iic t) = 1 - Real.exp (-t) := by
  have hc := exponentialCDFReal_eq (r := 1) (by norm_num) t
  simpa only [exponentialCDFReal, cdf_eq_real, if_pos ht, one_mul] using hc

theorem unitExponential_Ioi {t : ℝ} (ht : 0 ≤ t) :
    unitExponential.real (Ioi t) = Real.exp (-t) := by
  have hc := measureReal_compl (μ := unitExponential) measurableSet_Iic (s := Iic t)
  rw [compl_Iic, measureReal_univ_eq_one, unitExponential_Iic ht] at hc
  linarith

theorem unitExponential_Ici {t : ℝ} (ht : 0 ≤ t) :
    unitExponential.real (Ici t) = Real.exp (-t) := by
  rw [← measureReal_congr (Ioi_ae_eq_Ici : Ioi t =ᵐ[unitExponential] Ici t)]
  exact unitExponential_Ioi ht

theorem unitExponential_ae_pos : ∀ᵐ t ∂unitExponential, 0 < t := by
  rw [ae_iff]
  have hz : unitExponential.real (Iic 0) = 0 := by
    simpa using unitExponential_Iic (t := 0) le_rfl
  simpa only [Iic, not_lt] using
    (measureReal_eq_zero_iff (μ := unitExponential) (s := Iic 0)).mp hz

/-- Independent exponential variables indexed by all signed faces. Missing
faces impose no constraint in the random-rectangle event. -/
noncomputable def faceExponentialLaw (p : ℕ) : Measure (Face p → ℝ) :=
  Measure.pi (fun _ => unitExponential)

instance faceExponentialLaw_probability (p : ℕ) :
    IsProbabilityMeasure (faceExponentialLaw p) := by
  unfold faceExponentialLaw
  infer_instance

theorem faceExponentialLaw_ae_pos (p : ℕ) :
    ∀ᵐ e ∂faceExponentialLaw p, ∀ f, 0 < e f := by
  apply ae_all_iff.mpr
  intro f
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Face p => unitExponential)
    (i := f)) unitExponential_ae_pos

theorem faceExponentialLaw_tail {p : ℕ} (u : Face p → ℝ)
    (hu : ∀ f, 0 ≤ u f) :
    (faceExponentialLaw p).real {e | ∀ f, u f ≤ e f} =
      Real.exp (-(∑ f, u f)) := by
  classical
  have hset : {e : Face p → ℝ | ∀ f, u f ≤ e f} =
      Set.pi Set.univ (fun f => Ici (u f)) := by
    ext e
    exact ⟨fun h f _ => h f, fun h f => h f (mem_univ f)⟩
  rw [hset, measureReal_def, faceExponentialLaw, Measure.pi_pi, ENNReal.toReal_prod]
  simp_rw [← measureReal_def, unitExponential_Ici (hu _)]
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- The null exponential and all face exponentials are sampled independently. -/
noncomputable def exponentialRectangleLaw (p : ℕ) :
    Measure (ℝ × (Face p → ℝ)) := unitExponential.prod (faceExponentialLaw p)

instance exponentialRectangleLaw_probability (p : ℕ) :
    IsProbabilityMeasure (exponentialRectangleLaw p) := by
  unfold exponentialRectangleLaw
  infer_instance

theorem exponentialRectangleLaw_ae_pos (p : ℕ) :
    ∀ᵐ e ∂exponentialRectangleLaw p, 0 < e.1 ∧ ∀ f, 0 < e.2 f := by
  exact ((Measure.quasiMeasurePreserving_fst (μ := unitExponential)
    (ν := faceExponentialLaw p)).ae unitExponential_ae_pos).and
    ((Measure.quasiMeasurePreserving_snd (μ := unitExponential)
      (ν := faceExponentialLaw p)).ae (faceExponentialLaw_ae_pos p))

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- The exponential comparison event, before rewriting its positive samples
as logarithmic shifts of the original face offsets. -/
def exponentialEvent (x : Fin p → ℝ) : Set (ℝ × (Face p → ℝ)) :=
  {e | ∀ f, e.1 * (s.weights x).weight f ≤ e.2 f}

theorem measurableSet_exponentialEvent (x : Fin p → ℝ) :
    MeasurableSet (s.exponentialEvent x) := by
  simp only [exponentialEvent, setOf_forall]
  apply MeasurableSet.iInter
  intro f
  exact measurableSet_le (measurable_fst.mul_const _)
    ((measurable_pi_apply f).comp measurable_snd)

/-- The smoother is literally the probability of independent exponential
comparisons, including missing faces and an empty family of faces. -/
theorem F_eq_exponential_probability (x : Fin p → ℝ) :
    s.F x = (exponentialRectangleLaw p).real (s.exponentialEvent x) := by
  classical
  let g := (s.exponentialEvent x).indicator (fun _ => (1 : ℝ))
  have hg : Integrable g (exponentialRectangleLaw p) :=
    (integrable_const (1 : ℝ)).indicator (s.measurableSet_exponentialEvent x)
  have hinner : ∀ᵐ t ∂unitExponential,
      (∫ e, g (t, e) ∂faceExponentialLaw p) =
        Real.exp (-((s.weights x).T) * t) := by
    filter_upwards [unitExponential_ae_pos] with t ht
    have hset : (fun e => g (t, e)) =
        {e : Face p → ℝ | ∀ f, t * (s.weights x).weight f ≤ e f}.indicator
          (fun _ => (1 : ℝ)) := by rfl
    rw [hset, integral_indicator_const (1 : ℝ)
      (show MeasurableSet {e : Face p → ℝ | ∀ f, t * (s.weights x).weight f ≤ e f} from
        by
          simp only [setOf_forall]
          exact MeasurableSet.iInter fun f =>
            measurableSet_le measurable_const (measurable_pi_apply f))]
    simp only [smul_eq_mul, mul_one]
    rw [faceExponentialLaw_tail _ (fun f => mul_nonneg ht.le ((s.weights x).nonneg f))]
    congr 1
    simp only [← Finset.mul_sum, FaceWeights.T]
    ring
  calc
    _ = ∫ t, Real.exp (-((s.weights x).T) * t) ∂unitExponential := by
      exact (unitExponential_laplace (s.weights x).T_nonneg).symm
    _ = ∫ t, ∫ e, g (t, e) ∂faceExponentialLaw p ∂unitExponential :=
      (integral_congr_ae hinner).symm
    _ = ∫ z, g z ∂exponentialRectangleLaw p := (integral_prod g hg).symm
    _ = _ := by
      exact integral_indicator_one (s.measurableSet_exponentialEvent x)

/-- On the full-probability set of positive exponential samples, the
comparison event is an ordinary rectangle with explicit logarithmic offsets. -/
theorem exponentialEvent_iff_random_rectangle
    (x : Fin p → ℝ) (e : ℝ × (Face p → ℝ))
    (h0 : 0 < e.1) (hf : ∀ f, 0 < e.2 f) :
    e ∈ s.exponentialEvent x ↔
      ∀ f ∈ s.faces, normalDot f x ≤
        s.offsets f + s.bandwidth * Real.log (e.2 f / e.1) := by
  classical
  have hequiv (f : Face p) (hactive : f ∈ s.faces) :
      e.1 * (s.weights x).weight f ≤ e.2 f ↔
        normalDot f x ≤ s.offsets f + s.bandwidth * Real.log (e.2 f / e.1) := by
    simp only [weights, hactive, ↓reduceIte]
    rw [← le_div_iff₀' h0, ← Real.le_log_iff_exp_le (div_pos (hf f) h0),
      div_le_iff₀ s.bandwidth_pos]
    unfold faceScore
    constructor <;> intro h <;> linarith
  constructor
  · intro he f hactive
    exact (hequiv f hactive).mp (he f)
  · intro he f
    by_cases hactive : f ∈ s.faces
    · exact (hequiv f hactive).mpr (he f hactive)
    · simp only [weights, hactive, ↓reduceIte, mul_zero]
      exact (hf f).le

noncomputable def randomRectangle (e : ℝ × (Face p → ℝ)) : FaceSmoother p where
  faces := s.faces
  offsets f := s.offsets f + s.bandwidth * Real.log (e.2 f / e.1)
  bandwidth := s.bandwidth
  bandwidth_pos := s.bandwidth_pos

theorem exponentialEvent_iff_randomRectangle_Inside
    (x : Fin p → ℝ) (e : ℝ × (Face p → ℝ))
    (h0 : 0 < e.1) (hf : ∀ f, 0 < e.2 f) :
    e ∈ s.exponentialEvent x ↔ (s.randomRectangle e).Inside x := by
  rw [s.exponentialEvent_iff_random_rectangle x e h0 hf]
  unfold Inside faceScore randomRectangle
  constructor <;> intro h f hactive <;> have hh := h f hactive <;> linarith

theorem measurable_randomRectangle_probability
    (μ : Measure (Fin p → ℝ)) [IsProbabilityMeasure μ] :
    Measurable (fun e => μ.real {x | (s.randomRectangle e).Inside x}) := by
  let E : Set ((ℝ × (Face p → ℝ)) × (Fin p → ℝ)) :=
    {z | (s.randomRectangle z.1).Inside z.2}
  have h0 : Measurable (fun z : (ℝ × (Face p → ℝ)) × (Fin p → ℝ) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hf (f : Face p) :
      Measurable (fun z : (ℝ × (Face p → ℝ)) × (Fin p → ℝ) => z.1.2 f) :=
    (measurable_pi_apply f).comp (measurable_snd.comp measurable_fst)
  have hE : MeasurableSet E := by
    simp only [E, Inside, faceScore, randomRectangle, setOf_forall]
    apply MeasurableSet.iInter
    intro f
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le
      (((continuous_normalDot f).measurable.comp measurable_snd).sub
        (measurable_const.add (measurable_const.mul
          (((hf f).div h0).log)))) measurable_const
  exact (measurable_measure_prodMk_left hE).ennreal_toReal

theorem integrable_randomRectangle_probability
    (μ : Measure (Fin p → ℝ)) [IsProbabilityMeasure μ] :
    Integrable (fun e => μ.real {x | (s.randomRectangle e).Inside x})
      (exponentialRectangleLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (s.measurable_randomRectangle_probability μ).aestronglyMeasurable
  filter_upwards [] with e
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  simpa only [measureReal_univ_eq_one] using
    (measureReal_mono (μ := μ) (subset_univ {x | (s.randomRectangle e).Inside x}))

/-- Averaging against any actual probability law commutes with the random
rectangle representation. All measurability and Fubini premises are proved. -/
theorem integral_F_eq_randomRectangle_average
    (μ : Measure (Fin p → ℝ)) [IsProbabilityMeasure μ] :
    (∫ x, s.F x ∂μ) = ∫ e, μ.real {x | (s.randomRectangle e).Inside x}
      ∂exponentialRectangleLaw p := by
  classical
  let E : Set ((Fin p → ℝ) × (ℝ × (Face p → ℝ))) :=
    {z | z.2 ∈ s.exponentialEvent z.1}
  have hE : MeasurableSet E := by
    simp only [E, exponentialEvent, mem_setOf_eq, mem_iInter, setOf_forall]
    apply MeasurableSet.iInter
    intro f
    exact measurableSet_le ((measurable_fst.comp measurable_snd).mul
      ((s.continuous_weight f).measurable.comp measurable_fst))
      ((measurable_pi_apply f).comp (measurable_snd.comp measurable_snd))
  let g : (Fin p → ℝ) → (ℝ × (Face p → ℝ)) → ℝ :=
    fun x e => E.indicator (fun _ => (1 : ℝ)) (x, e)
  have hg : Integrable (Function.uncurry g) (μ.prod (exponentialRectangleLaw p)) :=
    (integrable_const (1 : ℝ)).indicator hE
  calc
    _ = ∫ x, ∫ e, g x e ∂exponentialRectangleLaw p ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (s.F_eq_exponential_probability x).trans
        (integral_indicator_one (s.measurableSet_exponentialEvent x)).symm
    _ = ∫ e, ∫ x, g x e ∂μ ∂exponentialRectangleLaw p := integral_integral_swap hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [exponentialRectangleLaw_ae_pos p] with e he
      have hge : (fun x => g x e) =
          {x | (s.randomRectangle e).Inside x}.indicator (fun _ => (1 : ℝ)) := by
        funext x
        simp only [g, E, Set.indicator, mem_setOf_eq,
          s.exponentialEvent_iff_randomRectangle_Inside x e he.1 he.2]
      rw [hge]
      exact integral_indicator_one (s.randomRectangle e).measurableSet_Inside

end FaceSmoother

end RectangleCLT
