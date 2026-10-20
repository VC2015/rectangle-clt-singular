import RectangleCLT.ExponentialMixture
import RectangleCLT.GaussianTubeGamma

/-!
# Gamma clocks for powers of the actual rectangle smoother

`gammaClock a` has the concrete Gamma distribution with shape `a+1` and
rate one. All face exponentials are independent of this clock. The resulting
ordinary random rectangle represents the exact power `F^(a+1)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion

noncomputable section

/-- Positive integral shape, indexed from zero to avoid a side condition. -/
def gammaClock (a : ℕ) : Measure ℝ := gammaMeasure ((a : ℝ) + 1) 1

instance gammaClock_probability (a : ℕ) : IsProbabilityMeasure (gammaClock a) :=
  isProbabilityMeasureGamma (by positivity) (by norm_num)

instance gammaClock_noAtoms (a : ℕ) : NoAtoms (gammaClock a) := by
  unfold gammaClock gammaMeasure
  exact ⟨fun x => withDensity_absolutelyContinuous _ _ (measure_singleton x)⟩

theorem gammaClock_ae_pos (a : ℕ) : ∀ᵐ t ∂gammaClock a, 0 < t := by
  have hneg : gammaClock a (Iio 0) = 0 := by
    rw [gammaClock, gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos le_rfl
  have hnonpos : gammaClock a (Iic 0) = 0 := by
    rw [← measure_congr (Iio_ae_eq_Iic : Iio (0 : ℝ) =ᵐ[gammaClock a] Iic 0)]
    exact hneg
  rw [ae_iff]
  simpa only [not_lt, Iic] using hnonpos

private theorem gammaPDFReal_nat (a : ℕ) (t : ℝ) :
    gammaPDFReal ((a : ℝ) + 1) 1 t =
      if 0 ≤ t then (a.factorial : ℝ)⁻¹ * t ^ a * Real.exp (-t) else 0 := by
  unfold gammaPDFReal
  simp only [Real.one_rpow, Real.Gamma_nat_eq_factorial, add_sub_cancel_right,
    Real.rpow_natCast, one_mul, one_div]

/-- Exact Laplace transform of the actual Gamma clock, including `T=0`. -/
theorem gammaClock_laplace (a : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t, Real.exp (-T * t) ∂gammaClock a) = (1 / (1 + T)) ^ (a + 1) := by
  unfold gammaClock gammaMeasure gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
      (measurable_gammaPDFReal ((a : ℝ) + 1) 1).ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [gammaPDF, ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg (by positivity : 0 < (a : ℝ) + 1) (by norm_num : (0 : ℝ) < 1) _),
    smul_eq_mul]
  have hfun : (fun t : ℝ => gammaPDFReal ((a : ℝ) + 1) 1 t * Real.exp (-T * t)) =
      (Ici (0 : ℝ)).indicator
        (fun t => (a.factorial : ℝ)⁻¹ * (t ^ a * Real.exp (-((1 + T) * t)))) := by
    funext t
    rw [gammaPDFReal_nat]
    simp only [Set.indicator, mem_Ici]
    split_ifs
    · rw [show (a.factorial : ℝ)⁻¹ * t ^ a * Real.exp (-t) * Real.exp (-T * t) =
          (a.factorial : ℝ)⁻¹ * (t ^ a * (Real.exp (-t) * Real.exp (-T * t))) by ring,
        ← Real.exp_add]
      congr 3
      ring
    · simp
  rw [hfun, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_natPow_mul_exp_neg_one_add_Ioi a hT]
  have hf : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  rw [one_div_pow]
  field_simp

/-- The Gamma clock and every face exponential are genuinely independent
under this concrete product law. -/
def gammaRectangleLaw (p a : ℕ) : Measure (ℝ × (Face p → ℝ)) :=
  (gammaClock a).prod (faceExponentialLaw p)

instance gammaRectangleLaw_probability (p a : ℕ) :
    IsProbabilityMeasure (gammaRectangleLaw p a) := by
  unfold gammaRectangleLaw
  infer_instance

theorem gammaRectangleLaw_ae_pos (p a : ℕ) :
    ∀ᵐ e ∂gammaRectangleLaw p a, 0 < e.1 ∧ ∀ f, 0 < e.2 f := by
  exact ((Measure.quasiMeasurePreserving_fst (μ := gammaClock a)
    (ν := faceExponentialLaw p)).ae (gammaClock_ae_pos a)).and
    ((Measure.quasiMeasurePreserving_snd (μ := gammaClock a)
      (ν := faceExponentialLaw p)).ae (faceExponentialLaw_ae_pos p))

/-- Conditional on any positive clock, each logarithmic exponential
threshold has an atomless actual distribution. -/
theorem unitExponential_log_div_noAtoms {t : ℝ} (ht : 0 < t) :
    NoAtoms (unitExponential.map (fun x : ℝ => Real.log (x / t))) := by
  constructor
  intro c
  have hlog : Measurable (fun x : ℝ => Real.log (x / t)) := (measurable_id.div_const t).log
  rw [Measure.map_apply hlog (measurableSet_singleton c)]
  have hset : (fun x : ℝ => Real.log (x / t)) ⁻¹' {c} =ᵐ[unitExponential]
      ({t * Real.exp c} : Set ℝ) := by
    filter_upwards [unitExponential_ae_pos] with x hx
    change (Real.log (x / t) = c) = (x = t * Real.exp c)
    apply propext
    constructor
    · intro heq
      have hh := congrArg Real.exp heq
      rw [Real.exp_log (div_pos hx ht)] at hh
      calc
        x = (x / t) * t := (div_mul_cancel₀ x ht.ne').symm
        _ = Real.exp c * t := by rw [hh]
        _ = t * Real.exp c := mul_comm _ _
    · intro heq
      rw [heq, mul_div_cancel_left₀ _ ht.ne', Real.log_exp]
  rw [measure_congr hset]
  exact measure_singleton _

/-- Adding a fixed face offset and a positive bandwidth keeps these
conditional threshold laws atomless. -/
theorem unitExponential_offset_log_noAtoms (o : ℝ) {h t : ℝ}
    (hh : 0 < h) (ht : 0 < t) :
    NoAtoms (unitExponential.map (fun x : ℝ => o + h * Real.log (x / t))) := by
  have hlog : Measurable (fun x : ℝ => Real.log (x / t)) := (measurable_id.div_const t).log
  have haff : Measurable (fun y : ℝ => o + h * y) :=
    measurable_const.add (measurable_const.mul measurable_id)
  change NoAtoms (unitExponential.map
    ((fun y : ℝ => o + h * y) ∘ (fun x : ℝ => Real.log (x / t))))
  rw [← Measure.map_map haff hlog]
  letI := unitExponential_log_div_noAtoms ht
  constructor
  intro c
  rw [Measure.map_apply haff (measurableSet_singleton c)]
  have hset : (fun y : ℝ => o + h * y) ⁻¹' {c} = {(c - o) / h} := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, eq_div_iff hh.ne']
    constructor <;> intro heq <;> linarith
  rw [hset]
  exact measure_singleton _

/-- For each fixed clock, the complete threshold vector has the actual
product of the transformed exponential marginal laws. This records the
conditional independence used in the random-polyhedron argument. -/
theorem faceExponential_offsets_map_eq_pi {p : ℕ} (s : FaceSmoother p) (t : ℝ) :
    (faceExponentialLaw p).map (fun e f => s.offsets f +
      s.bandwidth * Real.log (e f / t)) =
      Measure.pi (fun f : Face p => unitExponential.map
        (fun x : ℝ => s.offsets f + s.bandwidth * Real.log (x / t))) := by
  have hm (f : Face p) : Measurable
      (fun x : ℝ => s.offsets f + s.bandwidth * Real.log (x / t)) :=
    measurable_const.add (measurable_const.mul (measurable_id.div_const t).log)
  letI (f : Face p) : IsProbabilityMeasure (unitExponential.map
      (fun x : ℝ => s.offsets f + s.bandwidth * Real.log (x / t))) :=
    isProbabilityMeasure_map (hm f).aemeasurable
  exact (measurePreserving_pi (fun _ : Face p => unitExponential)
    (fun f : Face p => unitExponential.map
      (fun x : ℝ => s.offsets f + s.bandwidth * Real.log (x / t)))
    (fun f => ⟨hm f, rfl⟩)).map_eq

end

end RectangleCLT.Companion

namespace RectangleCLT.FaceSmoother

open RectangleCLT.Companion

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

/-- A Gamma clock of shape `a+1` represents exactly the corresponding
natural power of the concrete null-face probability. -/
theorem F_pow_eq_gamma_probability (a : ℕ) (x : Vector p) :
    s.F x ^ (a + 1) = (gammaRectangleLaw p a).real (s.exponentialEvent x) := by
  let g := (s.exponentialEvent x).indicator (fun _ => (1 : ℝ))
  have hg : Integrable g (gammaRectangleLaw p a) :=
    (integrable_const (1 : ℝ)).indicator (s.measurableSet_exponentialEvent x)
  have hinner : ∀ᵐ t ∂gammaClock a,
      (∫ e, g (t, e) ∂faceExponentialLaw p) = Real.exp (-((s.weights x).T) * t) := by
    filter_upwards [gammaClock_ae_pos a] with t ht
    change (∫ e, {e : Face p → ℝ | ∀ f, t * (s.weights x).weight f ≤ e f}.indicator
      (fun _ => (1 : ℝ)) e ∂faceExponentialLaw p) = _
    rw [integral_indicator_const (1 : ℝ)
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
    _ = ∫ t, Real.exp (-((s.weights x).T) * t) ∂gammaClock a := by
      exact (gammaClock_laplace a (s.weights x).T_nonneg).symm
    _ = ∫ t, ∫ e, g (t, e) ∂faceExponentialLaw p ∂gammaClock a :=
      (integral_congr_ae hinner).symm
    _ = ∫ z, g z ∂gammaRectangleLaw p a := (integral_prod g hg).symm
    _ = _ := integral_indicator_one (s.measurableSet_exponentialEvent x)

/-- On positive samples the Gamma comparison is the same explicit random
rectangle as in the exponential-clock construction. -/
theorem F_pow_eq_gamma_randomRectangle_probability (a : ℕ) (x : Vector p) :
    s.F x ^ (a + 1) =
      (gammaRectangleLaw p a).real {e | (s.randomRectangle e).Inside x} := by
  rw [s.F_pow_eq_gamma_probability]
  apply measureReal_congr
  filter_upwards [gammaRectangleLaw_ae_pos p a] with e he
  exact propext (s.exponentialEvent_iff_randomRectangle_Inside x e he.1 he.2)

theorem integrable_gamma_randomRectangle_probability (a : ℕ)
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] :
    Integrable (fun e => μ.real {x | (s.randomRectangle e).Inside x})
      (gammaRectangleLaw p a) := by
  apply (integrable_const (1 : ℝ)).mono'
    (s.measurable_randomRectangle_probability μ).aestronglyMeasurable
  filter_upwards [] with e
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  simpa only [measureReal_univ_eq_one] using
    (measureReal_mono (μ := μ) (subset_univ {x | (s.randomRectangle e).Inside x}))

/-- Actual probability-space averaging commutes with the Gamma mixture.
All joint measurability and Fubini hypotheses are discharged. -/
theorem integral_F_pow_eq_gamma_randomRectangle_average (a : ℕ)
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] :
    (∫ x, s.F x ^ (a + 1) ∂μ) =
      ∫ e, μ.real {x | (s.randomRectangle e).Inside x} ∂gammaRectangleLaw p a := by
  classical
  let E : Set ((Vector p) × (ℝ × (Face p → ℝ))) :=
    {z | z.2 ∈ s.exponentialEvent z.1}
  have hE : MeasurableSet E := by
    simp only [E, exponentialEvent, mem_setOf_eq, mem_iInter, setOf_forall]
    apply MeasurableSet.iInter
    intro f
    exact measurableSet_le ((measurable_fst.comp measurable_snd).mul
      ((s.continuous_weight f).measurable.comp measurable_fst))
      ((measurable_pi_apply f).comp (measurable_snd.comp measurable_snd))
  let g : Vector p → (ℝ × (Face p → ℝ)) → ℝ :=
    fun x e => E.indicator (fun _ => (1 : ℝ)) (x, e)
  have hg : Integrable (Function.uncurry g) (μ.prod (gammaRectangleLaw p a)) :=
    (integrable_const (1 : ℝ)).indicator hE
  calc
    _ = ∫ x, ∫ e, g x e ∂gammaRectangleLaw p a ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (s.F_pow_eq_gamma_probability a x).trans
        (integral_indicator_one (s.measurableSet_exponentialEvent x)).symm
    _ = ∫ e, ∫ x, g x e ∂μ ∂gammaRectangleLaw p a := integral_integral_swap hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [gammaRectangleLaw_ae_pos p a] with e he
      have hge : (fun x => g x e) =
          {x | (s.randomRectangle e).Inside x}.indicator (fun _ => (1 : ℝ)) := by
        funext x
        simp only [g, E, Set.indicator, mem_setOf_eq,
          s.exponentialEvent_iff_randomRectangle_Inside x e he.1 he.2]
      rw [hge]
      exact integral_indicator_one (s.randomRectangle e).measurableSet_Inside

end

end RectangleCLT.FaceSmoother
