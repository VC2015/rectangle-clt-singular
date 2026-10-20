import RectangleCLTCompanion.SharpMatrixApplication
import RectangleCLTCompanion.SignedSurfaceScoreExpansion
import RectangleCLTCompanion.SignedSurfaceConcentration
import RectangleCLTCompanion.SignedSurfaceClosure

/-! Actual signed trace and matrix estimates on the full split base. The
proof combines actual bounded/Gaussian concentration, the checked signed
surface theorem, exact base-law transports, and a finite binomial identity. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

open SignedSurface

/-- The actual vector law of the full retained array plus one Gaussian half. -/
def splitBaseDistribution {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) : Measure (Vector p) :=
  (splitBaseLaw μ ξ t).map (splitBaseValue A x t)

theorem splitBaseDistribution_isProbability
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (splitBaseDistribution μ ξ A x t) := by
  letI := splitBaseLaw_isProbability μ ξ hξ ht ht1
  exact isProbabilityMeasure_map (measurable_splitBaseValue A x t).aemeasurable

/-- No individual selector mask is conditioned upon in this representation. -/
theorem splitBaseDistribution_eq_bounded_shift
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) :
    splitBaseDistribution μ ξ A x t =
      ((bernoulliArrayLaw μ ξ t).prod (standardGaussian p)).map
        (fun z : (Fin n → Vector p) × Vector p =>
          sumVector (fun i (b : Fin n → Vector p) => b i) z.1 +
            (x + (splitGaussianScale t • A).mulVec z.2)) := by
  apply Measure.map_congr
  exact ae_of_all _ fun z => by
    simp only [splitBaseValue, arraySum, sumVector]
    abel

/-- The same vector law has a Gaussian base with the retained array as an
independent shift. Singular Gaussian factors are allowed. -/
theorem splitBaseDistribution_eq_gaussian_shift
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    splitBaseDistribution μ ξ A x t =
      ((gaussianLaw (splitGaussianScale t • A)).prod (bernoulliArrayLaw μ ξ t)).map
        (fun z : Vector p × (Fin n → Vector p) => z.1 + (x + arraySum z.2)) := by
  let B := bernoulliArrayLaw μ ξ t
  let G := splitGaussianScale t • A
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  let f : ((Fin n → Vector p) × Vector p) → Vector p × (Fin n → Vector p) :=
    fun z => (G.mulVec z.2, z.1)
  have hf : MeasurePreserving f (B.prod (standardGaussian p)) ((gaussianLaw G).prod B) :=
    (Measure.measurePreserving_swap (μ := B) (ν := gaussianLaw G)).comp
      ((MeasurePreserving.id B).prod
        (show MeasurePreserving G.mulVec (standardGaussian p) (gaussianLaw G) from
          ⟨measurable_mulVec G, rfl⟩))
  have hV : Measurable (fun z : Vector p × (Fin n → Vector p) => z.1 + (x + arraySum z.2)) :=
    measurable_fst.add (measurable_const.add ((measurable_arraySum p n).comp measurable_snd))
  change (B.prod (standardGaussian p)).map (splitBaseValue A x t) = _
  rw [← hf.map_eq, Measure.map_map hV hf.measurable]
  apply Measure.map_congr
  exact ae_of_all _ fun z => by simp only [Function.comp_apply, f, splitBaseValue, G]; abel


/-- A common constant for actual bounded and Gaussian shell concentration. -/
def splitBoundaryConstant : ℝ := 1073741824 + 12 * Real.exp (3 / 2 : ℝ)

theorem splitBoundaryConstant_nonneg : 0 ≤ splitBoundaryConstant := by
  unfold splitBoundaryConstant
  positivity

private theorem uniformBoundaryConcentration_weaken {p : ℕ}
    {μ : Measure (Vector p)} {C C' η η' v : ℝ}
    (hconc : UniformBoundaryConcentration μ C η v) (hp : 1 ≤ p)
    (hC : 0 ≤ C) (hCC : C ≤ C') (hη : 0 ≤ η) (hηη : η ≤ η')
    (hv : (1 / 4 : ℝ) ≤ v) :
    UniformBoundaryConcentration μ C' η' (1 / 4) := by
  intro sm r d hd
  have hC' : 0 ≤ C' := hC.trans hCC
  have hv0 : 0 < v := by linarith
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hroot : Real.sqrt (dimensionLog p / v) ≤ Real.sqrt (dimensionLog p / (1 / 4)) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left hL (by norm_num) hv
  exact (hconc sm r d hd).trans (mul_le_mul
    (mul_le_mul hCC (add_le_add_left hηη d) (by linarith) hC') hroot
      (Real.sqrt_nonneg _) (mul_nonneg hC' (by linarith)))

/-- Uniform shell concentration for the actual complete split base. This
combines the bounded and Gaussian time ranges with their proved input laws. -/
theorem uniformBoundaryConcentration_splitBase
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ)) (x : Vector p)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    UniformBoundaryConcentration (splitBaseDistribution μ ξ A x t)
      splitBoundaryConstant (2 * δ) (1 / 4) := by
  let B := bernoulliArrayLaw μ ξ t
  let G := splitGaussianScale t • A
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ hdata.measurable t ht ht1
  by_cases hhalf : t ≤ 1 / 2
  · have hv : 0 < 1 - t := by linarith
    have hb := uniformBoundaryConcentration_bounded_shift (hdata.thinned t ht ht1)
      hp hv (hdata.thinned_sum_unit_diagonal hunit t ht ht1) (standardGaussian p)
      (fun g => x + G.mulVec g) (measurable_const.add (measurable_mulVec G))
    rw [splitBaseDistribution_eq_bounded_shift]
    exact uniformBoundaryConcentration_weaken hb hp (by norm_num)
      (by unfold splitBoundaryConstant; linarith [Real.exp_nonneg (3 / 2 : ℝ)])
      (mul_nonneg (by norm_num) hdata.delta_nonneg) le_rfl (by linarith)
  · have hthalf : 1 / 2 ≤ t := le_of_lt (lt_of_not_ge hhalf)
    have hv : 0 < t / 2 := by linarith
    have hdiag (j : Fin p) : (G * G.transpose) j j = t / 2 := by
      have hh := congrArg (fun Q : Matrix (Fin p) (Fin p) ℝ => Q j j)
        (interpolatedGaussian_covariance A (show 0 ≤ t / 2 by positivity))
      rw [covariance_gaussianLaw] at hh
      simpa only [interpolatedGaussianFactor, Matrix.smul_apply, smul_eq_mul, hA, hunit,
        mul_one, G, splitGaussianScale] using hh
    have hg := uniformBoundaryConcentration_gaussian_shift hp G hv hdiag B
      (fun b => x + arraySum b) (measurable_const.add (measurable_arraySum p n))
    rw [splitBaseDistribution_eq_gaussian_shift μ ξ hdata.measurable A x ht ht1]
    exact uniformBoundaryConcentration_weaken hg hp (by positivity)
      (by unfold splitBoundaryConstant; linarith)
      le_rfl (mul_nonneg (by norm_num) hdata.delta_nonneg) (by linarith)

/-- The late-time cutoff supplies exactly the Gaussian scale needed to
absorb the bounded-array lattice term. -/
theorem splitGaussianScale_ge_two_delta_sqrt {δ t L : ℝ}
    (hδ : 0 ≤ δ) (hL : 0 ≤ L) (ht : 0 ≤ t) (hcut : 8 * δ ^ 2 * L ≤ t) :
    2 * δ * Real.sqrt L ≤ splitGaussianScale t := by
  have hs : 0 ≤ splitGaussianScale t := Real.sqrt_nonneg _
  have ha : 0 ≤ 2 * δ * Real.sqrt L := by positivity
  have he : (2 * δ * Real.sqrt L) ^ 2 = 4 * δ ^ 2 * L := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hL]
    ring
  have hsq := splitGaussianScale_sq ht
  nlinarith


/-- The interpolation switching scale is stronger than the lattice cutoff. -/
theorem splitGaussianScale_ge_two_delta_sqrt_of_bandwidth
    {δ h t L : ℝ} (hδ : 0 ≤ δ) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hband : 12 * δ ≤ h) (hcut : L * h ^ 2 ≤ t) :
    2 * δ * Real.sqrt L ≤ splitGaussianScale t := by
  apply splitGaussianScale_ge_two_delta_sqrt hδ hL ht
  have hs := pow_le_pow_left₀ (show 0 ≤ 12 * δ by positivity) hband 2
  have hs' : 8 * δ ^ 2 ≤ h ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hs' hL]

/-- The actual first Gaussian half has diagonal covariance `t/2`. -/
theorem splitGaussianFactor_diagonal {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A * A.transpose) j j = 1)
    {t : ℝ} (ht : 0 ≤ t) (j : Fin p) :
    (((splitGaussianScale t • A) * (splitGaussianScale t • A).transpose)) j j = t / 2 := by
  have hh := congrArg (fun Q : Matrix (Fin p) (Fin p) ℝ => Q j j)
    (interpolatedGaussian_covariance A (show 0 ≤ t / 2 by positivity))
  rw [covariance_gaussianLaw] at hh
  simpa only [interpolatedGaussianFactor, Matrix.smul_apply, smul_eq_mul, hA, mul_one,
    splitGaussianScale] using hh

/-- Exact transport of an averaged power trace to any concrete base map. -/
theorem averagedGaussianPowerTrace_map_eq_integral
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (a : ℕ) :
    averagedGaussianPowerTrace (ν.map V) s A a =
      ∫ ω, gaussianPowerTrace s A (V ω) a ∂ν := by
  letI : IsProbabilityMeasure (ν.map V) := isProbabilityMeasure_map hV.aemeasurable
  rw [averagedGaussianPowerTrace_eq_integral]
  exact integral_map hV.aemeasurable
    (integrable_gaussianPowerTrace_base (ν.map V) s A a).aestronglyMeasurable

/-- The signed tuple sum in the matrix estimate is the actual scalar
selector trace of the vector-valued base law. -/
theorem integral_selectorGaussianScore_trace_eq_averaged
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (q : ℕ) :
    (∫ ω, ∑ α : Fin q → Face p, Matrix.trace (selectorGaussianScore s A V α ω) ∂ν) =
      averagedGaussianSelectorTrace (ν.map V) s A q := by
  letI : IsProbabilityMeasure (ν.map V) := isProbabilityMeasure_map hV.aemeasurable
  rw [averagedGaussianSelectorTrace_eq_integral]
  rw [integral_map hV.aemeasurable
    (integrable_gaussianSelectorTrace_base (ν.map V) s A q).aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => sum_selectorWeight_trace_eq_gaussianSelectorTrace s A (V ω) q

/-- A simple universal constant absorbs both the binomial sum and its
power-trace constant, with no dependence on the tuple order. -/
def splitTraceConstant (C : ℝ) : ℝ := 2 * (C + 1)

theorem splitTraceConstant_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ splitTraceConstant C := by
  unfold splitTraceConstant
  positivity

private theorem selector_binomial_constant_le {C : ℝ} (hC : 0 ≤ C) {q : ℕ} (hq : 1 ≤ q) :
    (2 : ℝ) ^ (q - 1) * C ≤ splitTraceConstant C ^ (q + 1) := by
  have hD : 2 ≤ splitTraceConstant C := by unfold splitTraceConstant; linarith
  have hCD : C ≤ splitTraceConstant C := by unfold splitTraceConstant; linarith
  calc
    _ ≤ splitTraceConstant C ^ q * splitTraceConstant C :=
      mul_le_mul
        ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : q - 1 ≤ q)).trans
          (pow_le_pow_left₀ (by norm_num) hD q)) hCD hC
        (pow_nonneg (by linarith) _)
    _ = _ := (pow_succ _ _).symm

/-- Genuine finite-binomial closure of actual power trace estimates on the
full split base, in precisely the form consumed by the matrix application. -/
theorem signed_trace_splitBase_le_of_power_bounds
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (s : FaceSmoother p)
    {t C : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hpower : ∀ a : ℕ,
      |averagedGaussianPowerTrace (splitBaseDistribution μ ξ A x t) s
        (splitGaussianScale t • A) a| ≤
          C * (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) / ((a : ℝ) + 1)) :
    ∀ q : ℕ, 1 ≤ q →
      -(∫ ω, ∑ α : Fin q → Face p,
        Matrix.trace (selectorGaussianScore s (splitGaussianScale t • A)
          (splitBaseValue A x t) α ω) ∂splitBaseLaw μ ξ t) ≤
        splitTraceConstant C ^ (q + 1) *
          (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
  letI := splitBaseLaw_isProbability μ ξ hξ ht ht1
  letI := splitBaseDistribution_isProbability μ ξ hξ A x ht ht1
  let T := s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)
  have hT : 0 ≤ T := mul_nonneg (mul_nonneg s.bandwidth_pos.le
    (zero_le_one.trans (log_exp_mul_nat_ge_one hp))) (Real.sqrt_nonneg _)
  intro q hq
  rw [integral_selectorGaussianScore_trace_eq_averaged
    (splitBaseLaw μ ξ t) (splitBaseValue A x t) (measurable_splitBaseValue A x t)]
  change -averagedGaussianSelectorTrace (splitBaseDistribution μ ξ A x t) s
    (splitGaussianScale t • A) q ≤ _
  have hh := abs_averagedGaussianSelectorTrace_le_of_power_bounds
    (splitBaseDistribution μ ξ A x t) s (splitGaussianScale t • A) hq
    (mul_nonneg hC hT) (fun a _ => hpower a)
  calc
    _ ≤ |averagedGaussianSelectorTrace (splitBaseDistribution μ ξ A x t) s
      (splitGaussianScale t • A) q| := neg_le_abs _
    _ ≤ (2 : ℝ) ^ (q - 1) * (C * T) := hh
    _ ≤ splitTraceConstant C ^ (q + 1) * T := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (selector_binomial_constant_le hC hq) hT



/-- A vanishing Gaussian factor has zero actual signed power score. -/
theorem gaussianPowerTrace_zero_factor {p r : ℕ}
    (s : FaceSmoother p) (v : Vector p) (a : ℕ) :
    gaussianPowerTrace s (0 : Matrix (Fin p) (Fin r) ℝ) v a = 0 := by
  unfold gaussianPowerTrace
  simp only [Matrix.zero_mulVec, zero_add]
  rw [integral_mul_const,
    integral_sub (standardGaussian_integrable_vectorNormSq r) (integrable_const (r : ℝ)),
    standardGaussian_integral_vectorNormSq]
  simp

theorem averagedGaussianPowerTrace_zero_factor {p r : ℕ}
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] (s : FaceSmoother p) (a : ℕ) :
    averagedGaussianPowerTrace μ s (0 : Matrix (Fin p) (Fin r) ℝ) a = 0 := by
  rw [averagedGaussianPowerTrace_eq_integral]
  simp only [gaussianPowerTrace_zero_factor, integral_zero]

/-- The scale condition removes the lattice term from the actual surface
estimate, with an explicit factor two. -/
theorem signed_surface_lattice_factor_le {η σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 ≤ L) (hsmall : η * Real.sqrt L ≤ σ) :
    L * Real.sqrt L + (η / σ) * L ^ 2 ≤ 2 * (L * Real.sqrt L) := by
  have hr : η * Real.sqrt L / σ ≤ 1 := (div_le_one hσ).mpr hsmall
  have hLs : 0 ≤ L * Real.sqrt L := mul_nonneg hL (Real.sqrt_nonneg _)
  have heq : (η / σ) * L ^ 2 =
      (η * Real.sqrt L / σ) * (L * Real.sqrt L) := by
    rw [show (η * Real.sqrt L / σ) * (L * Real.sqrt L) =
      (η / σ) * L * (Real.sqrt L) ^ 2 by ring, Real.sq_sqrt hL]
    ring
  rw [heq]
  have hh := mul_le_mul_of_nonneg_right hr hLs
  nlinarith

theorem signed_surface_power_rate_le {C h η σ L : ℝ}
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hσ : 0 < σ) (hL : 0 ≤ L)
    (hsmall : η * Real.sqrt L ≤ σ) (a : ℕ) :
    C * h / ((a : ℝ) + 1) *
      (L * Real.sqrt L + (η / σ) * L ^ 2) ≤
        (2 * C) * (h * L * Real.sqrt L) / ((a : ℝ) + 1) := by
  calc
    _ ≤ C * h / ((a : ℝ) + 1) * (2 * (L * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (signed_surface_lattice_factor_le hσ hL hsmall)
        (div_nonneg (mul_nonneg hC hh) (by positivity))
    _ = _ := by ring

/-- Direct application interface for the independently proved actual
power-trace bound. The power premise is explicit at this intermediate step. -/
theorem averagedSelectorMatrixEstimate_splitBase_of_power_bounds
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ C : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (s : FaceSmoother p) (hband : 12 * δ ≤ s.bandwidth)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (hpower : ∀ a : ℕ,
      |averagedGaussianPowerTrace (splitBaseDistribution μ ξ A x t) s
        (splitGaussianScale t • A) a| ≤
          C * (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) / ((a : ℝ) + 1)) :
    AveragedSelectorMatrixEstimate s (splitBaseLaw μ ξ t)
      (splitGaussianScale t • A) (splitBaseValue A x t)
      (splitSelectorMatrixConstant (splitTraceConstant C))
      (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) :=
  averagedSelectorMatrixEstimate_splitBase_of_signed_trace_bound hdata hp hunit A hA x s
    hband ht ht1 (splitTraceConstant_nonneg hC)
    (signed_trace_splitBase_le_of_power_bounds μ ξ hdata.measurable A x s ht ht1 hp hC hpower)


/-- The genuine universal power-trace constant for the complete split base. -/
def splitPowerTraceConstant : ℝ := surfaceClosureConstant splitBoundaryConstant

theorem splitPowerTraceConstant_nonneg : 0 ≤ splitPowerTraceConstant :=
  surfaceClosureConstant_nonneg splitBoundaryConstant_nonneg

/-- The final universal matrix constant used by the sharp comparison. -/
def sharpSplitMatrixConstant : ℝ :=
  splitSelectorMatrixConstant (splitTraceConstant splitPowerTraceConstant)

theorem one_le_sharpSplitMatrixConstant : 1 ≤ sharpSplitMatrixConstant :=
  one_le_splitSelectorMatrixConstant (splitTraceConstant_nonneg splitPowerTraceConstant_nonneg)

/-- Actual per-power signed trace estimate on the complete retained-array
and half-Gaussian base. No quantitative trace or derivative premise remains. -/
theorem abs_averagedGaussianPowerTrace_splitBase_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (s : FaceSmoother p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hscale : 2 * δ * Real.sqrt (dimensionLog p) ≤ splitGaussianScale t) (a : ℕ) :
    |averagedGaussianPowerTrace (splitBaseDistribution μ ξ A x t) s
      (splitGaussianScale t • A) a| ≤
        splitPowerTraceConstant *
          (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) / ((a : ℝ) + 1) := by
  letI := splitBaseDistribution_isProbability μ ξ hdata.measurable A x ht ht1
  by_cases htpos : 0 < t
  · have hdiag (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA, hunit]
    have hh := abs_averagedGaussianPowerTrace_le_concentration hp
      (splitBaseDistribution μ ξ A x t)
      (uniformBoundaryConcentration_splitBase hdata hp hunit A hA x ht ht1)
      splitBoundaryConstant_nonneg (mul_nonneg (by norm_num) hdata.delta_nonneg)
      (le_refl (1 / 4 : ℝ)) s a A hdiag (splitGaussianScale_pos htpos) hscale
    exact hh.trans_eq (by dsimp [splitPowerTraceConstant]; ring)
  · have htzero : t = 0 := by linarith
    subst t
    simp only [splitGaussianScale, zero_div, Real.sqrt_zero, zero_smul,
      averagedGaussianPowerTrace_zero_factor, abs_zero]
    exact div_nonneg (mul_nonneg splitPowerTraceConstant_nonneg
      (mul_nonneg (mul_nonneg s.bandwidth_pos.le
        (zero_le_one.trans (log_exp_mul_nat_ge_one hp))) (Real.sqrt_nonneg _))) (by positivity)

/-- The actual signed selector-family trace estimate at the lattice cutoff. -/
theorem signed_trace_splitBase_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (s : FaceSmoother p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hcut : 8 * δ ^ 2 * dimensionLog p ≤ t) :
    ∀ q : ℕ, 1 ≤ q →
      -(∫ ω, ∑ α : Fin q → Face p,
        Matrix.trace (selectorGaussianScore s (splitGaussianScale t • A)
          (splitBaseValue A x t) α ω) ∂splitBaseLaw μ ξ t) ≤
        splitTraceConstant splitPowerTraceConstant ^ (q + 1) *
          (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
  have hscale := splitGaussianScale_ge_two_delta_sqrt hdata.delta_nonneg
    (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) ht hcut
  exact signed_trace_splitBase_le_of_power_bounds μ ξ hdata.measurable A x s ht ht1 hp
    splitPowerTraceConstant_nonneg
    (abs_averagedGaussianPowerTrace_splitBase_le hdata hp hunit A hA x s ht ht1 hscale)

/-- Fully discharged actual matrix estimate on the late interpolation
window. Its hypotheses contain no concentration, trace, or derivative oracle. -/
theorem averagedSelectorMatrixEstimate_splitBase
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (s : FaceSmoother p) (hband : 12 * δ ≤ s.bandwidth)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hlate : s.bandwidth ^ 2 * dimensionLog p ≤ t) :
    AveragedSelectorMatrixEstimate s (splitBaseLaw μ ξ t)
      (splitGaussianScale t • A) (splitBaseValue A x t) sharpSplitMatrixConstant
      (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
  have hscale := splitGaussianScale_ge_two_delta_sqrt_of_bandwidth hdata.delta_nonneg
    (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) ht hband
    (by
      change dimensionLog p * s.bandwidth ^ 2 ≤ t
      rw [mul_comm (dimensionLog p) (s.bandwidth ^ 2)]
      exact hlate)
  exact averagedSelectorMatrixEstimate_splitBase_of_power_bounds hdata hp hunit A hA x s
    hband ht ht1 splitPowerTraceConstant_nonneg
    (abs_averagedGaussianPowerTrace_splitBase_le hdata hp hunit A hA x s ht ht1 hscale)

end
end RectangleCLT.Companion
