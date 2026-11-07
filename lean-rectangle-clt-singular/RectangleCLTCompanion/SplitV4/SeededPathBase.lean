import RectangleCLTCompanion.SplitV4.SeededInterpolation
import RectangleCLTCompanion.SplitV4.NuclearSelectorMatrixInterface
import RectangleCLTCompanion.SharpTraceApplication

/-! Actual concentrated base for the seeded Gaussian half split. The
full retained-array law is retained throughout; no mask is conditioned upon
when the rectangle concentration theorem is applied. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def seededSplitGaussianScale (ε t : ℝ) : ℝ := Real.sqrt ((t + ε) / 2)

def seededSplitBaseValue {p n : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (ε t : ℝ) (z : (Fin n → Vector p) × Vector p) : Vector p :=
  x + arraySum z.1 + (seededSplitGaussianScale ε t • A).mulVec z.2

@[fun_prop] theorem measurable_seededSplitBaseValue {p n : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε t : ℝ) :
    Measurable (seededSplitBaseValue (n := n) A x ε t) :=
  (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
    ((measurable_mulVec _).comp measurable_snd)

def seededSplitBaseDistribution {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε t : ℝ) : Measure (Vector p) :=
  (splitBaseLaw μ ξ t).map (seededSplitBaseValue A x ε t)

theorem seededSplitBaseDistribution_isProbability
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (seededSplitBaseDistribution μ ξ A x ε t) := by
  letI := splitBaseLaw_isProbability μ ξ hξ ht ht1
  exact isProbabilityMeasure_map (measurable_seededSplitBaseValue A x ε t).aemeasurable

theorem seededSplitGaussianScale_sq {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    seededSplitGaussianScale ε t ^ 2 = (t + ε) / 2 :=
  Real.sq_sqrt (by positivity)

theorem seededSplitGaussianScale_pos {ε t : ℝ} (htε : 0 < t + ε) :
    0 < seededSplitGaussianScale ε t := Real.sqrt_pos.mpr (by linarith)

theorem seededSplitBaseDistribution_eq_bounded_shift
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε t : ℝ) :
    seededSplitBaseDistribution μ ξ A x ε t =
      ((bernoulliArrayLaw μ ξ t).prod (standardGaussian p)).map
        (fun z : (Fin n → Vector p) × Vector p =>
          sumVector (fun i (b : Fin n → Vector p) => b i) z.1 +
            (x + (seededSplitGaussianScale ε t • A).mulVec z.2)) := by
  apply Measure.map_congr
  exact ae_of_all _ (fun z => by simp only [seededSplitBaseValue, arraySum, sumVector]; abel)

theorem seededSplitBaseDistribution_eq_gaussian_shift
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    seededSplitBaseDistribution μ ξ A x ε t =
      ((gaussianLaw (seededSplitGaussianScale ε t • A)).prod (bernoulliArrayLaw μ ξ t)).map
        (fun z : Vector p × (Fin n → Vector p) => z.1 + (x + arraySum z.2)) := by
  let B := bernoulliArrayLaw μ ξ t
  let G := seededSplitGaussianScale ε t • A
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
  change (B.prod (standardGaussian p)).map (seededSplitBaseValue A x ε t) = _
  rw [← hf.map_eq, Measure.map_map hV hf.measurable]
  apply Measure.map_congr
  exact ae_of_all _ (fun z => by simp only [Function.comp_apply, f, seededSplitBaseValue, G]; abel)

theorem uniformBoundaryConcentration_weaken_seeded {p : ℕ}
    {μ : Measure (Vector p)} {C C' η η' v : ℝ}
    (hc : SignedSurface.UniformBoundaryConcentration μ C η v) (hp : 1 ≤ p)
    (hC : 0 ≤ C) (hCC : C ≤ C') (hη : 0 ≤ η) (hηη : η ≤ η')
    (hv : (1 / 4 : ℝ) ≤ v) :
    SignedSurface.UniformBoundaryConcentration μ C' η' (1 / 4) := by
  intro s r d hd
  have hC' : 0 ≤ C' := hC.trans hCC
  have hv0 : 0 < v := by linarith
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hroot : Real.sqrt (dimensionLog p / v) ≤ Real.sqrt (dimensionLog p / (1 / 4)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hL (by norm_num) hv)
  exact (hc s r d hd).trans (mul_le_mul
    (mul_le_mul hCC (add_le_add_left hηη d) (by linarith) hC') hroot
      (Real.sqrt_nonneg _) (mul_nonneg hC' (by linarith)))

theorem uniformBoundaryConcentration_seededSplitBase
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    SignedSurface.UniformBoundaryConcentration (seededSplitBaseDistribution μ ξ A x ε t)
      splitBoundaryConstant (2 * δ) (1 / 4) := by
  let B := bernoulliArrayLaw μ ξ t
  let G := seededSplitGaussianScale ε t • A
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ hdata.measurable t ht ht1
  by_cases hhalf : t ≤ 1 / 2
  · have hv : 0 < 1 - t := by linarith
    have hb := SignedSurface.uniformBoundaryConcentration_bounded_shift (hdata.thinned t ht ht1)
      hp hv (hdata.thinned_sum_unit_diagonal hunit t ht ht1) (standardGaussian p)
      (fun g => x + G.mulVec g) (measurable_const.add (measurable_mulVec G))
    rw [seededSplitBaseDistribution_eq_bounded_shift]
    exact uniformBoundaryConcentration_weaken_seeded hb hp (by norm_num)
      (by unfold splitBoundaryConstant; linarith [Real.exp_nonneg (3 / 2 : ℝ)])
      (mul_nonneg (by norm_num) hdata.delta_nonneg) le_rfl (by linarith)
  · have hv : 0 < (t + ε) / 2 := by linarith
    have hdiag (j : Fin p) : (G * G.transpose) j j = (t + ε) / 2 := by
      have hh := congrArg (fun Q : Matrix (Fin p) (Fin p) ℝ => Q j j)
        (interpolatedGaussian_covariance A (show 0 ≤ (t + ε) / 2 by positivity))
      rw [covariance_gaussianLaw] at hh
      simpa only [interpolatedGaussianFactor, Matrix.smul_apply, smul_eq_mul, hA, hunit,
        mul_one, G, seededSplitGaussianScale] using hh
    have hg := SignedSurface.uniformBoundaryConcentration_gaussian_shift hp G hv hdiag B
      (fun b => x + arraySum b) (measurable_const.add (measurable_arraySum p n))
    rw [seededSplitBaseDistribution_eq_gaussian_shift μ ξ hdata.measurable A x ε ht ht1]
    exact uniformBoundaryConcentration_weaken_seeded hg hp (by positivity)
      (by unfold splitBoundaryConstant; linarith)
      le_rfl (mul_nonneg (by norm_num) hdata.delta_nonneg) (by linarith)

def seededBaseConcentrationConstant : ℝ := 4 * splitBoundaryConstant

theorem seededBaseConcentrationConstant_pos : 0 < seededBaseConcentrationConstant := by
  unfold seededBaseConcentrationConstant splitBoundaryConstant
  positivity

theorem rectangleBaseConcentration_seededSplitBase
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    RectangleBaseConcentration (seededSplitBaseDistribution μ ξ A x ε t)
      seededBaseConcentrationConstant δ (dimensionLog p) := by
  intro s r d hd
  have hc := uniformBoundaryConcentration_seededSplitBase hdata hp hunit A hA x hε ht ht1 s r d hd
  have hroot : Real.sqrt (dimensionLog p / (1 / 4)) = 2 * Real.sqrt (dimensionLog p) := by
    rw [show dimensionLog p / (1 / 4 : ℝ) = 4 * dimensionLog p by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_nonneg (4 : ℝ)]
    rw [hs4]
  rw [hroot] at hc
  apply hc.trans
  unfold seededBaseConcentrationConstant
  have hC : 0 ≤ splitBoundaryConstant := splitBoundaryConstant_nonneg
  have hδ := hdata.delta_nonneg
  have hh := mul_nonneg (mul_nonneg hC hd.le) (Real.sqrt_nonneg (dimensionLog p))
  nlinarith

theorem seededSplitGaussianScale_ge_delta_sqrt {δ h L t : ℝ}
    (hδ : 0 ≤ δ) (hh : 0 ≤ h) (hL : 0 ≤ L) (ht : 0 ≤ t) (hband : 2 * δ ≤ h) :
    δ * Real.sqrt L ≤ seededSplitGaussianScale (L * h ^ 2) t := by
  have hs : 0 ≤ seededSplitGaussianScale (L * h ^ 2) t := Real.sqrt_nonneg _
  have hsq := seededSplitGaussianScale_sq (show 0 ≤ L * h ^ 2 by positivity) ht
  have he : (δ * Real.sqrt L) ^ 2 = δ ^ 2 * L := by
    rw [mul_pow, Real.sq_sqrt hL]
  have hbandSq : 4 * δ ^ 2 ≤ h ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hbandSq hL
  nlinarith [mul_nonneg hδ (Real.sqrt_nonneg L)]

theorem averagedSelectorMatrixEstimate_seededSplitBase
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hδh : δ ≤ s.bandwidth)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ seededSplitGaussianScale ε t) :
    AveragedSelectorMatrixEstimate s (splitBaseLaw μ ξ t)
      (seededSplitGaussianScale ε t • A) (seededSplitBaseValue A x ε t) logisticMatrixConstant
      (seededBaseConcentrationConstant * (s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p))) := by
  letI := splitBaseLaw_isProbability μ ξ hdata.measurable ht ht1
  apply averagedSelectorMatrixEstimate_of_rectangle_concentration hp
    (splitBaseLaw μ ξ t) (seededSplitBaseValue A x ε t)
    (measurable_seededSplitBaseValue A x ε t) s A
    (factor_coordinate_normSq_eq_one A hA hunit) seededBaseConcentrationConstant_pos
    hdata.delta_nonneg hδh (Real.sqrt_nonneg _) hscale
  exact rectangleBaseConcentration_seededSplitBase hdata hp hunit A hA x hε ht ht1

/-- Adding independent auxiliary copies does not alter the unconditional
concentrated-base law used in the B.4 estimate. -/
theorem map_seededSplitBaseValue_fst
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε t : ℝ) :
    ((splitBaseLaw μ ξ t).prod ν).map (fun z => seededSplitBaseValue A x ε t z.1) =
      seededSplitBaseDistribution μ ξ A x ε t := by
  change ((splitBaseLaw μ ξ t).prod ν).map (seededSplitBaseValue A x ε t ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_seededSplitBaseValue A x ε t) measurable_fst,
    Measure.map_fst_prod]
  simp only [measure_univ, one_smul, seededSplitBaseDistribution]

end

end RectangleCLT.Companion.SplitV4
