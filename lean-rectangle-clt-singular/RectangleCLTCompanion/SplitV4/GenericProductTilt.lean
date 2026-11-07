import RectangleCLTCompanion.LowerProductArray
import RectangleCLT.ScalarBerryEsseen
import Mathlib.Probability.Moments.Tilted
import Mathlib.MeasureTheory.Integral.Pi

/-! Nonidentical bounded scalar Esscher product laws and the checked scalar
Berry--Esseen theorem for their genuinely centered, standardized observations. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {n : ℕ}

/-- Product densities for distinct coordinate probability laws. -/
theorem generic_pi_withDensity
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (f : Fin n → ℝ → ℝ)
    (hfi : ∀ i, Integrable (f i) (ν i)) (hf0 : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (ν i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi ν).withDensity (fun z => ENNReal.ofReal (∏ i, f i (z i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  let ms : (i : Fin n) → MeasureSpace ℝ := fun i => ⟨(ν i).restrict (s i)⟩
  have hσ : ∀ i, @SigmaFinite ℝ (ms i).toMeasurableSpace (ms i).volume :=
    fun i => inferInstanceAs (SigmaFinite ((ν i).restrict (s i)))
  have hi : ∀ i, Integrable (f i) ((ms i).volume) := fun i => (hfi i).restrict
  have hprod := @Integrable.fintype_prod_dep ℝ inferInstance (Fin n) inferInstance
    (fun _ => ℝ) f ms hσ hi
  change Integrable (fun z : Fin n → ℝ => ∏ i, f i (z i))
    (Measure.pi (fun i => (ν i).restrict (s i))) at hprod
  have hp := @integral_fintype_prod_eq_prod ℝ inferInstance (Fin n) inferInstance
    (fun _ => ℝ) f ms hσ
  change (∫ z, ∏ i, f i (z i) ∂Measure.pi (fun i => (ν i).restrict (s i))) =
    ∏ i, ∫ x, f i x ∂(ν i).restrict (s i) at hp
  have hnonneg : ∀ z : Fin n → ℝ, 0 ≤ ∏ i, f i (z i) :=
    fun z => Finset.prod_nonneg (fun i _ => hf0 i (z i))
  rw [← ofReal_integral_eq_lintegral_ofReal hprod (ae_of_all _ hnonneg), hp]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0 i))]
  congr 1
  funext i
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hi i) (ae_of_all _ (hf0 i))

theorem generic_integrable_exp_of_bounded (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {δ : ℝ} (hbound : ∀ᵐ x ∂ν, |x| ≤ δ) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) ν := by
  apply (integrable_const (Real.exp (|t| * δ))).mono'
    (measurable_const.mul measurable_id |>.exp).aestronglyMeasurable
  filter_upwards [hbound] with x hx
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * x)).trans
    (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left hx (abs_nonneg t))

theorem generic_interior_integrableExpSet_of_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {δ : ℝ}
    (hbound : ∀ᵐ x ∂ν, |x| ≤ δ) (t : ℝ) :
    t ∈ interior (integrableExpSet id ν) := by
  have hset : integrableExpSet id ν = Set.univ := by
    ext u
    simp only [Set.mem_univ, iff_true]
    exact generic_integrable_exp_of_bounded ν hbound u
  rw [hset, interior_univ]
  trivial

def genericTiltedProduct (ν : Fin n → Measure ℝ) (t : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => (ν i).tilted (fun x => t * x))

theorem genericTiltedMarginal_isProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {δ : ℝ}
    (hbound : ∀ᵐ x ∂ν, |x| ≤ δ) (t : ℝ) :
    IsProbabilityMeasure (ν.tilted (fun x => t * x)) :=
  isProbabilityMeasure_tilted (generic_integrable_exp_of_bounded ν hbound t)

theorem genericTiltedProduct_isProbability
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) :
    IsProbabilityMeasure (genericTiltedProduct ν t) := by
  letI (i : Fin n) : IsProbabilityMeasure ((ν i).tilted (fun x => t * x)) :=
    genericTiltedMarginal_isProbability (ν i) (hbound i) t
  unfold genericTiltedProduct
  infer_instance

/-- The true nonidentical product change of measure, with the sum of the
actual coordinate cumulant generating functions as normalizer. -/
theorem genericTiltedProduct_eq_withDensity
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) :
    genericTiltedProduct ν t = (Measure.pi ν).withDensity
      (fun z => ENNReal.ofReal (Real.exp (t * (∑ i, z i) - ∑ i, cgf id (ν i) t))) := by
  have hm (i : Fin n) : (ν i).tilted (fun x => t * x) =
      (ν i).withDensity (fun x => ENNReal.ofReal (Real.exp (t * x - cgf id (ν i) t))) := by
    ext A hA
    rw [withDensity_apply _ hA]
    exact tilted_mul_apply_cgf' (X := id) hA
      (generic_integrable_exp_of_bounded (ν i) (hbound i) t)
  unfold genericTiltedProduct
  simp_rw [hm]
  rw [generic_pi_withDensity ν (fun i x => Real.exp (t * x - cgf id (ν i) t))
    (fun i => by
      simpa only [Real.exp_sub, div_eq_mul_inv] using
        (generic_integrable_exp_of_bounded (ν i) (hbound i) t).mul_const
          ((Real.exp (cgf id (ν i) t))⁻¹))
    (fun i x => (Real.exp_pos _).le)]
  congr 1
  funext z
  rw [← Real.exp_sum]
  congr 2
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem genericTiltedProduct_iIndepFun
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) :
    iIndepFun (fun i (z : Fin n → ℝ) => z i) (genericTiltedProduct ν t) := by
  letI (i : Fin n) : IsProbabilityMeasure ((ν i).tilted (fun x => t * x)) :=
    genericTiltedMarginal_isProbability (ν i) (hbound i) t
  exact lowerScalarPi_iIndepFun _

def genericTiltMean (ν : Measure ℝ) (t : ℝ) : ℝ := deriv (cgf id ν) t

def genericTiltVariance (ν : Measure ℝ) (t : ℝ) : ℝ := iteratedDeriv 2 (cgf id ν) t

def genericTiltTotalVariance (ν : Fin n → Measure ℝ) (t : ℝ) : ℝ :=
  ∑ i, genericTiltVariance (ν i) t

theorem genericTiltMean_eq_integral
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {δ : ℝ}
    (hbound : ∀ᵐ x ∂ν, |x| ≤ δ) (t : ℝ) :
    genericTiltMean ν t = ∫ x : ℝ, x ∂ν.tilted (fun x => t * x) :=
  (integral_tilted_mul_self
    (generic_interior_integrableExpSet_of_bounded ν hbound t)).symm

theorem genericTiltVariance_eq_integral
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {δ : ℝ}
    (hbound : ∀ᵐ x ∂ν, |x| ≤ δ) (t : ℝ) :
    genericTiltVariance ν t =
      ∫ x : ℝ, (x - genericTiltMean ν t) ^ 2 ∂ν.tilted (fun x => t * x) := by
  rw [genericTiltVariance, ← variance_tilted_mul
    (generic_interior_integrableExpSet_of_bounded ν hbound t),
    variance_eq_integral measurable_id.aemeasurable]
  simp only [id_eq]
  rw [← genericTiltMean_eq_integral ν hbound t]

theorem genericTiltedMarginal_bounded
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {δ : ℝ}
    (hbound : ∀ᵐ x ∂ν, |x| ≤ δ) (t : ℝ) :
    ∀ᵐ x ∂ν.tilted (fun x => t * x), |x| ≤ δ :=
  (tilted_absolutelyContinuous ν (fun x => t * x)).ae_le hbound

theorem genericTiltMean_abs_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {δ : ℝ}
    (hbound : ∀ᵐ x ∂ν, |x| ≤ δ) (t : ℝ) : |genericTiltMean ν t| ≤ δ := by
  letI := genericTiltedMarginal_isProbability ν hbound t
  rw [genericTiltMean_eq_integral ν hbound t]
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := ν.tilted (fun x => t * x))
      (f := fun x : ℝ => x) (C := δ) (by
      simpa only [Real.norm_eq_abs] using genericTiltedMarginal_bounded ν hbound t)

theorem genericTiltedProduct_map_eval
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) (i : Fin n) :
    (genericTiltedProduct ν t).map (fun z => z i) = (ν i).tilted (fun x => t * x) := by
  letI (i : Fin n) : IsProbabilityMeasure ((ν i).tilted (fun x => t * x)) :=
    genericTiltedMarginal_isProbability (ν i) (hbound i) t
  exact lowerScalarPi_map_eval _ i

def genericTiltedRawRows (ν : Fin n → Measure ℝ) (t : ℝ) (i : Fin n)
    (z : Fin n → ℝ) : Vector 1 := fun _ => z i - genericTiltMean (ν i) t

theorem genericTiltedRawRows_measurable
    (ν : Fin n → Measure ℝ) (t : ℝ) (i : Fin n) :
    Measurable (genericTiltedRawRows ν t i) :=
  measurable_pi_lambda _ (fun _ => (measurable_pi_apply i).sub measurable_const)

theorem genericTiltedRawRows_boundedIndependent
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) :
    BoundedIndependentHypotheses (genericTiltedProduct ν t)
      (genericTiltedRawRows ν t) (2 * δ) := by
  letI := genericTiltedProduct_isProbability ν hbound t
  refine ⟨genericTiltedRawRows_measurable ν t, ?_, ?_, ?_, by positivity⟩
  · exact (genericTiltedProduct_iIndepFun ν hbound t).comp
      (fun i x => fun _ : Fin 1 => x - genericTiltMean (ν i) t)
      (fun _ => measurable_pi_lambda _ (fun _ => measurable_id.sub measurable_const))
  · intro i j
    letI := genericTiltedMarginal_isProbability (ν i) (hbound i) t
    have hi : Integrable (fun x : ℝ => x) ((ν i).tilted (fun x => t * x)) := by
      apply (integrable_const δ).mono' measurable_id.aestronglyMeasurable
      simpa only [Real.norm_eq_abs] using genericTiltedMarginal_bounded (ν i) (hbound i) t
    have hm := integral_map (μ := genericTiltedProduct ν t)
      (f := fun x : ℝ => x - genericTiltMean (ν i) t)
      (measurable_pi_apply i).aemeasurable
      (measurable_id.sub measurable_const).aestronglyMeasurable
    rw [genericTiltedProduct_map_eval ν hbound t i] at hm
    change (∫ z, z i - genericTiltMean (ν i) t ∂genericTiltedProduct ν t) = 0
    rw [← hm, integral_sub hi (integrable_const _), integral_const,
      measureReal_univ_eq_one, one_smul, genericTiltMean_eq_integral (ν i) (hbound i) t]
    exact sub_self _
  · intro i
    have ha : ∀ᵐ z ∂genericTiltedProduct ν t, |z i| ≤ δ := by
      have hh := genericTiltedMarginal_bounded (ν i) (hbound i) t
      rw [← genericTiltedProduct_map_eval ν hbound t i] at hh
      exact (ae_map_iff (measurable_pi_apply i).aemeasurable
        (measurableSet_le measurable_id.abs measurable_const)).mp hh
    filter_upwards [ha] with z hz
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * δ)).mpr
    intro j
    change |z i - genericTiltMean (ν i) t| ≤ 2 * δ
    exact (abs_sub _ _).trans (by linarith [genericTiltMean_abs_le (ν i) (hbound i) t])

theorem genericTiltedRawRows_second
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) (i : Fin n) (j k : Fin 1) :
    (∫ z, genericTiltedRawRows ν t i z j * genericTiltedRawRows ν t i z k
      ∂genericTiltedProduct ν t) = genericTiltVariance (ν i) t := by
  have hm := integral_map (μ := genericTiltedProduct ν t)
    (f := fun x : ℝ => (x - genericTiltMean (ν i) t) ^ 2)
    (measurable_pi_apply i).aemeasurable
    ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable
  rw [genericTiltedProduct_map_eval ν hbound t i] at hm
  calc
    _ = ∫ x : ℝ, (x - genericTiltMean (ν i) t) ^ 2 ∂(ν i).tilted (fun x => t * x) := by
      simpa only [genericTiltedRawRows, pow_two] using hm.symm
    _ = _ := (genericTiltVariance_eq_integral (ν i) (hbound i) t).symm

def genericTiltNormalization (ν : Fin n → Measure ℝ) (t : ℝ) : ℝ :=
  1 / Real.sqrt (genericTiltTotalVariance ν t)

def genericTiltedNormalizedRows (ν : Fin n → Measure ℝ) (t : ℝ) (i : Fin n)
    (z : Fin n → ℝ) : Vector 1 :=
  genericTiltNormalization ν t • genericTiltedRawRows ν t i z

theorem genericTiltedNormalizedRows_boundedIndependent
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) :
    BoundedIndependentHypotheses (genericTiltedProduct ν t)
      (genericTiltedNormalizedRows ν t) (genericTiltNormalization ν t * (2 * δ)) :=
  (genericTiltedRawRows_boundedIndependent ν hδ hbound t).smul_of_nonneg
    (genericTiltNormalization ν t) (by unfold genericTiltNormalization; positivity)

theorem genericTiltedNormalizedRows_covariance
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ)
    (hV : 0 < genericTiltTotalVariance ν t) :
    covariance (genericTiltedProduct ν t) (sumVector (genericTiltedNormalizedRows ν t)) = 1 := by
  letI := genericTiltedProduct_isProbability ν hbound t
  have hdata := genericTiltedRawRows_boundedIndependent ν hδ hbound t
  change covariance (genericTiltedProduct ν t)
    (sumVector (fun i z => genericTiltNormalization ν t • genericTiltedRawRows ν t i z)) = _
  rw [hdata.covariance_sum_smul]
  ext j k
  rw [Matrix.smul_apply, smul_eq_mul, hdata.covariance_sum]
  simp_rw [genericTiltedRawRows_second ν hbound t]
  have hjk : j = k := Subsingleton.elim _ _
  simp only [Matrix.one_apply, if_pos hjk, genericTiltNormalization,
    div_pow, one_pow, Real.sq_sqrt hV.le]
  simpa only [one_div, genericTiltTotalVariance] using inv_mul_cancel₀ hV.ne'

def genericTiltedStandardizedSum (ν : Fin n → Measure ℝ) (t : ℝ)
    (z : Fin n → ℝ) : ℝ := sumVector (genericTiltedNormalizedRows ν t) z 0

theorem genericTiltedStandardizedSum_measurable
    (ν : Fin n → Measure ℝ) (t : ℝ) : Measurable (genericTiltedStandardizedSum ν t) := by
  apply (measurable_pi_apply (0 : Fin 1)).comp
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.smul (genericTiltedRawRows_measurable ν t i)

/-- Exact affine standardization of the actual tilted sum. -/
theorem genericTiltedStandardizedSum_eq
    (ν : Fin n → Measure ℝ) (t : ℝ) (z : Fin n → ℝ) :
    genericTiltedStandardizedSum ν t z =
      ((∑ i, z i) - ∑ i, genericTiltMean (ν i) t) /
        Real.sqrt (genericTiltTotalVariance ν t) := by
  simp only [genericTiltedStandardizedSum, sumVector, genericTiltedNormalizedRows,
    genericTiltedRawRows, genericTiltNormalization, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- A Berry--Esseen bound on genuine nonidentical tilted probabilities. Its
only variance input is the actual positive sum of tilted variances. -/
theorem genericTiltedStandardizedSum_cdf
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hn : 1 ≤ n) {δ : ℝ}
    (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ)
    (hV : 0 < genericTiltTotalVariance ν t) (x : ℝ) :
    |((genericTiltedProduct ν t).map (genericTiltedStandardizedSum ν t)).real (Iic x) -
      (gaussianReal 0 1).real (Iic x)| ≤
      scalarBerryEsseenConstant * (2 * δ / Real.sqrt (genericTiltTotalVariance ν t)) := by
  letI := genericTiltedProduct_isProbability ν hbound t
  have hunit : ∀ j, covariance (genericTiltedProduct ν t)
      (sumVector (genericTiltedNormalizedRows ν t)) j j = 1 := by
    intro j
    rw [genericTiltedNormalizedRows_covariance ν hδ hbound t hV]
    simp
  convert scalarBerryEsseenCDF (genericTiltedProduct ν t) hn
    (genericTiltedNormalizedRows ν t)
    (genericTiltedNormalizedRows_boundedIndependent ν hδ hbound t) hunit x using 1
  unfold genericTiltNormalization
  ring

theorem genericTiltedStandardizedSum_cdf_of_variance_lower
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hn : 1 ≤ n) {δ : ℝ}
    (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ)
    (hV : 1 / 2 ≤ genericTiltTotalVariance ν t) (x : ℝ) :
    |((genericTiltedProduct ν t).map (genericTiltedStandardizedSum ν t)).real (Iic x) -
      (gaussianReal 0 1).real (Iic x)| ≤ 4 * scalarBerryEsseenConstant * δ := by
  have hVpos : 0 < genericTiltTotalVariance ν t := by linarith
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt (genericTiltTotalVariance ν t) := by
    have hsq := Real.sq_sqrt hVpos.le
    have hn := Real.sqrt_nonneg (genericTiltTotalVariance ν t)
    nlinarith
  calc
    _ ≤ scalarBerryEsseenConstant * (2 * δ / Real.sqrt (genericTiltTotalVariance ν t)) :=
      genericTiltedStandardizedSum_cdf ν hn hδ hbound t hVpos x
    _ ≤ scalarBerryEsseenConstant * (4 * δ) := by
      apply mul_le_mul_of_nonneg_left _ scalarBerryEsseenConstant_pos.le
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hVpos)).mpr
      nlinarith
    _ = _ := by ring

theorem genericProduct_mgf_sum
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (t : ℝ) :
    mgf (fun z : Fin n → ℝ => ∑ i, z i) (Measure.pi ν) t = ∏ i, mgf id (ν i) t := by
  have hp := (lowerScalarPi_iIndepFun ν).mgf_sum (fun i => measurable_pi_apply i)
    (t := t) Finset.univ
  have hsum : (∑ i : Fin n, fun z : Fin n → ℝ => z i) = (fun z => ∑ i, z i) := by
    funext z
    exact Finset.sum_apply z _ _
  rw [hsum] at hp
  rw [hp]
  apply Finset.prod_congr rfl
  intro i _
  apply mgf_congr_of_identDistrib
  exact ⟨(measurable_pi_apply i).aemeasurable, measurable_id.aemeasurable,
    by rw [lowerScalarPi_map_eval ν i, Measure.map_id]⟩

theorem genericProduct_cgf_sum
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) :
    cgf (fun z : Fin n → ℝ => ∑ i, z i) (Measure.pi ν) t = ∑ i, cgf id (ν i) t := by
  unfold cgf
  rw [genericProduct_mgf_sum ν t, Real.log_prod]
  intro i _
  exact (mgf_pos (generic_integrable_exp_of_bounded (ν i) (hbound i) t)).ne'

/-- Genuine Bochner change of measure on the nonidentical product law. -/
theorem genericTiltedProduct_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) (F : (Fin n → ℝ) → E) :
    (∫ z, F z ∂genericTiltedProduct ν t) =
      ∫ z, Real.exp (t * (∑ i, z i) - ∑ i, cgf id (ν i) t) • F z ∂Measure.pi ν := by
  rw [genericTiltedProduct_eq_withDensity ν hbound t]
  have hm : Measurable (fun z : Fin n → ℝ => ENNReal.ofReal
      (Real.exp (t * (∑ i, z i) - ∑ i, cgf id (ν i) t))) :=
    ((measurable_const.mul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))).sub
      measurable_const).exp.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem genericTiltedProduct_integrable_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) (F : (Fin n → ℝ) → E) :
    Integrable F (genericTiltedProduct ν t) ↔
      Integrable (fun z => Real.exp (t * (∑ i, z i) - ∑ i, cgf id (ν i) t) • F z)
        (Measure.pi ν) := by
  rw [genericTiltedProduct_eq_withDensity ν hbound t]
  have hm : Measurable (fun z : Fin n → ℝ => ENNReal.ofReal
      (Real.exp (t * (∑ i, z i) - ∑ i, cgf id (ν i) t))) :=
    ((measurable_const.mul (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))).sub
      measurable_const).exp.ennreal_ofReal
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le] using
    (integrable_withDensity_iff_integrable_smul' hm
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) (g := F))

theorem genericTiltedProduct_inverse_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) (F : (Fin n → ℝ) → E) :
    (∫ z, Real.exp (-(t * (∑ i, z i) - ∑ i, cgf id (ν i) t)) • F z
      ∂genericTiltedProduct ν t) = ∫ z, F z ∂Measure.pi ν := by
  rw [genericTiltedProduct_integral ν hbound t]
  simp only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

theorem genericTiltedProduct_inverse_integrable_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂ν i, |x| ≤ δ) (t : ℝ) (F : (Fin n → ℝ) → E) :
    Integrable (fun z => Real.exp (-(t * (∑ i, z i) - ∑ i, cgf id (ν i) t)) • F z)
      (genericTiltedProduct ν t) ↔ Integrable F (Measure.pi ν) := by
  rw [genericTiltedProduct_integrable_iff ν hbound t]
  simp only [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

end
end RectangleCLT.Companion.SplitV4
