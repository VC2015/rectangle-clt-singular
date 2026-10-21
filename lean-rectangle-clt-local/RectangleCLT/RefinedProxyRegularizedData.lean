import RectangleCLT.BoundedIndependentScaling
import RectangleCLT.ProxyGaussianData
import RectangleCLT.RefinedProxyRegularizedGeometry

/-! Actual independent-product data for isotropic regularization. Moment
identities retain signed third-moment cancellation. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem map_comp_fst_of_probability
    {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure Ω) (ν : Measure E) [IsProbabilityMeasure ν]
    (f : Ω → F) (hf : Measurable f) :
    (μ.prod ν).map (fun z => f z.1) = μ.map f := by
  change (μ.prod ν).map (f ∘ Prod.fst) = μ.map f
  rw [← Measure.map_map hf measurable_fst]
  simp

theorem boundedIndependent_comp_fst
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) :
    BoundedIndependentHypotheses (μ.prod ν) (fun i z => ξ i z.1) δ := by
  have hfst : (μ.prod ν).map Prod.fst = μ := by simp
  refine ⟨fun i => (h.measurable i).comp measurable_fst, ?_, ?_, ?_, h.delta_nonneg⟩
  · apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => ((h.measurable i).comp measurable_fst).aemeasurable)).mpr
    change (μ.prod ν).map (fun z i => ξ i z.1) =
      Measure.pi (fun i => (μ.prod ν).map (fun z => ξ i z.1))
    rw [map_comp_fst_of_probability μ ν (fun ω i => ξ i ω)
      (measurable_pi_lambda _ h.measurable)]
    simp_rw [map_comp_fst_of_probability μ ν (ξ _) (h.measurable _)]
    exact (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (h.measurable i).aemeasurable)).mp h.independent
  · intro i j
    have hi := integral_fun_fst (μ := μ) (ν := ν) (fun ω => ξ i ω j)
    simpa only [measureReal_univ_eq_one, one_smul, h.centered] using hi
  · intro i
    have hs : MeasurableSet {ω | ‖ξ i ω‖ ≤ δ} :=
      measurableSet_le (h.measurable i).norm measurable_const
    have hb : ∀ᵐ ω ∂(μ.prod ν).map Prod.fst, ‖ξ i ω‖ ≤ δ := by
      rw [hfst]
      exact h.bounded i
    exact (ae_map_iff measurable_fst.aemeasurable hs).mp hb

theorem gamma3_comp_fst
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    (μ : Measure Ω) [SFinite μ] (ν : Measure E) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) :
    gamma3 (μ.prod ν) (fun i z => ξ i z.1) = gamma3 μ ξ := by
  unfold gamma3
  apply Finset.fold_congr
  intro jkl _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simpa only [measureReal_univ_eq_one, one_smul] using
    (integral_fun_fst (μ := μ) (ν := ν)
      (fun ω => ξ i ω jkl.1 * ξ i ω jkl.2.1 * ξ i ω jkl.2.2))

theorem gamma4_comp_fst
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p n : ℕ}
    (μ : Measure Ω) [SFinite μ] (ν : Measure E) [IsProbabilityMeasure ν]
    (ξ : Fin n → Ω → Vector p) :
    gamma4 (μ.prod ν) (fun i z => ξ i z.1) = gamma4 μ ξ := by
  unfold gamma4
  apply Finset.fold_congr
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simpa only [measureReal_univ_eq_one, one_smul] using
    (integral_fun_fst (μ := μ) (ν := ν) (fun ω => ξ i ω j ^ 4))

theorem gamma3_smul_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) {t : ℝ} (ht : 0 ≤ t) :
    gamma3 μ (fun i ω => t • ξ i ω) = t ^ 3 * gamma3 μ ξ := by
  have hm (j k l : Fin p) :
      (∑ i, ∫ ω, (t • ξ i ω) j * (t • ξ i ω) k * (t • ξ i ω) l ∂μ) =
        t ^ 3 * ∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      _ = ∑ i, ∫ ω, t ^ 3 * (ξ i ω j * ξ i ω k * ξ i ω l) ∂μ := by
        congr 1
        funext i
        congr 1
        funext ω
        ring
      _ = _ := by simp_rw [integral_const_mul]; rw [Finset.mul_sum]
  unfold gamma3
  simp_rw [hm, abs_mul, abs_of_nonneg (pow_nonneg ht 3)]
  have hf := (Finset.univ : Finset (Fin p × Fin p × Fin p)).fold_hom
    (op := max) (op' := max) (b := (0 : ℝ))
    (m := fun x : ℝ => t ^ 3 * x)
    (fun x y => mul_max_of_nonneg x y (pow_nonneg ht 3))
    (f := fun jkl => |∑ i, ∫ ω, ξ i ω jkl.1 * ξ i ω jkl.2.1 * ξ i ω jkl.2.2 ∂μ|)
  simpa only [mul_zero] using hf

theorem gamma4_smul
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (t : ℝ) :
    gamma4 μ (fun i ω => t • ξ i ω) = t ^ 4 * gamma4 μ ξ := by
  have hm (j : Fin p) : (∑ i, ∫ ω, (t • ξ i ω) j ^ 4 ∂μ) =
      t ^ 4 * ∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    simp_rw [integral_const_mul]
    rw [Finset.mul_sum]
  unfold gamma4
  simp_rw [hm]
  have hf := (Finset.univ : Finset (Fin p)).fold_hom
    (op := max) (op' := max) (b := (0 : ℝ))
    (m := fun x : ℝ => t ^ 4 * x)
    (fun x y => mul_max_of_nonneg x y (by positivity))
    (f := fun j => ∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ)
  simpa only [mul_zero] using hf

def refinedProxyNormalization (c : ℝ) : ℝ := (Real.sqrt (1 + c))⁻¹

def refinedProxyRegularizedArray {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (c : ℝ) (i : Fin n)
    (z : Ω × Vector p) : Vector p := refinedProxyNormalization c • ξ i z.1

def refinedProxyRegularizedGaussian {Ω : Type*} {p : ℕ} (c : ℝ)
    (z : Ω × Vector p) : Vector p :=
  (refinedProxyNormalization c * Real.sqrt c) • z.2

def refinedProxyRegularizedFactor (p : ℕ) (c : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (refinedProxyNormalization c * Real.sqrt c) • 1

theorem refinedProxyNormalization_pos {c : ℝ} (hc : 0 ≤ c) :
    0 < refinedProxyNormalization c :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))

theorem refinedProxyNormalization_le_one {c : ℝ} (hc : 0 ≤ c) :
    refinedProxyNormalization c ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (1 + c) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + c by linarith)
  exact inv_le_one_of_one_le₀ hs

theorem refinedProxyRegularizedArray_boundedIndependent
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ c : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hc : 0 ≤ c) :
    BoundedIndependentHypotheses (μ.prod (standardGaussian p))
      (refinedProxyRegularizedArray ξ c) (refinedProxyNormalization c * δ) :=
  (boundedIndependent_comp_fst μ (standardGaussian p) ξ h).smul_of_nonneg _
    (refinedProxyNormalization_pos hc).le

theorem refinedProxyRegularizedArray_gamma3
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {c : ℝ} (hc : 0 ≤ c) :
    gamma3 (μ.prod (standardGaussian p)) (refinedProxyRegularizedArray ξ c) =
      refinedProxyNormalization c ^ 3 * gamma3 μ ξ := by
  have hs := gamma3_smul_of_nonneg (μ.prod (standardGaussian p))
    (fun i (z : Ω × Vector p) => ξ i z.1) (refinedProxyNormalization_pos hc).le
  rw [gamma3_comp_fst] at hs
  exact hs

theorem refinedProxyRegularizedArray_gamma4
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) (c : ℝ) :
    gamma4 (μ.prod (standardGaussian p)) (refinedProxyRegularizedArray ξ c) =
      refinedProxyNormalization c ^ 4 * gamma4 μ ξ := by
  have hs := gamma4_smul (μ.prod (standardGaussian p))
    (fun i (z : Ω × Vector p) => ξ i z.1) (refinedProxyNormalization c)
  rw [gamma4_comp_fst] at hs
  exact hs

theorem refinedProxyRegularizedArray_gamma3_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {c : ℝ} (hc : 0 ≤ c) :
    gamma3 (μ.prod (standardGaussian p)) (refinedProxyRegularizedArray ξ c) ≤ gamma3 μ ξ := by
  rw [refinedProxyRegularizedArray_gamma3 μ ξ hc]
  exact mul_le_of_le_one_left (gamma3_nonneg μ ξ)
    (pow_le_one₀ (refinedProxyNormalization_pos hc).le
      (refinedProxyNormalization_le_one hc))

theorem refinedProxyRegularizedArray_gamma4_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {c : ℝ} (hc : 0 ≤ c) :
    gamma4 (μ.prod (standardGaussian p)) (refinedProxyRegularizedArray ξ c) ≤ gamma4 μ ξ := by
  rw [refinedProxyRegularizedArray_gamma4]
  exact mul_le_of_le_one_left (gamma4_nonneg μ ξ)
    (pow_le_one₀ (refinedProxyNormalization_pos hc).le
      (refinedProxyNormalization_le_one hc))

theorem refinedProxyRegularized_envelope_le {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c) :
    refinedProxyNormalization c * δ ≤ δ :=
  mul_le_of_le_one_left hδ (refinedProxyNormalization_le_one hc)

theorem refinedProxyRegularized_proxyHypotheses
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ c : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hc : 0 ≤ c) :
    ProxyHypotheses (μ.prod (standardGaussian p)) (refinedProxyRegularizedArray ξ c)
      (refinedProxyRegularizedGaussian c) (refinedProxyNormalization c * δ)
      (refinedProxyRegularizedFactor p c) := by
  let t := refinedProxyNormalization c * Real.sqrt c
  have hgauss : (μ.prod (standardGaussian p)).map (refinedProxyRegularizedGaussian (Ω := Ω) c) =
      gaussianLaw (refinedProxyRegularizedFactor p c) := by
    have hs : Measurable (fun z : Vector p => t • z) := measurable_const.smul measurable_id
    change (μ.prod (standardGaussian p)).map ((fun z : Vector p => t • z) ∘ Prod.snd) = _
    rw [← Measure.map_map hs measurable_snd]
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
    unfold gaussianLaw refinedProxyRegularizedFactor
    congr 1
    funext z
    change t • z = (t • (1 : Matrix (Fin p) (Fin p) ℝ)).mulVec z
    rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  refine ⟨refinedProxyRegularizedArray_boundedIndependent μ ξ h hc,
    measurable_const.smul measurable_snd, hgauss, ?_⟩
  have hproj : IndepFun (Prod.fst : Ω × Vector p → Ω) Prod.snd
      (μ.prod (standardGaussian p)) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map
      measurable_fst.aemeasurable measurable_snd.aemeasurable).mpr
    change (μ.prod (standardGaussian p)).map id = _
    simp
  have harray : Measurable (fun ω : Ω => fun i : Fin n =>
      refinedProxyNormalization c • ξ i ω) :=
    measurable_pi_lambda _ (fun i => measurable_const.smul (h.measurable i))
  exact hproj.comp harray (measurable_const.smul measurable_id)

theorem covariance_comp_fst
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p : ℕ}
    (μ : Measure Ω) [SFinite μ] (ν : Measure E) [IsProbabilityMeasure ν]
    (W : Ω → Vector p) : covariance (μ.prod ν) (fun z => W z.1) = covariance μ W := by
  ext j k
  have hprod := integral_fun_fst (μ := μ) (ν := ν) (fun ω => W ω j * W ω k)
  have hj := integral_fun_fst (μ := μ) (ν := ν) (fun ω => W ω j)
  have hk := integral_fun_fst (μ := μ) (ν := ν) (fun ω => W ω k)
  simp only [measureReal_univ_eq_one, one_smul] at hprod hj hk
  exact congrArg₂ (fun a b : ℝ => a - b) hprod (congrArg₂ (fun a b : ℝ => a * b) hj hk)

theorem refinedProxyNormalization_sq {c : ℝ} (hc : 0 ≤ c) :
    refinedProxyNormalization c ^ 2 = (1 + c)⁻¹ := by
  rw [refinedProxyNormalization, inv_pow, Real.sq_sqrt (by linarith)]

theorem refinedProxyRegularizedFactor_covariance {p : ℕ} (c : ℝ) :
    refinedProxyRegularizedFactor p c * (refinedProxyRegularizedFactor p c).transpose =
      (refinedProxyNormalization c * Real.sqrt c) ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) := by
  simp only [refinedProxyRegularizedFactor, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, pow_two]

theorem refinedProxyRegularized_covariance
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ c : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hc : 0 ≤ c) :
    covariance (μ.prod (standardGaussian p))
      (sumWithGaussian (refinedProxyRegularizedArray ξ c) (refinedProxyRegularizedGaussian c)) =
        refinedProxyRegularizedCovariance (covariance μ (sumVector ξ)) c := by
  rw [(refinedProxyRegularized_proxyHypotheses μ ξ h hc).covariance_sumWithGaussian,
    refinedProxyRegularizedFactor_covariance]
  have hlift := boundedIndependent_comp_fst μ (standardGaussian p) ξ h
  have hbound : covariance (μ.prod (standardGaussian p))
      (sumVector (refinedProxyRegularizedArray ξ c)) =
        refinedProxyNormalization c ^ 2 • covariance μ (sumVector ξ) := by
    rw [show refinedProxyRegularizedArray ξ c =
      (fun i z => refinedProxyNormalization c • ξ i z.1) from rfl,
      hlift.covariance_sum_smul]
    have heq : sumVector (fun i (z : Ω × Vector p) => ξ i z.1) =
        (fun z => sumVector ξ z.1) := by rfl
    rw [heq, covariance_comp_fst]
  rw [hbound, mul_pow, refinedProxyNormalization_sq hc, Real.sq_sqrt hc]
  simp only [refinedProxyRegularizedCovariance, smul_add, smul_smul]

theorem sumWithGaussian_refinedProxyRegularized
    {Ω : Type*} {p n : ℕ} (ξ : Fin n → Ω → Vector p) (c : ℝ) (z : Ω × Vector p) :
    sumWithGaussian (refinedProxyRegularizedArray ξ c) (refinedProxyRegularizedGaussian c) z =
      refinedProxyNormalization c • (sumVector ξ z.1 + Real.sqrt c • z.2) := by
  simp only [sumWithGaussian, refinedProxyRegularizedArray, refinedProxyRegularizedGaussian,
    sumVector, Finset.smul_sum, smul_add, smul_smul]

end

end RectangleCLT
