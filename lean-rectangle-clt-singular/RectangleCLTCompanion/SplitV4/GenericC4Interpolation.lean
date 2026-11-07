import RectangleCLTCompanion.SplitV4.GenericC4Taylor
import RectangleCLTCompanion.SplitV4.VariableAmplitudeInterpolation
import RectangleCLTCompanion.SplitV4.SlepianDerivative

/-! Actual seeded-path differentiation for an arbitrary C4 test. Bounded
derivatives give linear growth of the value and genuine integrability; a
global bound on the value itself is not assumed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace RectangleCLT.Companion.SplitV4.C4Test
noncomputable section
variable {p : ℕ} (f : C4Test p)

theorem integrable_variablePointNorm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (a b : ℝ) :
    Integrable (fun z : Ω × Vector p => ‖x+a • V z.1+b • z.2‖) (μ.prod (gaussianLaw A)) := by
  have hiV : Integrable (fun ω => ‖V ω‖) μ :=
    (integrable_const δ).mono' hV.norm.aestronglyMeasurable
      (hbound.mono fun ω hω => by simpa only [norm_norm] using hω)
  have hiVprod : Integrable (fun z : Ω × Vector p => ‖V z.1‖) (μ.prod (gaussianLaw A)) := by
    simpa only [mul_one] using hiV.mul_prod (integrable_const (1 : ℝ))
  have hiGprod : Integrable (fun z : Ω × Vector p => ‖z.2‖) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).mul_prod (gaussianLaw_integrable_norm A)
  have hm : Measurable (fun z : Ω × Vector p => x+a • V z.1+b • z.2) :=
    (measurable_const.add (measurable_const.smul (hV.comp measurable_fst))).add
      (measurable_const.smul measurable_snd)
  apply (((integrable_const ‖x‖).add (hiVprod.const_mul |a|)).add (hiGprod.const_mul |b|)).mono'
    hm.norm.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [norm_norm]
  calc
    _ ≤ ‖x+a • V z.1‖+‖b • z.2‖ := norm_add_le _ _
    _ ≤ ‖x‖+‖a • V z.1‖+‖b • z.2‖ := add_le_add_right (norm_add_le _ _) _
    _ = _ := by simp only [norm_smul, Real.norm_eq_abs, Pi.add_apply]

def genericVariableHeatExpectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∫ z : Ω × Vector p, f.value (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) ∂μ.prod (gaussianLaw A)

def genericVariableHeatDerivative {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∫ z : Ω × Vector p, f.gradient (x+γ t • V z.1+Real.sqrt (t+ε) • z.2)
    (γ' t • V z.1+(1/(2*Real.sqrt (t+ε))) • z.2) ∂μ.prod (gaussianLaw A)

theorem integrable_genericVariableHeatValue
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) :
    Integrable (fun z : Ω × Vector p => f.value (x+γ t • V z.1+Real.sqrt (t+ε) • z.2))
      (μ.prod (gaussianLaw A)) :=
  f.integrable_value_of_norm _ _
    ((measurable_const.add (measurable_const.smul (hV.comp measurable_fst))).add
      (measurable_const.smul measurable_snd))
    (integrable_variablePointNorm μ V hV hbound A x (γ t) (Real.sqrt (t+ε)))

theorem integrable_genericVariableHeatVelocity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) :
    Integrable (fun z : Ω × Vector p => f.gradient (x+γ t • V z.1+Real.sqrt (t+ε) • z.2)
      (γ' t • V z.1+(1/(2*Real.sqrt (t+ε))) • z.2)) (μ.prod (gaussianLaw A)) := by
  apply f.integrable_gradient_direction_of_norm
  · exact (measurable_const.add (measurable_const.smul (hV.comp measurable_fst))).add
      (measurable_const.smul measurable_snd)
  · exact (measurable_const.smul (hV.comp measurable_fst)).add (measurable_const.smul measurable_snd)
  · simpa only [zero_add] using integrable_variablePointNorm μ V hV hbound A 0
      (γ' t) (1/(2*Real.sqrt (t+ε)))

theorem hasDerivAt_genericVariableHeatExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hcont : ContinuousAt γ' t) :
    HasDerivAt (f.genericVariableHeatExpectation μ V A γ ε x)
      (f.genericVariableHeatDerivative μ V A γ γ' ε x t) t := by
  have hdote : ∀ᶠ r in 𝓝 t, dist (γ' r) (γ' t) < 1 :=
    hcont (Metric.ball_mem_nhds (γ' t) zero_lt_one)
  obtain ⟨η, hη, hdη⟩ := Metric.eventually_nhds_iff.mp hdote
  let radius := min (min t (1-t)) η / 2
  have hrad : 0 < radius := div_pos (lt_min (lt_min ht (by linarith)) hη) (by norm_num)
  have hrl : radius ≤ t/2 := div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
  have hrr : radius ≤ (1-t)/2 := div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num)
  have hrη : radius ≤ η := by
    have hh : radius ≤ η/2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  have htime {r : ℝ} (hr : r ∈ Metric.ball t radius) : r ∈ Set.Ioo (0 : ℝ) 1 := by
    have hh : |r-t| < radius := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    constructor <;> linarith [(abs_lt.mp hh).1, (abs_lt.mp hh).2]
  let C := |γ' t|+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdot {r : ℝ} (hr : r ∈ Metric.ball t radius) : |γ' r| ≤ C := by
    have hh := hdη ((Metric.mem_ball.mp hr).trans_le hrη)
    have hn := norm_le_norm_add_norm_sub (γ' t) (γ' r)
    simp only [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm (γ' t) (γ' r)] at hh hn
    dsimp [C]
    linarith
  let c := 1/(2*Real.sqrt (t/2+ε))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcoeff {r : ℝ} (hr : r ∈ Metric.ball t radius) :
      0 ≤ 1/(2*Real.sqrt (r+ε)) ∧ 1/(2*Real.sqrt (r+ε)) ≤ c := by
    have hh : |r-t| < radius := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have hlo : t/2 ≤ r := by linarith [(abs_lt.mp hh).1]
    refine ⟨by positivity, ?_⟩
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)
  have hpoint (r : ℝ) : Measurable (fun z : Ω × Vector p => x+γ r • V z.1+Real.sqrt (r+ε) • z.2) :=
    (measurable_const.add (measurable_const.smul (hV.comp measurable_fst))).add
      (measurable_const.smul measurable_snd)
  have hvelocity (r : ℝ) : Measurable (fun z : Ω × Vector p =>
      γ' r • V z.1+(1/(2*Real.sqrt (r+ε))) • z.2) :=
    (measurable_const.smul (hV.comp measurable_fst)).add (measurable_const.smul measurable_snd)
  have hF (r : ℝ) : AEStronglyMeasurable (fun z : Ω × Vector p =>
      f.value (x+γ r • V z.1+Real.sqrt (r+ε) • z.2)) (μ.prod (gaussianLaw A)) :=
    (f.continuous_value.measurable.comp (hpoint r)).aestronglyMeasurable
  have hD (r : ℝ) : AEStronglyMeasurable (fun z : Ω × Vector p =>
      f.gradient (x+γ r • V z.1+Real.sqrt (r+ε) • z.2)
        (γ' r • V z.1+(1/(2*Real.sqrt (r+ε))) • z.2)) (μ.prod (gaussianLaw A)) :=
    (f.continuous_gradient_eval.measurable.comp ((hpoint r).prodMk (hvelocity r))).aestronglyMeasurable
  have hiG : Integrable (fun z : Ω × Vector p => ‖z.2‖) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).mul_prod (gaussianLaw_integrable_norm A)
  have hi : Integrable (fun z : Ω × Vector p => f.bound*(C*δ+c*‖z.2‖)) (μ.prod (gaussianLaw A)) :=
    ((integrable_const _).add (hiG.const_mul c)).const_mul f.bound
  have hp : ∀ᵐ z : Ω × Vector p ∂μ.prod (gaussianLaw A), ‖V z.1‖ ≤ δ :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hbound
  have hnorm (z : Ω × Vector p) (hz : ‖V z.1‖ ≤ δ) (r : ℝ) (hr : r ∈ Metric.ball t radius) :
      ‖f.gradient (x+γ r • V z.1+Real.sqrt (r+ε) • z.2)
        (γ' r • V z.1+(1/(2*Real.sqrt (r+ε))) • z.2)‖ ≤ f.bound*(C*δ+c*‖z.2‖) := by
    apply (f.norm_gradient_eval_le _ _).trans
    apply mul_le_mul_of_nonneg_left _ f.bound_nonneg
    calc
      _ ≤ ‖γ' r • V z.1‖+‖(1/(2*Real.sqrt (r+ε))) • z.2‖ := norm_add_le _ _
      _ = |γ' r| * ‖V z.1‖+(1/(2*Real.sqrt (r+ε)))*‖z.2‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (hcoeff hr).1]
      _ ≤ _ := add_le_add (mul_le_mul (hdot hr) hz (norm_nonneg _) hC)
        (mul_le_mul_of_nonneg_right (hcoeff hr).2 (norm_nonneg _))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.prod (gaussianLaw A)) (ε := radius)
    (bound := fun z : Ω × Vector p => f.bound*(C*δ+c*‖z.2‖))
    (F := fun r z => f.value (x+γ r • V z.1+Real.sqrt (r+ε) • z.2))
    (F' := fun r z => f.gradient (x+γ r • V z.1+Real.sqrt (r+ε) • z.2)
      (γ' r • V z.1+(1/(2*Real.sqrt (r+ε))) • z.2))
    (x₀ := t) hrad (Filter.Eventually.of_forall hF)
    (f.integrable_genericVariableHeatValue μ V hV hbound A γ ε x t) (hD t)
    (hp.mono fun z hz r hr => hnorm z hz r hr) hi
    (ae_of_all _ fun z r hr => by
      have hg := (((hderiv r (htime hr)).smul_const (V z.1)).const_add x).add
        ((((hasDerivAt_id r).add_const ε).sqrt (by have := (htime hr).1; positivity)).smul_const z.2)
      simpa only [one_div] using (f.has_gradient _).comp_hasDerivAt r hg)
  exact hd.2

def genericVariableSelectorExpectation {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ mask : Kane.Cube n, Kane.maskWeight (variableRetention γ t) mask*
    f.genericVariableHeatExpectation μ (maskObservationSum ξ mask) A γ ε x t

def genericVariableSelectorDerivative {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ mask : Kane.Cube n,
    (selectorWeightDerivative (variableRetention γ t) (variableRetentionDerivative γ γ' t) mask*
      f.genericVariableHeatExpectation μ (maskObservationSum ξ mask) A γ ε x t+
    Kane.maskWeight (variableRetention γ t) mask*
      f.genericVariableHeatDerivative μ (maskObservationSum ξ mask) A γ γ' ε x t)

theorem hasDerivAt_genericVariableSelectorExpectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hpos : 0 < γ t) (hcont : ContinuousAt γ' t) :
    HasDerivAt (f.genericVariableSelectorExpectation μ ξ A γ ε x)
      (f.genericVariableSelectorDerivative μ ξ A γ γ' ε x t) t := by
  unfold genericVariableSelectorExpectation genericVariableSelectorDerivative
  apply HasDerivAt.sum
  intro mask _
  apply HasDerivAt.mul
  · exact hasDerivAt_maskWeight_curve mask (hasDerivAt_variableRetention (hderiv t ⟨ht,ht1⟩) hpos)
  · exact f.hasDerivAt_genericVariableHeatExpectation μ _
      (measurable_maskObservationSum ξ hξ mask) (mul_nonneg (Nat.cast_nonneg _) hδ)
      (maskObservationSum_bounded μ ξ hδ hbound mask) A γ γ' hε hderiv x ht ht1 hcont

theorem integral_variableSeededInterpolationLaw_eq_genericVariableSelectorExpectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ)
    (hq : variableRetention γ t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y, f.value (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε t) =
      f.genericVariableSelectorExpectation μ ξ A γ ε x t := by
  have hi (mask : Kane.Cube n) : Integrable (fun y => f.value (x+y))
      ((μ.prod (gaussianLaw A)).map (variableMaskPoint ξ γ ε t mask)) := by
    apply (integrable_map_measure
      (f.continuous_value.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (measurable_variableMaskPoint ξ hξ γ ε t mask).aemeasurable).mpr
    simpa only [Function.comp_apply, variableMaskPoint, add_assoc] using
      f.integrable_genericVariableHeatValue μ _ (measurable_maskObservationSum ξ hξ mask)
        (maskObservationSum_bounded μ ξ hδ hbound mask) A γ ε x t
  unfold variableSeededInterpolationLaw
  rw [integral_bernoulliMixtureLaw _ _ _ hq.1 hq.2 _ hi]
  unfold genericVariableSelectorExpectation
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [integral_map (f := fun y => f.value (x+y))
    (measurable_variableMaskPoint ξ hξ γ ε t mask).aemeasurable
    (f.continuous_value.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable]
  unfold genericVariableHeatExpectation variableMaskPoint
  simp only [add_assoc]

/-- Actual general-C4-test differentiation of the probability law in
Lemma B.1, including unbounded tests of at most linear growth. -/
theorem hasDerivAt_integral_variableSeededInterpolationLaw
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (hpos : ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 < γ r)
    (hq : ∀ r ∈ Set.Ioo (0 : ℝ) 1, variableRetention γ r ∈ Set.Icc (0 : ℝ) 1)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (hcont : ContinuousAt γ' t) :
    HasDerivAt (fun r => ∫ y, f.value (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε r)
      (f.genericVariableSelectorDerivative μ ξ A γ γ' ε x t) t := by
  apply (f.hasDerivAt_genericVariableSelectorExpectation μ ξ hξ hδ hbound A γ γ' hε hderiv x ht ht1
    (hpos t ⟨ht,ht1⟩) hcont).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht ht1] with r hr
  exact f.integral_variableSeededInterpolationLaw_eq_genericVariableSelectorExpectation
    μ ξ hξ hδ hbound A γ ε x r (hq r hr)

end
end RectangleCLT.Companion.SplitV4.C4Test
