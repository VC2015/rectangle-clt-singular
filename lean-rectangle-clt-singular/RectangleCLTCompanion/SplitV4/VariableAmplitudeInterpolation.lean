import RectangleCLTCompanion.SplitV4.SeededInterpolation

/-!
# Actual finite-mask differentiation for a variable amplitude

This supplies the general C¹-amplitude probability calculus in Lemma B.1.
It differentiates an actual independent product law; the resulting raw
gradient identity is a helper for the signed-Hessian/Taylor restoration.
The full arbitrary-amplitude fourth-order identity is not asserted here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def variableRetention (γ : ℝ → ℝ) (t : ℝ) : ℝ := (1-t)/(γ t)^2

def variableRetentionDerivative (γ γ' : ℝ → ℝ) (t : ℝ) : ℝ :=
  (-(γ t)-2*(1-t)*γ' t)/(γ t)^3

def variableEta (γ γ' : ℝ → ℝ) (t : ℝ) : ℝ := (1-t)*γ' t/γ t

theorem variable_covariance_calibration (γ : ℝ → ℝ) {t : ℝ} (hγ : γ t ≠ 0) :
    variableRetention γ t * (γ t)^2 = 1-t := by
  exact div_mul_cancel₀ _ (pow_ne_zero 2 hγ)

theorem variable_third_moment_calibration (γ : ℝ → ℝ) {t : ℝ} (hγ : γ t ≠ 0) :
    variableRetention γ t * (γ t)^3 = (1-t)*γ t := by
  unfold variableRetention
  field_simp
  <;> ring

theorem variable_signed_hessian_coefficient (γ γ' : ℝ → ℝ) {t : ℝ}
    (hγ : γ t ≠ 0) (r : ℝ) :
    variableRetentionDerivative γ γ' t * (γ t)^2 * (1-r) +
      variableRetention γ t * γ t * γ' t =
        -signedDensity (variableEta γ γ' t) r/2 := by
  unfold variableRetentionDerivative variableRetention variableEta signedDensity
  field_simp
  <;> ring

theorem variable_cubic_coefficient (γ γ' : ℝ → ℝ) {t : ℝ} (hγ : γ t ≠ 0) :
    -γ t * (1-variableEta γ γ' t)/6 = (-(γ t)+(1-t)*γ' t)/6 := by
  unfold variableEta
  field_simp
  <;> ring

theorem variable_independent_copy_cubic_coefficient (γ γ' : ℝ → ℝ) {t : ℝ}
    (hγ : γ t ≠ 0) :
    -((-(γ t)+(1-t)*γ' t)/6) * variableRetention γ t * γ t =
      (1-t)/6*(1-variableEta γ γ' t) := by
  unfold variableRetention variableEta
  field_simp
  <;> ring

theorem hasDerivAt_variableRetention {γ : ℝ → ℝ} {g t : ℝ}
    (hγ : HasDerivAt γ g t) (hpos : 0 < γ t) :
    HasDerivAt (variableRetention γ)
      ((-(γ t)-2*(1-t)*g)/(γ t)^3) t := by
  have hh := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).div (hγ.pow 2)
    (pow_ne_zero 2 hpos.ne')
  convert hh using 1
  field_simp [hpos.ne']
  <;> ring

theorem hasDerivAt_maskWeight_curve {n : ℕ} (mask : Kane.Cube n)
    {a : ℝ → ℝ} {b t : ℝ} (ha : HasDerivAt a b t) :
    HasDerivAt (fun r => Kane.maskWeight (a r) mask)
      (selectorWeightDerivative (a t) b mask) t := by
  exact HasDerivAt.finset_prod (u := Finset.univ)
    (f := fun i r => if mask i then a r else 1-a r)
    (f' := fun i => if mask i then b else -b)
    (fun i _ => by cases h : mask i <;> simp only [h, Bool.false_eq_true, ↓reduceIte]
                   · simpa using (hasDerivAt_const t (1 : ℝ)).sub ha
                   · exact ha)

def variableMaskPoint {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (γ : ℝ → ℝ)
    (ε t : ℝ) (mask : Kane.Cube n) (z : Ω × Vector p) : Vector p :=
  γ t • maskObservationSum ξ mask z.1 + Real.sqrt (t+ε) • z.2

/-- Actual independent masks, observations and standard Gaussian. -/
def variableSeededInterpolationLaw {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ : ℝ → ℝ) (ε t : ℝ) : Measure (Vector p) :=
  bernoulliMixtureLaw (μ.prod (gaussianLaw A)) (variableMaskPoint ξ γ ε t)
    (variableRetention γ t)

theorem measurable_variableMaskPoint {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (γ : ℝ → ℝ) (ε t : ℝ) (mask : Kane.Cube n) :
    Measurable (variableMaskPoint ξ γ ε t mask) :=
  (measurable_const.smul ((measurable_maskObservationSum ξ hξ mask).comp measurable_fst)).add
    (measurable_const.smul measurable_snd)

theorem variableSeededInterpolationLaw_isProbability
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (γ : ℝ → ℝ) (ε t : ℝ)
    (hq : variableRetention γ t ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (variableSeededInterpolationLaw μ ξ A γ ε t) :=
  bernoulliMixtureLaw_isProbability _ _ (measurable_variableMaskPoint ξ hξ γ ε t) _ hq.1 hq.2

end
end RectangleCLT.Companion.SplitV4

namespace RectangleCLT.FaceSmoother
noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem abs_variableDirectionalSum_le (x y : Vector p) :
    |∑ j, y j * s.coordinateDerivativeF x j| ≤ ‖y‖/s.bandwidth := by
  have heq : (∑ j, y j * s.coordinateDerivativeF x j) =
      -(s.F x/s.bandwidth)*(s.weights x).directionalMean y := by
    simpa only [line_zero] using
      (s.hasDerivAt_F_line_sum x y 0).unique (s.hasDerivAt_F_line x y 0)
  rw [heq]
  simpa only [line_zero] using s.abs_F_line_derivative_le x y 0

/-- The genuine Gaussian raw gradient integral is exactly the heat
covariance contraction. This follows from the already proved Gaussian
integration-by-parts identities, with a frozen affine tangent. -/
theorem gaussian_raw_velocity_integral_eq
    (A : Matrix (Fin p) (Fin p) ℝ) (x v : Vector p) {τ : ℝ} (hτ : 0 < τ) :
    (∫ y, ∑ j, (v j+(1/(2*Real.sqrt τ))*y j) *
      s.coordinateDerivativeF (x+Real.sqrt τ • y) j ∂gaussianLaw A) =
      (∑ j, v j * s.convolutionFirstDerivative (gaussianLaw (Real.sqrt τ • A)) x j) +
        (1/2 : ℝ) * ∑ j, ∑ k, (A*A.transpose) j k *
          s.convolutionSecondDerivative (gaussianLaw (Real.sqrt τ • A)) x j k := by
  have he : line (x-τ • v) v τ = x := by
    funext j
    simp only [line, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [he] using
    (s.hasDerivAt_gaussianHeat_line_raw A (x-τ • v) v hτ).unique
      (s.hasDerivAt_gaussianHeat_line A (x-τ • v) v hτ)

def variableHeatShiftExpectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∫ z : Ω × Vector p, s.F (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) ∂μ.prod (gaussianLaw A)

def variableHeatShiftDerivative {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∫ z : Ω × Vector p, ∑ j, (γ' t * V z.1 j + (1/(2*Real.sqrt (t+ε)))*z.2 j) *
    s.coordinateDerivativeF (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) j ∂μ.prod (gaussianLaw A)

theorem integrable_variableGradientKernel
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (a b c d : ℝ) (x : Vector p) :
    Integrable (fun z : Ω × Vector p => ∑ j, (a*V z.1 j+b*z.2 j) *
      s.coordinateDerivativeF (x+c • V z.1+d • z.2) j) (μ.prod (gaussianLaw A)) := by
  have hpoint : Measurable (fun z : Ω × Vector p => x+c • V z.1+d • z.2) :=
    (measurable_const.add (measurable_const.smul (hV.comp measurable_fst))).add
      (measurable_const.smul measurable_snd)
  apply integrable_finset_sum
  intro j _
  have hiV : Integrable (fun ω => V ω j) μ :=
    (integrable_const δ).mono' ((measurable_pi_apply j).comp hV).aestronglyMeasurable
      (hbound.mono fun ω hω => (norm_le_pi_norm (V ω) j).trans hω)
  have hiVprod : Integrable (fun z : Ω × Vector p => V z.1 j) (μ.prod (gaussianLaw A)) := by
    simpa only [mul_one] using hiV.mul_prod (integrable_const (1 : ℝ))
  have hiGprod : Integrable (fun z : Ω × Vector p => z.2 j) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).mul_prod
        (gaussianLaw_integrable_coordinate A j)
  have hi := ((hiVprod.const_mul a).add (hiGprod.const_mul b)).bdd_mul
    (((s.continuous_firstDerivative j).measurable.comp hpoint).aestronglyMeasurable)
    ⟨1/s.bandwidth, fun z => s.norm_firstDerivative_le _ j⟩
  simpa only [Function.comp_apply, Pi.add_apply, mul_comm] using hi

theorem variableHeatShiftDerivative_eq_heat
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ)
    (ε : ℝ) (x : Vector p) {t : ℝ} (htε : 0 < t+ε) :
    s.variableHeatShiftDerivative μ V A γ γ' ε x t =
      ∫ ω, (∑ j, (γ' t * V ω j) * s.convolutionFirstDerivative
        (gaussianLaw (Real.sqrt (t+ε) • A)) (x+γ t • V ω) j) +
          (1/2 : ℝ) * ∑ j, ∑ k, (A*A.transpose) j k *
            s.convolutionSecondDerivative (gaussianLaw (Real.sqrt (t+ε) • A))
              (x+γ t • V ω) j k ∂μ := by
  have hi : Integrable (fun z : Ω × Vector p => ∑ j,
      (γ' t * V z.1 j+(1/(2*Real.sqrt (t+ε)))*z.2 j) *
        s.coordinateDerivativeF (x+γ t • V z.1+Real.sqrt (t+ε) • z.2) j)
      (μ.prod (gaussianLaw A)) :=
    s.integrable_variableGradientKernel μ V hV hbound A
      (γ' t) (1/(2*Real.sqrt (t+ε))) (γ t) (Real.sqrt (t+ε)) x
  unfold variableHeatShiftDerivative
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  simpa only [Pi.smul_apply, smul_eq_mul] using
    s.gaussian_raw_velocity_integral_eq A (x+γ t • V ω) (γ' t • V ω) htε

theorem hasDerivAt_variableHeatShiftExpectation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hcont : ContinuousAt γ' t) :
    HasDerivAt (s.variableHeatShiftExpectation μ V A γ ε x)
      (s.variableHeatShiftDerivative μ V A γ γ' ε x t) t := by
  have hdote : ∀ᶠ r in 𝓝 t, dist (γ' r) (γ' t) < 1 :=
    hcont (Metric.ball_mem_nhds (γ' t) zero_lt_one)
  obtain ⟨η, hη, hdη⟩ := Metric.eventually_nhds_iff.mp hdote
  let radius := min (min t (1-t)) η / 2
  have hrad : 0 < radius := by
    exact div_pos (lt_min (lt_min ht (by linarith)) hη) (by norm_num)
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
    have hd : dist r t < η := (Metric.mem_ball.mp hr).trans_le hrη
    have hh := hdη hd
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
  have hpoint (r : ℝ) : Measurable (fun z : Ω × Vector p =>
      x+γ r • V z.1+Real.sqrt (r+ε) • z.2) :=
    (measurable_const.add (measurable_const.smul (hV.comp measurable_fst))).add
      (measurable_const.smul measurable_snd)
  have hF (r : ℝ) : AEStronglyMeasurable (fun z : Ω × Vector p =>
      s.F (x+γ r • V z.1+Real.sqrt (r+ε) • z.2)) (μ.prod (gaussianLaw A)) :=
    (s.continuous_F.measurable.comp (hpoint r)).aestronglyMeasurable
  have hD (r : ℝ) : AEStronglyMeasurable (fun z : Ω × Vector p =>
      ∑ j, (γ' r * V z.1 j + (1/(2*Real.sqrt (r+ε)))*z.2 j) *
        s.coordinateDerivativeF (x+γ r • V z.1+Real.sqrt (r+ε) • z.2) j)
      (μ.prod (gaussianLaw A)) := by
    apply Measurable.aestronglyMeasurable
    exact Finset.measurable_sum _ fun j _ =>
      ((((measurable_pi_apply j).comp (hV.comp measurable_fst)).const_mul _).add
        (((measurable_pi_apply j).comp measurable_snd).const_mul _)).mul
          ((s.continuous_firstDerivative j).measurable.comp (hpoint r))
  have hiG : Integrable (fun z : Ω × Vector p => ‖z.2‖) (μ.prod (gaussianLaw A)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).mul_prod (gaussianLaw_integrable_norm A)
  have hi : Integrable (fun z : Ω × Vector p => (C*δ+c*‖z.2‖)/s.bandwidth)
      (μ.prod (gaussianLaw A)) :=
    ((integrable_const _).add (hiG.const_mul c)).div_const _
  have hp : ∀ᵐ z : Ω × Vector p ∂μ.prod (gaussianLaw A), ‖V z.1‖ ≤ δ :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hbound
  have hnorm (z : Ω × Vector p) (hz : ‖V z.1‖ ≤ δ)
      (r : ℝ) (hr : r ∈ Metric.ball t radius) :
      ‖∑ j, (γ' r * V z.1 j + (1/(2*Real.sqrt (r+ε)))*z.2 j) *
        s.coordinateDerivativeF (x+γ r • V z.1+Real.sqrt (r+ε) • z.2) j‖ ≤
          (C*δ+c*‖z.2‖)/s.bandwidth := by
    have hh := s.abs_variableDirectionalSum_le
      (x+γ r • V z.1+Real.sqrt (r+ε) • z.2)
      (γ' r • V z.1 + (1/(2*Real.sqrt (r+ε))) • z.2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh
    apply (show ‖_‖ ≤ ‖γ' r • V z.1 + (1/(2*Real.sqrt (r+ε))) • z.2‖/s.bandwidth by
      simpa only [Real.norm_eq_abs] using hh).trans
    apply div_le_div_of_nonneg_right _ s.bandwidth_pos.le
    calc
      _ ≤ ‖γ' r • V z.1‖ + ‖(1/(2*Real.sqrt (r+ε))) • z.2‖ := norm_add_le _ _
      _ = |γ' r| * ‖V z.1‖ + (1/(2*Real.sqrt (r+ε)))*‖z.2‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (hcoeff hr).1]
      _ ≤ _ := add_le_add (mul_le_mul (hdot hr) hz (norm_nonneg _) hC)
        (mul_le_mul_of_nonneg_right (hcoeff hr).2 (norm_nonneg _))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ.prod (gaussianLaw A)) (ε := radius)
    (bound := fun z : Ω × Vector p => (C*δ+c*‖z.2‖)/s.bandwidth)
    (F := fun r z => s.F (x+γ r • V z.1+Real.sqrt (r+ε) • z.2))
    (F' := fun r z => ∑ j, (γ' r * V z.1 j + (1/(2*Real.sqrt (r+ε)))*z.2 j) *
      s.coordinateDerivativeF (x+γ r • V z.1+Real.sqrt (r+ε) • z.2) j)
    (x₀ := t) hrad (Filter.Eventually.of_forall hF)
    ((integrable_const (1 : ℝ)).mono' (hF t) (ae_of_all _ fun _ => s.norm_F_le_one _))
    (hD t) (hp.mono fun z hz r hr => hnorm z hz r hr) hi
    (ae_of_all _ fun z r hr => by
      have hg := (((hderiv r (htime hr)).smul_const (V z.1)).const_add x).add
        ((((hasDerivAt_id r).add_const ε).sqrt (by have := (htime hr).1; positivity)).smul_const z.2)
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_div] using s.hasDerivAt_F_curve hg)
  exact hd.2

def variableSelectorHeatExpectation {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ mask : Kane.Cube n, Kane.maskWeight (Companion.SplitV4.variableRetention γ t) mask *
    s.variableHeatShiftExpectation μ (maskObservationSum ξ mask) A γ ε x t

def variableSelectorHeatDerivative {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ γ' : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ mask : Kane.Cube n,
    (selectorWeightDerivative (Companion.SplitV4.variableRetention γ t)
      (Companion.SplitV4.variableRetentionDerivative γ γ' t) mask *
        s.variableHeatShiftExpectation μ (maskObservationSum ξ mask) A γ ε x t +
      Kane.maskWeight (Companion.SplitV4.variableRetention γ t) mask *
        s.variableHeatShiftDerivative μ (maskObservationSum ξ mask) A γ γ' ε x t)

theorem hasDerivAt_variableSelectorHeatExpectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hpos : 0 < γ t) (hcont : ContinuousAt γ' t) :
    HasDerivAt (s.variableSelectorHeatExpectation μ ξ A γ ε x)
      (s.variableSelectorHeatDerivative μ ξ A γ γ' ε x t) t := by
  unfold variableSelectorHeatExpectation variableSelectorHeatDerivative
  apply HasDerivAt.sum
  intro mask _
  apply HasDerivAt.mul
  · exact Companion.SplitV4.hasDerivAt_maskWeight_curve mask
      (Companion.SplitV4.hasDerivAt_variableRetention (hderiv t ⟨ht, ht1⟩) hpos)
  · exact s.hasDerivAt_variableHeatShiftExpectation μ _
      (measurable_maskObservationSum ξ hξ mask) (mul_nonneg (Nat.cast_nonneg _) hδ)
      (maskObservationSum_bounded μ ξ hδ hbound mask) A γ γ' hε hderiv x ht ht1 hcont

theorem integral_variableSeededInterpolationLaw_eq_variableSelectorHeatExpectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ)
    (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ)
    (hq : Companion.SplitV4.variableRetention γ t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y, s.F (x+y) ∂Companion.SplitV4.variableSeededInterpolationLaw μ ξ A γ ε t) =
      s.variableSelectorHeatExpectation μ ξ A γ ε x t := by
  have hi (mask : Kane.Cube n) : Integrable (fun y => s.F (x+y))
      ((μ.prod (gaussianLaw A)).map (Companion.SplitV4.variableMaskPoint ξ γ ε t mask)) := by
    letI : IsProbabilityMeasure
        ((μ.prod (gaussianLaw A)).map (Companion.SplitV4.variableMaskPoint ξ γ ε t mask)) :=
      isProbabilityMeasure_map (Companion.SplitV4.measurable_variableMaskPoint ξ hξ γ ε t mask).aemeasurable
    exact (integrable_const (1 : ℝ)).mono'
      (s.continuous_F.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun _ => s.norm_F_le_one _)
  unfold Companion.SplitV4.variableSeededInterpolationLaw
  rw [integral_bernoulliMixtureLaw _ _ _ hq.1 hq.2 _ hi]
  unfold variableSelectorHeatExpectation
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [integral_map (f := fun y => s.F (x+y))
    (Companion.SplitV4.measurable_variableMaskPoint ξ hξ γ ε t mask).aemeasurable
    (s.continuous_F.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable]
  unfold variableHeatShiftExpectation Companion.SplitV4.variableMaskPoint
  simp only [add_assoc]

/-- General C¹-amplitude differentiation under the actual probability
laws. The derivative is the computed finite-selector/raw-gradient expression;
no analytic path identity is assumed. -/
theorem hasDerivAt_integral_variableSeededInterpolationLaw
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (hpos : ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 < γ r)
    (hq : ∀ r ∈ Set.Ioo (0 : ℝ) 1, Companion.SplitV4.variableRetention γ r ∈ Set.Icc (0 : ℝ) 1)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hcont : ContinuousAt γ' t) :
    HasDerivAt (fun r => ∫ y, s.F (x+y)
      ∂Companion.SplitV4.variableSeededInterpolationLaw μ ξ A γ ε r)
      (s.variableSelectorHeatDerivative μ ξ A γ γ' ε x t) t := by
  apply (s.hasDerivAt_variableSelectorHeatExpectation μ ξ hξ hδ hbound A γ γ' hε hderiv x ht ht1
    (hpos t ⟨ht, ht1⟩) hcont).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht ht1] with r hr
  exact s.integral_variableSeededInterpolationLaw_eq_variableSelectorHeatExpectation
    μ ξ hξ A γ ε x r (hq r hr)

end
end RectangleCLT.FaceSmoother
