import RectangleCLTArxivV1.SupplementalHGammaThresholdLaw
import RectangleCLTArxivV1.SupplementalHSurfaceEstimates

/-! Actual Gamma averaging of positive ridge moments, the native leading
ridge term, and the complete signed ridge surface functional. Only the
auxiliary threshold law is absolutely continuous; the base may be singular. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

private theorem gamma_threshold_base_budget {m n : ℕ}
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (u : Fin m → Vector (n+1)) (a : Vector m) {h σ B : ℝ} (hh : 0<h)
    (F : Vector m → ℝ) (hF : Measurable F)
    (hbudget : ∀ᵐ b : Vector m ∂volume,
      Integrable (fun x => F (fun j => (b j-faceDot (u j) x)/σ)) ν ∧
      (∫ x, |F (fun j => (b j-faceDot (u j) x)/σ)| ∂ν)≤B) (q : ℕ) :
    Integrable (fun z => F (fun j =>
      (gammaAdjustedThreshold a h z.1 j-faceDot (u j) z.2)/σ))
      ((gammaRectangleLaw m q).prod ν) ∧
    (∫ e, ∫ x, |F (fun j =>
      (gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)| ∂ν ∂gammaRectangleLaw m q)≤B := by
  let J := fun z : (ℝ × (Face m → ℝ)) × Vector (n+1) =>
    F (fun j => (gammaAdjustedThreshold a h z.1 j-faceDot (u j) z.2)/σ)
  have hJ : Measurable J := hF.comp (by
    apply measurable_pi_lambda
    intro j
    exact (((measurable_pi_apply j).comp ((measurable_gammaAdjustedThreshold a h).comp measurable_fst)).sub
      ((continuous_faceDot_left (u j)).measurable.comp measurable_snd)).div_const σ)
  have hg := (supplementalH_gammaThreshold_absolutelyContinuous a hh q).ae_le hbudget
  have hs := ae_of_ae_map (measurable_gammaAdjustedThreshold a h).aemeasurable hg
  have hi : Integrable J ((gammaRectangleLaw m q).prod ν) := by
    apply (integrable_prod_iff hJ.aestronglyMeasurable).mpr
    refine ⟨hs.mono (fun e he => he.1),?_⟩
    have hm : AEStronglyMeasurable (fun e => ∫ x, ‖J (e,x)‖ ∂ν) (gammaRectangleLaw m q) :=
      (hJ.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
    apply (integrable_const B).mono' hm
    filter_upwards [hs] with e he
    change ‖∫ x, ‖J (e,x)‖ ∂ν‖≤B
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using he.2
  refine ⟨hi,?_⟩
  exact (integral_mono_ae hi.abs.integral_prod_left (integrable_const B)
    (hs.mono (fun e he => he.2))).trans_eq (by simp)

theorem supplementalH_gamma_positive_edge_mass_budget {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) (q : ℕ) :
    Integrable (fun z => ∑ e : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h z.1 j-faceDot (U (f j)) z.2)/σ) 0 e)
      ((gammaRectangleLaw m q).prod ν) ∧
    (∫ e, ∫ x, ∑ v : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h e j-faceDot (U (f j)) x)/σ) 0 v
        ∂ν ∂gammaRectangleLaw m q)≤
      (1024*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
        (σ*Real.sqrt (dimensionLog p)+δ*dimensionLog p) := by
  have hnonneg (b : Vector m) : 0≤∑ v : Fin m × Fin m,
      positiveEdgeTubeCoefficient (fun j => U (f j)) b 0 v :=
    Finset.sum_nonneg (fun v _ => positiveEdgeTubeCoefficient_nonneg _ _ _ v)
  have hbudget := ae_positiveEdgeTubeCoefficient_second_concentrated_base hp ν U f hK hδ hσ hu hbase
  have hF := Finset.measurable_sum Finset.univ (fun v _ =>
    measurable_positiveEdgeTubeCoefficient_threshold (fun j => U (f j)) 0 v)
  have hb := gamma_threshold_base_budget ν (fun j => U (f j)) a hh
    (fun b => ∑ v : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j)) b 0 v) hF
    (hbudget.mono (fun b hb => by simpa only [abs_of_nonneg (hnonneg _)] using hb)) q
  simpa only [abs_of_nonneg (hnonneg _)] using hb

theorem supplementalH_gamma_positive_edge_normSq_budget {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) (q : ℕ) :
    Integrable (fun z => ∑ e : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h z.1 j-faceDot (U (f j)) z.2)/σ) 2 e)
      ((gammaRectangleLaw m q).prod ν) ∧
    (∫ e, ∫ x, ∑ v : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h e j-faceDot (U (f j)) x)/σ) 2 v
        ∂ν ∂gammaRectangleLaw m q)≤
      (4096*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
        (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  have hnonneg (b : Vector m) : 0≤∑ v : Fin m × Fin m,
      positiveEdgeTubeCoefficient (fun j => U (f j)) b 2 v :=
    Finset.sum_nonneg (fun v _ => positiveEdgeTubeCoefficient_nonneg _ _ _ v)
  have hbudget := ae_positiveEdgeTubeCoefficient_fourth_concentrated_base hp ν U f hK hδ hσ hu hbase
  have hF := Finset.measurable_sum Finset.univ (fun v _ =>
    measurable_positiveEdgeTubeCoefficient_threshold (fun j => U (f j)) 2 v)
  have hb := gamma_threshold_base_budget ν (fun j => U (f j)) a hh
    (fun b => ∑ v : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j)) b 2 v) hF
    (hbudget.mono (fun b hb => by simpa only [abs_of_nonneg (hnonneg _)] using hb)) q
  simpa only [abs_of_nonneg (hnonneg _)] using hb

theorem supplementalH_gamma_ridge_leading_budget {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) (q : ℕ) :
    Integrable (fun z => hardGaussianRidgeLeadingIntegral (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h z.1 j-faceDot (U (f j)) z.2)/σ))
      ((gammaRectangleLaw m q).prod ν) ∧
    (∫ e, ∫ x, |hardGaussianRidgeLeadingIntegral (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h e j-faceDot (U (f j)) x)/σ)| ∂ν ∂gammaRectangleLaw m q)≤
      (3072*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
        (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  exact gamma_threshold_base_budget ν (fun j => U (f j)) a hh _
    (measurable_hardGaussianRidgeLeadingIntegral (fun j => U (f j)))
    (ae_hardGaussianRidgeLeadingIntegral_concentrated_base hp ν U f hK hδ hσ hu hbase) q

/-- The complete native signed ridge surface budget, including the actual
third-boundary contribution, under the actual Gamma threshold law. -/
theorem supplementalH_gamma_weighted_ridge_budget {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) (q : ℕ) :
    Integrable (fun z => hardGaussianWeightedRidgeIntegral (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h z.1 j-faceDot (U (f j)) z.2)/σ))
      ((gammaRectangleLaw m q).prod ν) ∧
    (∫ e, ∫ x, |hardGaussianWeightedRidgeIntegral (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h e j-faceDot (U (f j)) x)/σ)| ∂ν ∂gammaRectangleLaw m q)≤
      ((3072*Real.pi+6144)*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
        (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  exact gamma_threshold_base_budget ν (fun j => U (f j)) a hh _
    (measurable_hardGaussianWeightedRidgeIntegral (fun j => U (f j)))
    (ae_hardGaussianWeightedRidgeIntegral_concentrated_base hp ν U f hK hδ hσ hu hbase) q


/-- The actual bandwidth condition absorbs the base discretization cost. -/
theorem supplementalH_gamma_positive_edge_mass_budget_small_delta {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (q : ℕ) :
    (∫ e, ∫ x, ∑ v : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h e j-faceDot (U (f j)) x)/σ) 0 v ∂ν ∂gammaRectangleLaw m q)≤
      (2048*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*σ*(Real.sqrt (dimensionLog p)) := by
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hcost : δ*dimensionLog p≤σ*Real.sqrt (dimensionLog p) := by
    have ht := mul_le_mul_of_nonneg_right hδσ (Real.sqrt_nonneg (dimensionLog p))
    simpa only [mul_assoc,Real.mul_self_sqrt hL] using ht
  have hb := supplementalH_gamma_positive_edge_mass_budget hp ν U f a hK hδ hσ hh hu hbase q
  exact hb.2.trans ((mul_le_mul_of_nonneg_left (add_le_add_left hcost _) (by positivity)).trans_eq (by ring))

/-- The actual bandwidth condition absorbs the base discretization cost. -/
theorem supplementalH_gamma_positive_edge_normSq_budget_small_delta {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (q : ℕ) :
    (∫ e, ∫ x, ∑ v : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h e j-faceDot (U (f j)) x)/σ) 2 v ∂ν ∂gammaRectangleLaw m q)≤
      (8192*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*σ*(dimensionLog p*Real.sqrt (dimensionLog p)) := by
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hcost : δ*(dimensionLog p)^2≤σ*(dimensionLog p*Real.sqrt (dimensionLog p)) := by
    have ht := mul_le_mul_of_nonneg_right hδσ (mul_nonneg hL (Real.sqrt_nonneg (dimensionLog p)))
    calc
      _ = δ*dimensionLog p*(Real.sqrt (dimensionLog p))^2 := by rw [Real.sq_sqrt hL]; ring
      _ = (δ*Real.sqrt (dimensionLog p))*(dimensionLog p*Real.sqrt (dimensionLog p)) := by ring
      _ ≤ _ := ht
  have hb := supplementalH_gamma_positive_edge_normSq_budget hp ν U f a hK hδ hσ hh hu hbase q
  exact hb.2.trans ((mul_le_mul_of_nonneg_left (add_le_add_left hcost _) (by positivity)).trans_eq (by ring))

/-- The actual bandwidth condition absorbs the base discretization cost. -/
theorem supplementalH_gamma_ridge_leading_budget_small_delta {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (q : ℕ) :
    (∫ e, ∫ x, |hardGaussianRidgeLeadingIntegral (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h e j-faceDot (U (f j)) x)/σ)| ∂ν ∂gammaRectangleLaw m q)≤
      (6144*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*σ*(dimensionLog p*Real.sqrt (dimensionLog p)) := by
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hcost : δ*(dimensionLog p)^2≤σ*(dimensionLog p*Real.sqrt (dimensionLog p)) := by
    have ht := mul_le_mul_of_nonneg_right hδσ (mul_nonneg hL (Real.sqrt_nonneg (dimensionLog p)))
    calc
      _ = δ*dimensionLog p*(Real.sqrt (dimensionLog p))^2 := by rw [Real.sq_sqrt hL]; ring
      _ = (δ*Real.sqrt (dimensionLog p))*(dimensionLog p*Real.sqrt (dimensionLog p)) := by ring
      _ ≤ _ := ht
  have hb := supplementalH_gamma_ridge_leading_budget hp ν U f a hK hδ hσ hh hu hbase q
  exact hb.2.trans ((mul_le_mul_of_nonneg_left (add_le_add_left hcost _) (by positivity)).trans_eq (by ring))

/-- The actual bandwidth condition absorbs the base discretization cost. -/
theorem supplementalH_gamma_weighted_ridge_budget_small_delta {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ h : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (q : ℕ) :
    (∫ e, ∫ x, |hardGaussianWeightedRidgeIntegral (fun j => U (f j))
      (fun j => (gammaAdjustedThreshold a h e j-faceDot (U (f j)) x)/σ)| ∂ν ∂gammaRectangleLaw m q)≤
      ((6144*Real.pi+12288)*Real.exp ((3:ℝ)/2))*Real.exp 128*K*σ*(dimensionLog p*Real.sqrt (dimensionLog p)) := by
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hcost : δ*(dimensionLog p)^2≤σ*(dimensionLog p*Real.sqrt (dimensionLog p)) := by
    have ht := mul_le_mul_of_nonneg_right hδσ (mul_nonneg hL (Real.sqrt_nonneg (dimensionLog p)))
    calc
      _ = δ*dimensionLog p*(Real.sqrt (dimensionLog p))^2 := by rw [Real.sq_sqrt hL]; ring
      _ = (δ*Real.sqrt (dimensionLog p))*(dimensionLog p*Real.sqrt (dimensionLog p)) := by ring
      _ ≤ _ := ht
  have hb := supplementalH_gamma_weighted_ridge_budget hp ν U f a hK hδ hσ hh hu hbase q
  exact hb.2.trans ((mul_le_mul_of_nonneg_left (add_le_add_left hcost _) (by positivity)).trans_eq (by ring))

end
end RectangleCLTArxivV1
