import RectangleCLTArxivV1.SupplementalHPositiveEdgeSum
import RectangleCLTArxivV1.SupplementalHFourthTransportAveraged
import RectangleCLTArxivV1.SupplementalHLocalizedMoments
import RectangleCLTArxivV1.SupplementalHRidgeGreen

/-! Actual positive-edge mass, projected second moment and signed leading
ridge term averaged over a concentrated base. Threshold regularity is
removed by honest affine/product almost-everywhere transport. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem continuous_fourthRidgeNormalPoint_threshold {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) : Continuous (fun b => fourthRidgeNormalPoint u b j l) := by
  unfold fourthRidgeNormalPoint thresholdPairFirstLevel thresholdPairSecondLevel
  fun_prop

theorem measurable_hardGaussianRidgeDensity {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) : Measurable (fun b => hardGaussianRidgeDensity u b j l) := by
  have h1 : Measurable (fun b => thresholdPairFirstLevel u b j l) := by
    unfold thresholdPairFirstLevel
    fun_prop
  have h2 : Measurable (fun b => thresholdPairSecondLevel u b j l) := by
    unfold thresholdPairSecondLevel
    fun_prop
  have hp : Measurable (fun z : Vector m × Vector r => gaussianPairBase u z.1 j l z.2) :=
    (measurable_gaussianPairSectionMap (thresholdPairBisector u j l) (thresholdPairDifference u j l)).comp
      (((h1.comp measurable_fst).prodMk (h2.comp measurable_fst)).prodMk measurable_snd)
  let E : Set (Vector m × Vector r) := {z | ∀ k, k≠j → k≠l →
    faceDot (u k) (gaussianPairBase u z.1 j l z.2)≤z.1 k}
  have hE : MeasurableSet E := by
    unfold E
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
      measurableSet_le ((measurable_thresholdDot _).comp hp) ((measurable_pi_apply k).comp measurable_fst))))
  have hP : Measurable (fun b => (standardGaussian r).real {g | ∀ k, k≠j → k≠l →
      faceDot (u k) (gaussianPairBase u b j l g)≤b k}) := by
    have hm : Measurable (fun b : Vector m => ∫ g, E.indicator (fun _ => (1:ℝ)) (b,g) ∂standardGaussian r) :=
      ((measurable_const : Measurable (fun _ : Vector m × Vector r => (1:ℝ))).indicator hE).stronglyMeasurable.integral_prod_right'.measurable
    have he (b : Vector m) : (∫ g, E.indicator (fun _ => (1:ℝ)) (b,g) ∂standardGaussian r)=
        (standardGaussian r).real {g | ∀ k, k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)≤b k} := by
      have hS : MeasurableSet {g | ∀ k, k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)≤b k} := by
        simp only [setOf_forall]
        exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
          measurableSet_le ((measurable_thresholdDot _).comp (measurable_gaussianPairBase u b j l)) measurable_const)))
      change (∫ g, {g | ∀ k, k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)≤b k}.indicator
        (fun _ => (1:ℝ)) g ∂standardGaussian r)=_
      rw [integral_indicator_const _ hS,smul_eq_mul,mul_one]
    simpa only [he] using hm
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  exact ((((hpdf.measurable.comp h1).mul (hpdf.measurable.comp h2)).div_const _).mul hP)

theorem positiveEdgeTubeCoefficient_nonneg {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (k : ℕ) (q : Fin m × Fin m) : 0≤positiveEdgeTubeCoefficient u b k q := by
  classical
  unfold positiveEdgeTubeCoefficient
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Real.arccos_nonneg _) (pow_nonneg (norm_nonneg _) k))
      (Real.sqrt_nonneg _)) (hardGaussianRidgeDensity_nonneg u b q.1 q.2)
  · exact le_rfl

theorem measurable_positiveEdgeTubeCoefficient_threshold {m r : ℕ} (u : Fin m → Vector r)
    (k : ℕ) (q : Fin m × Fin m) : Measurable (fun b => positiveEdgeTubeCoefficient u b k q) := by
  classical
  unfold positiveEdgeTubeCoefficient
  split_ifs
  · exact measurable_const
  · exact ((measurable_const.mul ((continuous_fourthRidgeNormalPoint_threshold u q.1 q.2).measurable.norm.pow_const k)).mul_const _).mul
      (measurable_hardGaussianRidgeDensity u q.1 q.2)
  · exact measurable_const

def positiveEdgeLeadingTerm {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : ℝ :=
  (1/2:ℝ)*∑ q : Fin m × Fin m,
    (positiveEdgeTubeCoefficient u b 2 q-2*positiveEdgeTubeCoefficient u b 0 q)

theorem positiveEdgeLeadingTerm_abs_le {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) :
    |positiveEdgeLeadingTerm u b| ≤
      (1/2:ℝ)*(∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient u b 2 q)+
        ∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient u b 0 q := by
  have h2 : 0≤∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient u b 2 q :=
    Finset.sum_nonneg (fun q _ => positiveEdgeTubeCoefficient_nonneg u b 2 q)
  have h0 : 0≤∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient u b 0 q :=
    Finset.sum_nonneg (fun q _ => positiveEdgeTubeCoefficient_nonneg u b 0 q)
  unfold positiveEdgeLeadingTerm
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have hh := abs_sub (∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient u b 2 q)
    (2*∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient u b 0 q)
  rw [abs_of_nonneg h2,abs_of_nonneg (mul_nonneg (by norm_num) h0)] at hh
  nlinarith

theorem positiveEdge_outer_affine_integral_eq {p m r : ℕ}
    (U : Face p → Vector r) (f : Fin m → Face p) (a : Vector m) (x : Vector r)
    {σ : ℝ} (hσ : 0<σ) (k : ℕ) :
    (∫ g, (fourthOuterLayer (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ) (fourthThreeFaceRadius U)).indicator
        (fun g => supplementalHRadius U g^k) g ∂standardGaussian r)=
      ∫ g, (gaussianOutwardVariableTube (fun j => U (f j)) a σ (supplementalHRadius U)).indicator
        (fun z => supplementalHRadius U z.2^k) (x,g) ∂standardGaussian r := by
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    have he := fourthOuterLayer_shift_threshold (fun j => U (f j)) a x hσ (fourthThreeFaceRadius U) g
    change g∈fourthOuterLayer (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ) (fourthThreeFaceRadius U) ↔
      (x,g)∈gaussianOutwardVariableTube (fun j => U (f j)) a σ (supplementalHRadius U) at he
    by_cases hg : g∈fourthOuterLayer (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ) (fourthThreeFaceRadius U)
    · rw [indicator_of_mem hg,indicator_of_mem (he.mp hg)]
    · rw [indicator_of_not_mem hg,indicator_of_not_mem (fun h => hg (he.mpr h))])

private theorem positiveEdge_base_average_of_fixed {p m n : ℕ}
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m) {σ C : ℝ}
    (k d : ℕ) (hC : 0≤C)
    (hRd : Integrable (fun g => supplementalHRadius U g^d) (standardGaussian (n+1)))
    (hfixed : ∀ᵐ x ∂ν,
      (∑ q : Fin m × Fin m, positiveEdgeTubeCoefficient (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ) k q)≤
      C*(∫ g,(gaussianOutwardVariableTube (fun j => U (f j)) a σ (supplementalHRadius U)).indicator
        (fun z => supplementalHRadius U z.2^d) (x,g) ∂standardGaussian (n+1))) :
    Integrable (fun x => ∑ q : Fin m × Fin m, positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ) k q) ν ∧
    (∫ x, ∑ q : Fin m × Fin m, positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ) k q ∂ν)≤
      C*(∫ z,(gaussianOutwardVariableTube (fun j => U (f j)) a σ (supplementalHRadius U)).indicator
        (fun z => supplementalHRadius U z.2^d) z ∂ν.prod (standardGaussian (n+1))) := by
  let I := (gaussianOutwardVariableTube (fun j => U (f j)) a σ (supplementalHRadius U)).indicator
    (fun z => supplementalHRadius U z.2^d)
  have hIset := fourthTransport_measurableSet_gaussianOutwardVariableTube (fun j => U (f j)) a σ
    (supplementalHRadius U) (measurable_supplementalHRadius U)
  have hi : Integrable I (ν.prod (standardGaussian (n+1))) := by
    have hr : Integrable (fun z : Vector (n+1) × Vector (n+1) => supplementalHRadius U z.2^d)
        (ν.prod (standardGaussian (n+1))) := by
      simpa only [one_mul] using (integrable_const (μ := ν) (1:ℝ)).mul_prod hRd
    exact hr.indicator hIset
  have hthreshold : Measurable (fun x : Vector (n+1) => fun j => (a j-faceDot (U (f j)) x)/σ) := by
    apply measurable_pi_lambda
    intro j
    exact (measurable_const.sub (measurable_thresholdDot _)).div_const σ
  have hm := Finset.measurable_sum Finset.univ (fun q _ =>
    (measurable_positiveEdgeTubeCoefficient_threshold (fun j => U (f j)) k q).comp hthreshold)
  have hiF := (hi.integral_prod_left.const_mul C).mono' hm.aestronglyMeasurable
    (hfixed.mono (fun x hx => by
      simp only [Function.comp_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun (q : Fin m × Fin m) _ =>
        positiveEdgeTubeCoefficient_nonneg (fun j => U (f j)) (fun j => (a j-faceDot (U (f j)) x)/σ) k q))]
      exact hx))
  refine ⟨hiF, ?_⟩
  have hb := integral_mono_ae hiF (hi.integral_prod_left.const_mul C) hfixed
  rw [integral_const_mul,← integral_prod _ hi] at hb
  exact hb

theorem positiveEdgeTubeCoefficient_second_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ᵐ x ∂ν,∀ j,ResidualThresholdRegularity (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ) j)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) :
    Integrable (fun x => ∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ) 0 q) ν ∧
    (∫ x, ∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ) 0 q ∂ν)≤
      (1024*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*(σ*Real.sqrt (dimensionLog p)+δ*dimensionLog p) := by
  have hf : ∀ᵐ x ∂ν,
      (∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ) 0 q)≤
        (1024*Real.pi*Real.exp ((3:ℝ)/2))*(∫ g,
          (gaussianOutwardVariableTube (fun j => U (f j)) a σ (supplementalHRadius U)).indicator
            (fun z => supplementalHRadius U z.2^2) (x,g) ∂standardGaussian (n+1)) := by
    filter_upwards [hreg] with x hx
    have hh := positiveEdgeTubeCoefficient_second_threeFace_bound hp U f
      (fun j => (a j-faceDot (U (f j)) x)/σ) hu hx
    rwa [positiveEdge_outer_affine_integral_eq U f a x hσ 2] at hh
  have hh := positiveEdge_base_average_of_fixed ν U f a 0 2 (by positivity)
    (supplementalHRadius_moment_le hp U 2).1 hf
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (concentrated_base_threeFace_second_outward_tube hp ν
    (fun j => U (f j)) a U hK hδ hσ hbase) (by positivity : 0≤1024*Real.pi*Real.exp ((3:ℝ)/2))).trans_eq (by ring)

theorem positiveEdgeTubeCoefficient_fourth_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ᵐ x ∂ν,∀ j,ResidualThresholdRegularity (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ) j)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) :
    Integrable (fun x => ∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ) 2 q) ν ∧
    (∫ x, ∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ) 2 q ∂ν)≤
      (4096*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
        (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  have hf : ∀ᵐ x ∂ν,
      (∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ) 2 q)≤
        (4096*Real.pi*Real.exp ((3:ℝ)/2))*(∫ g,
          (gaussianOutwardVariableTube (fun j => U (f j)) a σ (supplementalHRadius U)).indicator
            (fun z => supplementalHRadius U z.2^4) (x,g) ∂standardGaussian (n+1)) := by
    filter_upwards [hreg] with x hx
    have hh := positiveEdgeTubeCoefficient_fourth_threeFace_bound hp U f
      (fun j => (a j-faceDot (U (f j)) x)/σ) hu hx
    rwa [positiveEdge_outer_affine_integral_eq U f a x hσ 4] at hh
  have hh := positiveEdge_base_average_of_fixed ν U f a 2 4 (by positivity)
    (supplementalHRadius_moment_le hp U 4).1 hf
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (concentrated_base_threeFace_weighted_outward_tube hp ν
    (fun j => U (f j)) a U hK hδ hσ hbase) (by positivity : 0≤4096*Real.pi*Real.exp ((3:ℝ)/2))).trans_eq (by ring)

theorem positiveEdgeLeadingTerm_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ᵐ x ∂ν,∀ j,ResidualThresholdRegularity (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ) j)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) :
    Integrable (fun x => positiveEdgeLeadingTerm (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ)) ν ∧
    (∫ x, |positiveEdgeLeadingTerm (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ)| ∂ν)≤
      (3072*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
        (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  let F := fun k (x : Vector (n+1)) => ∑ q : Fin m × Fin m,
    positiveEdgeTubeCoefficient (fun j => U (f j)) (fun j => (a j-faceDot (U (f j)) x)/σ) k q
  have h0 := positiveEdgeTubeCoefficient_second_concentrated_base hp ν U f a hK hδ hσ hu hreg hbase
  have h2 := positiveEdgeTubeCoefficient_fourth_concentrated_base hp ν U f a hK hδ hσ hu hreg hbase
  have he (x : Vector (n+1)) : positiveEdgeLeadingTerm (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ)=(1/2:ℝ)*(F 2 x-2*F 0 x) := by
    simp only [positiveEdgeLeadingTerm,F,Finset.sum_sub_distrib,← Finset.mul_sum]
  have hi : Integrable (fun x => positiveEdgeLeadingTerm (fun j => U (f j))
      (fun j => (a j-faceDot (U (f j)) x)/σ)) ν := by
    simpa only [he] using ((h2.1.sub (h0.1.const_mul 2)).const_mul (1/2:ℝ))
  refine ⟨hi, ?_⟩
  have hb := integral_mono hi.abs ((h2.1.const_mul (1/2:ℝ)).add h0.1)
    (fun x => positiveEdgeLeadingTerm_abs_le (fun j => U (f j)) _)
  simp only [Pi.add_apply] at hb
  rw [integral_add (h2.1.const_mul (1/2:ℝ)) h0.1,integral_const_mul] at hb
  have hL : 1≤dimensionLog p := log_exp_mul_nat_ge_one hp
  have hl : Real.sqrt (dimensionLog p) ≤ dimensionLog p*Real.sqrt (dimensionLog p) :=
    le_mul_of_one_le_left (Real.sqrt_nonneg _) hL
  have hll : dimensionLog p ≤ (dimensionLog p)^2 := by nlinarith
  have hcost : σ*Real.sqrt (dimensionLog p)+δ*dimensionLog p ≤
      σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2 :=
    add_le_add (mul_le_mul_of_nonneg_left hl hσ.le) (mul_le_mul_of_nonneg_left hll hδ)
  have h0' := h0.2.trans (mul_le_mul_of_nonneg_left hcost
    (by positivity : 0≤(1024*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K))
  exact hb.trans ((add_le_add (mul_le_mul_of_nonneg_left h2.2 (by norm_num : (0:ℝ)≤1/2)) h0').trans_eq (by ring))

theorem ae_positiveEdgeTubeCoefficient_second_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) :
    ∀ᵐ a : Vector m ∂volume,
      Integrable (fun x => ∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ) 0 q) ν ∧
      (∫ x, ∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ) 0 q ∂ν)≤
        (1024*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*(σ*Real.sqrt (dimensionLog p)+δ*dimensionLog p) := by
  filter_upwards [ae_threshold_ae_base_residualThresholdRegularity ν (fun j => U (f j)) hσ.ne'] with a ha
  exact positiveEdgeTubeCoefficient_second_concentrated_base hp ν U f a hK hδ hσ hu ha hbase

theorem ae_positiveEdgeTubeCoefficient_fourth_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) :
    ∀ᵐ a : Vector m ∂volume,
      Integrable (fun x => ∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ) 2 q) ν ∧
      (∫ x, ∑ q : Fin m × Fin m,positiveEdgeTubeCoefficient (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ) 2 q ∂ν)≤
        (4096*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
          (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  filter_upwards [ae_threshold_ae_base_residualThresholdRegularity ν (fun j => U (f j)) hσ.ne'] with a ha
  exact positiveEdgeTubeCoefficient_fourth_concentrated_base hp ν U f a hK hδ hσ hu ha hbase

theorem ae_positiveEdgeLeadingTerm_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) :
    ∀ᵐ a : Vector m ∂volume,
      Integrable (fun x => positiveEdgeLeadingTerm (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ)) ν ∧
      (∫ x, |positiveEdgeLeadingTerm (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ)| ∂ν)≤
        (3072*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
          (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  filter_upwards [ae_threshold_ae_base_residualThresholdRegularity ν (fun j => U (f j)) hσ.ne'] with a ha
  exact positiveEdgeLeadingTerm_concentrated_base hp ν U f a hK hδ hσ hu ha hbase

theorem positiveEdge_pairSectionProbability_eq {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b
      (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)=
      (standardGaussian r).real {g | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)≤b k} := by
  classical
  let E : Set (Vector r) := {g | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)≤b k}
  have hE : MeasurableSet E := by
    unfold E
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
      measurableSet_le ((measurable_thresholdDot _).comp (measurable_gaussianPairBase u b j l)) measurable_const)))
  have he : (∫ g, E.indicator (fun _ => (1:ℝ)) g ∂standardGaussian r)=(standardGaussian r).real E := by
    rw [integral_indicator_const _ hE,smul_eq_mul,mul_one]
  rw [← he]
  unfold hardGaussianPairSectionProbability
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have hiff : gaussianPairBase u b j l g∈gaussianFiniteThresholdEvent ((Finset.univ.erase j).erase l) u b ↔ g∈E := by
      simp only [gaussianFiniteThresholdEvent,mem_setOf_eq,Finset.mem_erase,Finset.mem_univ,and_true,E]
      constructor
      · intro h k hkj hkl
        exact h k ⟨hkl,hkj⟩
      · intro h k hk
        exact h k hk.2 hk.1
    change (gaussianFiniteThresholdEvent ((Finset.univ.erase j).erase l) u b).indicator
      (fun _ => (1:ℝ)) (gaussianPairBase u b j l g)=E.indicator (fun _ => (1:ℝ)) g
    by_cases hg : g∈E
    · rw [indicator_of_mem (hiff.mpr hg),indicator_of_mem hg]
    · rw [indicator_of_not_mem (fun h => hg (hiff.mp h)),indicator_of_not_mem hg])

theorem fourthRidgeNormalPoint_norm_sq_eq {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    ‖fourthRidgeNormalPoint u b j l‖^2=
      (thresholdPairFirstLevel u b j l)^2+(thresholdPairSecondLevel u b j l)^2 := by
  let U := projectionEuclideanVector (u j)
  let V := projectionEuclideanVector (u l)
  have hU : ‖U‖=1 := thresholdEuclideanNormal_unit _ hu
  have hV : ‖V‖=1 := thresholdEuclideanNormal_unit _ hv
  have he := norm_bisector U V hp
  have hf := norm_differenceDirection U V hm
  have hef := inner_bisector_differenceDirection U V (hU.trans hV.symm)
  rw [fourthRidgeNormalPoint,thresholdPairBisector_euclidean,thresholdPairDifference_euclidean,norm_add_sq_real]
  simp only [U,V,norm_smul,Real.norm_eq_abs,he,hf,mul_one,sq_abs,inner_smul_left,
    inner_smul_right,conj_trivial,hef,mul_zero,zero_mul,add_zero]

theorem positiveEdgeTubeCoefficient_sub_eq_ridgeLeading {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1) (j l : Fin m) :
    positiveEdgeTubeCoefficient u b 2 (j,l)-2*positiveEdgeTubeCoefficient u b 0 (j,l)=
      hardGaussianRidgeLeadingTerm u b j l := by
  classical
  by_cases hjl : j=l
  · subst l
    simp [positiveEdgeTubeCoefficient,hardGaussianRidgeLeadingTerm,hardGaussianRidgeNonparallel]
  · by_cases hp : hardGaussianRidgeNonparallel u j l
    · have hinner : ⟪projectionEuclideanVector (u j),projectionEuclideanVector (u l)⟫_ℝ=faceDot (u j) (u l) := by
        simp [projectionEuclideanVector,faceDot,PiLp.inner_apply,mul_comm]
      have hnorm := fourthRidgeNormalPoint_norm_sq_eq u b j l (hu j) (hu l) hp.1 hp.2
      have hsin : 0<gaussianThresholdResidualScale u j l := by
        rw [thresholdPair_residualScale_eq u j l (hu j) (hu l) hp.1 hp.2]
        exact mul_pos (mul_pos (by norm_num) (div_pos (norm_pos_iff.mpr hp.1) (by norm_num)))
          (div_pos (norm_pos_iff.mpr hp.2) (by norm_num))
      rw [gaussianThresholdResidualScale_eq_sqrt_of_unit u j l (hu j) (hu l)] at hsin
      have hp' : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 ∧
          projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0 := hp
      simp only [positiveEdgeTubeCoefficient,Prod.fst,Prod.snd,if_neg hjl,hardGaussianRidgeNonparallel,
        if_pos hp',pow_zero,mul_one,hardGaussianRidgeLeadingTerm,hnorm,hinner]
      rw [positiveEdge_pairSectionProbability_eq]
      unfold hardGaussianRidgeDensity hardGaussianRidgeNormalWeight
      field_simp [hsin.ne']
      ring
    · have hp' : ¬(projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 ∧
          projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) := hp
      simp only [positiveEdgeTubeCoefficient,Prod.fst,Prod.snd,if_neg hjl,hardGaussianRidgeNonparallel,
        if_neg hp',hardGaussianRidgeLeadingTerm,mul_zero,sub_self]

theorem positiveEdgeLeadingTerm_eq_hardGaussianRidgeLeadingIntegral {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1) :
    positiveEdgeLeadingTerm u b=hardGaussianRidgeLeadingIntegral u b := by
  unfold positiveEdgeLeadingTerm hardGaussianRidgeLeadingIntegral
  congr 1
  exact Finset.sum_congr rfl (fun q _ => positiveEdgeTubeCoefficient_sub_eq_ridgeLeading u b hu q.1 q.2)

/-- Actual native leading term of the signed Gaussian ridge Green
identity. Every threshold/base regularity and positive moment estimate has
been discharged; the signed third-boundary term is separate. -/
theorem ae_hardGaussianRidgeLeadingIntegral_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun j => U (f j)) b s)≤K*(s+δ)) :
    ∀ᵐ a : Vector m ∂volume,
      Integrable (fun x => hardGaussianRidgeLeadingIntegral (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ)) ν ∧
      (∫ x, |hardGaussianRidgeLeadingIntegral (fun j => U (f j))
        (fun j => (a j-faceDot (U (f j)) x)/σ)| ∂ν)≤
        (3072*Real.pi*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
          (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  have hh := ae_positiveEdgeLeadingTerm_concentrated_base hp ν U f hK hδ hσ hu hbase
  simpa only [positiveEdgeLeadingTerm_eq_hardGaussianRidgeLeadingIntegral _ _ hu] using hh

end
end RectangleCLTArxivV1
