import RectangleCLTArxivV1.SupplementalHLocalizedTube
import RectangleCLTArxivV1.SupplementalHRadius

/-! The actual concentrated-base Gaussian tube estimate for every
successive pair of ordinary radius moments. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT
open scoped BigOperators
noncomputable section

theorem concentrated_base_gaussian_weighted_tube_power {r m : ℕ}
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m)
    {K δ σ : ℝ} (hσ : 0 < σ)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0 < s → ν.real (faceLayer U b s) ≤ K*(s+δ))
    (R : Vector r → ℝ) (hR : Measurable R) (hRpos : ∀ g, 0 < R g)
    (k : ℕ)
    (hRprev : Integrable (fun g => (R g)^k) (standardGaussian r))
    (hRnext : Integrable (fun g => (R g)^(k+1)) (standardGaussian r)) :
    (∫ z, (gaussianVariableTube U a σ R).indicator (fun z => (R z.2)^(k+1)) z
      ∂ν.prod (standardGaussian r)) ≤
      K*(σ*(∫ g, (R g)^k ∂standardGaussian r)+
        δ*(∫ g, (R g)^(k+1) ∂standardGaussian r)) := by
  let S := gaussianVariableTube U a σ R
  let I : Vector r × Vector r → ℝ := S.indicator (fun z => (R z.2)^(k+1))
  have hS := measurableSet_gaussianVariableTube U a σ R hR
  have hI : Measurable I :=
    ((hR.comp measurable_snd).pow_const (k+1)).indicator hS
  have hprod : Integrable (fun z : Vector r × Vector r => (R z.2)^(k+1))
      (ν.prod (standardGaussian r)) := by
    simpa only [one_mul] using (integrable_const (μ := ν) (1:ℝ)).mul_prod hRnext
  have hiI : Integrable I (ν.prod (standardGaussian r)) := by
    apply hprod.mono' hI.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      by_cases hz : z ∈ S
      · simp only [I,Set.indicator_of_mem hz,Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (hRpos z.2).le (k+1)),le_refl]
      · simp only [I,Set.indicator_of_not_mem hz,norm_zero]
        exact pow_nonneg (hRpos z.2).le (k+1))
  have hfixed (g : Vector r) : (∫ x, I (x,g) ∂ν) =
      (R g)^(k+1)*ν.real {x | x+σ • g ∈ faceLayer U a (σ/R g)} := by
    have hE : MeasurableSet {x | x+σ • g ∈ faceLayer U a (σ/R g)} :=
      (measurableSet_faceLayer U a (σ/R g)).preimage (measurable_id.add_const _)
    change (∫ x, {x | x+σ • g ∈ faceLayer U a (σ/R g)}.indicator
      (fun _ => (R g)^(k+1)) x ∂ν) = _
    rw [integral_indicator hE,setIntegral_const,smul_eq_mul,mul_comm]
  have hsection (g : Vector r) : (∫ x, I (x,g) ∂ν) ≤
      K*(σ*(R g)^k+δ*(R g)^(k+1)) := by
    rw [hfixed,faceLayer_translate]
    have hh := hbase (fun j => a j-dotProduct (U j) (σ • g)) (σ/R g)
      (div_pos hσ (hRpos g))
    apply (mul_le_mul_of_nonneg_left hh (pow_nonneg (hRpos g).le (k+1))).trans_eq
    simp only [pow_succ]
    field_simp [(hRpos g).ne']
    ring
  have hiBound : Integrable (fun g => K*(σ*(R g)^k+δ*(R g)^(k+1))) (standardGaussian r) :=
    ((hRprev.const_mul σ).add (hRnext.const_mul δ)).const_mul K
  change (∫ z, I z ∂ν.prod (standardGaussian r)) ≤ _
  rw [integral_prod_symm I hiI]
  apply (integral_mono hiI.integral_prod_right hiBound hsection).trans_eq
  rw [integral_const_mul,integral_add (hRprev.const_mul σ) (hRnext.const_mul δ),
    integral_const_mul,integral_const_mul]


theorem concentrated_base_gaussian_weighted_outward_tube_power {r m : ℕ}
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m)
    {K δ σ : ℝ} (hσ : 0 < σ)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0 < s → ν.real (faceLayer U b s) ≤ K*(s+δ))
    (R : Vector r → ℝ) (hR : Measurable R) (hRpos : ∀ g, 0 < R g)
    (k : ℕ)
    (hRprev : Integrable (fun g => (R g)^k) (standardGaussian r))
    (hRnext : Integrable (fun g => (R g)^(k+1)) (standardGaussian r)) :
    (∫ z, (gaussianOutwardVariableTube U a σ R).indicator (fun z => (R z.2)^(k+1)) z
      ∂ν.prod (standardGaussian r)) ≤
      K*(σ*(∫ g, (R g)^k ∂standardGaussian r)+
        δ*(∫ g, (R g)^(k+1) ∂standardGaussian r)) := by
  have he := gaussianOutwardVariableTube_eq U a hσ.le R hRpos
  have hS := measurableSet_gaussianVariableTube U a σ R hR
  have hzero : MeasurableSet {z : Vector r × Vector r |
      z.1+σ • z.2 ∈ facePolyhedron U a 0} := by
    change MeasurableSet {z : Vector r × Vector r |
      ∀ j, dotProduct (U j) (z.1+σ • z.2) ≤ a j+0}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le
      ((measurable_pi_apply j).comp ((measurable_faceProjection U).comp
        (measurable_fst.add (measurable_const.smul measurable_snd)))) measurable_const
  have hOut : MeasurableSet (gaussianOutwardVariableTube U a σ R) := by
    rw [he]
    exact hS.diff hzero
  have hi : Integrable (fun z : Vector r × Vector r => (R z.2)^(k+1))
      (ν.prod (standardGaussian r)) := by
    simpa only [one_mul] using (integrable_const (μ := ν) (1:ℝ)).mul_prod hRnext
  apply (integral_mono (hi.indicator hOut) (hi.indicator hS) ?_).trans
    (concentrated_base_gaussian_weighted_tube_power ν U a hσ hbase R hR hRpos k hRprev hRnext)
  intro z
  by_cases hz : z ∈ gaussianOutwardVariableTube U a σ R
  · have hzS : z ∈ gaussianVariableTube U a σ R := by rw [he] at hz; exact hz.1
    simp only [Set.indicator_of_mem hz,Set.indicator_of_mem hzS,le_refl]
  · simp only [Set.indicator_of_not_mem hz]
    by_cases hzS : z ∈ gaussianVariableTube U a σ R
    · simp only [Set.indicator_of_mem hzS]
      exact pow_nonneg (hRpos z.2).le (k+1)
    · simp only [Set.indicator_of_not_mem hzS,le_refl]



/-- The actual three-face radius gives the sharp second-weight outward
budget, retaining sqrt(log) for the positive edge mass. -/
theorem concentrated_base_threeFace_second_outward_tube {p r m : ℕ} (hp : 1≤p)
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (B : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (U : Face p → Vector r)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0<s → ν.real (faceLayer B b s)≤K*(s+δ)) :
    (∫ z, (gaussianOutwardVariableTube B a σ (supplementalHRadius U)).indicator
      (fun z => (supplementalHRadius U z.2)^2) z ∂ν.prod (standardGaussian r))≤
      Real.exp 128*K*(σ*Real.sqrt (dimensionLog p)+δ*dimensionLog p) := by
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have h1 := supplementalHRadius_moment_le hp U 1
  have h2 := supplementalHRadius_moment_le hp U 2
  have h1b : (∫ g, (supplementalHRadius U g)^1 ∂standardGaussian r)≤
      Real.exp 128*Real.sqrt (dimensionLog p) := by
    have hh : (∫ g, (supplementalHRadius U g)^1 ∂standardGaussian r)≤
        (Real.sqrt (dimensionLog p))^1*Real.exp 128 := by
      apply h1.2.trans
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg _) 1)
      apply Real.exp_le_exp.mpr
      norm_num
    simpa only [pow_one,mul_comm] using hh
  have h2b : (∫ g, (supplementalHRadius U g)^2 ∂standardGaussian r)≤
      Real.exp 128*dimensionLog p := by
    have hh : (∫ g, (supplementalHRadius U g)^2 ∂standardGaussian r)≤
        (Real.sqrt (dimensionLog p))^2*Real.exp 128 := by
      apply h2.2.trans
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg _) 2)
      apply Real.exp_le_exp.mpr
      norm_num
    simpa only [Real.sq_sqrt hL,mul_comm] using hh
  have ht := concentrated_base_gaussian_weighted_outward_tube_power ν B a hσ hbase
    (supplementalHRadius U) (measurable_supplementalHRadius U) (supplementalHRadius_pos U) 1 h1.1 h2.1
  calc
    _ ≤ K*(σ*(∫ g, (supplementalHRadius U g)^1 ∂standardGaussian r)+
        δ*(∫ g, (supplementalHRadius U g)^2 ∂standardGaussian r)) := ht
    _ ≤ K*(σ*(Real.exp 128*Real.sqrt (dimensionLog p))+δ*(Real.exp 128*dimensionLog p)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1b hσ.le)
        (mul_le_mul_of_nonneg_left h2b hδ)) hK
    _ = _ := by ring

end
end RectangleCLTArxivV1
