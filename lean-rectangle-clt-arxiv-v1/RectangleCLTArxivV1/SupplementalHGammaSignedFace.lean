import RectangleCLTArxivV1.SupplementalHGammaAbsoluteFace
import RectangleCLTArxivV1.SupplementalHSignedThresholdDerivative

/-! Actual signed first Gamma coarea preceding mixed differentiation. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem supplementalH_hasDerivAt_gamma_signedFace_offset {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j : Fin m) (q : ℕ) :
    HasDerivAt (fun t => ∫ e, gaussianThresholdTrace u
      (fun k => (gammaAdjustedThreshold (Function.update a j (a j+t)) h e k-faceDot (u k) x)/σ)
      ∂gammaRectangleLaw m q)
      (σ⁻¹*(∫ e,
        gaussianPDFReal 0 1 ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)*
          Printed.thresholdSignedSection u
            (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j
            ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ) ∂gammaRectangleLaw m q)) 0 := by
  classical
  let b := fun e k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ
  let F := fun t e => gaussianThresholdTrace u (Function.update (b e) j (b e j+t/σ))
  let D := fun e => σ⁻¹*(gaussianPDFReal 0 1 (b e j)*Printed.thresholdSignedSection u (b e) j (b e j))
  have hb : Measurable b := by unfold b gammaAdjustedThreshold faceDot; fun_prop
  have hF (t : ℝ) : Measurable (F t) := (measurable_gaussianThresholdTrace_threshold u).comp (by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k=j
    · subst k
      simpa only [Function.update_self] using (((measurable_pi_apply j).comp hb).add_const (t/σ))
    · simpa only [Function.update_of_ne hk] using (measurable_pi_apply k).comp hb)
  have hFi : Integrable (F 0) (gammaRectangleLaw m q) := by
    apply (integrable_const (2*((n+1:ℕ):ℝ))).mono' (hF 0).aestronglyMeasurable
    exact ae_of_all _ (fun e => by
      simpa only [Real.norm_eq_abs] using abs_gaussianThresholdTrace_le_twice_dimension u _)
  have hD : Measurable D := by
    exact (((measurable_gaussianPDFReal 0 1).comp ((measurable_pi_apply j).comp hb)).mul
      ((measurable_thresholdSignedSection_threshold u j).comp hb)).const_mul _
  have hAffine : Measure.QuasiMeasurePreserving (fun c : Vector m =>
      σ⁻¹ • (c+ -(fun k => faceDot (u k) x))) volume volume :=
    (Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hσ.ne')).comp
      (MeasureTheory.quasiMeasurePreserving_add_right volume _)
  have hΓ : Measure.QuasiMeasurePreserving (gammaAdjustedThreshold a h) (gammaRectangleLaw m q) volume :=
    ⟨measurable_gammaAdjustedThreshold a h,supplementalH_gammaThreshold_absolutelyContinuous a hh q⟩
  have hAE := (hAffine.comp hΓ).ae (ae_hasDerivAt_gaussianThresholdTrace_update u hu)
  have heB (e) : σ⁻¹ • (gammaAdjustedThreshold a h e+ -(fun k => faceDot (u k) x))=b e := by
    funext k
    dsimp only [b,Pi.smul_apply,Pi.add_apply,Pi.neg_apply,smul_eq_mul]
    ring
  simp only [Function.comp_apply,heB] at hAE
  have hdiff : ∀ᵐ e ∂gammaRectangleLaw m q, HasDerivAt (fun t => F t e) (D e) 0 := by
    filter_upwards [hAE] with e he
    have ht : HasDerivAt (fun t : ℝ => b e j+t/σ) (σ⁻¹) 0 := by
      convert (hasDerivAt_const 0 (b e j)).add ((hasDerivAt_id 0).div_const σ) using 1 <;> simp
    have hhard : HasDerivAt (fun t => gaussianThresholdTrace u (Function.update (b e) j t))
        (gaussianPDFReal 0 1 (b e j)*Printed.thresholdSignedSection u (b e) j (b e j))
        (b e j+0/σ) := by simpa only [zero_div,add_zero] using he j
    have hd := hhard.comp 0 ht
    simpa only [zero_div,add_zero,F,D,mul_comm] using hd
  let C := gaussianSignedFaceDensityBudget (n+1)/σ
  have hC : 0≤C := div_nonneg (gaussianSignedFaceDensityBudget_nonneg _) hσ.le
  have hLip (e) : LipschitzWith (Real.nnabs C) (fun t => F t e) := by
    apply LipschitzWith.of_dist_le_mul
    intro c d
    have ht := gaussianThresholdTrace_update_increment_bound u (b e) j (hu j)
      (b e j+c/σ) (b e j+d/σ)
    rw [show b e j+c/σ-(b e j+d/σ)=(c-d)/σ by ring,abs_div,abs_of_pos hσ] at ht
    change |F c e-F d e|≤(Real.nnabs C:ℝ)*|c-d|
    rw [Real.coe_nnabs,abs_of_nonneg hC]
    exact ht.trans_eq (by dsimp [C]; ring)
  have ht := hasDerivAt_integral_of_dominated_loc_of_lip (μ := gammaRectangleLaw m q)
    (ε := 1) (bound := fun _ => C) (F := F) (F' := D) (x₀ := 0) (by norm_num)
    (Eventually.of_forall (fun t => (hF t).aestronglyMeasurable)) hFi hD.aestronglyMeasurable
    (ae_of_all _ (fun e => (hLip e).lipschitzOnWith)) (integrable_const C) hdiff
  have heF (t : ℝ) (e) :
      (fun k => (gammaAdjustedThreshold (Function.update a j (a j+t)) h e k-faceDot (u k) x)/σ)=
      Function.update (b e) j (b e j+t/σ) := by
    funext k
    by_cases hk : k=j
    · subst k
      simp only [gammaAdjustedThreshold,Function.update_self,b]
      ring
    · simp only [gammaAdjustedThreshold,Function.update_of_ne hk,b]
  have hefun : (fun t => ∫ e, gaussianThresholdTrace u
      (fun k => (gammaAdjustedThreshold (Function.update a j (a j+t)) h e k-faceDot (u k) x)/σ)
      ∂gammaRectangleLaw m q)=(fun t => ∫ e, F t e ∂gammaRectangleLaw m q) := by
    funext t
    apply integral_congr_ae
    exact ae_of_all _ (fun e => by dsimp only; rw [heF])
  rw [hefun]
  convert ht.2 using 1
  exact (integral_const_mul _ _).symm

/-- Actual signed first soft/coarea identity, used before differentiating
an independent second original threshold. -/
theorem supplementalH_signedFace_soft_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j : Fin m) (q : ℕ) :
    (((q:ℝ)+1)/h)*(∫ g, (vectorNormSq g-((n+1:ℕ):ℝ))*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*
        logisticFaceWeight u a h (x+σ • g) j) ∂standardGaussian (n+1)) =
      σ⁻¹*(∫ e, gaussianPDFReal 0 1 ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)*
        Printed.thresholdSignedSection u
          (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j
          ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ) ∂gammaRectangleLaw m q) := by
  let P := fun g : Vector (n+1) => vectorNormSq g-((n+1:ℕ):ℝ)
  let S := fun t : ℝ => ∫ g, P g*logisticNullWeight u
    (Function.update a j (a j+t)) h (x+σ • g)^(q+1) ∂standardGaussian (n+1)
  have hd := supplementalH_hasDerivAt_integral_logistic_power_offset
    (standardGaussian (n+1)) (fun g => x+σ • g) (by fun_prop)
    P ((SignedSurface.standardGaussian_integrable_vectorNormSq (n+1)).sub (integrable_const _)) u a hh j q (a j)
  have hinner : HasDerivAt (fun t : ℝ => a j+t) 1 0 := by simpa using (hasDerivAt_id 0).const_add (a j)
  have hdo : HasDerivAt
      (fun t => ∫ g, P g*logisticNullWeight u (Function.update a j t) h (x+σ • g)^(q+1)
        ∂standardGaussian (n+1))
      ((((q:ℝ)+1)/h)*(∫ g, P g*(logisticNullWeight u (Function.update a j (a j)) h (x+σ • g)^(q+1)*
        logisticFaceWeight u (Function.update a j (a j)) h (x+σ • g) j) ∂standardGaussian (n+1))) (a j+0) := by
    simpa only [add_zero] using hd
  have hs := hdo.comp 0 hinner
  have hg := supplementalH_hasDerivAt_gamma_signedFace_offset u hu a hh hσ x j q
  have heS : S=(fun t => ∫ e, gaussianThresholdTrace u
      (fun k => (gammaAdjustedThreshold (Function.update a j (a j+t)) h e k-faceDot (u k) x)/σ)
      ∂gammaRectangleLaw m q) := by
    funext t
    have hmix := signed_logistic_power_eq_gamma_hard_trace u (Function.update a j (a j+t)) hh hσ x q
    simp_rw [upperFaceSmoother_F] at hmix
    exact hmix
  change HasDerivAt S _ 0 at hs
  rw [heS] at hs
  have he := hs.unique hg
  simpa only [P,Function.update_eq_self,mul_one] using he

end
end RectangleCLTArxivV1
