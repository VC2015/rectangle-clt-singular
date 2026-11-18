import RectangleCLTArxivV1.SupplementalHGammaThresholdLaw

/-! Differentiation of actual Gamma threshold averages from ordinary
threshold-volume derivatives and a global coordinate Lipschitz bound. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology NNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem supplementalH_hasDerivAt_gamma_threshold_average {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector r) (l : Fin m) (q : ℕ)
    (ψ η : Vector m → ℝ) (hψ : Measurable ψ) (hη : Measurable η)
    (A : ℝ) (hA : ∀ b, ‖ψ b‖≤A) (B : ℝ≥0)
    (hLip : ∀ b, LipschitzWith B (fun z => ψ (Function.update b l z)))
    (hdiff : ∀ᵐ b : Vector m ∂volume,
      HasDerivAt (fun z => ψ (Function.update b l z)) (η b) (b l)) :
    HasDerivAt (fun t => ∫ e, ψ
      (fun k => (gammaAdjustedThreshold (Function.update a l (a l+t)) h e k-faceDot (u k) x)/σ)
      ∂gammaRectangleLaw m q)
      (σ⁻¹*(∫ e, η
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ)
        ∂gammaRectangleLaw m q)) 0 := by
  classical
  let b := fun e k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ
  let F := fun t e => ψ (Function.update (b e) l (b e l+t/σ))
  let D := fun e => σ⁻¹*η (b e)
  have hb : Measurable b := by unfold b gammaAdjustedThreshold faceDot; fun_prop
  have hF (t : ℝ) : Measurable (F t) := hψ.comp (by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k=l
    · subst k
      simpa only [Function.update_self] using (((measurable_pi_apply l).comp hb).add_const (t/σ))
    · simpa only [Function.update_of_ne hk] using (measurable_pi_apply k).comp hb)
  have hFi : Integrable (F 0) (gammaRectangleLaw m q) := by
    apply (integrable_const A).mono' (hF 0).aestronglyMeasurable
    exact ae_of_all _ (fun e => hA _)
  have hD : Measurable D := (hη.comp hb).const_mul _
  have hAffine : Measure.QuasiMeasurePreserving (fun c : Vector m =>
      σ⁻¹ • (c+ -(fun k => faceDot (u k) x))) volume volume :=
    (Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hσ.ne')).comp
      (MeasureTheory.quasiMeasurePreserving_add_right volume _)
  have hΓ : Measure.QuasiMeasurePreserving (gammaAdjustedThreshold a h) (gammaRectangleLaw m q) volume :=
    ⟨measurable_gammaAdjustedThreshold a h,supplementalH_gammaThreshold_absolutelyContinuous a hh q⟩
  have hAE := (hAffine.comp hΓ).ae hdiff
  have heB (e) : σ⁻¹ • (gammaAdjustedThreshold a h e+ -(fun k => faceDot (u k) x))=b e := by
    funext k
    dsimp only [b,Pi.smul_apply,Pi.add_apply,Pi.neg_apply,smul_eq_mul]
    ring
  simp only [Function.comp_apply,heB] at hAE
  have hFD : ∀ᵐ e ∂gammaRectangleLaw m q, HasDerivAt (fun t => F t e) (D e) 0 := by
    filter_upwards [hAE] with e he
    have ht : HasDerivAt (fun t : ℝ => b e l+t/σ) (σ⁻¹) 0 := by
      convert (hasDerivAt_const 0 (b e l)).add ((hasDerivAt_id 0).div_const σ) using 1
      simp
    have hd := (by simpa only [zero_div,add_zero] using he :
      HasDerivAt (fun z => ψ (Function.update (b e) l z)) (η (b e)) (b e l+0/σ)).comp 0 ht
    simpa only [F,D,mul_comm] using hd
  let C : ℝ := (B:ℝ)/σ
  have hC : 0≤C := div_nonneg B.coe_nonneg hσ.le
  have hFLip (e) : LipschitzWith (Real.nnabs C) (fun t => F t e) := by
    apply LipschitzWith.of_dist_le_mul
    intro c d
    have ht := (hLip (b e)).dist_le_mul (b e l+c/σ) (b e l+d/σ)
    simp only [Real.dist_eq] at ht
    rw [show b e l+c/σ-(b e l+d/σ)=(c-d)/σ by ring,
      abs_div,abs_of_pos hσ] at ht
    change dist (F c e) (F d e)≤(Real.nnabs C:ℝ)*|c-d|
    rw [Real.coe_nnabs,abs_of_nonneg hC]
    exact ht.trans_eq (by dsimp [C]; ring)
  have ht := hasDerivAt_integral_of_dominated_loc_of_lip (μ := gammaRectangleLaw m q)
    (ε := 1) (bound := fun _ => C) (F := F) (F' := D) (x₀ := 0) (by norm_num)
    (Eventually.of_forall (fun t => (hF t).aestronglyMeasurable)) hFi hD.aestronglyMeasurable
    (ae_of_all _ (fun e => (hFLip e).lipschitzOnWith)) (integrable_const C) hFD
  have heF (t : ℝ) (e) :
      (fun k => (gammaAdjustedThreshold (Function.update a l (a l+t)) h e k-faceDot (u k) x)/σ)=
      Function.update (b e) l (b e l+t/σ) := by
    funext k
    by_cases hk : k=l
    · subst k
      simp only [gammaAdjustedThreshold,Function.update_self,b]
      ring
    · simp only [gammaAdjustedThreshold,Function.update_of_ne hk,b]
  have hefun : (fun t => ∫ e, ψ
      (fun k => (gammaAdjustedThreshold (Function.update a l (a l+t)) h e k-faceDot (u k) x)/σ)
      ∂gammaRectangleLaw m q)=(fun t => ∫ e, F t e ∂gammaRectangleLaw m q) := by
    funext t
    apply integral_congr_ae
    exact ae_of_all _ (fun e => by dsimp only; rw [heF])
  rw [hefun]
  convert ht.2 using 1
  exact (integral_const_mul _ _).symm

end
end RectangleCLTArxivV1
