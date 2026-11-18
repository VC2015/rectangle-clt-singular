import RectangleCLTArxivV1.SupplementalHGammaThresholdLaw
import RectangleCLTArxivV1.SupplementalHWeightedThresholdLipschitz
import RectangleCLTArxivV1.SupplementalHFourthTransportAveraged
import RectangleCLTArxivV1.SupplementalHLogisticCoordinateDerivative

/-! Actual signed Gamma coarea for the cubic absolute-face trace. The
only differentiation domination is a genuine finite-dimensional bound. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem measurable_gaussianThresholdAbsoluteFaceTrace {m r : ℕ}
    (u : Fin m → Vector r) (j : Fin m) : Measurable (fun b => gaussianThresholdAbsoluteFaceTrace u b j) := by
  let E : Set (Vector m × Vector r) := {z | ∀ k, faceDot (u k) z.2≤z.1 k}
  have hE : MeasurableSet E := by
    unfold E
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_le
      ((continuous_faceDot_left (u k)).measurable.comp measurable_snd)
      ((measurable_pi_apply k).comp measurable_fst))
  let P := fun z : Vector m × Vector r => (vectorNormSq z.2-(r:ℝ))*|faceDot (u j) z.2|
  have hP : Measurable P := by unfold P vectorNormSq faceDot; fun_prop
  have hm := ((hP.indicator hE).stronglyMeasurable.integral_prod_right' (ν := standardGaussian r)).measurable
  simpa only [E,P,gaussianThresholdAbsoluteFaceTrace,gaussianFiniteThresholdEvent,
    Finset.mem_univ,forall_true_left] using hm

theorem norm_gaussianThresholdAbsoluteFaceTrace_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) :
    ‖gaussianThresholdAbsoluteFaceTrace u b j‖ ≤
      ∫ g, ‖(vectorNormSq g-(r:ℝ))*|faceDot (u j) g|‖ ∂standardGaussian r := by
  unfold gaussianThresholdAbsoluteFaceTrace
  exact norm_integral_le_of_norm_le (integrable_gaussianAbsoluteFaceScore (u j)).norm
    (ae_of_all _ (fun g => by
      by_cases hg : g∈gaussianFiniteThresholdEvent Finset.univ u b
      · simp [hg]
      · simp only [Set.indicator_of_not_mem hg,norm_zero]
        positivity))

/-- The Gamma mixture of the actual signed absolute-face test. -/
theorem supplementalH_absoluteFace_soft_power_eq_gamma {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector r) (j : Fin m) (q : ℕ) :
    (∫ g, ((vectorNormSq g-(r:ℝ))*|faceDot (u j) g|)*
      logisticNullWeight u a h (x+σ • g)^(q+1) ∂standardGaussian r) =
    ∫ e, gaussianThresholdAbsoluteFaceTrace u
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j ∂gammaRectangleLaw m q := by
  simp_rw [←upperFaceSmoother_F u a h hh]
  rw [gammaMixture_integral_signed_test (standardGaussian r)
    (fun g => Matrix.mulVec u (x+σ • g)) (by fun_prop) _
    (integrable_gaussianAbsoluteFaceScore (u j)) (upperFaceSmoother a h hh) q]
  apply integral_congr_ae
  exact ae_of_all _ (fun e => by
    unfold gaussianThresholdAbsoluteFaceTrace
    have hs : {g | ((upperFaceSmoother a h hh).randomRectangle e).Inside (Matrix.mulVec u (x+σ • g))} =
        gaussianFiniteThresholdEvent Finset.univ u
          (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) := by
      ext g
      rw [Set.mem_setOf_eq,upper_randomRectangle_inside_iff]
      change (∀ k,faceDot (u k) (x+σ • g)≤gammaAdjustedThreshold a h e k) ↔ _
      have he (k : Fin m) : faceDot (u k) (x+σ • g)=faceDot (u k) x+σ*faceDot (u k) g := by
        unfold faceDot
        simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
        rw [Finset.mul_sum,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l _
        ring
      simp only [gaussianFiniteThresholdEvent,Finset.mem_univ,forall_true_left]
      simp_rw [he]
      exact forall_congr' (fun k => by rw [le_div_iff₀ hσ]; constructor <;> intro hk <;> linarith)
    dsimp only
    rw [hs])

/-- Differentiate the actual auxiliary Gamma average at one original
offset. A.e. local coarea and a global primitive Lipschitz bound justify
the exchange without a global normal-independence hypothesis. -/
theorem supplementalH_hasDerivAt_gamma_absoluteFace_offset {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j : Fin m) (q : ℕ) :
    HasDerivAt (fun t => ∫ e, gaussianThresholdAbsoluteFaceTrace u
      (fun k => (gammaAdjustedThreshold (Function.update a j (a j+t)) h e k-faceDot (u k) x)/σ) j
      ∂gammaRectangleLaw m q)
      (σ⁻¹*(∫ e,
        |(gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ| *
          (gaussianPDFReal 0 1 ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)*
            Printed.thresholdSignedSection u
              (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j
              ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)) ∂gammaRectangleLaw m q)) 0 := by
  classical
  let b := fun e k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ
  let F := fun t e => gaussianThresholdAbsoluteFaceTrace u (Function.update (b e) j (b e j+t/σ)) j
  let D := fun e => σ⁻¹*(|b e j| *(gaussianPDFReal 0 1 (b e j)*Printed.thresholdSignedSection u (b e) j (b e j)))
  have hb : Measurable b := by unfold b gammaAdjustedThreshold faceDot; fun_prop
  have hF (t : ℝ) : Measurable (F t) := (measurable_gaussianThresholdAbsoluteFaceTrace u j).comp (by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k=j
    · subst k
      simpa only [Function.update_self] using (((measurable_pi_apply j).comp hb).add_const (t/σ))
    · simpa only [Function.update_of_ne hk] using (measurable_pi_apply k).comp hb)
  have hFi : Integrable (F 0) (gammaRectangleLaw m q) := by
    apply (integrable_const (∫ g, ‖(vectorNormSq g-((n+1:ℕ):ℝ))*|faceDot (u j) g|‖ ∂standardGaussian (n+1))).mono'
      (hF 0).aestronglyMeasurable
    exact ae_of_all _ (fun e => norm_gaussianThresholdAbsoluteFaceTrace_le u _ j)
  have hD : Measurable D := by
    have hpdf : Measurable (gaussianPDFReal 0 1) := measurable_gaussianPDFReal 0 1
    exact ((((measurable_pi_apply j).comp hb).abs).mul
      ((hpdf.comp ((measurable_pi_apply j).comp hb)).mul
        ((measurable_thresholdSignedSection_threshold u j).comp hb))).const_mul _
  have hAffine : Measure.QuasiMeasurePreserving (fun c : Vector m =>
      σ⁻¹ • (c+ -(fun k => faceDot (u k) x))) volume volume :=
    (Measure.quasiMeasurePreserving_smul (μ := volume) (inv_ne_zero hσ.ne')).comp
      (MeasureTheory.quasiMeasurePreserving_add_right volume _)
  have hΓ : Measure.QuasiMeasurePreserving (gammaAdjustedThreshold a h) (gammaRectangleLaw m q) volume :=
    ⟨measurable_gammaAdjustedThreshold a h,supplementalH_gammaThreshold_absolutelyContinuous a hh q⟩
  have hAE := (hAffine.comp hΓ).ae (ae_hasDerivAt_gaussianThresholdAbsoluteFaceTrace_update u hu)
  have heB (e) : σ⁻¹ • (gammaAdjustedThreshold a h e+ -(fun k => faceDot (u k) x))=b e := by
    funext k
    dsimp only [b,Pi.smul_apply,Pi.add_apply,Pi.neg_apply,smul_eq_mul]
    ring
  simp only [Function.comp_apply,heB] at hAE
  have hdiff : ∀ᵐ e ∂gammaRectangleLaw m q, HasDerivAt (fun t => F t e) (D e) 0 := by
    filter_upwards [hAE] with e he
    have ht : HasDerivAt (fun t : ℝ => b e j+t/σ) (σ⁻¹) 0 := by
      convert (hasDerivAt_const 0 (b e j)).add ((hasDerivAt_id 0).div_const σ) using 1 <;> simp
    have hhard : HasDerivAt (fun t => gaussianThresholdAbsoluteFaceTrace u (Function.update (b e) j t) j)
        (|b e j| *(gaussianPDFReal 0 1 (b e j)*Printed.thresholdSignedSection u (b e) j (b e j)))
        (b e j+0/σ) := by simpa only [zero_div,add_zero] using he j
    have hd := hhard.comp 0 ht
    simpa only [zero_div,add_zero,F,D,mul_comm] using hd
  let C := gaussianAbsoluteFaceDensityBudget (n+1)/σ
  have hC : 0≤C := div_nonneg (gaussianAbsoluteFaceDensityBudget_nonneg _) hσ.le
  have hLip (e) : LipschitzWith (Real.nnabs C) (fun t => F t e) := by
    apply LipschitzWith.of_dist_le_mul
    intro c d
    have ht := gaussianThresholdAbsoluteFaceTrace_update_increment_bound u (b e) j (hu j)
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
  have hefun : (fun t => ∫ e, gaussianThresholdAbsoluteFaceTrace u
      (fun k => (gammaAdjustedThreshold (Function.update a j (a j+t)) h e k-faceDot (u k) x)/σ) j
      ∂gammaRectangleLaw m q)=(fun t => ∫ e, F t e ∂gammaRectangleLaw m q) := by
    funext t
    apply integral_congr_ae
    exact ae_of_all _ (fun e => by dsimp only; rw [heF])
  rw [hefun]
  convert ht.2 using 1
  exact (integral_const_mul _ _).symm

/-- Exact first-coarea identity for the original soft power and actual
independent Gamma clocks, with the signed absolute-face test intact. -/
theorem supplementalH_absoluteFace_soft_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j : Fin m) (q : ℕ) :
    (((q:ℝ)+1)/h)*(∫ g, ((vectorNormSq g-((n+1:ℕ):ℝ))*|faceDot (u j) g|)*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*
        logisticFaceWeight u a h (x+σ • g) j) ∂standardGaussian (n+1)) =
      σ⁻¹*(∫ e, |(gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ| *
        (gaussianPDFReal 0 1 ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)*
          Printed.thresholdSignedSection u
            (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j
            ((gammaAdjustedThreshold a h e j-faceDot (u j) x)/σ)) ∂gammaRectangleLaw m q) := by
  let P := fun g : Vector (n+1) => (vectorNormSq g-((n+1:ℕ):ℝ))*|faceDot (u j) g|
  let S := fun t : ℝ => ∫ g, P g*logisticNullWeight u
    (Function.update a j (a j+t)) h (x+σ • g)^(q+1) ∂standardGaussian (n+1)
  have hd := supplementalH_hasDerivAt_integral_logistic_power_offset
    (standardGaussian (n+1)) (fun g => x+σ • g) (by fun_prop)
    P (integrable_gaussianAbsoluteFaceScore (u j)) u a hh j q (a j)
  have hinner : HasDerivAt (fun t : ℝ => a j+t) 1 0 := by simpa using (hasDerivAt_id 0).const_add (a j)
  have hdo : HasDerivAt
      (fun t => ∫ g, P g*logisticNullWeight u (Function.update a j t) h (x+σ • g)^(q+1)
        ∂standardGaussian (n+1))
      ((((q:ℝ)+1)/h)*(∫ g, P g*(logisticNullWeight u (Function.update a j (a j)) h (x+σ • g)^(q+1)*
        logisticFaceWeight u (Function.update a j (a j)) h (x+σ • g) j) ∂standardGaussian (n+1))) (a j+0) := by
    simpa only [add_zero] using hd
  have hs := hdo.comp 0 hinner
  have hg := supplementalH_hasDerivAt_gamma_absoluteFace_offset u hu a hh hσ x j q
  have heS : S=(fun t => ∫ e, gaussianThresholdAbsoluteFaceTrace u
      (fun k => (gammaAdjustedThreshold (Function.update a j (a j+t)) h e k-faceDot (u k) x)/σ) j
      ∂gammaRectangleLaw m q) := by
    funext t
    exact supplementalH_absoluteFace_soft_power_eq_gamma u (Function.update a j (a j+t)) hh hσ x j q
  change HasDerivAt S _ 0 at hs
  rw [heS] at hs
  have he := hs.unique hg
  simpa only [P,Function.update_eq_self,mul_one] using he

end
end RectangleCLTArxivV1
