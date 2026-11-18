import RectangleCLTArxivV1.SupplementalHGammaMixedCoarea
import RectangleCLTArxivV1.SupplementalHCubicGammaTrace
import RectangleCLTArxivV1.SupplementalIRestriction

/-! Angle cancellation and the genuine ordered-pair signed trace.
The factor two is retained explicitly when passing to native J_e. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem supplementalH_angle_zero_of_parallel {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : ¬hardGaussianRidgeNonparallel u j l) :
    correlationAngleWeight (faceDot (u j) (u l))=0 := by
  have hc := thresholdPair_coefficients_sq u j l hu hv
  have hs : faceDot (u j) (u l)^2=1 := by
    by_cases he : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)=0
    · have hf : thresholdPairFirstCoefficient u j l=0 := by
        simp only [thresholdPairFirstCoefficient,he,norm_zero,zero_div]
      rw [hf] at hc
      nlinarith [hc.1,hc.2]
    · have he' : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)=0 := by
        by_contra hn
        exact hp ⟨he,hn⟩
      have hf : thresholdPairSecondCoefficient u j l=0 := by
        simp only [thresholdPairSecondCoefficient,he',norm_zero,zero_div]
      rw [hf] at hc
      nlinarith [hc.1,hc.2]
  simp only [correlationAngleWeight,hs,sub_self,Real.sqrt_zero,mul_zero]

theorem supplementalH_angle_mul_signedMixedKernel {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : hardGaussianRidgeNonparallel u j l) :
    correlationAngleWeight (faceDot (u j) (u l))*supplementalHSignedMixedKernel u b j l=
      hardGaussianSignedRidgeTerm u b j l := by
  classical
  have hs : Real.sqrt (1-faceDot (u j) (u l)^2)≠0 := by
    rw [←gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv]
    exact (gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp.1 hp.2).2.2.ne'
  unfold supplementalHSignedMixedKernel correlationAngleWeight hardGaussianSignedRidgeTerm
  rw [if_pos hp]
  unfold hardGaussianRidgeNormalWeight
  field_simp [hs]
  ring

theorem norm_hardGaussianSignedRidgeTerm_le {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1) :
    ‖hardGaussianSignedRidgeTerm u b j l‖≤
      |Real.arccos (faceDot (u j) (u l))| *gaussianMixedSectionDensityBudget (n+1) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hsec := abs_hardGaussianPairSignedSection_le ((Finset.univ.erase j).erase l) u b
      (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairBisector_unit u j l hp.1) (thresholdPairDifference_unit u j l hp.2)
      (thresholdPair_frame_orthogonal u j l hu hv)
      (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)
    have h := (mul_le_mul_of_nonneg_left hsec
      (mul_nonneg (gaussianPDFReal_nonneg 0 1 _) (gaussianPDFReal_nonneg 0 1 _))).trans
        (gaussianPDFReal_pair_sq_add_dimension_le (n+1) _ _)
    have h' := mul_le_mul_of_nonneg_left h (abs_nonneg (Real.arccos (faceDot (u j) (u l))))
    simpa only [hardGaussianSignedRidgeTerm,hp,if_true,hardGaussianRidgeNormalWeight,
      Real.norm_eq_abs,abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _),mul_assoc] using h'
  · simp only [hardGaussianSignedRidgeTerm,hp,if_false,norm_zero]
    exact mul_nonneg (abs_nonneg _) (gaussianMixedSectionDensityBudget_nonneg _)

theorem integrable_gamma_signedRidgeTerm {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) (h σ : ℝ) (x : Vector (n+1)) (j l : Fin m) (q : ℕ) :
    Integrable (fun e => hardGaussianSignedRidgeTerm u
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l)
      (gammaRectangleLaw m q) := by
  have hb : Measurable (fun e k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) := by
    unfold gammaAdjustedThreshold faceDot
    fun_prop
  apply (integrable_const (|Real.arccos (faceDot (u j) (u l))| *
    gaussianMixedSectionDensityBudget (n+1))).mono'
    ((measurable_hardGaussianSignedRidgeTerm u j l).comp hb).aestronglyMeasurable
  exact ae_of_all _ (fun e => norm_hardGaussianSignedRidgeTerm_le u _ j l (hu j) (hu l))

theorem supplementalH_signedMixed_angle_soft_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j l : Fin m) (q : ℕ) :
    ((((q:ℝ)+1)/h)*(((q:ℝ)+2)/h))*(correlationAngleWeight (faceDot (u j) (u l))*
      (∫ g, (vectorNormSq g-((n+1:ℕ):ℝ))*
        (logisticNullWeight u a h (x+σ • g)^(q+1)*
          logisticFaceWeight u a h (x+σ • g) j*logisticFaceWeight u a h (x+σ • g) l)
        ∂standardGaussian (n+1))) =
      σ⁻¹*(σ⁻¹*(∫ e, hardGaussianSignedRidgeTerm u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l
        ∂gammaRectangleLaw m q)) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hjl : j≠l := by
      intro he
      subst l
      exact hp.2 (sub_self _)
    have he := congrArg (fun v : ℝ => correlationAngleWeight (faceDot (u j) (u l))*v)
      (supplementalH_signedMixed_soft_coarea u hu a hh hσ x j l hjl hp.1 hp.2 q)
    dsimp only at he
    have hi : correlationAngleWeight (faceDot (u j) (u l))*(∫ e, supplementalHSignedMixedKernel u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l ∂gammaRectangleLaw m q)=
        ∫ e, hardGaussianSignedRidgeTerm u
          (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l ∂gammaRectangleLaw m q := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun e => supplementalH_angle_mul_signedMixedKernel u _ j l (hu j) (hu l) hp)
    calc
      _ = correlationAngleWeight (faceDot (u j) (u l))*
        (((((q:ℝ)+1)/h)*(((q:ℝ)+2)/h))*(∫ g, (vectorNormSq g-((n+1:ℕ):ℝ))*
          (logisticNullWeight u a h (x+σ • g)^(q+1)*logisticFaceWeight u a h (x+σ • g) j*
            logisticFaceWeight u a h (x+σ • g) l) ∂standardGaussian (n+1))) := by ring
      _ = _ := by
        rw [he]
        calc
          _ = σ⁻¹*(σ⁻¹*(correlationAngleWeight (faceDot (u j) (u l))*
            (∫ e, supplementalHSignedMixedKernel u
              (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l
              ∂gammaRectangleLaw m q))) := by ring
          _ = _ := by rw [hi]
  · rw [supplementalH_angle_zero_of_parallel u j l (hu j) (hu l) hp,zero_mul,mul_zero]
    simp only [hardGaussianSignedRidgeTerm,hp,if_false,integral_zero,mul_zero]

theorem integrable_gaussian_logistic_power_pair {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0<h)
    (σ : ℝ) (x : Vector r) (j l : Fin m) (q : ℕ) :
    Integrable (fun g => (vectorNormSq g-(r:ℝ))*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*
        logisticFaceWeight u a h (x+σ • g) j*logisticFaceWeight u a h (x+σ • g) l))
      (standardGaussian r) := by
  have hm : Measurable (fun g => (vectorNormSq g-(r:ℝ))*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*
        logisticFaceWeight u a h (x+σ • g) j*logisticFaceWeight u a h (x+σ • g) l)) := by
    unfold vectorNormSq logisticFaceWeight logisticNullWeight faceDot
    fun_prop
  apply ((SignedSurface.standardGaussian_integrable_vectorNormSq r).sub (integrable_const (r:ℝ))).norm.mono'
    hm.aestronglyMeasurable
  exact ae_of_all _ (fun g => by
    have hb := supplementalH_logistic_power_face_bounds u a hh (x+σ • g) j q
    have hl : 0≤logisticFaceWeight u a h (x+σ • g) l ∧ logisticFaceWeight u a h (x+σ • g) l≤1 := by
      rw [←upperFaceSmoother_pi u a h hh]
      exact ⟨(FaceSmoother.weights _ _).pi_nonneg _,
        ((FaceSmoother.weights _ _).pi_le_theta _).trans (FaceSmoother.weights _ _).theta_lt_one.le⟩
    change |(vectorNormSq g-(r:ℝ))*_|≤|vectorNormSq g-(r:ℝ)|
    rw [abs_mul,abs_of_nonneg (mul_nonneg hb.1 hl.1)]
    exact mul_le_of_le_one_right (abs_nonneg _) (mul_le_one₀ hb.2 hl.1 hl.2))

/-- The actual signed sum is formed before its absolute value. Half of
the ordered normal-pair sum defines native J_e, hence the exact factor2. -/
theorem supplementalH_signedRidge_soft_sum_coarea_scaled {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (q : ℕ) :
    ((((q:ℝ)+1)/h)*(((q:ℝ)+2)/h))*(∫ g, ∑ jl : Fin m × Fin m,
      correlationAngleWeight (faceDot (u jl.1) (u jl.2))*((vectorNormSq g-((n+1:ℕ):ℝ))*
        (logisticNullWeight u a h (x+σ • g)^(q+1)*
          logisticFaceWeight u a h (x+σ • g) jl.1*logisticFaceWeight u a h (x+σ • g) jl.2))
      ∂standardGaussian (n+1)) =
    (2/σ^2)*(∫ e, hardGaussianWeightedRidgeIntegral u
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) ∂gammaRectangleLaw m q) := by
  classical
  rw [integral_finset_sum _ (fun jl _ =>
    (integrable_gaussian_logistic_power_pair u a hh σ x jl.1 jl.2 q).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  simp_rw [supplementalH_signedMixed_angle_soft_coarea u hu a hh hσ x]
  have hi (jl : Fin m × Fin m) : Integrable (fun e => hardGaussianSignedRidgeTerm u
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) jl.1 jl.2)
      (gammaRectangleLaw m q) := integrable_gamma_signedRidgeTerm u hu a h σ x jl.1 jl.2 q
  simp only [hardGaussianWeightedRidgeIntegral]
  rw [integral_const_mul,integral_finset_sum _ (fun jl _ => hi jl)]
  simp_rw [←mul_assoc]
  rw [←Finset.mul_sum]
  field_simp
  ring

theorem supplementalH_signedRidge_soft_sum_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (q : ℕ) :
    (∫ g, ∑ jl : Fin m × Fin m,
      correlationAngleWeight (faceDot (u jl.1) (u jl.2))*((vectorNormSq g-((n+1:ℕ):ℝ))*
        (logisticNullWeight u a h (x+σ • g)^(q+1)*
          logisticFaceWeight u a h (x+σ • g) jl.1*logisticFaceWeight u a h (x+σ • g) jl.2))
      ∂standardGaussian (n+1)) =
    (2*h^2/(((q:ℝ)+1)*((q:ℝ)+2)*σ^2))*(∫ e, hardGaussianWeightedRidgeIntegral u
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) ∂gammaRectangleLaw m q) := by
  have he := supplementalH_signedRidge_soft_sum_coarea_scaled u hu a hh hσ x q
  have hq1 : (q:ℝ)+1≠0 := by positivity
  have hq2 : (q:ℝ)+2≠0 := by positivity
  apply (mul_left_cancel₀ (mul_ne_zero (div_ne_zero hq1 hh.ne') (div_ne_zero hq2 hh.ne')))
  rw [he]
  field_simp
  ring

end
end RectangleCLTArxivV1
