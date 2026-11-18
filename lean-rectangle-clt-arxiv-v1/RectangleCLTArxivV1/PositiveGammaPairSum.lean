import RectangleCLTArxivV1.PositiveGammaMixedCoarea
import RectangleCLTArxivV1.SupplementalHGammaRidgeTrace
import RectangleCLTArxivV1.SupplementalHPositiveEdgeAveraged

/-! The actual baseline soft ordered-pair mass and projected moment.
True angle/Gram weights cancel the exact mixed coarea Jacobian before
the finite Gamma sum is formed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def positiveGammaSoftOrderedPairMass {m r : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h σ : ℝ) (x : Vector r) : ℝ :=
  ∫ g,∑ jl : Fin m × Fin m,correlationAngleWeight (faceDot (u jl.1) (u jl.2))*
    (logisticNullWeight u a h (x+σ • g)*logisticFaceWeight u a h (x+σ • g) jl.1*
      logisticFaceWeight u a h (x+σ • g) jl.2) ∂standardGaussian r

def positiveGammaSoftOrderedPairProjection {m r : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h σ : ℝ) (x : Vector r) : ℝ :=
  ∫ g,∑ jl : Fin m × Fin m,correlationAngleWeight (faceDot (u jl.1) (u jl.2))*
    (vectorNormSq ((supplementalHPairPlane (u jl.1) (u jl.2)).mulVec g)*
      (logisticNullWeight u a h (x+σ • g)*logisticFaceWeight u a h (x+σ • g) jl.1*
        logisticFaceWeight u a h (x+σ • g) jl.2)) ∂standardGaussian r

theorem positiveGammaMixedMassKernel_eq_ridgeDensity {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    positiveGammaMixedMassKernel u b j l=hardGaussianRidgeDensity u b j l := by
  unfold positiveGammaMixedMassKernel hardGaussianRidgeDensity
  rw [positiveEdge_pairSectionProbability_eq]

theorem positiveGamma_angle_mul_massKernel {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1) :
    correlationAngleWeight (faceDot (u j) (u l))*positiveGammaMixedMassKernel u b j l=
      positiveEdgeTubeCoefficient u b 0 (j,l) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hjl : j≠l := by intro h; subst l; exact hp.2 (sub_self _)
    change projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 ∧
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0 at hp
    unfold positiveEdgeTubeCoefficient
    rw [if_neg hjl,if_pos hp]
    simp only [Prod.fst,Prod.snd,pow_zero,mul_one]
    rw [positiveGammaMixedMassKernel_eq_ridgeDensity]
    unfold correlationAngleWeight
    rw [faceDot_eq_euclidean_inner]
    rfl
  · rw [supplementalH_angle_zero_of_parallel u j l hu hv hp,zero_mul]
    simp only [positiveEdgeTubeCoefficient,Prod.fst,Prod.snd]
    split_ifs <;> simp_all [hardGaussianRidgeNonparallel]

theorem positiveGamma_angle_mul_planeKernel {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1) :
    correlationAngleWeight (faceDot (u j) (u l))*positiveGammaMixedPlaneKernel u b j l=
      positiveEdgeTubeCoefficient u b 2 (j,l) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hjl : j≠l := by intro h; subst l; exact hp.2 (sub_self _)
    change projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 ∧
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0 at hp
    unfold positiveGammaMixedPlaneKernel positiveEdgeTubeCoefficient
    rw [if_neg hjl,if_pos hp]
    simp only [Prod.fst,Prod.snd]
    rw [fourthRidgeNormalPoint_norm_sq_eq u b j l hu hv hp.1 hp.2,
      ← gaussianPair_conditional_normalLength_eq_native u b j l hu hv hp.1 hp.2,
      positiveGammaMixedMassKernel_eq_ridgeDensity]
    unfold correlationAngleWeight
    rw [faceDot_eq_euclidean_inner]
    simp only [projectionEuclideanVector]
    ring
  · rw [supplementalH_angle_zero_of_parallel u j l hu hv hp,zero_mul]
    simp only [positiveEdgeTubeCoefficient,Prod.fst,Prod.snd]
    split_ifs <;> simp_all [hardGaussianRidgeNonparallel]

theorem positiveGammaMixedMassKernel_norm_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    ‖positiveGammaMixedMassKernel u b j l‖≤positiveMixedMassBudget/gaussianThresholdResidualScale u j l := by
  have hν := (gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm).2.2
  have hP := hardGaussianPairSectionProbability_bounds ((Finset.univ.erase j).erase l) u b
    (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)
  unfold positiveGammaMixedMassKernel
  rw [← gaussianPair_conditional_density_jacobian_eq u b j l hu hv hp hm,
    Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
      (div_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)) hν.le) hP.1)]
  have hn : 0≤gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
      gaussianThresholdResidualScale u j l :=
    div_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)) hν.le
  have hd := div_le_div_of_nonneg_right
    (gaussianPDFReal_pair_le_positiveMixedMassBudget (b j) (gaussianPairConditionalLevel u b j l)) hν.le
  exact (mul_le_mul_of_nonneg_left hP.2 hn).trans ((mul_one _).le.trans hd)

theorem positiveGammaMixedPlaneKernel_norm_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    ‖positiveGammaMixedPlaneKernel u b j l‖≤positiveMixedPlaneBudget/gaussianThresholdResidualScale u j l := by
  have hν := (gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm).2.2
  have hP := hardGaussianPairSectionProbability_bounds ((Finset.univ.erase j).erase l) u b
    (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)
  unfold positiveGammaMixedPlaneKernel positiveGammaMixedMassKernel
  rw [← gaussianPair_conditional_density_jacobian_eq u b j l hu hv hp hm]
  have hn : 0≤(b j)^2+(gaussianPairConditionalLevel u b j l)^2 := by positivity
  have hpdf : 0≤gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
      gaussianThresholdResidualScale u j l :=
    div_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)) hν.le
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg
    (div_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)) hν.le) hP.1) hn)]
  calc
    _ ≤ (gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)/
        gaussianThresholdResidualScale u j l)*((b j)^2+(gaussianPairConditionalLevel u b j l)^2) :=
      mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hP.2 hpdf).trans_eq (mul_one _)) hn
    _ = (gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 (gaussianPairConditionalLevel u b j l)*
        ((b j)^2+(gaussianPairConditionalLevel u b j l)^2))/gaussianThresholdResidualScale u j l := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (gaussianPDFReal_pair_normSq_le_positiveMixedPlaneBudget (b j) (gaussianPairConditionalLevel u b j l)) hν.le

private theorem positiveGamma_standardized_measurable {m r : ℕ} (u : Fin m → Vector r)
    (a : Vector m) (h σ : ℝ) (x : Vector r) :
    Measurable (fun e k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) := by
  unfold gammaAdjustedThreshold faceDot
  fun_prop

theorem integrable_gamma_positiveEdge_mass {m r : ℕ}
    (u : Fin m → Vector r) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) (h σ : ℝ) (x : Vector r) (j l : Fin m) (q : ℕ) :
    Integrable (fun e => positiveEdgeTubeCoefficient u
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 0 (j,l))
      (gammaRectangleLaw m q) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hi : Integrable (fun e => positiveGammaMixedMassKernel u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l) (gammaRectangleLaw m q) := by
      apply (integrable_const (positiveMixedMassBudget/gaussianThresholdResidualScale u j l)).mono'
        ((measurable_positiveGammaMixedMassKernel u j l).comp
          (positiveGamma_standardized_measurable u a h σ x)).aestronglyMeasurable
      exact ae_of_all _ (fun e => positiveGammaMixedMassKernel_norm_le u _ j l (hu j) (hu l) hp.1 hp.2)
    simpa only [positiveGamma_angle_mul_massKernel u _ j l (hu j) (hu l)] using
      hi.const_mul (correlationAngleWeight (faceDot (u j) (u l)))
  · have he (b : Vector m) : positiveEdgeTubeCoefficient u b 0 (j,l)=0 := by
      simp only [positiveEdgeTubeCoefficient,Prod.fst,Prod.snd]
      split_ifs <;> simp_all [hardGaussianRidgeNonparallel]
    simpa only [he] using (integrable_zero _ _ (μ := gammaRectangleLaw m q))

theorem integrable_gamma_positiveEdge_projection {m r : ℕ}
    (u : Fin m → Vector r) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) (h σ : ℝ) (x : Vector r) (j l : Fin m) (q : ℕ) :
    Integrable (fun e => positiveEdgeTubeCoefficient u
      (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 2 (j,l))
      (gammaRectangleLaw m q) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hi : Integrable (fun e => positiveGammaMixedPlaneKernel u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l) (gammaRectangleLaw m q) := by
      apply (integrable_const (positiveMixedPlaneBudget/gaussianThresholdResidualScale u j l)).mono'
        ((measurable_positiveGammaMixedPlaneKernel u j l).comp
          (positiveGamma_standardized_measurable u a h σ x)).aestronglyMeasurable
      exact ae_of_all _ (fun e => positiveGammaMixedPlaneKernel_norm_le u _ j l (hu j) (hu l) hp.1 hp.2)
    simpa only [positiveGamma_angle_mul_planeKernel u _ j l (hu j) (hu l)] using
      hi.const_mul (correlationAngleWeight (faceDot (u j) (u l)))
  · have he (b : Vector m) : positiveEdgeTubeCoefficient u b 2 (j,l)=0 := by
      simp only [positiveEdgeTubeCoefficient,Prod.fst,Prod.snd]
      split_ifs <;> simp_all [hardGaussianRidgeNonparallel]
    simpa only [he] using (integrable_zero _ _ (μ := gammaRectangleLaw m q))

private theorem positiveGamma_logistic_pair_bounds {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0<h)
    (y : Vector r) (j l : Fin m) :
    0≤logisticNullWeight u a h y*logisticFaceWeight u a h y j*logisticFaceWeight u a h y l ∧
      logisticNullWeight u a h y*logisticFaceWeight u a h y j*logisticFaceWeight u a h y l≤1 := by
  have hj := supplementalH_logistic_power_face_bounds u a hh y j 0
  simp only [Nat.zero_add,pow_one] at hj
  have hl : 0≤logisticFaceWeight u a h y l ∧ logisticFaceWeight u a h y l≤1 := by
    rw [←upperFaceSmoother_pi u a h hh]
    exact ⟨(FaceSmoother.weights _ _).pi_nonneg _,
      ((FaceSmoother.weights _ _).pi_le_theta _).trans (FaceSmoother.weights _ _).theta_lt_one.le⟩
  exact ⟨mul_nonneg hj.1 hl.1,mul_le_one₀ hj.2 hl.1 hl.2⟩

theorem integrable_gaussian_positive_soft_pair_mass {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0<h)
    (σ : ℝ) (x : Vector r) (j l : Fin m) :
    Integrable (fun g => logisticNullWeight u a h (x+σ • g)*
      logisticFaceWeight u a h (x+σ • g) j*logisticFaceWeight u a h (x+σ • g) l)
      (standardGaussian r) := by
  have hm : Measurable (fun g => logisticNullWeight u a h (x+σ • g)*
      logisticFaceWeight u a h (x+σ • g) j*logisticFaceWeight u a h (x+σ • g) l) := by
    unfold logisticFaceWeight logisticNullWeight faceDot
    fun_prop
  apply (integrable_const (μ := standardGaussian r) (1:ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun g => by
    rw [Real.norm_eq_abs,abs_of_nonneg (positiveGamma_logistic_pair_bounds u a hh _ j l).1]
    exact (positiveGamma_logistic_pair_bounds u a hh _ j l).2)

theorem integrable_gaussian_positive_soft_pair_projection {m r : ℕ}
    (u : Fin m → Vector r) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h : ℝ} (hh : 0<h) (σ : ℝ) (x : Vector r) (j l : Fin m) :
    Integrable (fun g => correlationAngleWeight (faceDot (u j) (u l))*
      (vectorNormSq ((supplementalHPairPlane (u j) (u l)).mulVec g)*
        (logisticNullWeight u a h (x+σ • g)*logisticFaceWeight u a h (x+σ • g) j*
          logisticFaceWeight u a h (x+σ • g) l))) (standardGaussian r) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · let P := positiveGaussianPlaneTest (u j) (gaussianPairConditionalDirection u j l)
    have hm : Measurable (fun g => P g*(logisticNullWeight u a h (x+σ • g)*
        logisticFaceWeight u a h (x+σ • g) j*logisticFaceWeight u a h (x+σ • g) l)) := by
      unfold P positiveGaussianPlaneTest logisticFaceWeight logisticNullWeight faceDot
      fun_prop
    have hi : Integrable (fun g => P g*(logisticNullWeight u a h (x+σ • g)*
        logisticFaceWeight u a h (x+σ • g) j*logisticFaceWeight u a h (x+σ • g) l))
        (standardGaussian r) := by
      apply (integrable_positiveGaussianPlaneTest _ _).norm.mono' hm.aestronglyMeasurable
      exact ae_of_all _ (fun g => by
        change |P g*_|≤|P g|
        rw [abs_mul,abs_of_nonneg (positiveGamma_logistic_pair_bounds u a hh _ j l).1]
        exact mul_le_of_le_one_right (abs_nonneg _) (positiveGamma_logistic_pair_bounds u a hh _ j l).2)
    simpa only [P,positiveGaussianPlaneTest_eq_actual_projection u j l (hu j) (hu l) hp.1 hp.2] using
      hi.const_mul (correlationAngleWeight (faceDot (u j) (u l)))
  · simpa only [supplementalH_angle_zero_of_parallel u j l (hu j) (hu l) hp,zero_mul] using
      (integrable_zero _ _ (μ := standardGaussian r))

theorem positiveGamma_mass_angle_soft_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j l : Fin m) :
    ((1/h)*(2/h))*(correlationAngleWeight (faceDot (u j) (u l))*
      (∫ g,logisticNullWeight u a h (x+σ • g)*logisticFaceWeight u a h (x+σ • g) j*
        logisticFaceWeight u a h (x+σ • g) l ∂standardGaussian (n+1)))=
      σ⁻¹*(σ⁻¹*(∫ e,positiveEdgeTubeCoefficient u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 0 (j,l)
          ∂gammaRectangleLaw m 0)) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hjl : j≠l := by intro he; subst l; exact hp.2 (sub_self _)
    have he := congrArg (fun v : ℝ => correlationAngleWeight (faceDot (u j) (u l))*v)
      (positiveMass_soft_mixed_coarea u hu a hh hσ x j l hjl hp.1 hp.2 0)
    simp only [Nat.cast_zero,zero_add,pow_one] at he
    have hi : correlationAngleWeight (faceDot (u j) (u l))*(∫ e,positiveGammaMixedMassKernel u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l ∂gammaRectangleLaw m 0)=
        ∫ e,positiveEdgeTubeCoefficient u
          (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 0 (j,l) ∂gammaRectangleLaw m 0 := by
      rw [←integral_const_mul]
      exact integral_congr_ae (ae_of_all _ (fun e => positiveGamma_angle_mul_massKernel u _ j l (hu j) (hu l)))
    calc
      _ = correlationAngleWeight (faceDot (u j) (u l))*
          (((1/h)*(2/h))*(∫ g,logisticNullWeight u a h (x+σ • g)*
            logisticFaceWeight u a h (x+σ • g) j*logisticFaceWeight u a h (x+σ • g) l
              ∂standardGaussian (n+1))) := by ring
      _ = _ := by
        rw [he]
        calc
          _ = σ⁻¹*(σ⁻¹*(correlationAngleWeight (faceDot (u j) (u l))*(∫ e,positiveGammaMixedMassKernel u
              (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l ∂gammaRectangleLaw m 0))) := by ring
          _ = _ := by rw [hi]
  · rw [supplementalH_angle_zero_of_parallel u j l (hu j) (hu l) hp,zero_mul,mul_zero]
    have hz (b : Vector m) : positiveEdgeTubeCoefficient u b 0 (j,l)=0 := by
      rw [←positiveGamma_angle_mul_massKernel u b j l (hu j) (hu l),
        supplementalH_angle_zero_of_parallel u j l (hu j) (hu l) hp,zero_mul]
    simp only [hz,integral_zero,mul_zero]

theorem positiveGamma_projection_angle_soft_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j l : Fin m) :
    ((1/h)*(2/h))*(correlationAngleWeight (faceDot (u j) (u l))*
      (∫ g,vectorNormSq ((supplementalHPairPlane (u j) (u l)).mulVec g)*
        (logisticNullWeight u a h (x+σ • g)*logisticFaceWeight u a h (x+σ • g) j*
          logisticFaceWeight u a h (x+σ • g) l) ∂standardGaussian (n+1)))=
      σ⁻¹*(σ⁻¹*(∫ e,positiveEdgeTubeCoefficient u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 2 (j,l)
          ∂gammaRectangleLaw m 0)) := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hjl : j≠l := by intro he; subst l; exact hp.2 (sub_self _)
    have he := congrArg (fun v : ℝ => correlationAngleWeight (faceDot (u j) (u l))*v)
      (positivePlane_soft_mixed_coarea u hu a hh hσ x j l hjl hp.1 hp.2 0)
    simp only [Nat.cast_zero,zero_add,pow_one] at he
    simp_rw [positiveGaussianPlaneTest_eq_actual_projection u j l (hu j) (hu l) hp.1 hp.2] at he
    have hi : correlationAngleWeight (faceDot (u j) (u l))*(∫ e,positiveGammaMixedPlaneKernel u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l ∂gammaRectangleLaw m 0)=
        ∫ e,positiveEdgeTubeCoefficient u
          (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 2 (j,l) ∂gammaRectangleLaw m 0 := by
      rw [←integral_const_mul]
      exact integral_congr_ae (ae_of_all _ (fun e => positiveGamma_angle_mul_planeKernel u _ j l (hu j) (hu l)))
    calc
      _ = correlationAngleWeight (faceDot (u j) (u l))*
          (((1/h)*(2/h))*(∫ g,vectorNormSq ((supplementalHPairPlane (u j) (u l)).mulVec g)*
            (logisticNullWeight u a h (x+σ • g)*logisticFaceWeight u a h (x+σ • g) j*
              logisticFaceWeight u a h (x+σ • g) l) ∂standardGaussian (n+1))) := by ring
      _ = _ := by
        rw [he]
        calc
          _ = σ⁻¹*(σ⁻¹*(correlationAngleWeight (faceDot (u j) (u l))*(∫ e,positiveGammaMixedPlaneKernel u
              (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l ∂gammaRectangleLaw m 0))) := by ring
          _ = _ := by rw [hi]
  · rw [supplementalH_angle_zero_of_parallel u j l (hu j) (hu l) hp,zero_mul,mul_zero]
    have hz (b : Vector m) : positiveEdgeTubeCoefficient u b 2 (j,l)=0 := by
      rw [←positiveGamma_angle_mul_planeKernel u b j l (hu j) (hu l),
        supplementalH_angle_zero_of_parallel u j l (hu j) (hu l) hp,zero_mul]
    simp only [hz,integral_zero,mul_zero]

theorem positiveGammaSoftOrderedPairMass_coarea_scaled {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ) (x : Vector (n+1)) :
    ((1/h)*(2/h))*positiveGammaSoftOrderedPairMass u a h σ x=
      σ⁻¹*(σ⁻¹*(∫ e,∑ jl : Fin m × Fin m,positiveEdgeTubeCoefficient u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 0 jl ∂gammaRectangleLaw m 0)) := by
  classical
  unfold positiveGammaSoftOrderedPairMass
  rw [integral_finset_sum _ (fun jl _ =>
    (integrable_gaussian_positive_soft_pair_mass u a hh σ x jl.1 jl.2).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  simp_rw [positiveGamma_mass_angle_soft_coarea u hu a hh hσ x]
  rw [integral_finset_sum _ (fun jl _ => integrable_gamma_positiveEdge_mass u hu a h σ x jl.1 jl.2 0)]
  simp_rw [←mul_assoc]
  rw [←Finset.mul_sum]

theorem positiveGammaSoftOrderedPairProjection_coarea_scaled {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ) (x : Vector (n+1)) :
    ((1/h)*(2/h))*positiveGammaSoftOrderedPairProjection u a h σ x=
      σ⁻¹*(σ⁻¹*(∫ e,∑ jl : Fin m × Fin m,positiveEdgeTubeCoefficient u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 2 jl ∂gammaRectangleLaw m 0)) := by
  classical
  unfold positiveGammaSoftOrderedPairProjection
  rw [integral_finset_sum _ (fun jl _ => integrable_gaussian_positive_soft_pair_projection u hu a hh σ x jl.1 jl.2)]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  simp_rw [positiveGamma_projection_angle_soft_coarea u hu a hh hσ x]
  rw [integral_finset_sum _ (fun jl _ => integrable_gamma_positiveEdge_projection u hu a h σ x jl.1 jl.2 0)]
  simp_rw [←mul_assoc]
  rw [←Finset.mul_sum]

theorem positiveGammaSoftOrderedPairMass_eq_gamma {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ) (x : Vector (n+1)) :
    positiveGammaSoftOrderedPairMass u a h σ x=
      (h^2/(2*σ^2))*(∫ e,∑ jl : Fin m × Fin m,positiveEdgeTubeCoefficient u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 0 jl ∂gammaRectangleLaw m 0) := by
  have he := positiveGammaSoftOrderedPairMass_coarea_scaled u hu a hh hσ x
  apply mul_left_cancel₀ (mul_ne_zero (div_ne_zero (by norm_num : (1:ℝ)≠0) hh.ne')
    (div_ne_zero (by norm_num : (2:ℝ)≠0) hh.ne'))
  rw [he]
  field_simp
  ring

theorem positiveGammaSoftOrderedPairProjection_eq_gamma {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ) (x : Vector (n+1)) :
    positiveGammaSoftOrderedPairProjection u a h σ x=
      (h^2/(2*σ^2))*(∫ e,∑ jl : Fin m × Fin m,positiveEdgeTubeCoefficient u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) 2 jl ∂gammaRectangleLaw m 0) := by
  have he := positiveGammaSoftOrderedPairProjection_coarea_scaled u hu a hh hσ x
  apply mul_left_cancel₀ (mul_ne_zero (div_ne_zero (by norm_num : (1:ℝ)≠0) hh.ne')
    (div_ne_zero (by norm_num : (2:ℝ)≠0) hh.ne'))
  rw [he]
  field_simp
  ring

end
end RectangleCLTArxivV1
