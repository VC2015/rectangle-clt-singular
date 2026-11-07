import RectangleCLTCompanion.SplitV4.DirectSlepianCubic

/-! The actual Slepian initialization law and its continuous endpoints.
The retention is identically one in the open interval, so the generic
independent-mask seeded interpolation is exactly the direct Slepian path. -/

open MeasureTheory Set
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def slepianAmplitude (v : ℝ) : ℝ := Real.sqrt (1-v)
def slepianAmplitudeDerivative (v : ℝ) : ℝ := -1/(2*Real.sqrt (1-v))

theorem slepianAmplitude_pos {v : ℝ} (hv : v < 1) : 0 < slepianAmplitude v :=
  Real.sqrt_pos.mpr (sub_pos.mpr hv)

theorem hasDerivAt_slepianAmplitude {v : ℝ} (hv : v < 1) :
    HasDerivAt slepianAmplitude (slepianAmplitudeDerivative v) v := by
  have hd := ((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)).sqrt (sub_pos.mpr hv).ne'
  simpa only [slepianAmplitude,slepianAmplitudeDerivative,id_eq,zero_sub] using hd

theorem continuousAt_slepianAmplitudeDerivative {v : ℝ} (hv : v < 1) :
    ContinuousAt slepianAmplitudeDerivative v := by
  unfold slepianAmplitudeDerivative
  fun_prop (disch := exact mul_ne_zero (by norm_num) (slepianAmplitude_pos hv).ne')

theorem variableRetention_slepianAmplitude {v : ℝ} (hv : v < 1) :
    variableRetention slepianAmplitude v = 1 := by
  unfold variableRetention slepianAmplitude
  rw [Real.sq_sqrt (sub_pos.mpr hv).le]
  exact div_self (sub_pos.mpr hv).ne'

theorem variableEta_slepianAmplitude {v : ℝ} (hv : v < 1) :
    variableEta slepianAmplitude slepianAmplitudeDerivative v = -(1/2 : ℝ) := by
  have hroot := (slepianAmplitude_pos hv).ne'
  have hs := Real.sq_sqrt (sub_pos.mpr hv).le
  unfold variableEta slepianAmplitude slepianAmplitudeDerivative at *
  field_simp [hroot]
  nlinarith

theorem variableRetentionDerivative_slepianAmplitude {v : ℝ} (hv : v < 1) :
    variableRetentionDerivative slepianAmplitude slepianAmplitudeDerivative v = 0 := by
  have hroot := (slepianAmplitude_pos hv).ne'
  have hs := Real.sq_sqrt (sub_pos.mpr hv).le
  unfold variableRetentionDerivative slepianAmplitude slepianAmplitudeDerivative at *
  field_simp [hroot]
  nlinarith

theorem variableSeededInterpolationLaw_eq_directSlepian
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : v < 1) :
    variableSeededInterpolationLaw μ ξ A slepianAmplitude 0 v =
      (μ.prod (gaussianLaw A)).map (directSlepianPoint ξ v) := by
  classical
  unfold variableSeededInterpolationLaw bernoulliMixtureLaw
  rw [variableRetention_slepianAmplitude hv]
  simp_rw [maskWeight_one, apply_ite ENNReal.ofReal]
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  congr 1
  funext z
  simp only [variableMaskPoint, slepianAmplitude, add_zero, directSlepianPoint,
    maskObservationSum, ↓reduceIte, sumVector]

theorem variableSeededInterpolationLaw_eq_directSlepian_one
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) :
    variableSeededInterpolationLaw μ ξ A slepianAmplitude 0 1 =
      (μ.prod (gaussianLaw A)).map (directSlepianPoint ξ 1) := by
  classical
  unfold variableSeededInterpolationLaw bernoulliMixtureLaw
  norm_num only [variableRetention,slepianAmplitude,sub_self,Real.sqrt_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),zero_div]
  simp_rw [Kane.maskWeight_zero, apply_ite ENNReal.ofReal]
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_zero, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  congr 1
  funext z
  simp only [variableMaskPoint,slepianAmplitude,sub_self,Real.sqrt_zero,zero_smul,
    zero_add,Real.sqrt_one,one_smul,directSlepianPoint,add_zero]

theorem variableSeededInterpolationLaw_eq_directSlepian_of_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : v ≤ 1) :
    variableSeededInterpolationLaw μ ξ A slepianAmplitude 0 v =
      (μ.prod (gaussianLaw A)).map (directSlepianPoint ξ v) := by
  rcases lt_or_eq_of_le hv with hv | rfl
  · exact variableSeededInterpolationLaw_eq_directSlepian μ ξ A hv
  · exact variableSeededInterpolationLaw_eq_directSlepian_one μ ξ A

def directSlepianExpectation {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (v : ℝ) : ℝ :=
  ∫ z : Ω × Vector p, s.F (directSlepianPoint ξ v z) ∂μ.prod (gaussianLaw A)

theorem integrable_directSlepianExpectation_kernel
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (v : ℝ) :
    Integrable (fun z : Ω × Vector p => s.F (directSlepianPoint ξ v z)) (μ.prod (gaussianLaw A)) := by
  apply (integrable_const (1 : ℝ)).mono'
    (s.continuous_F.measurable.comp (measurable_directSlepianPoint ξ hξ v)).aestronglyMeasurable
  exact ae_of_all _ fun z => s.norm_F_le_one _

theorem continuous_directSlepianExpectation
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) : Continuous (directSlepianExpectation s μ ξ A) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro v
    exact (s.continuous_F.measurable.comp (measurable_directSlepianPoint ξ hξ v)).aestronglyMeasurable
  · intro v
    exact ae_of_all _ fun z => s.norm_F_le_one _
  · exact integrable_const 1
  · apply ae_of_all
    intro z
    exact s.continuous_F.comp (show Continuous (fun v : ℝ => directSlepianPoint ξ v z) by
      unfold directSlepianPoint
      fun_prop)

theorem continuousOn_directSlepianExpectation
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) :
    ContinuousOn (directSlepianExpectation s μ ξ A) (Icc (0 : ℝ) 1) :=
  (continuous_directSlepianExpectation s μ ξ hξ A).continuousOn

theorem directSlepianExpectation_eq_seededLaw
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : v < 1) :
    directSlepianExpectation s μ ξ A v =
      ∫ y, s.F y ∂variableSeededInterpolationLaw μ ξ A slepianAmplitude 0 v := by
  rw [variableSeededInterpolationLaw_eq_directSlepian μ ξ A hv]
  exact (integral_map (measurable_directSlepianPoint ξ hξ v).aemeasurable
    s.continuous_F.aestronglyMeasurable).symm

theorem directSlepianExpectation_zero
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) :
    directSlepianExpectation s μ ξ A 0 = ∫ ω, s.F (sumVector ξ ω) ∂μ := by
  simp only [directSlepianExpectation,directSlepianPoint,sub_zero,Real.sqrt_one,one_smul,
    Real.sqrt_zero,zero_smul,add_zero]
  simpa only [measureReal_univ_eq_one,one_smul] using
    (integral_fun_fst (μ := μ) (ν := gaussianLaw A) (fun ω => s.F (sumVector ξ ω)))

theorem directSlepianExpectation_one
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) :
    directSlepianExpectation s μ ξ A 1 = ∫ g, s.F g ∂gaussianLaw A := by
  simp only [directSlepianExpectation,directSlepianPoint,sub_self,Real.sqrt_zero,zero_smul,
    Real.sqrt_one,one_smul,zero_add]
  simpa only [measureReal_univ_eq_one,one_smul] using
    (integral_fun_snd (μ := μ) (ν := gaussianLaw A) s.F)

def directSlepianFourthRemainder
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (v : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, genericManuscriptFourthPathIntegrand μ (gaussianLaw A) s.F ξ 0
    1 (Real.sqrt (1-v)) (Real.sqrt v) (-(1/2 : ℝ)) v r

theorem hasDerivAt_directSlepianExpectation
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt (directSlepianExpectation s μ ξ A)
      (-Real.sqrt (1-v)/4*directSlepianCubicTerm s μ ξ A v+
        directSlepianFourthRemainder s μ ξ A v) v := by
  have hF : ContDiff ℝ 4 s.F := s.contDiff_F_translation.of_le (by simp)
  have hd := hasDerivAt_integral_genericVariableSeededInterpolationLaw_tensor μ ξ h hF
    (smootherC4Bound_nonneg s) (smoother_iteratedFDeriv_norm_le s) A hA
    slepianAmplitude slepianAmplitudeDerivative (ε := 0) le_rfl
    (fun r hr => hasDerivAt_slepianAmplitude hr.2) (fun r hr => slepianAmplitude_pos hr.2)
    (fun r hr => by rw [variableRetention_slepianAmplitude hr.2]; exact ⟨zero_le_one,le_rfl⟩)
    0 hv0 hv1 (continuousAt_slepianAmplitudeDerivative hv1)
  have hcf : genericCubicContraction μ s.F ξ = canonicalSignedCubicContraction μ s.F ξ :=
    funext (genericCubicContraction_eq_signedTensor μ ξ h s.F)
  have hc := continuous_genericCubicContraction μ ξ h hF (smootherC4Bound_nonneg s)
    (smoother_iteratedFDeriv_norm_le s 3 (by decide) (by decide))
  rw [hcf] at hc
  have hclaw : (∫ y, canonicalSignedCubicContraction μ s.F ξ y
      ∂variableSeededInterpolationLaw μ ξ A slepianAmplitude 0 v) =
      directSlepianCubicTerm s μ ξ A v := by
    rw [variableSeededInterpolationLaw_eq_directSlepian μ ξ A hv1]
    exact integral_map (measurable_directSlepianPoint ξ h.measurable v).aemeasurable hc.aestronglyMeasurable
  have hcoef : (-slepianAmplitude v+(1-v)*slepianAmplitudeDerivative v)/6 =
      -Real.sqrt (1-v)/4 := by
    have he := variable_cubic_coefficient slepianAmplitude slepianAmplitudeDerivative
      (slepianAmplitude_pos hv1).ne'
    rw [variableEta_slepianAmplitude hv1] at he
    calc
      _ = -slepianAmplitude v*(1-(-(1/2 : ℝ)))/6 := he.symm
      _ = _ := by unfold slepianAmplitude; ring
  simp only [zero_add,add_zero,hclaw,variableRetention_slepianAmplitude hv1,
    variableEta_slepianAmplitude hv1] at hd
  rw [hcoef] at hd
  change HasDerivAt _ (-Real.sqrt (1-v)/4*directSlepianCubicTerm s μ ξ A v+
    directSlepianFourthRemainder s μ ξ A v) v at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hv0 hv1] with r hr
  exact directSlepianExpectation_eq_seededLaw s μ ξ h.measurable A hr.2

theorem intervalIntegrable_directSlepianFourthRemainder_kernel
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : v < 1) :
    IntervalIntegrable (genericManuscriptFourthPathIntegrand μ (gaussianLaw A) s.F ξ 0
      1 (Real.sqrt (1-v)) (Real.sqrt v) (-(1/2 : ℝ)) v) volume 0 1 := by
  have hi := intervalIntegrable_genericManuscriptFourthPathIntegrand μ ξ h
    (s.contDiff_F_translation.of_le (by simp)) (smootherC4Bound_nonneg s)
    (smoother_iteratedFDeriv_norm_le s 4 (by decide) (by decide)) A
    slepianAmplitude slepianAmplitudeDerivative (slepianAmplitude_pos hv).ne' 0 (Real.sqrt v)
  simpa only [variableRetention_slepianAmplitude hv,variableEta_slepianAmplitude hv,slepianAmplitude] using hi

end
end RectangleCLT.Companion.SplitV4
