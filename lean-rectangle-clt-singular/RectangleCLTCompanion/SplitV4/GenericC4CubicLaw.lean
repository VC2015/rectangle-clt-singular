import RectangleCLTCompanion.SplitV4.GenericC4FourthIdentity

/-! The cubic tensor contraction at the actual common seeded law. All
fresh-copy, original-sample, Gaussian, and finite-selector interchanges use
genuine integrability from the bounded third derivative and bounded rows. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def genericCubicContraction {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p) (y : Vector p) : ℝ :=
  ∑ i, ∫ u, canonicalDiagonal F 3 y (ξ i u) ∂μ

theorem integrable_canonicalMoment_comp
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p k : ℕ}
    (ρ : Measure Β) [IsFiniteMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) (hk : k ≤ 4) {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hjet : ∀ y, ‖iteratedFDeriv ℝ k F y‖ ≤ C)
    (W : Β → Vector p) (hW : Measurable W) (T : Ω → Vector p) (hT : Measurable T)
    (hbound : ∀ᵐ u ∂μ, ‖T u‖ ≤ δ) :
    Integrable (fun β => ∫ u, canonicalDiagonal F k (W β) (T u) ∂μ) ρ :=
  (integrable_canonicalDiagonal_bounded (ρ.prod μ) hF hk (fun z => W z.1) (fun z => T z.2)
    (hW.comp measurable_fst) (hT.comp measurable_snd) hC hδ hjet
    (Measure.quasiMeasurePreserving_snd.ae hbound)).integral_prod_left

theorem continuous_canonicalMoment
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (hk : k ≤ 4) {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hjet : ∀ y, ‖iteratedFDeriv ℝ k F y‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ u ∂μ, ‖T u‖ ≤ δ) :
    Continuous (fun y => ∫ u, canonicalDiagonal F k y (T u) ∂μ) := by
  apply continuous_of_dominated
    (bound := fun _ : Ω => C*δ^k)
  · intro y
    exact (integrable_canonicalDiagonal_bounded μ hF hk (fun _ => y) T measurable_const hT hC hδ hjet hbound).aestronglyMeasurable
  · intro y
    filter_upwards [hbound] with u hu
    exact (norm_canonicalDiagonal_le F y (T u) (hjet y)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu k) hC)
  · exact integrable_const _
  · exact ae_of_all _ (fun u => continuous_canonicalDiagonal_base hF hk (T u))

theorem norm_canonicalMoment_le
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Vector p → ℝ) {C δ : ℝ}
    (hC : 0 ≤ C) (hjet : ∀ y, ‖iteratedFDeriv ℝ k F y‖ ≤ C)
    (T : Ω → Vector p) (hbound : ∀ᵐ u ∂μ, ‖T u‖ ≤ δ) (y : Vector p) :
    ‖∫ u, canonicalDiagonal F k y (T u) ∂μ‖ ≤ C*δ^k := by
  have hh := norm_integral_le_of_norm_le_const (μ := μ) (f := fun u => canonicalDiagonal F k y (T u))
    (hbound.mono (fun u hu => (norm_canonicalDiagonal_le F y (T u) (hjet y)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu k) hC)))
  simpa only [measureReal_univ_eq_one, mul_one] using hh

theorem continuous_genericCubicContraction
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ y, ‖iteratedFDeriv ℝ 3 F y‖ ≤ C) :
    Continuous (genericCubicContraction μ F ξ) :=
  continuous_finset_sum _ (fun i _ => continuous_canonicalMoment μ hF (by decide) hC h.delta_nonneg hjet
    (ξ i) (h.measurable i) (h.bounded i))

theorem norm_genericCubicContraction_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (F : Vector p → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ y, ‖iteratedFDeriv ℝ 3 F y‖ ≤ C) (y : Vector p) :
    ‖genericCubicContraction μ F ξ y‖ ≤ (n : ℝ)*C*δ^3 := by
  calc
    _ ≤ ∑ i, ‖∫ u, canonicalDiagonal F 3 y (ξ i u) ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, C*δ^3 := Finset.sum_le_sum (fun i _ => norm_canonicalMoment_le μ F hC hjet (ξ i) (h.bounded i) y)
    _ = _ := by simp; ring

theorem integrable_genericCubicContraction_comp
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p n : ℕ}
    (ρ : Measure Β) [IsFiniteMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ y, ‖iteratedFDeriv ℝ 3 F y‖ ≤ C)
    (W : Β → Vector p) (hW : Measurable W) :
    Integrable (fun β => genericCubicContraction μ F ξ (W β)) ρ :=
  integrable_finset_sum _ (fun i _ => integrable_canonicalMoment_comp ρ μ hF (by decide) hC h.delta_nonneg
    hjet W hW (ξ i) (h.measurable i) (h.bounded i))

theorem genericCommonCubic_eq_sum_mask_integral
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ y, ‖iteratedFDeriv ℝ 3 F y‖ ≤ C) (x : Vector p) (q a : ℝ) :
    genericCommonCubic μ F ξ x q a =
      ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
        ∫ ω, genericCubicContraction μ F ξ (x+a • maskObservationSum ξ mask ω) ∂μ := by
  unfold genericCommonCubic genericFullMoment
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mask _
  rw [← Finset.mul_sum]
  congr 1
  exact (integral_finset_sum _ (fun i _ => integrable_canonicalMoment_comp μ μ hF (by decide) hC h.delta_nonneg
    hjet _ (measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ h.measurable mask)))
    (ξ i) (h.measurable i) (h.bounded i))).symm

theorem integrable_genericCommonCubic_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ y, ‖iteratedFDeriv ℝ 3 F y‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q a b : ℝ) :
    Integrable (fun g => genericCommonCubic μ F ξ (x+b • g) q a) (gaussianLaw A) := by
  simp_rw [genericCommonCubic_eq_sum_mask_integral μ ξ h hF hC hjet]
  apply integrable_finset_sum
  intro mask _
  apply Integrable.const_mul
  have hh := integrable_genericCubicContraction_comp ((gaussianLaw A).prod μ) μ ξ h hF hC hjet
    (fun z => (x+b • z.1)+a • maskObservationSum ξ mask z.2)
    ((measurable_const.add (measurable_const.smul measurable_fst)).add
      (measurable_const.smul ((measurable_maskObservationSum ξ h.measurable mask).comp measurable_snd)))
  exact hh.integral_prod_left

theorem integrable_genericCubicContraction_seededLaw
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ y, ‖iteratedFDeriv ℝ 3 F y‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ)
    (hq : variableRetention γ t ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun y => genericCubicContraction μ F ξ (x+y))
      (variableSeededInterpolationLaw μ ξ A γ ε t) := by
  letI := variableSeededInterpolationLaw_isProbability μ ξ h.measurable A γ ε t hq
  exact integrable_genericCubicContraction_comp _ μ ξ h hF hC hjet _ (measurable_const.add measurable_id)

/-- The cubic contribution is the genuine cubic tensor contraction at
`W_t`, under the actual independent-mask/original/Gaussian probability law. -/
theorem integral_genericCommonCubic_eq_seededLaw
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ y, ‖iteratedFDeriv ℝ 3 F y‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ)
    (hq : variableRetention γ t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ g, genericCommonCubic μ F ξ (x+Real.sqrt (t+ε) • g) (variableRetention γ t) (γ t) ∂gaussianLaw A) =
      ∫ y, genericCubicContraction μ F ξ (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε t := by
  let ν := gaussianLaw A
  let q := variableRetention γ t
  let b := Real.sqrt (t+ε)
  let a := γ t
  let K : Vector p → ℝ := fun y => genericCubicContraction μ F ξ (x+y)
  have hK : Continuous K := (continuous_genericCubicContraction μ ξ h hF hC hjet).comp (continuous_const.add continuous_id)
  have hi (mask : Kane.Cube n) : Integrable (fun z : Ω × Vector p => K (variableMaskPoint ξ γ ε t mask z)) (μ.prod ν) :=
    integrable_genericCubicContraction_comp _ μ ξ h hF hC hjet _
      (measurable_const.add (measurable_variableMaskPoint ξ h.measurable γ ε t mask))
  have him (mask : Kane.Cube n) : Integrable K ((μ.prod ν).map (variableMaskPoint ξ γ ε t mask)) :=
    (integrable_map_measure hK.aestronglyMeasurable (measurable_variableMaskPoint ξ h.measurable γ ε t mask).aemeasurable).mpr (hi mask)
  have hh (mask : Kane.Cube n) : Integrable (fun g => ∫ ω,
      genericCubicContraction μ F ξ ((x+b • g)+a • maskObservationSum ξ mask ω) ∂μ) ν := by
    have hd := (hi mask).integral_prod_right
    convert hd using 1
    funext g
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => by dsimp [K, variableMaskPoint]; congr 1; dsimp [a,b]; abel)
  simp_rw [genericCommonCubic_eq_sum_mask_integral μ ξ h hF hC hjet]
  rw [integral_finset_sum Finset.univ (fun mask _ => (hh mask).const_mul _)]
  simp only [integral_const_mul]
  change _ = ∫ y, K y ∂variableSeededInterpolationLaw μ ξ A γ ε t
  unfold variableSeededInterpolationLaw
  rw [integral_bernoulliMixtureLaw _ _ _ hq.1 hq.2 _ him]
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [integral_map (measurable_variableMaskPoint ξ h.measurable γ ε t mask).aemeasurable hK.aestronglyMeasurable,
    integral_prod_symm _ (hi mask)]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => integral_congr_ae (ae_of_all _ (fun ω => by
    dsimp [K, variableMaskPoint]
    congr 1
    abel)))

end
end RectangleCLT.Companion.SplitV4
