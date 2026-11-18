import RectangleCLTArxivV1.ActualMatrixTransport
import RectangleCLTArxivV1.HFourthSeededPhysicalBase
import RectangleCLTArxivV1.HFourthSeededScales
import RectangleCLTArxivV1.SeededIntrinsic

/-! The actual normalized half-base, its physical support reconstruction
and its original concentrated law. No conditional concentration is used. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_seededSplitBase_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε t : ℝ) :
    ((bernoulliArrayLaw μ ξ t).prod (standardGaussian p)).map (capSeededBaseValue (n := n) A x ε t)=
      seededSplitBaseDistribution μ ξ A x ε t := rfl

theorem actual_seeded_physical_concentration
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ)) (x : Vector p) (ε : ℝ)
    {t C₀ κ : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hc : IntrinsicRectangleConcentration (seededSplitBaseDistribution μ ξ A x ε t) C₀ δ κ) :
    IntrinsicRectangleConcentration
      ((((bernoulliArrayLaw μ ξ t).prod (standardGaussian p)).map
        (hFourthPhysicalSeededBase (n := n) A ε t)).map (fun b => x+A.mulVec b)) C₀ δ κ := by
  have hrec := hFourth_seeded_base_eq_physical h A hA x ε ht
  rw [←actualMatrix_physical_pushforward ((bernoulliArrayLaw μ ξ t).prod (standardGaussian p)) A x
    (hFourthPhysicalSeededBase A ε t) (hFourthPhysicalSeededBase_continuous A ε t).measurable
    (capSeededBaseValue A x ε t) hrec,actual_seededSplitBase_map_eq]
  exact hc

/-- The complete actual cubic family at every normalized time. Original
concentration, support, normal scaling and seed-scale restrictions are
discharged; only a numerical domination of the universal constant remains. -/
theorem actual_normalized_cubic_supplier
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) {C₀ κ C t : ℝ} (hC₀ : 0<C₀) (hκ : 0<κ)
    (hband : 2*δ≤s.bandwidth) (hsmall : dimensionLog p*s.bandwidth^2≤1/4)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hc : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ)
    (hC : supplementalHCubicMatrixConstant C₀≤C) :
    let ε := dimensionLog p*s.bandwidth^2
    let hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    ∀ ℓ : ℕ,(∫ ω,∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore (seededRescaledSmoother s ε hε)
        (seededSplitGaussianScale ε t•A) (capRectangularFactorNormal A)
        (capSeededBaseValue A 0 ε t) γ ω)
          ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian p))≤
      C^(ℓ+2)*((seededRescaledSmoother s ε hε).bandwidth*
        (κ*dimensionLog p*Real.sqrt (dimensionLog p))) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  let ε := dimensionLog p*s.bandwidth^2
  have hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
  let f := seededRescaledSmoother s ε hε
  have hδ := h.delta_nonneg
  have hscale := hFourth_normalized_seed_scale_range hp s hδ hband ht hsmall
  have hrows (j : Fin p) : vectorNormSq (A j)=1 := by
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,vectorNormSq,pow_two] using
      (show (A*A.transpose) j j=1 by rw [hA,hunit j])
  have hδh : δ≤f.bandwidth :=
    (by linarith : δ≤s.bandwidth).trans (seededRescaledSmoother_bandwidth_ge s hε)
  exact actualMatrix_cubic_supplier_of_physical hp
    ((bernoulliArrayLaw μ ξ t).prod (standardGaussian p)) f A 0
    (hFourthPhysicalSeededBase A ε t) (hFourthPhysicalSeededBase_continuous A ε t).measurable
    (capSeededBaseValue A 0 ε t) (hFourth_seeded_base_eq_physical h A hA 0 ε ht)
    hC₀ hδ hκ hscale.1 hrows hδh
    (by simpa only [actual_seededSplitBase_map_eq] using hc) hscale.2.1 hC

end
end RectangleCLTArxivV1
