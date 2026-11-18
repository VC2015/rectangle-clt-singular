import RectangleCLTArxivV1.SupplementalHMixedCoareaLipschitz
import RectangleCLTArxivV1.SupplementalHPairPlane

/-! The actual positive mass and pair-plane tests on a first facet,
and their exact remaining two-normal sections. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def positiveMixedPlaneFacetWeight {r : ℕ} (q : Vector r) (a : ℝ) (g : Vector r) : ℝ :=
  a^2+faceDot q g^2

def positiveMixedFirstMassDensity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j : Fin m) : ℝ :=
  gaussianPDFReal 0 1 (b j)*gaussianFiniteWeightedThreshold (Finset.univ.erase j)
    (fun k => gaussianNormalProjection (u j) (u k))
    (fun k => b k-b j*faceDot (u k) (u j)) (fun _ => 1)

def positiveMixedFirstPlaneDensity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  gaussianPDFReal 0 1 (b j)*gaussianFiniteWeightedThreshold (Finset.univ.erase j)
    (fun k => gaussianNormalProjection (u j) (u k))
    (fun k => b k-b j*faceDot (u k) (u j))
    (positiveMixedPlaneFacetWeight (gaussianPairConditionalDirection u j l) (b j))

theorem measurable_positiveMixedPlaneFacetWeight {r : ℕ} (q : Vector r) (a : ℝ) :
    Measurable (positiveMixedPlaneFacetWeight q a) :=
  measurable_const.add ((continuous_faceDot_left q).measurable.pow_const 2)

theorem integrable_positiveMixedPlaneFacetWeight {r : ℕ} (q : Vector r) (a : ℝ) :
    Integrable (positiveMixedPlaneFacetWeight q a) (standardGaussian r) :=
  (integrable_const _).add (standardGaussian_integrable_faceDot_sq q)

theorem gaussianPairConditionalDirection_eq_referenceComplement {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1) :
    gaussianPairConditionalDirection u j l=hReferencePairComplement (u j) (u l) := by
  unfold gaussianPairConditionalDirection hReferencePairComplement
  rw [gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv]

theorem positiveMixed_pair_gram_pos {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    (faceDot (u j) (u l))^2<1 := by
  have h := (gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm).2.2
  rw [gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv] at h
  have hh := Real.sqrt_pos.mp h
  linarith

/-- The reduced first-facet weight is the squared length of the actual
rank-two projection, not an abstract moment proxy. -/
theorem positiveMixedPlaneFacetWeight_eq_actual_projection {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (a : ℝ) (g : Vector r) :
    positiveMixedPlaneFacetWeight (gaussianPairConditionalDirection u j l) a g=
      vectorNormSq ((supplementalHPairPlane (u j) (u l)).mulVec (gaussianSectionPoint (u j) a g)) := by
  let q := gaussianPairConditionalDirection u j l
  have ho := (gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm).2.1
  have hq : faceDot q (gaussianSectionPoint (u j) a g)=faceDot q g := by
    rw [gaussianSectionPoint_eq,threshold_faceDot_add_right,threshold_faceDot_smul_right,
      faceDot_comm q (u j),ho,mul_zero,add_zero]
  rw [supplementalHPairPlane_normSq _ _ _ hu hv (positiveMixed_pair_gram_pos u j l hu hv hp hm),
    ← gaussianPairConditionalDirection_eq_referenceComplement u j l hu hv,
    gaussianSectionPoint_on_hyperplane _ a hu,hq]
  rfl

theorem gaussianFiniteWeightedThreshold_one_eq_cdf {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) :
    gaussianFiniteWeightedThreshold s u b (fun _ => 1)=gaussianFiniteThresholdCDF s u b :=
  (gaussianFiniteThresholdCDF_eq_integral s u b).symm

theorem gaussianFiniteWeightedSection_one_eq_sectionProbability {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (q : Vector r) (t : ℝ) :
    gaussianFiniteWeightedSection s u b q (fun _ => 1) t=
      gaussianThresholdSectionProbability s u b q t := by
  unfold gaussianThresholdSectionProbability
  rw [gaussianFiniteThresholdCDF_eq_integral]
  unfold gaussianFiniteWeightedSection
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have hiff : gaussianSectionPoint q t g∈gaussianFiniteThresholdEvent s u b ↔
        g∈gaussianFiniteThresholdEvent s (fun k => gaussianNormalProjection q (u k))
          (fun k => b k-t*faceDot (u k) q) := by
      constructor <;> intro h k hk
      · have hh := h k hk
        rw [gaussianSectionPoint_faceDot] at hh
        change faceDot (gaussianNormalProjection q (u k)) g≤b k-t*faceDot (u k) q
        linarith
      · have hh := h k hk
        rw [gaussianSectionPoint_faceDot]
        dsimp only at hh
        linarith
    dsimp only
    by_cases hg : g∈gaussianFiniteThresholdEvent s (fun k => gaussianNormalProjection q (u k))
        (fun k => b k-t*faceDot (u k) q)
    · rw [indicator_of_mem (hiff.mpr hg),indicator_of_mem hg]
    · rw [indicator_of_not_mem (fun h => hg (hiff.mp h)),indicator_of_not_mem hg])

theorem gaussianFiniteWeightedSection_plane_eq_probability {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (q : Vector r)
    (hq : vectorNormSq q=1) (a t : ℝ) :
    gaussianFiniteWeightedSection s u b q (positiveMixedPlaneFacetWeight q a) t=
      (a^2+t^2)*gaussianThresholdSectionProbability s u b q t := by
  rw [← gaussianFiniteWeightedSection_one_eq_sectionProbability]
  unfold gaussianFiniteWeightedSection
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    by_cases hg : gaussianSectionPoint q t g∈gaussianFiniteThresholdEvent s u b
    · rw [indicator_of_mem hg,indicator_of_mem hg]
      rw [positiveMixedPlaneFacetWeight,gaussianSectionPoint_on_hyperplane q t hq,mul_one]
    · rw [indicator_of_not_mem hg,indicator_of_not_mem hg,mul_zero])

theorem gaussianFiniteWeightedSection_one_eq_pairProbability {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (e q : Vector r) (a t : ℝ) :
    gaussianFiniteWeightedSection s (fun k => gaussianNormalProjection e (u k))
      (fun k => b k-a*faceDot (u k) e) q (fun _ => 1) t=
      hardGaussianPairSectionProbability s u b e q a t := by
  unfold gaussianFiniteWeightedSection hardGaussianPairSectionProbability
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have hiff : gaussianPairSectionPoint e q a t g∈gaussianFiniteThresholdEvent s u b ↔
        gaussianSectionPoint q t g∈gaussianFiniteThresholdEvent s
          (fun k => gaussianNormalProjection e (u k)) (fun k => b k-a*faceDot (u k) e) := by
      constructor <;> intro h k hk
      · have hh := h k hk
        change faceDot (u k) (gaussianSectionPoint e a (gaussianSectionPoint q t g))≤b k at hh
        rw [gaussianSectionPoint_faceDot] at hh
        change faceDot (gaussianNormalProjection e (u k)) (gaussianSectionPoint q t g)≤b k-a*faceDot (u k) e
        linarith
      · have hh := h k hk
        change faceDot (u k) (gaussianSectionPoint e a (gaussianSectionPoint q t g))≤b k
        rw [gaussianSectionPoint_faceDot]
        dsimp only at hh
        linarith
    dsimp only
    by_cases hg : gaussianSectionPoint q t g∈gaussianFiniteThresholdEvent s
        (fun k => gaussianNormalProjection e (u k)) (fun k => b k-a*faceDot (u k) e)
    · rw [indicator_of_mem hg,indicator_of_mem (hiff.mpr hg)]
    · rw [indicator_of_not_mem hg,indicator_of_not_mem (fun h => hg (hiff.mp h))])

theorem hardGaussianConditionalPairProbability_eq_native {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    hardGaussianPairSectionProbability s u b (u j) (gaussianPairConditionalDirection u j l)
      (b j) (gaussianPairConditionalLevel u b j l)=
      hardGaussianPairSectionProbability s u b (thresholdPairBisector u j l)
        (thresholdPairDifference u j l) (thresholdPairFirstLevel u b j l)
        (thresholdPairSecondLevel u b j l) :=
  hardGaussianConditionalPairSection_eq_pairSection s u b j l hu hv hp hm _

theorem gaussianPair_conditional_normalLength_eq_native {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    (b j)^2+(gaussianPairConditionalLevel u b j l)^2=
      (thresholdPairFirstLevel u b j l)^2+(thresholdPairSecondLevel u b j l)^2 := by
  have hs := (thresholdPair_coefficients_sq u j l hu hv).1
  have hl := gaussianPair_coordinate_rotation_levels u b j l hu hv hp hm
  calc
    _ = ((thresholdPairFirstCoefficient u j l)^2+(thresholdPairSecondCoefficient u j l)^2)*
        ((b j)^2+(gaussianPairConditionalLevel u b j l)^2) := by rw [hs,one_mul]
    _ = (thresholdPairFirstCoefficient u j l*b j+
        thresholdPairSecondCoefficient u j l*gaussianPairConditionalLevel u b j l)^2+
        (thresholdPairSecondCoefficient u j l*b j-
        thresholdPairFirstCoefficient u j l*gaussianPairConditionalLevel u b j l)^2 := by ring
    _ = _ := by rw [hl.1,hl.2]

end
end RectangleCLTArxivV1
