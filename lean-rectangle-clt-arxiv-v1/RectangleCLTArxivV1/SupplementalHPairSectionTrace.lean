import RectangleCLTArxivV1.SupplementalHSectionTrace
import RectangleCLTArxivV1.SupplementalHLocalFiniteThreshold

/-! Exact signed Gaussian Green decomposition on an actual codimension-two
orthonormal section. Every remaining hard inequality is retained. The
normal score cancellation uses actual Gaussian Fubini twice. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section

/-- Projection to the common orthogonal complement of an orthonormal
pair, applied successively in its two concrete normal directions. -/
def hardPairResidualNormal {r : ℕ} (e f v : Vector r) : Vector r :=
  gaussianNormalProjection f (gaussianNormalProjection e v)

def hardPairResidualNormals {m r : ℕ} (u : Fin m → Vector r) (e f : Vector r) : Fin m → Vector r :=
  fun k => hardPairResidualNormal e f (u k)

def hardPairResidualLevels {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (a c : ℝ) : Vector m :=
  fun k => b k-a*faceDot (u k) e-c*faceDot (u k) f

/-- The actual hard-event probability on the concrete pair section. -/
def hardGaussianPairSectionProbability {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (e f : Vector r) (a c : ℝ) : ℝ :=
  ∫ g, (gaussianFiniteThresholdEvent s u b).indicator (fun _ => (1 : ℝ))
    (gaussianPairSectionPoint e f a c g) ∂standardGaussian r

/-- The actual signed radial Gaussian score on the concrete pair section. -/
def hardGaussianPairSignedSection {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (e f : Vector r) (a c : ℝ) : ℝ :=
  ∫ g, (gaussianFiniteThresholdEvent s u b).indicator
    (fun x => vectorNormSq x-(r : ℝ)) (gaussianPairSectionPoint e f a c g) ∂standardGaussian r

theorem hardPairResidualNormal_orthogonal {r : ℕ} (e f v : Vector r)
    (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hef : faceDot e f=0) :
    faceDot (hardPairResidualNormal e f v) e=0 ∧
      faceDot (hardPairResidualNormal e f v) f=0 := by
  have hve : faceDot (gaussianNormalProjection e v) e=0 := by
    rw [faceDot_comm]
    exact gaussianNormalProjection_orthogonal e v he
  constructor
  · unfold hardPairResidualNormal gaussianNormalProjection
    rw [threshold_faceDot_sub_left,threshold_faceDot_smul_left,faceDot_comm f e,hef,mul_zero,sub_zero]
    exact hve
  · rw [faceDot_comm]
    exact gaussianNormalProjection_orthogonal f _ hf

theorem gaussianPairSectionPoint_faceDot_residual {r : ℕ}
    (e f v : Vector r) (a c : ℝ) (g : Vector r) (hef : faceDot e f=0) :
    faceDot v (gaussianPairSectionPoint e f a c g)=
      a*faceDot v e+c*faceDot v f+faceDot (hardPairResidualNormal e f v) g := by
  have hvf : faceDot (gaussianNormalProjection e v) f=faceDot v f := by
    rw [gaussianNormalProjection,threshold_faceDot_sub_left,threshold_faceDot_smul_left,
      hef,mul_zero,sub_zero]
  unfold gaussianPairSectionPoint
  rw [gaussianSectionPoint_faceDot,gaussianSectionPoint_faceDot,hvf]
  simp only [hardPairResidualNormal,add_assoc]

theorem vectorNormSq_gaussianPairSectionPoint {r : ℕ}
    (e f : Vector r) (he : vectorNormSq e=1) (hf : vectorNormSq f=1)
    (hef : faceDot e f=0) (a c : ℝ) (g : Vector r) :
    vectorNormSq (gaussianPairSectionPoint e f a c g)=
      vectorNormSq g-faceDot e g^2-faceDot f g^2+a^2+c^2 := by
  have hd : faceDot e (gaussianSectionPoint f c g)=faceDot e g := by
    rw [gaussianSectionPoint_eq,threshold_faceDot_add_right,threshold_faceDot_smul_right,
      hef,mul_zero,add_zero]
  unfold gaussianPairSectionPoint
  rw [vectorNormSq_gaussianSectionPoint e a he,vectorNormSq_gaussianSectionPoint f c hf,hd]
  ring

/-- Every retained original inequality is transported pointwise to the
actual double residual event. No strictness conversion is made. -/
theorem gaussianPairSectionPoint_mem_event_iff {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (a c : ℝ) (g : Vector r) (hef : faceDot e f=0) :
    gaussianPairSectionPoint e f a c g∈gaussianFiniteThresholdEvent s u b ↔
      g∈gaussianFiniteThresholdEvent s (hardPairResidualNormals u e f)
        (hardPairResidualLevels u b e f a c) := by
  simp only [gaussianFiniteThresholdEvent,mem_setOf_eq]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro _
  rw [gaussianPairSectionPoint_faceDot_residual e f (u k) a c g hef]
  change a*faceDot (u k) e+c*faceDot (u k) f+faceDot (hardPairResidualNormal e f (u k)) g≤b k ↔
    faceDot (hardPairResidualNormal e f (u k)) g≤b k-a*faceDot (u k) e-c*faceDot (u k) f
  constructor <;> intro h <;> linarith

theorem hardGaussianPairSectionProbability_eq_residual_CDF {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (a c : ℝ) (hef : faceDot e f=0) :
    hardGaussianPairSectionProbability s u b e f a c=
      gaussianFiniteThresholdCDF s (hardPairResidualNormals u e f) (hardPairResidualLevels u b e f a c) := by
  unfold hardGaussianPairSectionProbability
  rw [gaussianFiniteThresholdCDF_eq_integral]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have hiff := gaussianPairSectionPoint_mem_event_iff s u b e f a c g hef
    dsimp only
    by_cases hg : g∈gaussianFiniteThresholdEvent s (hardPairResidualNormals u e f)
        (hardPairResidualLevels u b e f a c)
    · rw [Set.indicator_of_mem (hiff.mpr hg),Set.indicator_of_mem hg]
    · rw [Set.indicator_of_not_mem (fun h => hg (hiff.mp h)),Set.indicator_of_not_mem hg])

/-- The codimension-two signed section is a genuine finite Gaussian
expectation, including every hard retained inequality. -/
theorem hardGaussianPairSignedSection_integrable {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1)
    (hef : faceDot e f=0) (a c : ℝ) :
    Integrable (fun g => (gaussianFiniteThresholdEvent s u b).indicator
      (fun x => vectorNormSq x-((n+1 : ℕ) : ℝ)) (gaussianPairSectionPoint e f a c g))
      (standardGaussian (n+1)) := by
  let Q := gaussianFiniteThresholdEvent s (hardPairResidualNormals u e f)
    (hardPairResidualLevels u b e f a c)
  have hQ : MeasurableSet Q := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have hnorm : Integrable (fun g => vectorNormSq (gaussianPairSectionPoint e f a c g))
      (standardGaussian (n+1)) := by
    simp_rw [vectorNormSq_gaussianPairSectionPoint e f he hf hef]
    exact ((((standardGaussian_integrable_vectorNormSq _).sub
      (standardGaussian_integrable_faceDot_sq e)).sub
      (standardGaussian_integrable_faceDot_sq f)).add (integrable_const (a^2))).add (integrable_const (c^2))
  have hi := (hnorm.sub (integrable_const ((n+1 : ℕ) : ℝ))).indicator hQ
  convert hi using 1
  funext g
  have hiff := gaussianPairSectionPoint_mem_event_iff s u b e f a c g hef
  by_cases hg : g∈Q
  · rw [Set.indicator_of_mem (hiff.mpr hg),Set.indicator_of_mem hg]
    rfl
  · rw [Set.indicator_of_not_mem (fun h => hg (hiff.mp h)),Set.indicator_of_not_mem hg]

/-- Actual codimension-two Green decomposition. Both centered normal
scores vanish by genuine Gaussian Fubini on the residual event. -/
theorem hardGaussianPairSignedSection_eq_residual_trace {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1)
    (hef : faceDot e f=0) (a c : ℝ) :
    hardGaussianPairSignedSection s u b e f a c=
      (a^2+c^2-2)*hardGaussianPairSectionProbability s u b e f a c+
      gaussianFiniteThresholdRadialTrace s (hardPairResidualNormals u e f)
        (hardPairResidualLevels u b e f a c) := by
  let v := hardPairResidualNormals u e f
  let d := hardPairResidualLevels u b e f a c
  let Q := gaussianFiniteThresholdEvent s v d
  have hQ : MeasurableSet Q := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have h1 : Integrable (Q.indicator (fun _ => (1 : ℝ))) (standardGaussian (n+1)) :=
    (integrable_const _).indicator hQ
  have hscore : Integrable (Q.indicator (fun g => vectorNormSq g-((n+1 : ℕ) : ℝ)))
      (standardGaussian (n+1)) :=
    ((standardGaussian_integrable_vectorNormSq _).sub (integrable_const _)).indicator hQ
  have hE : Integrable (Q.indicator (fun g => faceDot e g^2-1)) (standardGaussian (n+1)) :=
    ((standardGaussian_integrable_faceDot_sq e).sub (integrable_const _)).indicator hQ
  have hF : Integrable (Q.indicator (fun g => faceDot f g^2-1)) (standardGaussian (n+1)) :=
    ((standardGaussian_integrable_faceDot_sq f).sub (integrable_const _)).indicator hQ
  have hze := gaussianFiniteThreshold_normal_score_zero s v d e he
    (fun k _ => (hardPairResidualNormal_orthogonal e f (u k) he hf hef).1)
  have hzf := gaussianFiniteThreshold_normal_score_zero s v d f hf
    (fun k _ => (hardPairResidualNormal_orthogonal e f (u k) he hf hef).2)
  have heq (g : Vector (n+1)) : (gaussianFiniteThresholdEvent s u b).indicator
      (fun x => vectorNormSq x-((n+1 : ℕ) : ℝ)) (gaussianPairSectionPoint e f a c g)=
      (a^2+c^2-2)*Q.indicator (fun _ => (1 : ℝ)) g+
        Q.indicator (fun g => vectorNormSq g-((n+1 : ℕ) : ℝ)) g-
        Q.indicator (fun g => faceDot e g^2-1) g-
        Q.indicator (fun g => faceDot f g^2-1) g := by
    have hiff := gaussianPairSectionPoint_mem_event_iff s u b e f a c g hef
    by_cases hg : g∈Q
    · rw [Set.indicator_of_mem (hiff.mpr hg),Set.indicator_of_mem hg,
        Set.indicator_of_mem hg,Set.indicator_of_mem hg,Set.indicator_of_mem hg,
        vectorNormSq_gaussianPairSectionPoint e f he hf hef]
      ring
    · rw [Set.indicator_of_not_mem (fun h => hg (hiff.mp h)),Set.indicator_of_not_mem hg,
        Set.indicator_of_not_mem hg,Set.indicator_of_not_mem hg,Set.indicator_of_not_mem hg]
      ring
  unfold hardGaussianPairSignedSection
  simp_rw [heq]
  have hsubF := integral_sub (((h1.const_mul (a^2+c^2-2)).add hscore).sub hE) hF
  have hsubE := integral_sub ((h1.const_mul (a^2+c^2-2)).add hscore) hE
  have hadd := integral_add (h1.const_mul (a^2+c^2-2)) hscore
  simp only [Pi.add_apply,Pi.sub_apply] at hsubF hsubE hadd
  rw [hsubF,hsubE,hadd,integral_const_mul,hze,hzf,sub_zero,sub_zero]
  rw [hardGaussianPairSectionProbability_eq_residual_CDF s u b e f a c hef,
    gaussianFiniteThresholdCDF_eq_integral]
  rfl

/-- The actual pair-section Green sum of genuine third-face residual
densities, assuming only ordinary local residual slack. -/
theorem hardGaussianPairSection_Green_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1)
    (hef : faceDot e f=0) (a c : ℝ)
    (hreg : LocalFiniteThresholdRegularity s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    hardGaussianPairSignedSection s u b e f a c=
      (a^2+c^2-2)*hardGaussianPairSectionProbability s u b e f a c-
      ∑ k∈s, hardPairResidualLevels u b e f a c k*
        gaussianFiniteThresholdFirst s (hardPairResidualNormals u e f)
          (hardPairResidualLevels u b e f a c) k := by
  rw [hardGaussianPairSignedSection_eq_residual_trace s u b e f he hf hef a c]
  have ht := gaussianFiniteThreshold_radialTrace_retained_of_slack s
    (hardPairResidualNormals u e f) (hardPairResidualLevels u b e f a c) hreg
  change gaussianFiniteThresholdRadialTrace s (hardPairResidualNormals u e f)
    (hardPairResidualLevels u b e f a c)=_ at ht
  rw [ht]
  ring

/-- Multiplying the actual section Green identity by its Gaussian normal
coefficient retains the exact signed third-face coefficients. The weight
may include the pair's Gaussian densities and Gram Jacobian. -/
theorem hardGaussianPairSection_Green_weighted_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1)
    (hef : faceDot e f=0) (a c W : ℝ)
    (hreg : LocalFiniteThresholdRegularity s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    W*hardGaussianPairSignedSection s u b e f a c=
      (a^2+c^2-2)*(W*hardGaussianPairSectionProbability s u b e f a c)-
      ∑ k∈s, hardPairResidualLevels u b e f a c k*
        (W*gaussianFiniteThresholdFirst s (hardPairResidualNormals u e f)
          (hardPairResidualLevels u b e f a c) k) := by
  rw [hardGaussianPairSection_Green_of_slack s u b e f he hf hef a c hreg,
    mul_sub,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k _
    ring

end
end RectangleCLTArxivV1
