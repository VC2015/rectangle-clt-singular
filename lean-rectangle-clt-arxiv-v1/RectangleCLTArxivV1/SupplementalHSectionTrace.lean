import RectangleCLTArxivV1.SupplementalHLocalThreshold
import RectangleCLTCompanion.SplitV4.GaussianPairSections
import RectangleCLTCompanion.SplitV4.Printed.GammaDifferentiation

/-! The signed score on a genuine affine section splits into its normal
coefficient and the actual residual hard-polyhedron radial trace. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section

def gaussianFiniteThresholdRadialTrace {m r : ℕ} (s : Finset (Fin m))
    (v : Fin m → Vector r) (c : Vector m) : ℝ :=
  ∫ g, (gaussianFiniteThresholdEvent s v c).indicator (fun g => vectorNormSq g-(r:ℝ)) g
    ∂standardGaussian r

/-- A hard polyhedron whose retained normals are tangent to u is
independent of the normal Gaussian score, proved by actual Fubini. -/
theorem gaussianFiniteThreshold_normal_score_zero {m n : ℕ}
    (s : Finset (Fin m)) (v : Fin m → Vector (n+1)) (c : Vector m)
    (u : Vector (n+1)) (hu : vectorNormSq u=1)
    (hortho : ∀ l∈s, faceDot (v l) u=0) :
    (∫ g, (gaussianFiniteThresholdEvent s v c).indicator
      (fun g => faceDot u g^2-1) g ∂standardGaussian (n+1))=0 := by
  let Q := gaussianFiniteThresholdEvent s v c
  have hQ : MeasurableSet Q := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have hi : Integrable (Q.indicator (fun g => faceDot u g^2-1)) (standardGaussian (n+1)) :=
    ((standardGaussian_integrable_faceDot_sq u).sub (integrable_const _)).indicator hQ
  rw [standardGaussian_integral_normal_sections (0 : Fin (n+1)) u hi]
  have he (y : Vector n) (t : ℝ) :
      Q.indicator (fun g => faceDot u g^2-1) (normalSectionChart (0 : Fin (n+1)) u t y)=
      Q.indicator (fun _ => (1:ℝ)) (normalSectionChart (0 : Fin (n+1)) u 0 y)*(t^2-1) := by
    have hiff : normalSectionChart (0 : Fin (n+1)) u t y∈Q ↔
        normalSectionChart (0 : Fin (n+1)) u 0 y∈Q := by
      rw [normalSectionChart_eq_normal_add_base _ u hu]
      constructor <;> intro h l hl
      · have hh := h l hl
        rw [threshold_faceDot_add_right,threshold_faceDot_smul_right,hortho l hl,mul_zero,zero_add] at hh
        exact hh
      · change faceDot (v l) (t • u+normalSectionChart (0 : Fin (n+1)) u 0 y)≤c l
        rw [threshold_faceDot_add_right,threshold_faceDot_smul_right,hortho l hl,mul_zero,zero_add]
        exact h l hl
    by_cases hy : normalSectionChart (0 : Fin (n+1)) u 0 y∈Q
    · rw [Set.indicator_of_mem (hiff.mpr hy),Set.indicator_of_mem hy,
        normalSectionChart_on_hyperplane _ u hu,one_mul]
    · rw [Set.indicator_of_not_mem (fun hh => hy (hiff.mp hh)),Set.indicator_of_not_mem hy,zero_mul]
  simp_rw [he,integral_const_mul]
  have ht : (∫ t : ℝ, t^2-1 ∂gaussianReal 0 1)=0 := by
    rw [integral_sub (standardRealGaussian_integrable_pow 2) (integrable_const _),
      standardRealGaussian_integral_sq,integral_const]
    simp
  simp only [ht,mul_zero,integral_zero]

/-- Exact decomposition of the actual signed affine Gaussian section;
no family independence, no coarea estimate, and no regularity premise. -/
theorem thresholdSignedSection_eq_residual_trace {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (t : ℝ) :
    Printed.thresholdSignedSection u b j t=
      (t^2-1)*gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) t+
      gaussianFiniteThresholdRadialTrace (Finset.univ.erase j)
        (fun l => gaussianNormalProjection (u j) (u l))
        (fun l => b l-t*faceDot (u l) (u j)) := by
  let s := Finset.univ.erase j
  let v := fun l => gaussianNormalProjection (u j) (u l)
  let c := fun l => b l-t*faceDot (u l) (u j)
  let Q := gaussianFiniteThresholdEvent s v c
  have hQ : MeasurableSet Q := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have h1 : Integrable (Q.indicator (fun _ => (1:ℝ))) (standardGaussian (n+1)) :=
    (integrable_const _).indicator hQ
  have hscore : Integrable (Q.indicator (fun g => vectorNormSq g-((n+1:ℕ):ℝ))) (standardGaussian (n+1)) :=
    ((standardGaussian_integrable_vectorNormSq _).sub (integrable_const _)).indicator hQ
  have hnormal : Integrable (Q.indicator (fun g => faceDot (u j) g^2-1)) (standardGaussian (n+1)) :=
    ((standardGaussian_integrable_faceDot_sq _).sub (integrable_const _)).indicator hQ
  have he (g : Vector (n+1)) : Q.indicator
      (fun g => vectorNormSq (gaussianSectionPoint (u j) t g)-((n+1:ℕ):ℝ)) g=
      (t^2-1)*Q.indicator (fun _ => (1:ℝ)) g+
        Q.indicator (fun g => vectorNormSq g-((n+1:ℕ):ℝ)) g-
        Q.indicator (fun g => faceDot (u j) g^2-1) g := by
    by_cases hg : g∈Q
    · simp only [Set.indicator_of_mem hg,vectorNormSq_gaussianSectionPoint _ _ hu,mul_one]
      ring
    · simp only [Set.indicator_of_not_mem hg,mul_zero,add_zero,sub_zero]
  have hz := gaussianFiniteThreshold_normal_score_zero s v c (u j) hu
    (fun l _ => by rw [faceDot_comm]; exact gaussianNormalProjection_orthogonal _ _ hu)
  have hprob : (∫ g, Q.indicator (fun _ => (1:ℝ)) g ∂standardGaussian (n+1))=
      gaussianThresholdSectionProbability s u b (u j) t :=
    (gaussianFiniteThresholdCDF_eq_integral s v c).symm
  change (∫ g, Q.indicator
    (fun g => vectorNormSq (gaussianSectionPoint (u j) t g)-((n+1:ℕ):ℝ)) g
    ∂standardGaussian (n+1))=(t^2-1)*gaussianThresholdSectionProbability s u b (u j) t+
      gaussianFiniteThresholdRadialTrace s v c
  simp_rw [he]
  have hsub := integral_sub ((h1.const_mul (t^2-1)).add hscore) hnormal
  have hadd := integral_add (h1.const_mul (t^2-1)) hscore
  simp only [Pi.add_apply,Pi.sub_apply] at hsub hadd
  rw [hsub,hadd,integral_const_mul,hz,hprob,sub_zero]
  rfl

end
end RectangleCLTArxivV1
