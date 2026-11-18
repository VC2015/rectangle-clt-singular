import RectangleCLTArxivV1.SupplementalHCubicWeights
import RectangleCLT.GaussianFourthRecursion
import RectangleCLTCompanion.SplitV4.Printed.GaussianOrthogonalIndependence

/-! The positive-linear-factor weights in H have genuine finite Gaussian
second moments and positive mass. No boundedness of these weights is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem supplementalH_integrable_abs_linear_normSq {r : ℕ} (u : Vector r) :
    Integrable (fun g => |faceDot u g| *vectorNormSq g) (standardGaussian r) := by
  have hi := integrable_finset_sum Finset.univ (fun j (_ : j ∈ Finset.univ) =>
    (standardGaussian_integrable_faceDot_triple u (localBasisVector j) (localBasisVector j)).abs)
  have he (j : Fin r) : faceDot (localBasisVector j) = (fun g : Vector r => g j) := by
    funext g
    simp [faceDot,localBasisVector]
  simp_rw [he] at hi
  convert hi using 1
  funext g
  simp only [vectorNormSq,Finset.mul_sum,abs_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← pow_two, sq_abs]

theorem supplementalH_positive_selector_moments {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : Fin K → Face p) (u : Vector r) :
    Integrable (fun g => supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v))
      (standardGaussian r) ∧
    Integrable (fun g => vectorNormSq g*
      (supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v))) (standardGaussian r) := by
  have hm : Measurable (fun g => supplementalHPositiveDirection u g*
      selectorWeight s α (A.mulVec g+v)) := by
    apply Measurable.mul _ (continuous_selectorWeight_affine s α A v).measurable
    unfold supplementalHPositiveDirection faceDot
    fun_prop
  have hb (g : Vector r) : 0 ≤ supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v) ∧
      supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v) ≤ |faceDot u g| := by
    have hp := supplementalHPositiveDirection_nonneg u g
    refine ⟨mul_nonneg hp (selectorWeight_nonneg s α _),?_⟩
    exact (mul_le_of_le_one_right hp (selectorWeight_le_one s α _)).trans
      (max_le (le_abs_self _) (abs_nonneg _))
  constructor
  · apply (standardGaussian_integrable_faceDot u).abs.mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hb g).1]
      exact (hb g).2)
  · apply (supplementalH_integrable_abs_linear_normSq u).mono'
      ((show Measurable (vectorNormSq : Vector r → ℝ) by unfold vectorNormSq; fun_prop).mul hm).aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by unfold vectorNormSq; positivity) (hb g).1)]
      exact (mul_le_mul_of_nonneg_left (hb g).2 (by unfold vectorNormSq; positivity)).trans_eq (mul_comm _ _))

/-- A nondegenerate scalar Gaussian gives positive mass to its positive
half-line. Absolute continuity in both directions retains this fact. -/
theorem supplementalH_standardNormal_positive_halfline : 0 < gaussianReal 0 1 (Ioi (0:ℝ)) := by
  have hvol : volume (Ioi (0:ℝ)) ≠ 0 := by simp
  have hne : gaussianReal 0 1 (Ioi (0:ℝ)) ≠ 0 := by
    intro hzero
    exact hvol ((gaussianReal_absolutelyContinuous' (0:ℝ) (by norm_num : (1:NNReal) ≠ 0)) hzero)
  exact hne.bot_lt

theorem supplementalH_positive_selector_mass_pos {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : Fin K → Face p) (ha : ∀ i, α i ∈ s.faces) (u : Vector r) (hu : vectorNormSq u=1) :
    0 < weightMass (standardGaussian r)
      (fun g => supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v)) := by
  unfold weightMass
  rw [integral_pos_iff_support_of_nonneg
    (fun g => mul_nonneg (supplementalHPositiveDirection_nonneg u g) (selectorWeight_nonneg s α _))
    (supplementalH_positive_selector_moments s A v α u).1]
  have he : Function.support (fun g => supplementalHPositiveDirection u g*
      selectorWeight s α (A.mulVec g+v)) = {g | 0 < faceDot u g} := by
    ext g
    by_cases hg : 0 < faceDot u g
    · simp only [Function.mem_support, mul_ne_zero_iff, mem_setOf_eq]
      exact ⟨fun _ => hg,fun _ => ⟨(by simpa only [supplementalHPositiveDirection,max_eq_left hg.le] using hg.ne'),
        (selectorWeight_pos s α ha _).ne'⟩⟩
    · simp [Function.mem_support,supplementalHPositiveDirection,max_eq_right (le_of_not_gt hg),hg]
  rw [he]
  have hmap := Printed.standardGaussian_map_unit_faceDot u hu
  have heq : (standardGaussian r) {g | 0 < faceDot u g} = gaussianReal 0 1 (Ioi (0:ℝ)) := by
    rw [← hmap,Measure.map_apply (by unfold faceDot; fun_prop) measurableSet_Ioi]
    rfl
  rw [heq]
  exact supplementalH_standardNormal_positive_halfline

/-- The unbounded positive-linear-factor weight satisfies the actual
H.2 matrix inequality, with no Gaussian moment premise left to discharge. -/
theorem supplementalH_positive_selector_matrix_reduction {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : Fin K → Face p) (ha : ∀ i, α i ∈ s.faces) (u : Vector r) (hu : vectorNormSq u=1) :
    symmetricNuclearNorm (weightedScore (standardGaussian r) id
      (fun g => supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v))) ≤
      2*weightMass (standardGaussian r)
          (fun g => supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v))*
        vectorNormSq (weightMean (standardGaussian r) id
          (fun g => supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v)))-
      ∫ g, (vectorNormSq g-(r:ℝ))*
        (supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v)) ∂standardGaussian r := by
  have hm : Measurable (fun g => supplementalHPositiveDirection u g*
      selectorWeight s α (A.mulVec g+v)) := by
    apply Measurable.mul _ (continuous_selectorWeight_affine s α A v).measurable
    unfold supplementalHPositiveDirection faceDot
    fun_prop
  exact (lemma_H2_gaussian_matrix _ hm
    (fun g => mul_nonneg (supplementalHPositiveDirection_nonneg u g) (selectorWeight_nonneg s α _))
    (supplementalH_positive_selector_moments s A v α u).1
    (supplementalH_positive_selector_moments s A v α u).2
    (supplementalH_positive_selector_mass_pos s A v α ha u hu)
    (supplementalH_positive_selector_logConcave s A v α ha u)).2

end
end RectangleCLTArxivV1
