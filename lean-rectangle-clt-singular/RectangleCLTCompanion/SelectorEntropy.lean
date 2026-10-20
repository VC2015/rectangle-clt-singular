import RectangleCLTCompanion.TiltContraction
import RectangleCLTCompanion.EntropyAveraging

/-! Actual one-face domination and entropy algebra for selector tuples. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

variable {p r k : ℕ}

/-- The normalized logistic boundary weight of one face. -/
def oneFaceReference (s : FaceSmoother p) (f : Face p) (x : Vector p) : ℝ :=
  Real.exp (s.faceScore f x / s.bandwidth) /
    (1 + Real.exp (s.faceScore f x / s.bandwidth)) ^ 2

lemma oneFaceReference_bounds (s : FaceSmoother p) (f : Face p) (x : Vector p) :
    0 ≤ oneFaceReference s f x ∧ oneFaceReference s f x ≤ 1 := by
  let e := Real.exp (s.faceScore f x / s.bandwidth)
  have he : 0 < e := Real.exp_pos _
  change 0 ≤ e / (1 + e) ^ 2 ∧ e / (1 + e) ^ 2 ≤ 1
  constructor
  · positivity
  · apply (div_le_one (sq_pos_of_pos (by positivity))).mpr
    nlinarith [sq_nonneg e]

lemma F_mul_pi_le_oneFaceReference (s : FaceSmoother p) (f : Face p) (x : Vector p) :
    s.F x * s.pi x f ≤ oneFaceReference s f x := by
  classical
  by_cases hf : f ∈ s.faces
  · have hw : (s.weights x).weight f = Real.exp (s.faceScore f x / s.bandwidth) := by
      simp only [FaceSmoother.weights, hf, ↓reduceIte]
    have he := (s.weights x).weight_le_T f
    rw [hw] at he
    change (1 / (1 + (s.weights x).T)) *
      ((s.weights x).weight f / (1 + (s.weights x).T)) ≤ _
    rw [hw]
    unfold oneFaceReference
    have hden : (1 + Real.exp (s.faceScore f x / s.bandwidth)) ^ 2 ≤
        (1 + (s.weights x).T) ^ 2 := by
      have he0 := Real.exp_pos (s.faceScore f x / s.bandwidth)
      nlinarith
    calc
      _ = Real.exp (s.faceScore f x / s.bandwidth) / (1 + (s.weights x).T) ^ 2 := by
        field_simp [(s.weights x).denominator_pos.ne']
        ring
      _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_nonneg _)
        (sq_pos_of_pos (by positivity)) hden
  · have hz : s.pi x f = 0 := by
      simp only [FaceSmoother.pi, FaceWeights.pi, FaceSmoother.weights, hf, ↓reduceIte,
        zero_div]
    rw [hz, mul_zero]
    exact (oneFaceReference_bounds s f x).1

lemma selectorWeight_le_oneFaceReference (s : FaceSmoother p)
    (faces : Fin (k + 1) → Face p) (x : Vector p) :
    selectorWeight s faces x ≤ oneFaceReference s (faces 0) x := by
  have hp : (∏ i : Fin k, s.pi x (faces i.succ)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _
      exact (s.weights x).pi_nonneg _
    · intro i _
      exact ((s.weights x).pi_le_theta _).trans (s.weights x).theta_lt_one.le
  unfold selectorWeight
  rw [Fin.prod_univ_succ, ← mul_assoc]
  exact (mul_le_of_le_one_right
    (mul_nonneg (s.F_pos x).le ((s.weights x).pi_nonneg _)) hp).trans
    (F_mul_pi_le_oneFaceReference s (faces 0) x)

/-- Summing all tuples, including tuples with omitted faces of weight zero,
gives the concrete scalar transition weight. -/
theorem sum_selectorWeight_eq (s : FaceSmoother p) (x : Vector p) (k : ℕ) :
    (∑ faces : Fin k → Face p, selectorWeight s faces x) = s.F x * s.theta x ^ k := by
  simp only [selectorWeight, ← Finset.mul_sum]
  congr 1
  rw [← Fintype.prod_sum]
  simp only [FaceSmoother.pi, FaceSmoother.theta, FaceWeights.sum_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Signed normal of a face after an arbitrary rectangular factor. -/
def selectorFaceNormal (A : Matrix (Fin p) (Fin r) ℝ) (f : Face p) : Vector r :=
  fun j => if f.2 then A f.1 j else -A f.1 j

lemma selectorFaceNormal_normSq (A : Matrix (Fin p) (Fin r) ℝ)
    (hunit : ∀ j, vectorNormSq (A j) = 1) (f : Face p) :
    vectorNormSq (selectorFaceNormal A f) = 1 := by
  unfold vectorNormSq selectorFaceNormal
  cases hf : f.2 <;> simp only [hf, Bool.false_eq_true, ↓reduceIte, neg_sq]
  all_goals exact hunit f.1

lemma normalDot_affine (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (σ : ℝ) (f : Face p) (g : Vector r) :
    FaceSmoother.normalDot f (σ • A.mulVec g + v) =
      σ * faceDot (selectorFaceNormal A f) g + FaceSmoother.normalDot f v := by
  unfold FaceSmoother.normalDot faceDot selectorFaceNormal Matrix.mulVec dotProduct
  cases hf : f.2 <;>
    simp only [hf, Bool.false_eq_true, ↓reduceIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      neg_mul, Finset.sum_neg_distrib]
  · ring

/-- The reference is a measurable scalar function of one unit normal
coordinate, with the random base point held fixed. -/
def oneFaceReferenceProfile (s : FaceSmoother p) (v : Vector p) (σ : ℝ)
    (f : Face p) (t : ℝ) : ℝ :=
  let e := Real.exp ((σ * t + FaceSmoother.normalDot f v - s.offsets f) / s.bandwidth)
  e / (1 + e) ^ 2

lemma oneFaceReferenceProfile_eq (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (σ : ℝ) (f : Face p) (g : Vector r) :
    oneFaceReferenceProfile s v σ f (faceDot (selectorFaceNormal A f) g) =
      oneFaceReference s f (σ • A.mulVec g + v) := by
  unfold oneFaceReferenceProfile oneFaceReference FaceSmoother.faceScore
  rw [normalDot_affine]

lemma measurable_oneFaceReferenceProfile (s : FaceSmoother p)
    (v : Vector p) (σ : ℝ) (f : Face p) :
    Measurable (oneFaceReferenceProfile s v σ f) := by
  unfold oneFaceReferenceProfile
  fun_prop

lemma oneFaceReferenceProfile_bounds (s : FaceSmoother p)
    (v : Vector p) (σ : ℝ) (f : Face p) (t : ℝ) :
    0 ≤ oneFaceReferenceProfile s v σ f t ∧ oneFaceReferenceProfile s v σ f t ≤ 1 := by
  let e := Real.exp ((σ * t + FaceSmoother.normalDot f v - s.offsets f) / s.bandwidth)
  have he : 0 < e := Real.exp_pos _
  change 0 ≤ e / (1 + e) ^ 2 ∧ e / (1 + e) ^ 2 ≤ 1
  constructor
  · positivity
  · apply (div_le_one (sq_pos_of_pos (by positivity))).mpr
    nlinarith [sq_nonneg e]

/-- The actual finite selector mean bound, with the first face as its
one-dimensional reference. Its only geometric assumption is unit row norms;
the Gaussian factor is allowed to be rectangular and singular. -/
theorem selector_family_means_le_entropy
    (s : FaceSmoother p) (S : Finset (Fin (k + 1) → Face p)) (hS : S.Nonempty)
    (hactive : ∀ α ∈ S, ∀ i, α i ∈ s.faces)
    (A : Matrix (Fin p) (Fin r) ℝ) (hunit : ∀ j, vectorNormSq (A j) = 1)
    (v : Vector p) (σ : ℝ) :
    (∑ α ∈ S, weightMass (standardGaussian r)
      (fun g => selectorWeight s α ((σ • A).mulVec g + v)) *
      vectorNormSq (weightMean (standardGaussian r) id
        (fun g => selectorWeight s α ((σ • A).mulVec g + v)))) ≤
      (∫ g, ∑ α ∈ S, selectorWeight s α ((σ • A).mulVec g + v) *
        (faceDot (selectorFaceNormal A (α 0)) g) ^ 2 ∂standardGaussian r) +
      2 * massEntropy
        (∑ α ∈ S, weightMass (standardGaussian r)
          (fun g => selectorWeight s α ((σ • A).mulVec g + v)))
        (∑ α ∈ S, ∫ g, oneFaceReferenceProfile s v σ (α 0)
          (faceDot (selectorFaceNormal A (α 0)) g) ∂standardGaussian r) := by
  apply sum_gaussian_mean_relative_to_faces S
    (fun α => selectorFaceNormal A (α 0)) (fun α => oneFaceReferenceProfile s v σ (α 0))
    (fun α g => selectorWeight s α ((σ • A).mulVec g + v))
  · intro α _
    exact selectorFaceNormal_normSq A hunit _
  · intro α _
    exact measurable_oneFaceReferenceProfile s v σ _
  · intro α _ t
    exact (oneFaceReferenceProfile_bounds s v σ _ t).1
  · intro α _ t
    exact (oneFaceReferenceProfile_bounds s v σ _ t).2
  · intro α _
    exact (continuous_selectorWeight_affine s α (σ • A) v).measurable
  · intro α _ g
    refine ⟨selectorWeight_nonneg s α _, ?_⟩
    rw [oneFaceReferenceProfile_eq, ← Matrix.smul_mulVec_assoc]
    exact selectorWeight_le_oneFaceReference s α _
  · intro α hα
    exact selectorWeight_affine_mass_pos s α (hactive α hα) (σ • A) v
  · exact hS

end
end RectangleCLT.Companion
