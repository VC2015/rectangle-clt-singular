import RectangleCLTCompanion.SplitV4.Restoration
import RectangleCLTCompanion.SplitV4.RelativeMoments
import RectangleCLTCompanion.SplitV4.ProductConditional
import RectangleCLTCompanion.SupportRows

/-! Raw relative moment comparisons supply the actual conditional budgets
used in seeded restoration. Pseudowhitening preserves singular covariance;
its fixed coefficients enter moment justifications, never the final budget.
The cubic sum keeps its sign before the operator bound is applied. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem integrable_linear_weighted_entry
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (c : Fin n → Ω → ℝ)
    (L : Matrix (Fin r) (Fin p) ℝ)
    (hi : ∀ i j k, Integrable (fun ω => c i ω * (ξ i ω j * ξ i ω k)) μ)
    (i : Fin n) (a b : Fin r) :
    Integrable (fun ω => c i ω * (L.mulVec (ξ i ω) a * L.mulVec (ξ i ω) b)) μ := by
  have he := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => ((hi i j k).const_mul (L a j)).mul_const (L b k)))
  convert he using 1
  funext ω
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem restorationCoefficient_linear_quadratic
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (c : Fin n → Ω → ℝ)
    (L : Matrix (Fin r) (Fin p) ℝ)
    (hi : ∀ i j k, Integrable (fun ω => c i ω * (ξ i ω j * ξ i ω k)) μ)
    (u : Vector r) :
    matrixQuadratic (restorationCoefficient μ (fun i ω => L.mulVec (ξ i ω)) c) u =
      matrixQuadratic (restorationCoefficient μ ξ c) (L.transpose.mulVec u) := by
  rw [matrixQuadratic_restorationCoefficient_of_integrable μ _ c
      (integrable_linear_weighted_entry μ ξ c L hi) u,
    matrixQuadratic_restorationCoefficient_of_integrable μ ξ c hi (L.transpose.mulVec u)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext ω
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

theorem whitened_covariance_quadratic
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (u : Vector r) :
    matrixQuadratic (covariance μ (sumVector ξ)) ((ambientWhitening A).transpose.mulVec u) =
      matrixQuadratic (ambientSupportProjection A) u := by
  have he := matrixQuadratic_congruence (ambientWhitening A) (A * A.transpose) u
  rw [ambientWhitening_covariance, hA] at he
  exact he.symm

private theorem quadratic_smul_seed {p : ℕ} (a : ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) (u : Vector p) :
    matrixQuadratic (a • M) u = a * matrixQuadratic M u := by
  simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem relativeThird_whitened_budget
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) {M₃ M₄ : ℝ}
    (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (j : Fin p) (u : Vector r) :
    |matrixQuadratic (restorationCoefficient μ (whitenedObservation A ξ) (fun i ω => ξ i ω j)) u| ≤
      M₃ * vectorNormSq u := by
  rw [show whitenedObservation A ξ = (fun i ω => (ambientWhitening A).mulVec (ξ i ω)) by rfl,
    restorationCoefficient_linear_quadratic μ ξ _ _ (fun i k l => hrel.third_integrable i j k l)]
  have hl := hrel.third_lower j ((ambientWhitening A).transpose.mulVec u)
  have hu := hrel.third_upper j ((ambientWhitening A).transpose.mulVec u)
  rw [quadratic_smul_seed, whitened_covariance_quadratic μ ξ A hA] at hl hu
  have ha : |matrixQuadratic (relativeThirdMatrix μ ξ j) ((ambientWhitening A).transpose.mulVec u)| ≤
      M₃ * matrixQuadratic (ambientSupportProjection A) u := by
    apply abs_le.mpr
    constructor
    · linarith only [hl]
    · exact hu
  exact ha.trans (mul_le_mul_of_nonneg_left (ambientSupportProjection_quadratic_le A u) hrel.s₃_nonneg)

theorem relativeFourth_whitened_budget
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) {M₃ M₄ : ℝ}
    (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (j : Fin p) (u : Vector r) :
    matrixQuadratic (restorationCoefficient μ (whitenedObservation A ξ) (fun i ω => ξ i ω j ^ 2)) u ≤
      M₄ * vectorNormSq u := by
  rw [show whitenedObservation A ξ = (fun i ω => (ambientWhitening A).mulVec (ξ i ω)) by rfl,
    restorationCoefficient_linear_quadratic μ ξ _ _ (fun i k l => hrel.fourth_integrable i j k l)]
  have hu := hrel.fourth_upper j ((ambientWhitening A).transpose.mulVec u)
  rw [quadratic_smul_seed, whitened_covariance_quadratic μ ξ A hA] at hu
  exact hu.trans (mul_le_mul_of_nonneg_left (ambientSupportProjection_quadratic_le A u) hrel.s₄_nonneg)

theorem relativeFreshFourthMatrix_eq_first_copy
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) (j : Fin p) :
    restorationCoefficient (μ.prod μ) (fun i z => ξ i z.1)
      (fun i z => ξ i z.2 j ^ 2) = relativeFreshFourthMatrix μ ξ j := by
  ext k l
  simp only [restorationCoefficient, relativeFreshFourthMatrix]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ z : Ω × Ω, (ξ i z.1 k * ξ i z.1 l) * ξ i z.2 j ^ 2 ∂μ.prod μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)
    _ = (∫ ω, ξ i ω k * ξ i ω l ∂μ) * (∫ ω, ξ i ω j ^ 2 ∂μ) :=
      integral_prod_mul (fun ω => ξ i ω k * ξ i ω l) (fun ω => ξ i ω j ^ 2)
    _ = _ := mul_comm _ _

theorem integrable_fresh_relative_weighted_entry
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {M₃ M₄ : ℝ}
    (hrel : RelativeMomentBounds μ ξ M₃ M₄) (i : Fin n) (j k l : Fin p) :
    Integrable (fun z : Ω × Ω => ξ i z.2 j ^ 2 * (ξ i z.1 k * ξ i z.1 l)) (μ.prod μ) := by
  have hs : Integrable (fun ω => ξ i ω j ^ 2) μ := by
    simpa only [pow_two] using hrel.second_integrable i j j
  convert (hrel.second_integrable i k l).mul_prod hs using 1
  funext z
  ring

theorem relativeFreshFourth_whitened_budget
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {M₃ M₄ : ℝ}
    (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (j : Fin p) (u : Vector r) :
    matrixQuadratic (restorationCoefficient (μ.prod μ)
      (fun i z => whitenedObservation A ξ i z.1) (fun i z => ξ i z.2 j ^ 2)) u ≤
      M₄ * vectorNormSq u := by
  rw [show (fun (i : Fin n) (z : Ω × Ω) => whitenedObservation A ξ i z.1) =
      (fun i z => (ambientWhitening A).mulVec (ξ i z.1)) by rfl,
    restorationCoefficient_linear_quadratic (μ.prod μ) (fun i z => ξ i z.1)
      (fun i z => ξ i z.2 j ^ 2) (ambientWhitening A)
      (fun i k l => integrable_fresh_relative_weighted_entry μ ξ hrel i j k l),
    relativeFreshFourthMatrix_eq_first_copy]
  have hu := hrel.fresh_fourth_upper j ((ambientWhitening A).transpose.mulVec u)
  rw [quadratic_smul_seed, whitened_covariance_quadratic μ ξ A hA] at hu
  exact hu.trans (mul_le_mul_of_nonneg_left (ambientSupportProjection_quadratic_le A u) hrel.s₄_nonneg)

theorem conditionalRestorationCoefficient_copy_ae_eq
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {r n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (hZ : ∀ i, Measurable (Z i)) (hc : ∀ i, Measurable (c i))
    (hi : ∀ i j k, Integrable (fun ω => c i ω * (Z i ω j * Z i ω k)) μ) :
    (fun z : Β × Ω => conditionalRestorationCoefficient (ρ.prod μ) originalSigma
      (fun i z => Z i z.2) (fun i z => c i z.2) z) =ᵐ[ρ.prod μ]
      (fun _ => restorationCoefficient μ Z c) := by
  have he (j k : Fin r) : (fun z : Β × Ω =>
      conditionalRestorationCoefficient (ρ.prod μ) originalSigma
        (fun i z => Z i z.2) (fun i z => c i z.2) z j k) =ᵐ[ρ.prod μ]
      (fun _ => restorationCoefficient μ Z c j k) := by
    let f : Ω → ℝ := fun ω => ∑ i, c i ω * (Z i ω j * Z i ω k)
    have hfm : Measurable f := Finset.measurable_sum _ (fun i _ => (hc i).mul
      (((measurable_pi_apply j).comp (hZ i)).mul ((measurable_pi_apply k).comp (hZ i))))
    have hfi : Integrable f μ := integrable_finset_sum _ (fun i _ => hi i j k)
    have hsnd : MeasurePreserving (Prod.snd : Β × Ω → Ω) (ρ.prod μ) μ := ⟨measurable_snd, by simp⟩
    have hp := copyAverage_ae_eq_condExp ρ μ (fun z : Β × Ω => f z.2)
      (hfm.comp measurable_snd).stronglyMeasurable
      ((hsnd.integrable_comp hfi.aestronglyMeasurable).mpr hfi)
    have hval : (fun z : Β × Ω => copyAverage μ (fun z : Β × Ω => f z.2) z.1) =
        (fun _ => restorationCoefficient μ Z c j k) := by
      funext z
      change (∫ ω, ∑ i, c i ω * (Z i ω j * Z i ω k) ∂μ) = _
      rw [integral_finset_sum _ (fun i _ => hi i j k)]
      rfl
    rw [hval] at hp
    exact hp.symm
  filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => he j k))] with z hz
  ext j k
  exact hz j k

theorem restorationCoefficient_prod_fst
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) :
    restorationCoefficient (μ.prod ν) (fun i z => Z i z.1) (fun i z => c i z.1) =
      restorationCoefficient μ Z c := by
  ext j k
  simp only [restorationCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  simpa using integral_fun_fst (μ := μ) (ν := ν) (fun ω => c i ω * (Z i ω j * Z i ω k))

theorem relativeThird_whitened_face_budget
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) {M₃ M₄ : ℝ}
    (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (f : Face p) (u : Vector r) :
    |matrixQuadratic (restorationCoefficient μ (whitenedObservation A ξ)
      (fun i ω => FaceSmoother.normalDot f (ξ i ω))) u| ≤ M₃ * vectorNormSq u := by
  rcases f with ⟨j, b⟩
  cases b
  · have he : restorationCoefficient μ (whitenedObservation A ξ) (fun i ω => -ξ i ω j) =
        -restorationCoefficient μ (whitenedObservation A ξ) (fun i ω => ξ i ω j) := by
      ext k l
      simp only [restorationCoefficient, neg_mul, integral_neg, Finset.sum_neg_distrib, Matrix.neg_apply]
    simp only [FaceSmoother.normalDot, Bool.false_eq_true, if_false, he]
    have hn (M : Matrix (Fin r) (Fin r) ℝ) : matrixQuadratic (-M) u = -matrixQuadratic M u := by
      simp only [matrixQuadratic, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
    rw [hn, abs_neg]
    exact relativeThird_whitened_budget μ ξ hrel A hA j u
  · simpa only [FaceSmoother.normalDot, if_true] using relativeThird_whitened_budget μ ξ hrel A hA j u

theorem relativeFourth_whitened_face_budget
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) {M₃ M₄ : ℝ}
    (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (f : Face p) (u : Vector r) :
    matrixQuadratic (restorationCoefficient μ (whitenedObservation A ξ)
      (fun i ω => FaceSmoother.normalDot f (ξ i ω) ^ 2)) u ≤ M₄ * vectorNormSq u := by
  rcases f with ⟨j, b⟩
  cases b <;> simpa only [FaceSmoother.normalDot, Bool.false_eq_true, if_false, if_true, neg_sq] using
    relativeFourth_whitened_budget μ ξ hrel A hA j u

theorem relativeFreshFourth_whitened_face_budget
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {M₃ M₄ : ℝ}
    (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (f : Face p) (u : Vector r) :
    matrixQuadratic (restorationCoefficient (μ.prod μ)
      (fun i z => whitenedObservation A ξ i z.1)
      (fun i z => FaceSmoother.normalDot f (ξ i z.2) ^ 2)) u ≤ M₄ * vectorNormSq u := by
  rcases f with ⟨j, b⟩
  cases b <;> simpa only [FaceSmoother.normalDot, Bool.false_eq_true, if_false, if_true, neg_sq] using
    relativeFreshFourth_whitened_budget μ ξ hrel A hA j u

def seededCopyWhitened {Β Ω : Type*} {p r n : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (z : Β × (Ω × Ω)) : Vector r := whitenedObservation A ξ i z.2.1

def seededCopyOriginal {Β Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (i : Fin n) (z : Β × (Ω × Ω)) : Vector p := ξ i z.2.1

def seededCopyFresh {Β Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (i : Fin n) (z : Β × (Ω × Ω)) : Vector p := ξ i z.2.2

theorem seeded_copy_conditional_third_budget
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p r n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ M₃ M₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (f : Face p) : ∀ᵐ z ∂ρ.prod (μ.prod μ), ∀ u,
    |matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma
      (seededCopyWhitened A ξ) (fun i z => FaceSmoother.normalDot f (seededCopyOriginal ξ i z)) z) u| ≤
      M₃ * vectorNormSq u := by
  have hw := whitenedObservation_hypotheses h A
  let Z : Fin n → Ω × Ω → Vector r := fun i z => whitenedObservation A ξ i z.1
  let c : Fin n → Ω × Ω → ℝ := fun i z => FaceSmoother.normalDot f (ξ i z.1)
  have hc (i : Fin n) : Measurable (fun ω => FaceSmoother.normalDot f (ξ i ω)) :=
    (FaceSmoother.continuous_normalDot f).measurable.comp (h.measurable i)
  have hi (i : Fin n) (j k : Fin r) : Integrable
      (fun ω => FaceSmoother.normalDot f (ξ i ω) *
        (whitenedObservation A ξ i ω j * whitenedObservation A ξ i ω k)) μ :=
    (hw.integrable_coordinate_pair i j k).bdd_mul' (hc i).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using ((h.bounded i).mono
        (fun _ hω => FaceSmoother.abs_normalDot_le_of_norm_le f hω)))
  have hf : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ := ⟨measurable_fst, by simp⟩
  have hce := conditionalRestorationCoefficient_copy_ae_eq ρ (μ.prod μ) Z c
    (fun i => (hw.measurable i).comp measurable_fst) (fun i => (hc i).comp measurable_fst)
    (fun i j k => (hf.integrable_comp (hi i j k).aestronglyMeasurable).mpr (hi i j k))
  filter_upwards [hce] with z hz
  intro u
  change |matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma
    (fun i z => Z i z.2) (fun i z => c i z.2) z) u| ≤ _
  rw [hz]
  change |matrixQuadratic (restorationCoefficient (μ.prod μ)
    (fun i z => whitenedObservation A ξ i z.1) (fun i z => FaceSmoother.normalDot f (ξ i z.1))) u| ≤ _
  rw [restorationCoefficient_prod_fst μ μ (whitenedObservation A ξ)
    (fun i ω => FaceSmoother.normalDot f (ξ i ω))]
  exact relativeThird_whitened_face_budget μ ξ hrel A hA f u

theorem seeded_copy_conditional_fourth_budget
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p r n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ M₃ M₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (f : Face p) : ∀ᵐ z ∂ρ.prod (μ.prod μ), ∀ u,
    matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma
      (seededCopyWhitened A ξ) (fun i z => FaceSmoother.normalDot f (seededCopyOriginal ξ i z) ^ 2) z) u ≤
      M₄ * vectorNormSq u := by
  have hw := whitenedObservation_hypotheses h A
  let Z : Fin n → Ω × Ω → Vector r := fun i z => whitenedObservation A ξ i z.1
  let c : Fin n → Ω × Ω → ℝ := fun i z => FaceSmoother.normalDot f (ξ i z.1) ^ 2
  have hc (i : Fin n) : Measurable (fun ω => FaceSmoother.normalDot f (ξ i ω) ^ 2) :=
    ((FaceSmoother.continuous_normalDot f).measurable.comp (h.measurable i)).pow_const 2
  have hcb (i : Fin n) : ∀ᵐ ω ∂μ, |FaceSmoother.normalDot f (ξ i ω) ^ 2| ≤ δ ^ 2 := by
    filter_upwards [h.bounded i] with ω hω
    simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _)
      (FaceSmoother.abs_normalDot_le_of_norm_le f hω) 2
  have hi (i : Fin n) (j k : Fin r) : Integrable
      (fun ω => FaceSmoother.normalDot f (ξ i ω) ^ 2 *
        (whitenedObservation A ξ i ω j * whitenedObservation A ξ i ω k)) μ :=
    (hw.integrable_coordinate_pair i j k).bdd_mul' (hc i).aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hcb i)
  have hf : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ := ⟨measurable_fst, by simp⟩
  have hce := conditionalRestorationCoefficient_copy_ae_eq ρ (μ.prod μ) Z c
    (fun i => (hw.measurable i).comp measurable_fst) (fun i => (hc i).comp measurable_fst)
    (fun i j k => (hf.integrable_comp (hi i j k).aestronglyMeasurable).mpr (hi i j k))
  filter_upwards [hce] with z hz
  intro u
  change matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma
    (fun i z => Z i z.2) (fun i z => c i z.2) z) u ≤ _
  rw [hz]
  change matrixQuadratic (restorationCoefficient (μ.prod μ)
    (fun i z => whitenedObservation A ξ i z.1) (fun i z => FaceSmoother.normalDot f (ξ i z.1) ^ 2)) u ≤ _
  rw [restorationCoefficient_prod_fst μ μ (whitenedObservation A ξ)
    (fun i ω => FaceSmoother.normalDot f (ξ i ω) ^ 2)]
  exact relativeFourth_whitened_face_budget μ ξ hrel A hA f u

theorem seeded_copy_conditional_fresh_fourth_budget
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p r n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ M₃ M₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (f : Face p) : ∀ᵐ z ∂ρ.prod (μ.prod μ), ∀ u,
    matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma
      (seededCopyWhitened A ξ) (fun i z => FaceSmoother.normalDot f (seededCopyFresh ξ i z) ^ 2) z) u ≤
      M₄ * vectorNormSq u := by
  have hw := whitenedObservation_hypotheses h A
  let Z : Fin n → Ω × Ω → Vector r := fun i z => whitenedObservation A ξ i z.1
  let c : Fin n → Ω × Ω → ℝ := fun i z => FaceSmoother.normalDot f (ξ i z.2) ^ 2
  have hc (i : Fin n) : Measurable (fun ω => FaceSmoother.normalDot f (ξ i ω) ^ 2) :=
    ((FaceSmoother.continuous_normalDot f).measurable.comp (h.measurable i)).pow_const 2
  have hci (i : Fin n) : Integrable (fun ω => FaceSmoother.normalDot f (ξ i ω) ^ 2) μ := by
    rcases f with ⟨j, b⟩
    cases b <;> simpa only [FaceSmoother.normalDot, Bool.false_eq_true, if_false, if_true, neg_sq, pow_two, neg_mul_neg]
      using h.integrable_coordinate_pair i j j
  have hi (i : Fin n) (j k : Fin r) : Integrable
      (fun z : Ω × Ω => c i z * (Z i z j * Z i z k)) (μ.prod μ) := by
    convert (hw.integrable_coordinate_pair i j k).mul_prod (hci i) using 1
    funext z
    dsimp only [Z, c]
    ring
  have hce := conditionalRestorationCoefficient_copy_ae_eq ρ (μ.prod μ) Z c
    (fun i => (hw.measurable i).comp measurable_fst) (fun i => (hc i).comp measurable_snd) hi
  filter_upwards [hce] with z hz
  intro u
  change matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma
    (fun i z => Z i z.2) (fun i z => c i z.2) z) u ≤ _
  rw [hz]
  exact relativeFreshFourth_whitened_face_budget μ ξ hrel A hA f u

theorem seeded_copy_conditional_covariance_budget
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p r n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ)) :
    ∀ᵐ z ∂ρ.prod (μ.prod μ), ∀ u,
    matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma
      (seededCopyWhitened A ξ) (fun _ _ => 1) z) u ≤ vectorNormSq u := by
  have hw := whitenedObservation_hypotheses h A
  let Z : Fin n → Ω × Ω → Vector r := fun i z => whitenedObservation A ξ i z.1
  have hi (i : Fin n) (j k : Fin r) : Integrable
      (fun ω => (1 : ℝ) * (whitenedObservation A ξ i ω j * whitenedObservation A ξ i ω k)) μ := by
    simpa only [one_mul] using hw.integrable_coordinate_pair i j k
  have hf : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ := ⟨measurable_fst, by simp⟩
  have hce := conditionalRestorationCoefficient_copy_ae_eq ρ (μ.prod μ) Z (fun _ _ => 1)
    (fun i => (hw.measurable i).comp measurable_fst) (fun _ => measurable_const)
    (fun i j k => (hf.integrable_comp (hi i j k).aestronglyMeasurable).mpr (hi i j k))
  filter_upwards [hce] with z hz
  intro u
  change matrixQuadratic (conditionalRestorationCoefficient (ρ.prod (μ.prod μ)) originalSigma
    (fun i z => Z i z.2) (fun _ _ => 1) z) u ≤ _
  rw [hz]
  change matrixQuadratic (restorationCoefficient (μ.prod μ)
    (fun i z => whitenedObservation A ξ i z.1) (fun i z => (fun _ _ => (1 : ℝ)) i z.1)) u ≤ _
  rw [restorationCoefficient_prod_fst μ μ (whitenedObservation A ξ) (fun _ _ => (1 : ℝ)),
    matrixQuadratic_restorationCoefficient_of_integrable μ (whitenedObservation A ξ) _ hi]
  simp only [one_mul]
  exact whitenedObservation_covariance_budget h A hA u

theorem seededCopyWhitened_measurable
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ) (i : Fin n) :
    Measurable (seededCopyWhitened (Β := Β) A ξ i) :=
  ((whitenedObservation_measurable h A i).comp measurable_fst).comp measurable_snd

theorem seededCopyOriginal_measurable
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (i : Fin n) :
    Measurable (seededCopyOriginal (Β := Β) ξ i) :=
  ((hξ i).comp measurable_fst).comp measurable_snd

theorem seededCopyFresh_measurable
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (i : Fin n) :
    Measurable (seededCopyFresh (Β := Β) ξ i) :=
  ((hξ i).comp measurable_snd).comp measurable_snd

theorem seededCopyWhitened_integrable_coordinate_pair
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p r n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (i : Fin n) (j k : Fin r) :
    Integrable (fun z : Β × (Ω × Ω) =>
      seededCopyWhitened A ξ i z j * seededCopyWhitened A ξ i z k) (ρ.prod (μ.prod μ)) := by
  have hi := (whitenedObservation_hypotheses h A).integrable_coordinate_pair i j k
  have hf : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ := ⟨measurable_fst, by simp⟩
  have hs : MeasurePreserving (Prod.snd : Β × (Ω × Ω) → Ω × Ω) (ρ.prod (μ.prod μ)) (μ.prod μ) :=
    ⟨measurable_snd, by simp⟩
  exact ((hf.comp hs).integrable_comp hi.aestronglyMeasurable).mpr hi

theorem seededCopyWhitened_reconstruct
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p r n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ)) (i : Fin n) :
    (fun z : Β × (Ω × Ω) => A.mulVec (seededCopyWhitened A ξ i z)) =ᵐ[ρ.prod (μ.prod μ)]
      seededCopyOriginal ξ i :=
  Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae
    (whitenedObservation_reconstruct h A hA i))

theorem seededCopyOriginal_bounded
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) :
    ∀ᵐ z : Β × (Ω × Ω) ∂ρ.prod (μ.prod μ), ‖seededCopyOriginal ξ i z‖ ≤ δ :=
  Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae (h.bounded i))

theorem seededCopyFresh_bounded
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p n : ℕ}
    (ρ : Measure Β) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) :
    ∀ᵐ z : Β × (Ω × Ω) ∂ρ.prod (μ.prod μ), ‖seededCopyFresh ξ i z‖ ≤ δ :=
  Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae (h.bounded i))

end

end RectangleCLT.Companion.SplitV4
