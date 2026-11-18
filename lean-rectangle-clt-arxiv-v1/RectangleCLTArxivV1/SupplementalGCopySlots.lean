import RectangleCLTArxivV1.SupplementalGCopyModel
import RectangleCLTArxivV1.SupplementalGPairCopies

/-! Old and fresh whitened slots retain their actual copy covariance budgets.
This supplies all three small-angle coefficient patterns. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def capWhitenedSlot {Ω : Type*} {p r n : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (ξ : Fin n → Ω → Vector p) (fresh : Bool) (i : Fin n) (z : Ω × Ω) : Vector r :=
  if fresh then whitenedObservation A ξ i z.2 else whitenedObservation A ξ i z.1

theorem capWhitenedSlot_measurable
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ) (fresh : Bool) (i : Fin n) :
    Measurable (capWhitenedSlot A ξ fresh i) := by
  cases fresh
  · exact (whitenedObservation_measurable h A i).comp measurable_fst
  · exact (whitenedObservation_measurable h A i).comp measurable_snd

theorem capWhitenedSlot_integrable_coordinate_pair
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (fresh : Bool) (i : Fin n) (j k : Fin r) :
    Integrable (fun z => capWhitenedSlot A ξ fresh i z j*capWhitenedSlot A ξ fresh i z k) (μ.prod μ) := by
  have hi := (whitenedObservation_hypotheses h A).integrable_coordinate_pair i j k
  cases fresh
  · simpa only [capWhitenedSlot,Bool.false_eq_true,if_false,mul_one] using
      hi.mul_prod (integrable_const (μ := μ) (1 : ℝ))
  · simpa only [capWhitenedSlot,if_true,one_mul] using
      (integrable_const (μ := μ) (1 : ℝ)).mul_prod hi

theorem capWhitenedSlot_quadratic_budget
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (fresh : Bool) (y : Vector r) :
    (∑ i, ∫ z, (faceDot y (capWhitenedSlot A ξ fresh i z))^2 ∂μ.prod μ) ≤ vectorNormSq y := by
  cases fresh
  · exact capWhitenedCopy_quadratic_budget h A hA y
  · have he (i : Fin n) : (∫ z : Ω × Ω, (faceDot y (whitenedObservation A ξ i z.2))^2 ∂μ.prod μ) =
        ∫ ω, (faceDot y (whitenedObservation A ξ i ω))^2 ∂μ := by
      simpa only [measureReal_univ_eq_one,one_smul] using
        (integral_fun_snd (μ := μ) (ν := μ) (fun ω => (faceDot y (whitenedObservation A ξ i ω))^2))
    simp only [capWhitenedSlot,if_true]
    simp_rw [he]
    exact whitenedObservation_covariance_budget h A hA y

theorem capWhitenedSlot_reconstruct
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (fresh : Bool) (i : Fin n) :
    (fun z => A.mulVec (capWhitenedSlot A ξ fresh i z)) =ᵐ[μ.prod μ] capOriginalCopy ξ fresh i := by
  cases fresh
  · exact Measure.quasiMeasurePreserving_fst.ae (whitenedObservation_reconstruct h A hA i)
  · exact Measure.quasiMeasurePreserving_snd.ae (whitenedObservation_reconstruct h A hA i)

theorem capOriginalCopy_pair_eq_factor_ae
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (a b : Bool) (f g : RectangleCLT.Face p) (i : Fin n) :
    (fun z => capRectangularPairCoefficient A f g (capOriginalCopy ξ a i z) (capOriginalCopy ξ b i z)) =ᵐ[μ.prod μ]
      (fun z => capPairCoefficient (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)
        (capWhitenedSlot A ξ a i z) (capWhitenedSlot A ξ b i z)) := by
  filter_upwards [capWhitenedSlot_reconstruct h A hA a i,capWhitenedSlot_reconstruct h A hA b i] with z ha hb
  rw [← ha,← hb,capRectangularPairCoefficient_factor]

end
end RectangleCLTArxivV1
