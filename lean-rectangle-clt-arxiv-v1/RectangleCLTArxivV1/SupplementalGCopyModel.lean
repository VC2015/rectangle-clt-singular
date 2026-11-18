import RectangleCLTArxivV1.SupplementalGRectangularDecomposition
import RectangleCLTArxivV1.SupplementalGSingleRemainderAE

/-! The actual independent row copies used by all three complementary
remainder patterns. Their rank-space second moment budget is proved from
the original covariance, including singular covariance factors. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def capWhitenedCopy {Ω : Type*} {p r n : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (ξ : Fin n → Ω → Vector p) (i : Fin n) (z : Ω × Ω) : Vector r :=
  whitenedObservation A ξ i z.1

def capOriginalCopy {Ω : Type*} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (fresh : Bool) (i : Fin n) (z : Ω × Ω) : Vector p := if fresh then ξ i z.2 else ξ i z.1

theorem capWhitenedCopy_measurable
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ) (i : Fin n) :
    Measurable (capWhitenedCopy A ξ i) := (whitenedObservation_measurable h A i).comp measurable_fst

theorem capWhitenedCopy_integrable_coordinate_pair
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (i : Fin n) (j k : Fin r) :
    Integrable (fun z => capWhitenedCopy A ξ i z j*capWhitenedCopy A ξ i z k) (μ.prod μ) := by
  have hi := (whitenedObservation_hypotheses h A).integrable_coordinate_pair i j k
  simpa only [mul_one,capWhitenedCopy] using hi.mul_prod (integrable_const (μ := μ) (1 : ℝ))

theorem capWhitenedCopy_quadratic_budget
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (y : Vector r) :
    (∑ i, ∫ z, (faceDot y (capWhitenedCopy A ξ i z))^2 ∂μ.prod μ) ≤ vectorNormSq y := by
  have he (i : Fin n) : (∫ z : Ω × Ω, (faceDot y (whitenedObservation A ξ i z.1))^2 ∂μ.prod μ) =
      ∫ ω, (faceDot y (whitenedObservation A ξ i ω))^2 ∂μ := by
    simpa only [measureReal_univ_eq_one,one_smul] using
      (integral_fun_fst (μ := μ) (ν := μ) (fun ω => (faceDot y (whitenedObservation A ξ i ω))^2))
  simp only [capWhitenedCopy]
  simp_rw [he]
  exact whitenedObservation_covariance_budget h A hA y

theorem capWhitenedCopy_reconstruct
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (i : Fin n) :
    (fun z => A.mulVec (capWhitenedCopy A ξ i z)) =ᵐ[μ.prod μ] capOriginalCopy ξ false i := by
  exact Measure.quasiMeasurePreserving_fst.ae (whitenedObservation_reconstruct h A hA i)

theorem capOriginalCopy_measurable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (fresh : Bool) (i : Fin n) :
    Measurable (capOriginalCopy ξ fresh i) := by
  cases fresh
  · exact (hξ i).comp measurable_fst
  · exact (hξ i).comp measurable_snd

theorem capOriginalCopy_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (fresh : Bool) (i : Fin n) :
    ∀ᵐ z ∂μ.prod μ, ‖capOriginalCopy ξ fresh i z‖ ≤ δ := by
  cases fresh
  · exact Measure.quasiMeasurePreserving_fst.ae (h.bounded i)
  · exact Measure.quasiMeasurePreserving_snd.ae (h.bounded i)

/-- The single-face coefficient has the actual δ² envelope for every pair
of old/fresh copy choices, including the three printed fourth-order patterns. -/
theorem capOriginalCopy_face_product_bounded
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (a b : Bool) (f : Face p) (i : Fin n) :
    ∀ᵐ z ∂μ.prod μ,
      |normalDot f (capOriginalCopy ξ a i z)*normalDot f (capOriginalCopy ξ b i z)| ≤ δ^2 := by
  filter_upwards [capOriginalCopy_bounded h a i,capOriginalCopy_bounded h b i] with z ha hb
  rw [abs_mul]
  have h1 := abs_normalDot_le_of_norm_le f ha
  have h2 := abs_normalDot_le_of_norm_le f hb
  exact (mul_le_mul h1 h2 (abs_nonneg _) h.delta_nonneg).trans_eq (by ring)

/-- A concrete bandwidth constant supplies the convergent restoration ratio
for the actual seeded displacement bound 4δ. -/
theorem cap_seeded_shift_ratio {p : ℕ} (s : FaceSmoother p) {δ : ℝ}
    (hband : 16*δ ≤ s.bandwidth) : 4*δ/s.bandwidth ≤ Real.log (3/2 : ℝ) := by
  have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3/2)
  have hq : (1/4 : ℝ) ≤ Real.log (3/2 : ℝ) := by norm_num at hl ⊢; linarith
  apply (div_le_iff₀ s.bandwidth_pos).mpr
  have ht := mul_le_mul_of_nonneg_right hq s.bandwidth_pos.le
  nlinarith

end
end RectangleCLTArxivV1
