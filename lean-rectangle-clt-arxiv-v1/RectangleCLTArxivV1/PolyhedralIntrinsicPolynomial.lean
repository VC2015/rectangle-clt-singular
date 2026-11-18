import RectangleCLTArxivV1.PolyhedralIntrinsicZeroFaces
import RectangleCLTArxivV1.TransfersMain

/-! The envelope and fourth-moment parts of Corollary 3, at the exact
scales `JB` and `J²B`, respectively. The common constant is chosen before
all dimensions, arrays, probability models and normal vectors. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
universe u

def PolyhedralPolynomialEnvelopeBound (q C : ℝ) : Prop :=
  ∀ (p m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ B : ℝ, 1 ≤ B →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p), PolynomialEnvelopeHypotheses μ X q B →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose=covariance μ (normalizedObservationSum X) →
  ∀ (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ),
    (∀ α, 0 < σ α) → 1 ≤ J → (∀ α, (∑ j, |ν α j|)≤J*σ α) →
    (∀ α, dotProduct (ν α) ((covariance μ (normalizedObservationSum X)).mulVec (ν α))=(σ α)^2) →
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤ C*
      min 1 (polynomialEnvelopeWidthRate n m (J*B) q
        (projectedGaussianMean A (standardizedFaceMap ν σ)))

def PolyhedralPolynomialFourthBound (q C : ℝ) : Prop :=
  ∀ (p m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ B : ℝ, 1 ≤ B →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p), PolynomialFourthHypotheses μ X q B →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose=covariance μ (normalizedObservationSum X) →
  ∀ (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ),
    (∀ α, 0 < σ α) → 1 ≤ J → (∀ α, (∑ j, |ν α j|)≤J*σ α) →
    (∀ α, dotProduct (ν α) ((covariance μ (normalizedObservationSum X)).mulVec (ν α))=(σ α)^2) →
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤ C*
      min 1 (polynomialFourthWidthRate n m (J^2*B) q
        (projectedGaussianMean A (standardizedFaceMap ν σ)))

/-- Envelope-only polynomial projection, including its actual covariance
factor, unit variances, Gaussian width and original polyhedral distance. -/
theorem polynomialPolyhedralEnvelope_inputs
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p) {q B : ℝ} (hq : 2 < q) (hB : 1 ≤ B)
    (h : PolynomialEnvelopeHypotheses μ X q B)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (normalizedObservationSum X))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 1 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|)≤J*σ α)
    (hvariance : ∀ α, dotProduct (ν α) ((covariance μ (normalizedObservationSum X)).mulVec (ν α))=(σ α)^2) :
    let M := standardizedFaceMap ν σ
    let Y := fun i ω => M.mulVec (X i ω)
    PolynomialEnvelopeHypotheses μ Y q (J*B) ∧
    ∃ C : Matrix (Fin m) (Fin m) ℝ,
      C*C.transpose=covariance μ (normalizedObservationSum Y) ∧
      gaussianMaximumMean C=projectedGaussianMean A M ∧
      polyhedralDistance μ (normalizedObservationSum X) A ν≤
        rectangleDistance μ (normalizedObservationSum Y) C := by
  let M := standardizedFaceMap ν σ
  let Y := fun i ω => M.mulVec (X i ω)
  have hM := standardizedFaceMap_row_l1_le ν σ J hσ hν
  have hunit := standardizedFaceMap_covariance_unit_diagonal ν σ
    (covariance μ (normalizedObservationSum X)) hσ hvariance
  have hY := h.projected hq (zero_le_one.trans hB) M (zero_le_one.trans hJ) hM hunit
  obtain ⟨C,hC⟩ := hY.gaussian_factor_exists hq
  have hgram : C*C.transpose=M*(A*A.transpose)*M.transpose := by
    rw [hA]
    exact hC.trans (h.projected_covariance hq M)
  refine ⟨hY,C,hC,gaussianMaximumMean_projected M A C hgram,?_⟩
  have hd := polyhedralDistance_le_standardizedRectangleDistance μ (normalizedObservationSum X) A C ν σ hσ hgram
  rw [normalizedObservationSum_mulVec]
  exact hd

/-- The printed dimension bound for the actual standardized projected
width. It follows from unit marginal variance, without a rank condition. -/
theorem polynomialPolyhedralWidth_le
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : 1 ≤ m)
    (X : Fin n → Ω → Vector p) {q B : ℝ} (hq : 2 < q) (hB : 1 ≤ B)
    (h : PolynomialEnvelopeHypotheses μ X q B)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (normalizedObservationSum X))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 1 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|)≤J*σ α)
    (hvariance : ∀ α, dotProduct (ν α) ((covariance μ (normalizedObservationSum X)).mulVec (ν α))=(σ α)^2) :
    projectedGaussianMean A (standardizedFaceMap ν σ)≤2*Real.sqrt (dimensionLog m) := by
  obtain ⟨hY,C,hC,hwidth,_⟩ := polynomialPolyhedralEnvelope_inputs μ X hq hB h A hA ν σ J hσ hJ hν hvariance
  rw [←hwidth]
  exact gaussianLaw_integral_norm_le hm C (fun α => by rw [hC]; exact hY.unit_covariance hq α)

/-- Both polynomial claims in Corollary 3 follow from the newly checked
Theorem 2; its rate is recomputed at each exact substituted parameter. -/
theorem polynomialPolyhedralCLT_intrinsic (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 0 < C ∧ PolyhedralPolynomialEnvelopeBound.{u} q C ∧
      PolyhedralPolynomialFourthBound.{u} q C := by
  obtain ⟨C,hC,hEnv,hFourth⟩ := theorem_2_intrinsic.{u} q hq
  refine ⟨C,hC,?_,?_⟩
  · intro p m n hm hn B hB Ω mΩ μ hprob X hX A hA ν σ J hσ hJ hν hvariance
    obtain ⟨hY,D,hD,hwidth,hd⟩ := polynomialPolyhedralEnvelope_inputs μ X hq hB hX A hA ν σ J hσ hJ hν hvariance
    have hJB : 1 ≤ J*B := hJ.trans (le_mul_of_one_le_right (zero_le_one.trans hJ) hB)
    have hh := hEnv m n hm hn (J*B) hJB μ _ hY D hD
    rw [hwidth] at hh
    exact hd.trans hh
  · intro p m n hm hn B hB Ω mΩ μ hprob X hX A hA ν σ J hσ hJ hν hvariance
    let M := standardizedFaceMap ν σ
    let Y := fun i ω => M.mulVec (X i ω)
    have hM := standardizedFaceMap_row_l1_le ν σ J hσ hν
    have hunit := standardizedFaceMap_covariance_unit_diagonal ν σ
      (covariance μ (normalizedObservationSum X)) hσ hvariance
    have hY := hX.projected hq (zero_le_one.trans hB) M hJ hM hunit
    obtain ⟨_,D,hD,hwidth,hd⟩ := polynomialPolyhedralEnvelope_inputs μ X hq hB hX.toPolynomialEnvelopeHypotheses A hA ν σ J hσ hJ hν hvariance
    have hJJB : 1 ≤ J^2*B := (one_le_pow₀ hJ).trans (le_mul_of_one_le_right (sq_nonneg J) hB)
    have hh := hFourth m n hm hn (J^2*B) hJJB μ Y hY D hD
    rw [hwidth] at hh
    exact hd.trans hh


def PolyhedralAllFacesEnvelopeBound (q C : ℝ) : Prop :=
  ∀ (p m n : ℕ), 1 ≤ n → ∀ B : ℝ, 1 ≤ B →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p), PolynomialEnvelopeHypotheses μ X q B →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose=covariance μ (normalizedObservationSum X) →
  ∀ (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ), 1 ≤ J → PolyhedralNormalBound A ν J →
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤ C*
      min 1 (polynomialEnvelopeWidthRate n (positivePolyhedralFaceCount A ν) (J*B) q
        (polyhedralIntrinsicWidth A ν))

def PolyhedralAllFacesFourthBound (q C : ℝ) : Prop :=
  ∀ (p m n : ℕ), 1 ≤ n → ∀ B : ℝ, 1 ≤ B →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p), PolynomialFourthHypotheses μ X q B →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose=covariance μ (normalizedObservationSum X) →
  ∀ (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ), 1 ≤ J → PolyhedralNormalBound A ν J →
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤ C*
      min 1 (polynomialFourthWidthRate n (positivePolyhedralFaceCount A ν) (J^2*B) q
        (polyhedralIntrinsicWidth A ν))

def PolyhedralAllFacesCombinedBound (q C : ℝ) : Prop :=
  ∀ (p m n : ℕ), 1 ≤ n → ∀ B : ℝ, 1 ≤ B →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p), PolynomialFourthHypotheses μ X q B →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ), A*A.transpose=covariance μ (normalizedObservationSum X) →
  ∀ (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ), 1 ≤ J → PolyhedralNormalBound A ν J →
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤ C*min 1
      (min (polynomialEnvelopeWidthRate n (positivePolyhedralFaceCount A ν) (J*B) q
        (polyhedralIntrinsicWidth A ν))
      (polynomialFourthWidthRate n (positivePolyhedralFaceCount A ν) (J^2*B) q
        (polyhedralIntrinsicWidth A ν)))

/-- Ordinary finite second moments and centering of the actual normalized
sum, for use in the exact zero-face probability identities. -/
theorem PolynomialEnvelopeHypotheses.normalized_sum_L2_centered
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {q B : ℝ} (h : PolynomialEnvelopeHypotheses μ X q B) (hq : 2 < q) :
    (∀ j, MemLp (fun ω => normalizedObservationSum X ω j) 2 μ) ∧
    (∀ j, (∫ ω, normalizedObservationSum X ω j ∂μ)=0) := by
  constructor
  · simpa only [sumVector_normalizedSummands] using
      memLp_sumVector_coordinate (normalizedSummands_coordinate_memLp_two (h.coordinate_memLp_two hq))
  · simpa only [sumVector_normalizedSummands] using
      integral_sumVector_coordinate_zero
        (fun i j => ((normalizedSummands_coordinate_memLp_two (h.coordinate_memLp_two hq) i j).integrable
          (by norm_num))) (normalizedSummands_centered h.centered)

/-- The polynomial conclusions include arbitrary zero-variance and empty
face families, selected and standardized from the actual covariance. -/
theorem polynomialPolyhedralCLT_all_faces_intrinsic (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 0 < C ∧ PolyhedralAllFacesEnvelopeBound.{u} q C ∧
      PolyhedralAllFacesFourthBound.{u} q C ∧ PolyhedralAllFacesCombinedBound.{u} q C := by
  obtain ⟨C,hC,hEnv,hFourth⟩ := polynomialPolyhedralCLT_intrinsic.{u} q hq
  have hEnvAll : PolyhedralAllFacesEnvelopeBound.{u} q C := by
    intro p m n hn B hB Ω mΩ μ hprob X hX A hA ν J hJ hν
    obtain ⟨hL2,hc⟩ := hX.normalized_sum_L2_centered hq
    by_cases hk : positivePolyhedralFaceCount A ν=0
    · have hd := polyhedralDistance_zero_of_no_positive_faces μ (normalizedObservationSum X) A hL2 hc hA ν hk
      have hg := polyhedralIntrinsicWidth_zero_of_no_positive_faces A ν hk
      simp [hd,hg,polynomialEnvelopeWidthRate]
    · have hpos : 1 ≤ positivePolyhedralFaceCount A ν := by omega
      rw [polyhedralDistance_eq_positive_faces μ (normalizedObservationSum X) A hL2 hc hA ν]
      exact hEnv p (positivePolyhedralFaceCount A ν) n hpos hn B hB μ X hX A hA
        (positivePolyhedralFaceNormals A ν) (positivePolyhedralFaceScale A ν) J
        (positivePolyhedralFaceScale_pos A ν) hJ hν.positive_faces
        (positivePolyhedralFace_variance_identity μ (normalizedObservationSum X) A hA ν)
  have hFourthAll : PolyhedralAllFacesFourthBound.{u} q C := by
    intro p m n hn B hB Ω mΩ μ hprob X hX A hA ν J hJ hν
    obtain ⟨hL2,hc⟩ := hX.toPolynomialEnvelopeHypotheses.normalized_sum_L2_centered hq
    by_cases hk : positivePolyhedralFaceCount A ν=0
    · have hd := polyhedralDistance_zero_of_no_positive_faces μ (normalizedObservationSum X) A hL2 hc hA ν hk
      have hg := polyhedralIntrinsicWidth_zero_of_no_positive_faces A ν hk
      simp [hd,hg,polynomialFourthWidthRate]
    · have hpos : 1 ≤ positivePolyhedralFaceCount A ν := by omega
      rw [polyhedralDistance_eq_positive_faces μ (normalizedObservationSum X) A hL2 hc hA ν]
      exact hFourth p (positivePolyhedralFaceCount A ν) n hpos hn B hB μ X hX A hA
        (positivePolyhedralFaceNormals A ν) (positivePolyhedralFaceScale A ν) J
        (positivePolyhedralFaceScale_pos A ν) hJ hν.positive_faces
        (positivePolyhedralFace_variance_identity μ (normalizedObservationSum X) A hA ν)
  refine ⟨C,hC,hEnvAll,hFourthAll,?_⟩
  intro p m n hn B hB Ω mΩ μ hprob X hX A hA ν J hJ hν
  exact le_common_capped_min_of_two
    (hEnvAll p m n hn B hB μ X hX.toPolynomialEnvelopeHypotheses A hA ν J hJ hν)
    (hFourthAll p m n hn B hB μ X hX A hA ν J hJ hν)

/-- The canonical width obeys the same bound even when no face remains. -/
theorem polynomialPolyhedralWidth_all_faces_le
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin n → Ω → Vector p) {q B : ℝ} (hq : 2 < q) (hB : 1 ≤ B)
    (h : PolynomialEnvelopeHypotheses μ X q B)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (normalizedObservationSum X))
    (ν : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 1 ≤ J) (hν : PolyhedralNormalBound A ν J) :
    polyhedralIntrinsicWidth A ν≤2*Real.sqrt (dimensionLog (positivePolyhedralFaceCount A ν)) := by
  by_cases hk : positivePolyhedralFaceCount A ν=0
  · rw [polyhedralIntrinsicWidth_zero_of_no_positive_faces A ν hk]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  · have hpos : 1 ≤ positivePolyhedralFaceCount A ν := by omega
    exact polynomialPolyhedralWidth_le μ hpos X hq hB h A hA
      (positivePolyhedralFaceNormals A ν) (positivePolyhedralFaceScale A ν) J
      (positivePolyhedralFaceScale_pos A ν) hJ hν.positive_faces
      (positivePolyhedralFace_variance_identity μ (normalizedObservationSum X) A hA ν)

end
end RectangleCLTArxivV1
