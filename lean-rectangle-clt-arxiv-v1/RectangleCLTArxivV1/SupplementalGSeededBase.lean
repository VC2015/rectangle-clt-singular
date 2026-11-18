import RectangleCLTArxivV1.SupplementalGProjectionModel
import RectangleCLT.ThinnedHypotheses
import RectangleCLTCompanion.SplitV4.SeededGaussianSplit

/-! Actual projected bounded-plus-Gaussian constructors for Supplemental G.
The retained array is averaged under its full unconditional mask law. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def capSignedFactor {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ) (f g : Face p) :
    Matrix (Fin 2) (Fin r) ℝ := ![capRectangularFactorNormal A f,capRectangularFactorNormal A g]

theorem capSignedFactor_mulVec {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (f g : Face p) (z : Vector r) :
    (capSignedFactor A f g).mulVec z = capSignedProjection f g (A.mulVec z) := by
  ext j
  fin_cases j <;> simp only [capSignedFactor,capSignedProjection,Matrix.mulVec,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact (cap_rectangular_normalDot_factor A f z).symm
  · exact (cap_rectangular_normalDot_factor A g z).symm

theorem capSignedFactor_gram {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (hdiag : ∀ j, (A*A.transpose) j j = 1) (f g : Face p) :
    (capSignedFactor A f g)*(capSignedFactor A f g).transpose =
      !![1,faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g);
        faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g),1] := by
  have hu := capRectangularFactorNormal_unit A hdiag f
  have hv := capRectangularFactorNormal_unit A hdiag g
  change (∑ j, (capRectangularFactorNormal A f j)^2)=1 at hu
  change (∑ j, (capRectangularFactorNormal A g j)^2)=1 at hv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply,Matrix.transpose_apply,capSignedFactor,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  · simpa only [← pow_two] using hu
  · rfl
  · exact faceDot_comm _ _
  · simpa only [← pow_two] using hv

/-- Actual projected covariance from the original covariance Gram factor. -/
theorem capSignedProjection_covariance_scaledGram
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ} (μ : Measure Ω)
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin r) ℝ)
    (hdiag : ∀ j, (A*A.transpose) j j = 1) {a : ℝ}
    (hcov : covariance μ (sumVector ξ) = a • (A*A.transpose)) (f g : Face p) :
    covariance μ (sumVector (fun i ω => capSignedProjection f g (ξ i ω))) =
      !![a,a*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g);
        a*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g),a] := by
  have he : sumVector (fun i ω => capSignedProjection f g (ξ i ω)) =
      fun ω => capSignedProjection f g (sumVector ξ ω) := funext (capSignedProjection_sum f g ξ)
  rw [he]
  have h00 : covariance μ (fun ω => capSignedProjection f g (sumVector ξ ω)) 0 0 = a := by
    rw [capSignedProjection_covariance_zero_zero,hcov]
    simp only [Matrix.smul_apply,smul_eq_mul,hdiag,mul_one]
  have h11 : covariance μ (fun ω => capSignedProjection f g (sumVector ξ ω)) 1 1 = a := by
    rw [capSignedProjection_covariance_one_one,hcov]
    simp only [Matrix.smul_apply,smul_eq_mul,hdiag,mul_one]
  have h01 : covariance μ (fun ω => capSignedProjection f g (sumVector ξ ω)) 0 1 =
      a*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g) := by
    rw [capSignedProjection_covariance_zero_one,hcov,capRectangularFactorNormal_gram]
    simp only [Matrix.smul_apply,smul_eq_mul]
    ring
  have h10 : covariance μ (fun ω => capSignedProjection f g (sumVector ξ ω)) 1 0 =
      a*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g) := by
    have hs := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1)
      (covariance_transpose μ (fun ω => capSignedProjection f g (sumVector ξ ω)))
    simpa only [Matrix.transpose_apply,h01] using hs
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- The true mixed covariance of the projected raw array and independent
Gaussian factor. No covariance or concentration supplier is assumed. -/
theorem cap_signed_mixed_covariance
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ} (μ : Measure Ω)
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin r) ℝ)
    (hdiag : ∀ j, (A*A.transpose) j j = 1) {a : ℝ}
    (hcov : covariance μ (sumVector ξ) = a • (A*A.transpose)) (σ : ℝ) (f g : Face p) :
    capMixedCovariance μ (fun i ω => capSignedProjection f g (ξ i ω)) (σ • capSignedFactor A f g) =
      !![a+σ^2,(a+σ^2)*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g);
        (a+σ^2)*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g),a+σ^2] := by
  unfold capMixedCovariance
  rw [capSignedProjection_covariance_scaledGram μ ξ A hdiag hcov f g,
    Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,capSignedFactor_gram A hdiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] <;> ring

/-- Exact projection of an actual mixed-value process, including singular
rectangular factors. -/
theorem cap_signed_mixed_value
    {Ω : Type*} {p r n : ℕ} (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (f g : Face p) (z : Ω × Vector r) :
    capMixedValue (fun i ω => capSignedProjection f g (ξ i ω)) (σ • capSignedFactor A f g) z =
      capSignedProjection f g (sumVector ξ z.1+(σ • A).mulVec z.2) := by
  unfold capMixedValue
  rw [capSignedProjection_sum,Matrix.smul_mulVec_assoc,capSignedFactor_mulVec,Matrix.smul_mulVec_assoc]
  ext j
  fin_cases j <;> simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,capSignedProjection,
    Matrix.cons_val_zero,Matrix.cons_val_one,normalDot_add]
  all_goals unfold normalDot; split <;> simp [smul_eq_mul]

/-- The projected retained/rescaled array has envelope2δ under its actual
unconditional mask law. -/
theorem cap_seeded_projection_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (f g : Face p) :
    BoundedIndependentHypotheses (bernoulliArrayLaw μ ξ t)
      (fun i b => capSignedProjection f g (b i)) (2*δ) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  exact capSignedProjection_hypotheses (h.thinned t ht ht1) f g

/-- Generic actual covariance for the projected retained array plus a
rectangular independent Gaussian image. -/
theorem cap_thinned_mixed_covariance
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (σ : ℝ) (f g : Face p) :
    capMixedCovariance (bernoulliArrayLaw μ ξ t)
      (fun i b => capSignedProjection f g (b i)) (σ • capSignedFactor A f g) =
      !![1-t+σ^2,(1-t+σ^2)*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g);
        (1-t+σ^2)*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g),1-t+σ^2] := by
  have hc : covariance (bernoulliArrayLaw μ ξ t) (sumVector (fun i b => b i)) =
      (1-t) • (A*A.transpose) := by rw [h.thinned_sum_covariance t ht ht1,← hA]
  exact cap_signed_mixed_covariance (p := p) (r := r) (n := n) (bernoulliArrayLaw μ ξ t)
    (fun i (b : Fin n → Vector p) => b i) A hdiag hc σ f g

/-- The actual G0 half-base covariance scalar. -/
theorem cap_seededSplit_mixed_covariance
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hdiag : ∀ j, (A*A.transpose) j j = 1)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) (f g : Face p) :
    capMixedCovariance (bernoulliArrayLaw μ ξ t)
      (fun i b => capSignedProjection f g (b i)) (seededSplitGaussianScale ε t • capSignedFactor A f g) =
      !![1-t/2+ε/2,(1-t/2+ε/2)*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g);
        (1-t/2+ε/2)*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g),1-t/2+ε/2] := by
  have he : 1-t+(seededSplitGaussianScale ε t)^2 = 1-t/2+ε/2 := by
    rw [seededSplitGaussianScale_sq hε ht]
    ring
  simpa only [he] using cap_thinned_mixed_covariance h A hA hdiag t ht ht1 (seededSplitGaussianScale ε t) f g

/-- The true whole seeded point has covariance(1+ε)Σ. -/
theorem cap_seededWhole_mixed_covariance
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hdiag : ∀ j, (A*A.transpose) j j = 1)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) (f g : Face p) :
    capMixedCovariance (bernoulliArrayLaw μ ξ t)
      (fun i b => capSignedProjection f g (b i)) (Real.sqrt (t+ε) • capSignedFactor A f g) =
      !![1+ε,(1+ε)*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g);
        (1+ε)*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g),1+ε] := by
  have he : 1-t+(Real.sqrt (t+ε))^2 = 1+ε := by
    rw [Real.sq_sqrt (add_nonneg ht hε)]
    ring
  simpa only [he] using cap_thinned_mixed_covariance h A hA hdiag t ht ht1 (Real.sqrt (t+ε)) f g

theorem cap_seededSplit_variance_band {ε t : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1/2 : ℝ) ≤ 1-t/2+ε/2 ∧ 1-t/2+ε/2 ≤ 9/8 := by constructor <;> linarith

theorem cap_signed_mixed_projection_zero
    {Ω : Type*} {p r n : ℕ} (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (f g : Face p) (x : Vector p) (z : Ω × Vector r) :
    normalDot f (x+sumVector ξ z.1+(σ • A).mulVec z.2) =
      capMixedValue (fun i ω => capSignedProjection f g (ξ i ω)) (σ • capSignedFactor A f g) z 0+normalDot f x := by
  have hp := congrArg (fun y : Vector 2 => y 0) (cap_signed_mixed_value ξ A σ f g z)
  change capMixedValue (fun i ω => capSignedProjection f g (ξ i ω)) (σ • capSignedFactor A f g) z 0 =
    normalDot f (sumVector ξ z.1+(σ • A).mulVec z.2) at hp
  rw [hp,normalDot_add,normalDot_add,normalDot_add]
  ring

theorem cap_signed_mixed_projection_one
    {Ω : Type*} {p r n : ℕ} (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (f g : Face p) (x : Vector p) (z : Ω × Vector r) :
    normalDot g (x+sumVector ξ z.1+(σ • A).mulVec z.2) =
      capMixedValue (fun i ω => capSignedProjection f g (ξ i ω)) (σ • capSignedFactor A f g) z 1+normalDot g x := by
  have hp := congrArg (fun y : Vector 2 => y 1) (cap_signed_mixed_value ξ A σ f g z)
  change capMixedValue (fun i ω => capSignedProjection f g (ξ i ω)) (σ • capSignedFactor A f g) z 1 =
    normalDot g (sumVector ξ z.1+(σ • A).mulVec z.2) at hp
  rw [hp,normalDot_add,normalDot_add,normalDot_add]
  ring

/-- Actual one-face mass for the entire retained array and an independent
rectangular Gaussian image, with no native-model supplier premise. -/
theorem cap_thinned_single_face_mass
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (σ : ℝ) (hvar : (1/2:ℝ) ≤ 1-t+σ^2)
    (s : FaceSmoother p) (hband : 2*δ ≤ s.bandwidth) (f : Face p) (x : Vector p) :
    (∫ z, selectorTupleWeight s ![f] (x+arraySum z.1+(σ • A).mulVec z.2)
      ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) ≤
      16*Real.exp (1/2)*s.bandwidth*Real.sqrt (Real.pi/capGaussianExponent) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  have hd := cap_seeded_projection_hypotheses h t ht ht1 f f
  have hcov := cap_thinned_mixed_covariance h A hA hdiag t ht ht1 σ f f
  have hvar' : (1/2:ℝ) ≤ capMixedCovariance (bernoulliArrayLaw μ ξ t)
      (fun i b => capSignedProjection f f (b i)) (σ • capSignedFactor A f f) 0 0 := by
    rw [hcov]
    simpa using hvar
  apply cap_original_single_face_mass hd (σ • capSignedFactor A f f) hvar' s hband f
    (fun z => x+arraySum z.1+(σ • A).mulVec z.2)
    (by
      exact (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
        ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd)) (normalDot f x)
  intro z
  exact cap_signed_mixed_projection_zero (fun i b => b i) A σ f f x z

/-- Actual two-face mass for the retained array and independent Gaussian.
The only angle premise concerns the genuine signed factor rows. -/
theorem cap_thinned_pair_face_mass
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (σ : ℝ) (hvar : (1/2:ℝ) ≤ 1-t+σ^2)
    (s : FaceSmoother p) (hband : 4*δ ≤ s.bandwidth) (f g : Face p)
    (hρ : (faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g))^2 < 1)
    (x : Vector p) :
    (∫ z, selectorTupleWeight s ![f,g] (x+arraySum z.1+(σ • A).mulVec z.2)
      ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) ≤
      64*Real.exp 1*Real.pi^3*s.bandwidth^2/
        Real.sqrt (1-(faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g))^2) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  have hd := cap_seeded_projection_hypotheses h t ht ht1 f g
  have hcov := cap_thinned_mixed_covariance h A hA hdiag t ht ht1 σ f g
  apply cap_original_pair_face_mass hd (σ • capSignedFactor A f g) hvar hρ hcov s
    (by linarith) f g (fun z => x+arraySum z.1+(σ • A).mulVec z.2)
    (by
      exact (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
        ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd)) (normalDot f x) (normalDot g x)
  · intro z
    exact cap_signed_mixed_projection_zero (fun i b => b i) A σ f g x z
  · intro z
    exact cap_signed_mixed_projection_one (fun i b => b i) A σ f g x z

/-- The half-base one-face mass under the exact archived seeded base law. -/
theorem cap_seededSplitBase_single_mass
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hdiag : ∀ j, (A*A.transpose) j j = 1)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (s : FaceSmoother p) (hband : 2*δ ≤ s.bandwidth) (f : Face p) (x : Vector p) :
    (∫ y, selectorTupleWeight s ![f] y ∂seededSplitBaseDistribution μ ξ A x ε t) ≤
      16*Real.exp (1/2)*s.bandwidth*Real.sqrt (Real.pi/capGaussianExponent) := by
  have hv : (1/2:ℝ) ≤ 1-t+(seededSplitGaussianScale ε t)^2 := by
    rw [seededSplitGaussianScale_sq hε ht]
    linarith
  have ht' := cap_thinned_single_face_mass h A hA hdiag t ht ht1 (seededSplitGaussianScale ε t) hv s hband f x
  unfold seededSplitBaseDistribution
  have hm : Measurable (selectorTupleWeight s ![f]) := by
    simpa only [id_eq] using measurable_selectorTupleWeight_comp s ![f] id measurable_id
  rw [integral_map (measurable_seededSplitBaseValue A x ε t).aemeasurable hm.aestronglyMeasurable]
  exact ht'

/-- The half-base pair mass under the exact archived seeded base law. -/
theorem cap_seededSplitBase_pair_mass
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hdiag : ∀ j, (A*A.transpose) j j = 1)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (s : FaceSmoother p) (hband : 4*δ ≤ s.bandwidth) (f g : Face p)
    (hρ : (faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g))^2 < 1)
    (x : Vector p) :
    (∫ y, selectorTupleWeight s ![f,g] y ∂seededSplitBaseDistribution μ ξ A x ε t) ≤
      64*Real.exp 1*Real.pi^3*s.bandwidth^2/
        Real.sqrt (1-(faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g))^2) := by
  have hv : (1/2:ℝ) ≤ 1-t+(seededSplitGaussianScale ε t)^2 := by
    rw [seededSplitGaussianScale_sq hε ht]
    linarith
  have ht' := cap_thinned_pair_face_mass h A hA hdiag t ht ht1 (seededSplitGaussianScale ε t) hv s hband f g hρ x
  unfold seededSplitBaseDistribution
  have hm : Measurable (selectorTupleWeight s ![f,g]) := by
    simpa only [id_eq] using measurable_selectorTupleWeight_comp s ![f,g] id measurable_id
  rw [integral_map (measurable_seededSplitBaseValue A x ε t).aemeasurable hm.aestronglyMeasurable]
  exact ht'

/-- The whole actual retained-plus-Gaussian process is the seeded path law,
including an arbitrary deterministic center. -/
theorem cap_seededWhole_map_law
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ((bernoulliArrayLaw μ ξ t).prod (standardGaussian p)).map
      (fun z => x+arraySum z.1+(Real.sqrt (t+ε) • A).mulVec z.2) =
      (seededInterpolationLaw μ ξ A ε t).map (fun y => x+y) := by
  let B := bernoulliArrayLaw μ ξ t
  let M := Real.sqrt (t+ε) • A
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  letI : IsProbabilityMeasure (B.map arraySum) := isProbabilityMeasure_map (measurable_arraySum p n).aemeasurable
  have hseed := seededInterpolationLaw_eq_shifted_heat μ ξ hξ A hε ht ht1
  change seededInterpolationLaw μ ξ A ε t = Measure.conv (B.map arraySum) (gaussianLaw M) at hseed
  have hshift : (B.map arraySum).map (fun y => x+y) = B.map (fun b => x+arraySum b) :=
    Measure.map_map (measurable_const.add measurable_id) (measurable_arraySum p n)
  calc
    _ = Measure.conv (B.map (fun b => x+arraySum b)) (gaussianLaw M) :=
      map_sum_standardGaussian_factor B _ (measurable_const.add (measurable_arraySum p n)) M
    _ = (Measure.conv (B.map arraySum) (gaussianLaw M)).map (fun y => x+y) := by
      rw [map_add_left_conv,hshift]
    _ = _ := by rw [hseed]

end
end RectangleCLTArxivV1
