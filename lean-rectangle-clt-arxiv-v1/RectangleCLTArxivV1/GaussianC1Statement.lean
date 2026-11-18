import RectangleCLTArxivV1.IntrinsicGaussianBoundary
import RectangleCLTArxivV1.ChainingComparison
import RectangleCLTArxivV1.GaussianCalibration
import RectangleCLT.InterpolationCovariance

/-! Gaussian part of Lemma 1 with the actual opposite-paired face family.
The Gaussian model is the pushforward by a possibly singular square factor.
Using this ambient model instead of a rank-dimensional factor changes no
projection equation or Gaussian law. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT
open RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable section

/-- The concrete Gaussian law has exactly its factor Gram covariance,
including singular factors and arbitrary measurable presentations. -/
theorem gaussianModel_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {r : ℕ} (V : Ω → Vector r) (hV : Measurable V)
    (A : Matrix (Fin r) (Fin r) ℝ) (hLaw : μ.map V = gaussianLaw A) :
    covariance μ V = A*A.transpose := by
  rw [← covariance_map μ V hV, hLaw, covariance_gaussianLaw]

/-- The ambient factor representation is supported on its actual range;
zero eigenvalues impose no invertibility requirement. -/
theorem gaussianModel_supported_on_factor_range {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {r : ℕ} (V : Ω → Vector r) (hV : Measurable V)
    (A : Matrix (Fin r) (Fin r) ℝ) (hLaw : μ.map V = gaussianLaw A) :
    ∀ᵐ ω ∂μ, V ω ∈ Set.range A.mulVec := by
  have hh := gaussianLaw_ae_mem_factor_range A
  rw [← hLaw] at hh
  exact (ae_map_iff hV.aemeasurable (by
    exact (LinearMap.range (Matrix.mulVecLin A)).closed_of_finiteDimensional.measurableSet)).mp hh

/-- The smallest threshold among rows equal to a chosen normal. -/
def mergedGaussianThreshold {m r : ℕ} (w : Fin m → Vector r) (a : Fin m → ℝ)
    (α : Fin m) : ℝ := by
  classical
  exact (Finset.univ.filter (fun β => w β = w α)).inf'
    ⟨α, by simp⟩ a

theorem mergedGaussianThreshold_le {m r : ℕ} (w : Fin m → Vector r)
    (a : Fin m → ℝ) (α : Fin m) : mergedGaussianThreshold w a α ≤ a α := by
  classical
  exact Finset.inf'_le _ (by simp)

theorem mergedGaussianThreshold_attains {m r : ℕ} (w : Fin m → Vector r)
    (a : Fin m → ℝ) (α : Fin m) :
    ∃ β, w β = w α ∧ mergedGaussianThreshold w a α = a β := by
  classical
  obtain ⟨β, hβ, he⟩ := Finset.exists_mem_eq_inf'
    (s := Finset.univ.filter (fun β => w β = w α)) ⟨α, by simp⟩ a
  exact ⟨β, (Finset.mem_filter.mp hβ).2, he⟩

/-- Replacing every duplicate normal's threshold by its class minimum
preserves the affine maximum pointwise. This is the threshold-merging step
that precedes deletion of repeated identical affine functions in the paper. -/
theorem gaussianAffineMaximum_merge_thresholds {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ) (x : Vector r) :
    gaussianAffineMaximum w (mergedGaussianThreshold w a) x = gaussianAffineMaximum w a x := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro α _
    obtain ⟨β, hβ, he⟩ := mergedGaussianThreshold_attains w a α
    rw [he, ← hβ]
    exact affineBranch_le_gaussianAffineMaximum w a x β
  · apply Finset.sup'_le
    intro α _
    exact (sub_le_sub_left (mergedGaussianThreshold_le w a α) _).trans
      (affineBranch_le_gaussianAffineMaximum w (mergedGaussianThreshold w a) x α)

/-- Opposite rows turn the positive maximum of linear forms into the
maximum absolute projection used in the paper. -/
theorem positiveGaussianFaceMaximum_eq_projection_norm {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (hopposite : ∀ α, ∃ β, w β = -w α) (x : Vector r) :
    positiveGaussianFaceMaximum w x = ‖linearProjectionFamily w x‖ := by
  apply le_antisymm (positiveGaussianFaceMaximum_le_projection_norm w x)
  apply (pi_norm_le_iff_of_nonneg (positiveGaussianFaceMaximum_nonneg w x)).mpr
  intro α
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · obtain ⟨β, hβ⟩ := hopposite α
    have hb := faceDot_le_positiveGaussianFaceMaximum w x β
    rw [hβ] at hb
    simp only [faceDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at hb
    change -positiveGaussianFaceMaximum w x ≤ faceDot (w α) x
    dsimp only [faceDot]
    linarith
  · exact faceDot_le_positiveGaussianFaceMaximum w x α

theorem normalizedGaussianFaceRows_opposite {p m : ℕ}
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ) (v : ℝ)
    (hopposite : ∀ α, ∃ β, ν β = -ν α) :
    ∀ α, ∃ β, normalizedGaussianFaceRows ν A v β = -normalizedGaussianFaceRows ν A v α := by
  intro α
  obtain ⟨β, hβ⟩ := hopposite α
  refine ⟨β, ?_⟩
  ext j
  simp [normalizedGaussianFaceRows, Matrix.mul_apply, hβ, Finset.sum_neg_distrib, neg_div]

/-- Actual expected projection norm, before weakening the face count. -/
theorem gaussianFaceNorm_mean_le_sharp {p m : ℕ} [NeZero m]
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : 0 < v)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v)
    (hopposite : ∀ α, ∃ β, ν β = -ν α) :
    (∫ x, ‖ν.mulVec x‖ ∂gaussianLaw A) ≤
      Real.sqrt v * Real.sqrt (2*Real.log ((m : ℝ)+1)) := by
  have hmean := gaussianUnitRowsMaximum_logarithmic (normalizedGaussianFaceRows ν A v)
    (normalizedGaussianFaceRows_unit ν A hv hvariance)
  simp_rw [positiveGaussianFaceMaximum_eq_projection_norm _
    (normalizedGaussianFaceRows_opposite ν A v hopposite)] at hmean
  rw [normalizedGaussianFaceRows_integral_projection_norm ν A hv] at hmean
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hv)).mp hmean |>.trans_eq (mul_comm _ _)

/-- At most `2p` faces have logarithm at most `2 log(ep)`, including `p=1`. -/
theorem face_log_le_two_dimensionLog {p m : ℕ} (hp : 1 ≤ p) (hm : m ≤ 2*p) :
    Real.log ((m : ℝ)+1) ≤ 2*dimensionLog p := by
  have hcard : (m : ℝ)+1 ≤ ((2*p+1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hm 1
  exact (Real.log_le_log (by positivity) hcard).trans (signed_card_log_le_dimensionLog hp)

theorem gaussianFaceNorm_mean_le_dimension {r m : ℕ} [NeZero m]
    (ν : Matrix (Fin m) (Fin r) ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (p : ℕ) (hp : 1 ≤ p) (hm : m ≤ 2*p) {v : ℝ} (hv : 0 < v)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v)
    (hopposite : ∀ α, ∃ β, ν β = -ν α) :
    (∫ x, ‖ν.mulVec x‖ ∂gaussianLaw A) ≤ 2*Real.sqrt (v*dimensionLog p) := by
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hlog := face_log_le_two_dimensionLog hp hm
  have hsqrt : Real.sqrt (2*Real.log ((m : ℝ)+1)) ≤ 2*Real.sqrt (dimensionLog p) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hL]
      linarith
  have hh := (gaussianFaceNorm_mean_le_sharp ν A hv hvariance hopposite).trans
    (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg v))
  rw [Real.sqrt_mul hv.le]
  convert hh using 1 <;> ring

/-- The second inequality in the Gaussian assertion of Lemma 1 bounds the
intrinsic coefficient itself, rather than only giving a separate event bound. -/
theorem gaussianFaceNorm_intrinsic_coefficient_le {r m : ℕ} [NeZero m]
    (ν : Matrix (Fin m) (Fin r) ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (p : ℕ) (hp : 1 ≤ p) (hm : m ≤ 2*p) {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v)
    (hopposite : ∀ α, ∃ β, ν β = -ν α) :
    min 1 ((2*s/v)*(∫ x, ‖ν.mulVec x‖ ∂gaussianLaw A)) ≤
      4*min 1 (s*Real.sqrt (dimensionLog p/v)) := by
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hm := gaussianFaceNorm_mean_le_dimension ν A p hp hm hv hvariance hopposite
  have hb := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*s/v)
  apply min_one_le_mul_min_one (by norm_num : (1 : ℝ) ≤ 4)
  apply hb.trans_eq
  rw [Real.sqrt_mul hv.le, Real.sqrt_div hL]
  have hv0 := (Real.sqrt_pos.mpr hv).ne'
  have hv2 := Real.sq_sqrt hv.le
  field_simp
  ring_nf
  rw [hv2]
  ring

/-- Gaussian part of Lemma 1 for the actual concrete Gaussian model,
opposite-paired face system, and arbitrary independent measurable shifts. -/
theorem lemma_C1_gaussian_model
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r m : ℕ} [NeZero m] (V R : Ω → Vector r) (hV : Measurable V) (hR : Measurable R)
    (hind : IndepFun V R μ) (ν : Matrix (Fin m) (Fin r) ℝ)
    (A : Matrix (Fin r) (Fin r) ℝ) (hLaw : μ.map V = gaussianLaw A)
    (p : ℕ) (hp : 1 ≤ p) (hm : m ≤ 2*p) (hopposite : ∀ α, ∃ β, ν β = -ν α)
    (a : Vector m) {v s : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v) :
    μ.real {ω | V ω+R ω ∈ faceLayer ν a s} ≤
        min 1 ((2*s/v)*(∫ ω, faceNorm ν (V ω) ∂μ)) ∧
      min 1 ((2*s/v)*(∫ ω, faceNorm ν (V ω) ∂μ)) ≤
        4*min 1 (s*Real.sqrt (dimensionLog p/v)) := by
  refine ⟨gaussianFaceLayer_bound μ V R hV hR hind ν A hLaw a hv hs hvariance, ?_⟩
  have he : (∫ ω, faceNorm ν (V ω) ∂μ) = ∫ x, ‖ν.mulVec x‖ ∂gaussianLaw A := by
    rw [← hLaw]
    exact (integral_map hV.aemeasurable (continuous_faceProjectionNorm ν).aestronglyMeasurable).symm
  rw [he]
  exact gaussianFaceNorm_intrinsic_coefficient_le ν A p hp hm hv hs.le hvariance hopposite

end
end RectangleCLTArxivV1
