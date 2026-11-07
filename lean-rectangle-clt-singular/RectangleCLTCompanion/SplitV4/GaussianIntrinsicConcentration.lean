import RectangleCLTCompanion.SplitV4.IntrinsicGaussianBoundary
import RectangleCLTCompanion.SplitV4.GaussianFaceTransfer
import RectangleCLTCompanion.SubexponentialRates
import Mathlib.Probability.Independence.Basic

/-! The full Gaussian part of Lemma C.1: positive common face variance,
possibly singular Gaussian factors, and arbitrary independent measurable
shifts. The event is the actual difference of the two closed polyhedra.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {p m : ℕ} [NeZero m]

/-- The actual maximum absolute projection on the given face directions. -/
def faceProjectionNorm (ν : Matrix (Fin m) (Fin p) ℝ) (x : Vector p) : ℝ :=
  ‖ν.mulVec x‖

/-- Uniform displacement of every face threshold defines the polyhedral
boundary layer, including inconsistent systems of face inequalities. -/
def gaussianPolyhedronLayer (ν : Matrix (Fin m) (Fin p) ℝ)
    (a : Vector m) (s : ℝ) : Set (Vector p) :=
  facePolyhedron ν (fun α => a α + s) \ facePolyhedron ν (fun α => a α - s)

theorem continuous_faceProjectionNorm (ν : Matrix (Fin m) (Fin p) ℝ) :
    Continuous (faceProjectionNorm ν) :=
  (continuous_const.matrix_mulVec continuous_id).norm

theorem measurableSet_gaussianPolyhedronLayer (ν : Matrix (Fin m) (Fin p) ℝ)
    (a : Vector m) (s : ℝ) : MeasurableSet (gaussianPolyhedronLayer ν a s) :=
  (measurableSet_facePolyhedron ν _).diff (measurableSet_facePolyhedron ν _)

def normalizedGaussianFaceRows (ν : Matrix (Fin m) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (v : ℝ) : Fin m → Vector p :=
  fun α j => (ν * A) α j / Real.sqrt v

theorem gaussianFaceRow_normSq (ν : Matrix (Fin m) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (α : Fin m) :
    vectorNormSq ((ν * A) α) =
      dotProduct (ν α) ((A * A.transpose).mulVec (ν α)) := by
  have hg : vectorNormSq ((ν * A) α) = ((ν * A) * (ν * A).transpose) α α := by
    simp only [vectorNormSq, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  rw [hg, Matrix.transpose_mul]
  rw [show ν * A * (A.transpose * ν.transpose) = ν * (A * A.transpose) * ν.transpose by
    simp only [Matrix.mul_assoc]]
  exact faceCovariance_diagonal ν (A * A.transpose) α

/-- Common positive face variance gives true unit Euclidean normal rows
after division by its square root. No factor-rank condition is used. -/
theorem normalizedGaussianFaceRows_unit (ν : Matrix (Fin m) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hvariance : ∀ α, dotProduct (ν α) ((A * A.transpose).mulVec (ν α)) = v)
    (α : Fin m) : vectorNormSq (normalizedGaussianFaceRows ν A v α) = 1 := by
  have hs : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv.le
  have hrow := (gaussianFaceRow_normSq ν A α).trans (hvariance α)
  simp only [vectorNormSq, normalizedGaussianFaceRows, div_pow, ← Finset.sum_div, hs]
  exact (congrArg (fun z : ℝ => z / v) hrow).trans (div_self hv.ne')

theorem normalizedGaussianFaceRows_dot (ν : Matrix (Fin m) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (v : ℝ) (g : Vector p) (α : Fin m) :
    faceDot (normalizedGaussianFaceRows ν A v α) g =
      ν.mulVec (A.mulVec g) α / Real.sqrt v := by
  rw [Matrix.mulVec_mulVec]
  simp only [faceDot, normalizedGaussianFaceRows, Matrix.mulVec, dotProduct,
    div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem normalizedGaussianFaceRows_projection_norm
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : 0 < v) (g : Vector p) :
    ‖linearProjectionFamily (normalizedGaussianFaceRows ν A v) g‖ =
      faceProjectionNorm ν (A.mulVec g) / Real.sqrt v := by
  have he : linearProjectionFamily (normalizedGaussianFaceRows ν A v) g =
      (Real.sqrt v)⁻¹ • ν.mulVec (A.mulVec g) := by
    funext α
    change faceDot (normalizedGaussianFaceRows ν A v α) g = _
    rw [normalizedGaussianFaceRows_dot]
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hv))]
  exact (div_eq_inv_mul _ _).symm

/-- The actual boundary event after a deterministic shift lies in the
standardized affine-maximum shell. -/
theorem gaussianPolyhedronLayer_subset_standardized_shell
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (a : Vector m) (b : Vector p) {v : ℝ} (hv : 0 < v) (s : ℝ) :
    {g | A.mulVec g + b ∈ gaussianPolyhedronLayer ν a s} ⊆
      {g | -(s / Real.sqrt v) ≤
        gaussianAffineMaximum (normalizedGaussianFaceRows ν A v)
          (fun α => (a α - ν.mulVec b α) / Real.sqrt v) g ∧
        gaussianAffineMaximum (normalizedGaussianFaceRows ν A v)
          (fun α => (a α - ν.mulVec b α) / Real.sqrt v) g ≤ s / Real.sqrt v} := by
  intro g hg
  have hsqrt : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hdot (α : Fin m) :
      faceDot (normalizedGaussianFaceRows ν A v α) g -
        (a α - ν.mulVec b α) / Real.sqrt v =
        (ν.mulVec (A.mulVec g + b) α - a α) / Real.sqrt v := by
    rw [normalizedGaussianFaceRows_dot, Matrix.mulVec_add]
    simp only [Pi.add_apply]
    ring
  have hup : ∀ α, ν.mulVec (A.mulVec g + b) α ≤ a α + s := hg.1
  have hlo : ∃ α, a α - s < ν.mulVec (A.mulVec g + b) α := by
    have hh : ¬ ∀ α, ν.mulVec (A.mulVec g + b) α ≤ a α - s := hg.2
    simpa only [not_forall, not_le] using hh
  constructor
  · obtain ⟨α, hα⟩ := hlo
    have hh := affineBranch_le_gaussianAffineMaximum (normalizedGaussianFaceRows ν A v)
      (fun α => (a α - ν.mulVec b α) / Real.sqrt v) g α
    rw [hdot] at hh
    have hl : -(s / Real.sqrt v) <
        (ν.mulVec (A.mulVec g + b) α - a α) / Real.sqrt v := by
      rw [← neg_div]
      exact (div_lt_div_iff_of_pos_right hsqrt).mpr (by linarith)
    exact (hl.trans_le hh).le
  · apply Finset.sup'_le
    intro α _
    rw [hdot]
    exact (div_le_div_iff_of_pos_right hsqrt).mpr (by linarith [hup α])

theorem gaussianFaceProjection_integral_standardGaussian
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ) :
    (∫ g, faceProjectionNorm ν (A.mulVec g) ∂standardGaussian p) =
      ∫ x, faceProjectionNorm ν x ∂gaussianLaw A := by
  exact (integral_map (measurable_mulVec A).aemeasurable
    (continuous_faceProjectionNorm ν).aestronglyMeasurable).symm

theorem integrable_gaussian_faceProjectionNorm
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (faceProjectionNorm ν) (gaussianLaw A) := by
  apply (integrable_map_measure (continuous_faceProjectionNorm ν).aestronglyMeasurable
    (measurable_mulVec A).aemeasurable).mpr
  have he : (fun g => faceProjectionNorm ν (A.mulVec g)) =
      fun g => ‖linearProjectionFamily (ν * A) g‖ := by
    funext g
    unfold faceProjectionNorm
    rw [Matrix.mulVec_mulVec]
    rfl
  change Integrable (fun g => faceProjectionNorm ν (A.mulVec g)) (standardGaussian p)
  rw [he]
  exact integrable_gaussian_projection_norm (ν * A)

theorem integrable_faceProjectionNorm_of_gaussian_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Ω → Vector p) (hV : Measurable V) (ν : Matrix (Fin m) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hLaw : μ.map V = gaussianLaw A) :
    Integrable (fun ω => faceProjectionNorm ν (V ω)) μ := by
  have hi := integrable_gaussian_faceProjectionNorm ν A
  rw [← hLaw] at hi
  exact (integrable_map_measure (continuous_faceProjectionNorm ν).aestronglyMeasurable
    hV.aemeasurable).mp hi

theorem normalizedGaussianFaceRows_integral_projection_norm
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : 0 < v) :
    (∫ g, ‖linearProjectionFamily (normalizedGaussianFaceRows ν A v) g‖ ∂standardGaussian p) =
      (∫ x, faceProjectionNorm ν x ∂gaussianLaw A) / Real.sqrt v := by
  simp_rw [normalizedGaussianFaceRows_projection_norm ν A hv]
  rw [integral_div, gaussianFaceProjection_integral_standardGaussian]

/-- General common variance and a fixed arbitrary threshold translation:
the intrinsic coefficient is exactly `2*s/v`. -/
theorem gaussianIntrinsicConcentration_fixed_shift
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (a : Vector m) (b : Vector p) {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s)
    (hvariance : ∀ α, dotProduct (ν α) ((A * A.transpose).mulVec (ν α)) = v) :
    (gaussianLaw A).real {x | x + b ∈ gaussianPolyhedronLayer ν a s} ≤
      min 1 ((2 * s / v) * ∫ x, faceProjectionNorm ν x ∂gaussianLaw A) := by
  have he : (gaussianLaw A).real {x | x + b ∈ gaussianPolyhedronLayer ν a s} =
      (standardGaussian p).real {g | A.mulVec g + b ∈ gaussianPolyhedronLayer ν a s} := by
    exact map_measureReal_apply (measurable_mulVec A)
      ((measurableSet_gaussianPolyhedronLayer ν a s).preimage (measurable_id.add_const b))
  rw [he]
  apply le_min measureReal_le_one
  have hb := (measureReal_mono (gaussianPolyhedronLayer_subset_standardized_shell ν A a b hv s)).trans
    (intrinsicGaussianBoundary_absoluteMaximum (normalizedGaussianFaceRows ν A v)
      (fun α => (a α - ν.mulVec b α) / Real.sqrt v)
      (normalizedGaussianFaceRows_unit ν A hv hvariance) (div_nonneg hs (Real.sqrt_nonneg v)))
  rw [normalizedGaussianFaceRows_integral_projection_norm ν A hv] at hb
  convert hb using 1
  have hsqrt : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hv.le
  field_simp [(Real.sqrt_pos.mpr hv).ne', hv.ne']

/-- The sharp logarithmic specialization before weakening its universal
constant: exact `sqrt (2 log (m+1))` and actual variance scaling. -/
theorem gaussianIntrinsicConcentration_fixed_shift_log_sharp
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (a : Vector m) (b : Vector p) {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s)
    (hvariance : ∀ α, dotProduct (ν α) ((A * A.transpose).mulVec (ν α)) = v) :
    (gaussianLaw A).real {x | x + b ∈ gaussianPolyhedronLayer ν a s} ≤
      min 1 ((2 * (s / Real.sqrt v)) * Real.sqrt (2 * Real.log ((m : ℝ) + 1))) := by
  have he : (gaussianLaw A).real {x | x + b ∈ gaussianPolyhedronLayer ν a s} =
      (standardGaussian p).real {g | A.mulVec g + b ∈ gaussianPolyhedronLayer ν a s} := by
    exact map_measureReal_apply (measurable_mulVec A)
      ((measurableSet_gaussianPolyhedronLayer ν a s).preimage (measurable_id.add_const b))
  rw [he]
  apply le_min measureReal_le_one
  exact (measureReal_mono (gaussianPolyhedronLayer_subset_standardized_shell ν A a b hv s)).trans
    (intrinsicGaussianBoundary_logarithmic (normalizedGaussianFaceRows ν A v)
      (fun α => (a α - ν.mulVec b α) / Real.sqrt v)
      (normalizedGaussianFaceRows_unit ν A hv hvariance) (div_nonneg hs (Real.sqrt_nonneg v)))

theorem face_log_succ_le_dimensionLog : Real.log ((m : ℝ) + 1) ≤ dimensionLog m := by
  have hm : 1 ≤ (m : ℝ) := by exact_mod_cast NeZero.pos m
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  apply Real.log_le_log (by positivity)
  change (m : ℝ) + 1 ≤ Real.exp 1 * m
  nlinarith

theorem gaussianIntrinsicConcentration_fixed_shift_logarithmic
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (a : Vector m) (b : Vector p) {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s)
    (hvariance : ∀ α, dotProduct (ν α) ((A * A.transpose).mulVec (ν α)) = v) :
    (gaussianLaw A).real {x | x + b ∈ gaussianPolyhedronLayer ν a s} ≤
      4 * min 1 (s * Real.sqrt (dimensionLog m / v)) := by
  have hL : 0 ≤ dimensionLog m :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (log_exp_mul_nat_ge_one (NeZero.pos m))
  have hlog := face_log_succ_le_dimensionLog (m := m)
  have hsqrt : Real.sqrt (2 * Real.log ((m : ℝ) + 1)) ≤ 2 * Real.sqrt (dimensionLog m) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hL]
      have hlog0 : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
      nlinarith
  have hb : (2 * (s / Real.sqrt v)) * Real.sqrt (2 * Real.log ((m : ℝ) + 1)) ≤
      4 * (s * Real.sqrt (dimensionLog m / v)) := by
    rw [Real.sqrt_div hL]
    have hh := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hs (Real.sqrt_nonneg v)))
    convert hh using 1 <;> ring
  exact (gaussianIntrinsicConcentration_fixed_shift_log_sharp ν A a b hv hs hvariance).trans
    (min_one_le_mul_min_one (by norm_num : (1 : ℝ) ≤ 4) hb)

/-- Uniform section bounds integrate over a completely arbitrary shift
law. This uses a bounded indicator, so no shift moment is introduced. -/
theorem product_event_probability_le_of_sections
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (τ : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure τ]
    (S : Set (E × F)) (hS : MeasurableSet S) (K : ℝ)
    (hsection : ∀ b, μ.real {x | (x, b) ∈ S} ≤ K) : (μ.prod τ).real S ≤ K := by
  let I : E × F → ℝ := S.indicator (fun _ => 1)
  have hi : Integrable I (μ.prod τ) := (integrable_const (1 : ℝ)).indicator hS
  have hfixed (b : F) : (∫ x, I (x, b) ∂μ) = μ.real {x | (x, b) ∈ S} := by
    have hSb : MeasurableSet {x | (x, b) ∈ S} := hS.preimage (measurable_id.prodMk measurable_const)
    change (∫ x, {x | (x, b) ∈ S}.indicator (fun _ => (1 : ℝ)) x ∂μ) = _
    exact integral_indicator_one hSb
  have hc : (μ.prod τ).real S = ∫ b, ∫ x, I (x, b) ∂μ ∂τ := by
    rw [← integral_indicator_one hS]
    exact integral_prod_symm I hi
  rw [hc]
  have hbound (b : F) : (∫ x, I (x, b) ∂μ) ≤ K := by rw [hfixed]; exact hsection b
  have hh := integral_mono hi.integral_prod_right (integrable_const K) hbound
  simpa only [integral_const, measureReal_univ_eq_one, one_smul] using hh

theorem gaussianIntrinsicConcentration_product
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (τ : Measure (Vector p)) [IsProbabilityMeasure τ] (a : Vector m)
    {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s)
    (hvariance : ∀ α, dotProduct (ν α) ((A * A.transpose).mulVec (ν α)) = v) :
    ((gaussianLaw A).prod τ).real {z | z.1 + z.2 ∈ gaussianPolyhedronLayer ν a s} ≤
      min 1 ((2 * s / v) * ∫ x, faceProjectionNorm ν x ∂gaussianLaw A) := by
  apply product_event_probability_le_of_sections (gaussianLaw A) τ _
    ((measurableSet_gaussianPolyhedronLayer ν a s).preimage (measurable_fst.add measurable_snd))
  intro b
  exact gaussianIntrinsicConcentration_fixed_shift ν A a b hv hs hvariance

theorem gaussianIntrinsicConcentration_product_logarithmic
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (τ : Measure (Vector p)) [IsProbabilityMeasure τ] (a : Vector m)
    {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s)
    (hvariance : ∀ α, dotProduct (ν α) ((A * A.transpose).mulVec (ν α)) = v) :
    ((gaussianLaw A).prod τ).real {z | z.1 + z.2 ∈ gaussianPolyhedronLayer ν a s} ≤
      4 * min 1 (s * Real.sqrt (dimensionLog m / v)) := by
  apply product_event_probability_le_of_sections (gaussianLaw A) τ _
    ((measurableSet_gaussianPolyhedronLayer ν a s).preimage (measurable_fst.add measurable_snd))
  intro b
  exact gaussianIntrinsicConcentration_fixed_shift_logarithmic ν A a b hv hs hvariance

/-- Actual independent functions are transported to the concrete product
law. The shift is only measurable; it has no integrability hypothesis. -/
theorem gaussianIntrinsicConcentration_independent_shift
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V R : Ω → Vector p) (hV : Measurable V) (hR : Measurable R)
    (hind : IndepFun V R μ) (ν : Matrix (Fin m) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hLaw : μ.map V = gaussianLaw A)
    (a : Vector m) {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s)
    (hvariance : ∀ α, dotProduct (ν α) ((A * A.transpose).mulVec (ν α)) = v) :
    μ.real {ω | V ω + R ω ∈ gaussianPolyhedronLayer ν a s} ≤
      min 1 ((2 * s / v) * ∫ ω, faceProjectionNorm ν (V ω) ∂μ) := by
  letI : IsProbabilityMeasure (μ.map R) := isProbabilityMeasure_map hR.aemeasurable
  let S : Set (Vector p × Vector p) := {z | z.1 + z.2 ∈ gaussianPolyhedronLayer ν a s}
  have hS : MeasurableSet S := (measurableSet_gaussianPolyhedronLayer ν a s).preimage
    (measurable_fst.add measurable_snd)
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hR.aemeasurable).mp hind
  have he : μ.real {ω | V ω + R ω ∈ gaussianPolyhedronLayer ν a s} =
      ((gaussianLaw A).prod (μ.map R)).real S := by
    rw [← hLaw, ← hlaw]
    exact (map_measureReal_apply (hV.prodMk hR) hS).symm
  have hmean : (∫ x, faceProjectionNorm ν x ∂gaussianLaw A) =
      ∫ ω, faceProjectionNorm ν (V ω) ∂μ := by
    rw [← hLaw]
    exact integral_map hV.aemeasurable (continuous_faceProjectionNorm ν).aestronglyMeasurable
  rw [he, ← hmean]
  exact gaussianIntrinsicConcentration_product ν A (μ.map R) a hv hs hvariance

theorem gaussianIntrinsicConcentration_independent_shift_logarithmic
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V R : Ω → Vector p) (hV : Measurable V) (hR : Measurable R)
    (hind : IndepFun V R μ) (ν : Matrix (Fin m) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hLaw : μ.map V = gaussianLaw A)
    (a : Vector m) {v s : ℝ} (hv : 0 < v) (hs : 0 ≤ s)
    (hvariance : ∀ α, dotProduct (ν α) ((A * A.transpose).mulVec (ν α)) = v) :
    μ.real {ω | V ω + R ω ∈ gaussianPolyhedronLayer ν a s} ≤
      4 * min 1 (s * Real.sqrt (dimensionLog m / v)) := by
  letI : IsProbabilityMeasure (μ.map R) := isProbabilityMeasure_map hR.aemeasurable
  let S : Set (Vector p × Vector p) := {z | z.1 + z.2 ∈ gaussianPolyhedronLayer ν a s}
  have hS : MeasurableSet S := (measurableSet_gaussianPolyhedronLayer ν a s).preimage
    (measurable_fst.add measurable_snd)
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hR.aemeasurable).mp hind
  have he : μ.real {ω | V ω + R ω ∈ gaussianPolyhedronLayer ν a s} =
      ((gaussianLaw A).prod (μ.map R)).real S := by
    rw [← hLaw, ← hlaw]
    exact (map_measureReal_apply (hV.prodMk hR) hS).symm
  rw [he]
  exact gaussianIntrinsicConcentration_product_logarithmic ν A (μ.map R) a hv hs hvariance

end

end RectangleCLT.Companion.SplitV4
