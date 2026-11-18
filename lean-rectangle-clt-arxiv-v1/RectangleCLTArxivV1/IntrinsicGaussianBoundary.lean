import RectangleCLTArxivV1.FaceCoordinates
import RectangleCLTCompanion.SplitV4.GaussianIntrinsicConcentration
import RectangleCLTCompanion.SplitV4.Printed.GaussianMollification

/-!
# The printed intrinsic Gaussian boundary route in Appendix C.1

The unit-row bound uses the archive's actual soft-maximum Stein proof followed
by the printed convolution of a linear ramp. Scaling and conditioning preserve
the intrinsic expected maximum. No concentration inequality is assumed.

The Gaussian law is represented concretely by `gaussianLaw A`. A singular
matrix is allowed. Relating an arbitrary presentation of a centered Gaussian
to this law is a separate representation obligation when this theorem is used.
-/
namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT
open RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable section

/-- The shared paper-facing layer is the actual archived difference of
closed face polyhedra. -/
@[simp] theorem faceLayer_eq_gaussianPolyhedronLayer {p m : ℕ} [NeZero m]
    (ν : Matrix (Fin m) (Fin p) ℝ) (a : Vector m) (s : ℝ) :
    faceLayer ν a s = gaussianPolyhedronLayer ν a s := rfl

/-- Frozen main lines 6319--6335, using the literal linear-ramp mollification
proof and its smooth-maximum Stein input. Repeated rows are allowed. -/
theorem gaussianUnitRowsBoundary_printed {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ)
    (hw : ∀ α, vectorNormSq (w α) = 1) {s : ℝ} (hs : 0 < s) :
    (standardGaussian r).real {x | -s ≤ gaussianAffineMaximum w a x ∧
      gaussianAffineMaximum w a x ≤ s} ≤
      (2*s) * ∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r :=
  RectangleCLT.Companion.SplitV4.Printed.intrinsicGaussianBoundary_printed_mollification
    w a hw hs

/-- Frozen main lines 6336--6341: the Gaussian MGF supplies the logarithmic
bound for the positive face maximum. -/
theorem gaussianUnitRowsMaximum_logarithmic {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (hw : ∀ α, vectorNormSq (w α) = 1) :
    (∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r) ≤
      Real.sqrt (2*Real.log ((m : ℝ)+1)) :=
  integral_positiveGaussianFaceMaximum_le_sqrt_log w hw

/-- The logarithmic unit-row boundary estimate retains the printed
mollification proof in its dependency closure. -/
theorem gaussianUnitRowsBoundary_logarithmic_printed {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ)
    (hw : ∀ α, vectorNormSq (w α) = 1) {s : ℝ} (hs : 0 < s) :
    (standardGaussian r).real {x | -s ≤ gaussianAffineMaximum w a x ∧
      gaussianAffineMaximum w a x ≤ s} ≤
      (2*s) * Real.sqrt (2*Real.log ((m : ℝ)+1)) :=
  (gaussianUnitRowsBoundary_printed w a hw hs).trans
    (mul_le_mul_of_nonneg_left (gaussianUnitRowsMaximum_logarithmic w hw) (by positivity))

/-- Frozen main lines 6346--6354: variance normalization of the intrinsic
Gaussian estimate, with an arbitrary fixed shift of the thresholds. -/
theorem gaussianIntrinsicBoundary_fixed_shift {p m : ℕ} [NeZero m]
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (a : Vector m) (b : Vector p) {v s : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v) :
    (gaussianLaw A).real {x | x+b ∈ gaussianPolyhedronLayer ν a s} ≤
      min 1 ((2*s/v) * ∫ x, ‖ν.mulVec x‖ ∂gaussianLaw A) := by
  have he : (gaussianLaw A).real {x | x+b ∈ gaussianPolyhedronLayer ν a s} =
      (standardGaussian p).real {g | A.mulVec g+b ∈ gaussianPolyhedronLayer ν a s} :=
    map_measureReal_apply (measurable_mulVec A)
      ((measurableSet_gaussianPolyhedronLayer ν a s).preimage (measurable_id.add_const b))
  rw [he]
  apply le_min measureReal_le_one
  have hunit := gaussianUnitRowsBoundary_printed (normalizedGaussianFaceRows ν A v)
    (fun α => (a α-ν.mulVec b α)/Real.sqrt v)
    (normalizedGaussianFaceRows_unit ν A hv hvariance)
    (div_pos hs (Real.sqrt_pos.mpr hv))
  have hproj := integral_positiveGaussianFaceMaximum_le_projection_norm
    (normalizedGaussianFaceRows ν A v)
  have hbound := (measureReal_mono
    (gaussianPolyhedronLayer_subset_standardized_shell ν A a b hv s)).trans
    (hunit.trans (mul_le_mul_of_nonneg_left hproj (by positivity)))
  rw [normalizedGaussianFaceRows_integral_projection_norm ν A hv] at hbound
  change _ ≤ (2*s/v) * ∫ x, faceProjectionNorm ν x ∂gaussianLaw A
  convert hbound using 1
  have hsqrt : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
  field_simp [(Real.sqrt_pos.mpr hv).ne', hv.ne']

/-- The fixed-shift estimate integrates over any shift law. No moment
hypothesis on that law is needed. -/
theorem gaussianIntrinsicBoundary_product {p m : ℕ} [NeZero m]
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (τ : Measure (Vector p)) [IsProbabilityMeasure τ] (a : Vector m)
    {v s : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v) :
    ((gaussianLaw A).prod τ).real {z | z.1+z.2 ∈ gaussianPolyhedronLayer ν a s} ≤
      min 1 ((2*s/v) * ∫ x, ‖ν.mulVec x‖ ∂gaussianLaw A) := by
  apply product_event_probability_le_of_sections (gaussianLaw A) τ _
    ((measurableSet_gaussianPolyhedronLayer ν a s).preimage (measurable_fst.add measurable_snd))
  intro b
  exact gaussianIntrinsicBoundary_fixed_shift ν A a b hv hs hvariance

/-- The intrinsic expected maximum is a genuine finite expectation under
the concrete Gaussian law; integrability is not an extra hypothesis. -/
theorem integrable_gaussianFaceProjectionNorm_of_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p m : ℕ} [NeZero m] (V : Ω → Vector p) (hV : Measurable V)
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hLaw : μ.map V = gaussianLaw A) :
    Integrable (fun ω => ‖ν.mulVec (V ω)‖) μ :=
  integrable_faceProjectionNorm_of_gaussian_law μ V hV ν A hLaw

/-- Frozen main lines 6356--6362: arbitrary independent measurable shifts,
with the intrinsic coefficient exactly `2*s/v`. Covariance singularity,
repeated faces and inconsistent threshold systems are allowed. -/
theorem gaussianIntrinsicBoundary_independent_shift
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p m : ℕ} [NeZero m] (V R : Ω → Vector p) (hV : Measurable V) (hR : Measurable R)
    (hind : IndepFun V R μ) (ν : Matrix (Fin m) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hLaw : μ.map V = gaussianLaw A)
    (a : Vector m) {v s : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v) :
    μ.real {ω | V ω+R ω ∈ gaussianPolyhedronLayer ν a s} ≤
      min 1 ((2*s/v) * ∫ ω, ‖ν.mulVec (V ω)‖ ∂μ) := by
  letI : IsProbabilityMeasure (μ.map R) := isProbabilityMeasure_map hR.aemeasurable
  let S : Set (Vector p × Vector p) := {z | z.1+z.2 ∈ gaussianPolyhedronLayer ν a s}
  have hS : MeasurableSet S := (measurableSet_gaussianPolyhedronLayer ν a s).preimage
    (measurable_fst.add measurable_snd)
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hR.aemeasurable).mp hind
  have he : μ.real {ω | V ω+R ω ∈ gaussianPolyhedronLayer ν a s} =
      ((gaussianLaw A).prod (μ.map R)).real S := by
    rw [← hLaw, ← hlaw]
    exact (map_measureReal_apply (hV.prodMk hR) hS).symm
  have hmean : (∫ x, ‖ν.mulVec x‖ ∂gaussianLaw A) =
      ∫ ω, ‖ν.mulVec (V ω)‖ ∂μ := by
    rw [← hLaw]
    exact integral_map hV.aemeasurable (continuous_faceProjectionNorm ν).aestronglyMeasurable
  rw [he, ← hmean]
  exact gaussianIntrinsicBoundary_product ν A (μ.map R) a hv hs hvariance

/-- The intrinsic Gaussian assertion of Lemma 1 in the shared face notation.
The concrete Gaussian law and actual common variance are the probabilistic
inputs; no target boundary inequality occurs among the premises. -/
theorem gaussianFaceLayer_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p m : ℕ} [NeZero m] (V R : Ω → Vector p) (hV : Measurable V) (hR : Measurable R)
    (hind : IndepFun V R μ) (U : Fin m → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hLaw : μ.map V = gaussianLaw A)
    (a : Vector m) {v s : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hvariance : ∀ α, dotProduct (U α) ((A*A.transpose).mulVec (U α)) = v) :
    μ.real {ω | V ω+R ω ∈ faceLayer U a s} ≤
      min 1 ((2*s/v) * ∫ ω, faceNorm U (V ω) ∂μ) := by
  simpa only [faceLayer_eq_gaussianPolyhedronLayer, faceNorm, faceProjection_eq_mulVec] using
    gaussianIntrinsicBoundary_independent_shift μ V R hV hR hind U A hLaw a hv hs hvariance

/-- The literal mollification proof also gives the sharp logarithmic
fixed-shift bound after normalizing the common projected variance. -/
theorem gaussianIntrinsicBoundary_fixed_shift_log_sharp {p m : ℕ} [NeZero m]
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (a : Vector m) (b : Vector p) {v s : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v) :
    (gaussianLaw A).real {x | x+b ∈ gaussianPolyhedronLayer ν a s} ≤
      min 1 ((2*(s/Real.sqrt v))*Real.sqrt (2*Real.log ((m : ℝ)+1))) := by
  have he : (gaussianLaw A).real {x | x+b ∈ gaussianPolyhedronLayer ν a s} =
      (standardGaussian p).real {g | A.mulVec g+b ∈ gaussianPolyhedronLayer ν a s} :=
    map_measureReal_apply (measurable_mulVec A)
      ((measurableSet_gaussianPolyhedronLayer ν a s).preimage (measurable_id.add_const b))
  rw [he]
  apply le_min measureReal_le_one
  exact (measureReal_mono
    (gaussianPolyhedronLayer_subset_standardized_shell ν A a b hv s)).trans
    (gaussianUnitRowsBoundary_logarithmic_printed (normalizedGaussianFaceRows ν A v)
      (fun α => (a α-ν.mulVec b α)/Real.sqrt v)
      (normalizedGaussianFaceRows_unit ν A hv hvariance)
      (div_pos hs (Real.sqrt_pos.mpr hv)))

/-- Numerical weakening of the logarithmic estimate; its dependency closure
retains the printed convolution-of-a-ramp argument. -/
theorem gaussianIntrinsicBoundary_fixed_shift_logarithmic {p m : ℕ} [NeZero m]
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (a : Vector m) (b : Vector p) {v s : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v) :
    (gaussianLaw A).real {x | x+b ∈ gaussianPolyhedronLayer ν a s} ≤
      4*min 1 (s*Real.sqrt (dimensionLog m/v)) := by
  have hL : 0 ≤ dimensionLog m :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (log_exp_mul_nat_ge_one (NeZero.pos m))
  have hlog := face_log_succ_le_dimensionLog (m := m)
  have hsqrt : Real.sqrt (2*Real.log ((m : ℝ)+1)) ≤ 2*Real.sqrt (dimensionLog m) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hL]
      have hlog0 : 0 ≤ Real.log ((m : ℝ)+1) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])
      nlinarith
  have hb : (2*(s/Real.sqrt v))*Real.sqrt (2*Real.log ((m : ℝ)+1)) ≤
      4*(s*Real.sqrt (dimensionLog m/v)) := by
    rw [Real.sqrt_div hL]
    have hh := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (div_nonneg hs.le (Real.sqrt_nonneg v)))
    convert hh using 1 <;> ring
  exact (gaussianIntrinsicBoundary_fixed_shift_log_sharp ν A a b hv hs hvariance).trans
    (min_one_le_mul_min_one (by norm_num : (1 : ℝ) ≤ 4) hb)

/-- No moment condition is introduced when the logarithmic bound is
integrated over an arbitrary independent shift law. -/
theorem gaussianIntrinsicBoundary_product_logarithmic {p m : ℕ} [NeZero m]
    (ν : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (τ : Measure (Vector p)) [IsProbabilityMeasure τ] (a : Vector m)
    {v s : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v) :
    ((gaussianLaw A).prod τ).real {z | z.1+z.2 ∈ gaussianPolyhedronLayer ν a s} ≤
      4*min 1 (s*Real.sqrt (dimensionLog m/v)) := by
  apply product_event_probability_le_of_sections (gaussianLaw A) τ _
    ((measurableSet_gaussianPolyhedronLayer ν a s).preimage (measurable_fst.add measurable_snd))
  intro b
  exact gaussianIntrinsicBoundary_fixed_shift_logarithmic ν A a b hv hs hvariance

/-- The logarithmic specialization for arbitrary independent measurable
shifts, using the same concrete Gaussian-law input as the intrinsic bound. -/
theorem gaussianIntrinsicBoundary_independent_shift_logarithmic
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p m : ℕ} [NeZero m] (V R : Ω → Vector p) (hV : Measurable V) (hR : Measurable R)
    (hind : IndepFun V R μ) (ν : Matrix (Fin m) (Fin p) ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hLaw : μ.map V = gaussianLaw A)
    (a : Vector m) {v s : ℝ} (hv : 0 < v) (hs : 0 < s)
    (hvariance : ∀ α, dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = v) :
    μ.real {ω | V ω+R ω ∈ gaussianPolyhedronLayer ν a s} ≤
      4*min 1 (s*Real.sqrt (dimensionLog m/v)) := by
  letI : IsProbabilityMeasure (μ.map R) := isProbabilityMeasure_map hR.aemeasurable
  let S : Set (Vector p × Vector p) := {z | z.1+z.2 ∈ gaussianPolyhedronLayer ν a s}
  have hS : MeasurableSet S := (measurableSet_gaussianPolyhedronLayer ν a s).preimage
    (measurable_fst.add measurable_snd)
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hR.aemeasurable).mp hind
  have he : μ.real {ω | V ω+R ω ∈ gaussianPolyhedronLayer ν a s} =
      ((gaussianLaw A).prod (μ.map R)).real S := by
    rw [← hLaw, ← hlaw]
    exact (map_measureReal_apply (hV.prodMk hR) hS).symm
  rw [he]
  exact gaussianIntrinsicBoundary_product_logarithmic ν A (μ.map R) a hv hs hvariance

end
end RectangleCLTArxivV1
