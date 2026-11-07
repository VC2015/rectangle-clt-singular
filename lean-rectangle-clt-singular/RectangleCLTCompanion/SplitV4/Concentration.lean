import RectangleCLTCompanion.SplitV4.BoundedFaceIntrinsicConcentration

/-! Whole Lemma 1 (`lem:concentration`). A single absolute constant is
chosen before all probability spaces, dimensions, vectors, face normals,
and shifts. The Gaussian intrinsic coefficient remains exactly `2`.
There are `2p` signed faces, and `L=log(e p)` uses the original `p`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem dimensionLog_double_le {p : ℕ} [NeZero p] :
    dimensionLog (2 * p) ≤ 2 * dimensionLog p := by
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne p))
  have heq : dimensionLog (2 * p) = Real.log 2 + dimensionLog p := by
    unfold dimensionLog
    rw [Nat.cast_mul, Nat.cast_ofNat,
      show Real.exp 1 * (2 * (p : ℝ)) = 2 * (Real.exp 1 * (p : ℝ)) by ring,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (mul_pos (Real.exp_pos _) hpR))]
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [heq]
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  linarith

theorem sqrt_dimensionLog_double_div_le {p : ℕ} [NeZero p] {v : ℝ} (hv : 0 < v) :
    Real.sqrt (dimensionLog (2 * p) / v) ≤ 2 * Real.sqrt (dimensionLog p / v) := by
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hratio := div_le_div_of_nonneg_right (dimensionLog_double_le (p := p)) hv.le
  rw [mul_div_assoc] at hratio
  have hratio₀ : 0 ≤ dimensionLog p / v := div_nonneg hL hv.le
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [mul_pow, Real.sq_sqrt hratio₀]
    nlinarith [hratio]

theorem concentration_min_log_dilation (I x y : ℝ) (hI : 0 ≤ I) (hxy : x ≤ 2 * y) :
    min 1 (min I x) ≤ 2 * min 1 (min I y) := by
  have h₁ : min 1 (min I x) ≤ 1 := min_le_left _ _
  have h₂ : min 1 (min I x) ≤ I := (min_le_right _ _).trans (min_le_left _ _)
  have h₃ : min 1 (min I x) ≤ 2 * y := (min_le_right _ _).trans ((min_le_right _ _).trans hxy)
  have hd : min 1 (min I x) / 2 ≤ min 1 (min I y) := by
    apply le_min
    · linarith
    · exact le_min (by linarith) (by linarith)
  have hf := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hd
  linarith

/-- Full bounded assertion with the manuscript's `L=log(e p)` for `2p`
signed face directions. The bound is valid for arbitrary such rows. -/
theorem bounded_face_intrinsic_concentration_signed_faces
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin (2 * p)) (Fin r) ℝ)
    (ξ : Fin n → Ω → Vector r) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hξi : ∀ i, Integrable (ξ i) μ)
    (hcenter : ∀ i, (∫ ω, ξ i ω ∂μ) = 0) {η v : ℝ} (hη : 0 ≤ η) (hv : 0 < v)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceProjectionNorm U (ξ i ω) ≤ η)
    (hvariance : ∀ α, variance (fun ω => dotProduct (U α) (sumVector ξ ω)) μ = v)
    (R : Ω → Vector r) (hR : Measurable R) (hRind : IndepFun (sumVector ξ) R μ)
    (a : Vector (2 * p)) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | (sumVector ξ ω + R ω) ∈ gaussianPolyhedronLayer U a s} ≤
      512 * min 1 (min (((s + η) / v) * ∫ ω, faceProjectionNorm U (sumVector ξ ω) ∂μ)
        ((s + η) * Real.sqrt (dimensionLog p / v))) := by
  have hb := bounded_face_intrinsic_concentration μ U ξ hξ hind hξi hcenter hη hv
    hbound hvariance R hR hRind a hs
  have hI : 0 ≤ ((s + η) / v) * ∫ ω, faceProjectionNorm U (sumVector ξ ω) ∂μ :=
    mul_nonneg (div_nonneg (add_nonneg hs hη) hv.le) (integral_nonneg (fun _ => norm_nonneg _))
  have hlog : (s + η) * Real.sqrt (dimensionLog (2 * p) / v) ≤
      2 * ((s + η) * Real.sqrt (dimensionLog p / v)) := by
    have hh := mul_le_mul_of_nonneg_left (sqrt_dimensionLog_double_div_le (p := p) hv) (add_nonneg hs hη)
    nlinarith
  have hm := concentration_min_log_dilation _ _ _ hI hlog
  exact hb.trans (by nlinarith [hm])

theorem gaussian_intrinsic_concentration_signed_faces
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V R : Ω → Vector r)
    (hV : Measurable V) (hR : Measurable R) (hind : IndepFun V R μ)
    (U : Matrix (Fin (2 * p)) (Fin r) ℝ) (A : Matrix (Fin r) (Fin r) ℝ)
    (hLaw : μ.map V = gaussianLaw A) (a : Vector (2 * p)) {v s : ℝ}
    (hv : 0 < v) (hs : 0 ≤ s)
    (hvariance : ∀ α, dotProduct (U α) ((A * A.transpose).mulVec (U α)) = v) :
    μ.real {ω | V ω + R ω ∈ gaussianPolyhedronLayer U a s} ≤
      min 1 ((2 * s / v) * ∫ ω, faceProjectionNorm U (V ω) ∂μ) ∧
    μ.real {ω | V ω + R ω ∈ gaussianPolyhedronLayer U a s} ≤
      512 * min 1 (s * Real.sqrt (dimensionLog p / v)) := by
  refine ⟨gaussianIntrinsicConcentration_independent_shift μ V R hV hR hind U A hLaw a hv hs hvariance, ?_⟩
  have hb := gaussianIntrinsicConcentration_independent_shift_logarithmic μ V R hV hR hind U A hLaw a hv hs hvariance
  have hlog : s * Real.sqrt (dimensionLog (2 * p) / v) ≤ 2 * (s * Real.sqrt (dimensionLog p / v)) := by
    have hh := mul_le_mul_of_nonneg_left (sqrt_dimensionLog_double_div_le (p := p) hv) hs
    nlinarith
  have hm := concentration_min_log_dilation 1 _ _ (by norm_num) hlog
  simp only [← min_assoc, min_self] at hm
  have hn : 0 ≤ min 1 (s * Real.sqrt (dimensionLog p / v)) := le_min (by norm_num) (by positivity)
  exact hb.trans (by nlinarith [hm])

/-- The bounded model class of Lemma 1, universally quantified after its
absolute constant. `η` bounds only actual face projections. -/
def BoundedConcentrationContract (C : ℝ) : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p r n : ℕ) [NeZero p] (U : Matrix (Fin (2 * p)) (Fin r) ℝ)
    (ξ : Fin n → Ω → Vector r),
    (∀ i, Measurable (ξ i)) → iIndepFun ξ μ → (∀ i, Integrable (ξ i) μ) →
    (∀ i, (∫ ω, ξ i ω ∂μ) = 0) → ∀ (η v : ℝ), 0 ≤ η → 0 < v →
    (∀ i, ∀ᵐ ω ∂μ, faceProjectionNorm U (ξ i ω) ≤ η) →
    (∀ α, variance (fun ω => dotProduct (U α) (sumVector ξ ω)) μ = v) →
    ∀ (R : Ω → Vector r), Measurable R → IndepFun (sumVector ξ) R μ →
    ∀ (a : Vector (2 * p)) (s : ℝ), 0 ≤ s →
    μ.real {ω | (sumVector ξ ω + R ω) ∈ gaussianPolyhedronLayer U a s} ≤
      C * min 1 (min (((s + η) / v) * ∫ ω, faceProjectionNorm U (sumVector ξ ω) ∂μ)
        ((s + η) * Real.sqrt (dimensionLog p / v)))

/-- The Gaussian model class of Lemma 1. Its exact intrinsic coefficient
is `2`, and only its logarithmic bound uses the universal constant. -/
def GaussianConcentrationContract (C : ℝ) : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p r : ℕ) [NeZero p] (V R : Ω → Vector r), Measurable V → Measurable R → IndepFun V R μ →
    ∀ (U : Matrix (Fin (2 * p)) (Fin r) ℝ) (A : Matrix (Fin r) (Fin r) ℝ),
    μ.map V = gaussianLaw A → ∀ (a : Vector (2 * p)) (v s : ℝ), 0 < v → 0 ≤ s →
    (∀ α, dotProduct (U α) ((A * A.transpose).mulVec (U α)) = v) →
    (μ.real {ω | V ω + R ω ∈ gaussianPolyhedronLayer U a s} ≤
      min 1 ((2 * s / v) * ∫ ω, faceProjectionNorm U (V ω) ∂μ)) ∧
    (μ.real {ω | V ω + R ω ∈ gaussianPolyhedronLayer U a s} ≤
      C * min 1 (s * Real.sqrt (dimensionLog p / v)))

/-- **Lemma 1 (`lem:concentration`), both complete assertions.** The same
absolute constant is fixed before every bounded or Gaussian model. -/
theorem lemma_concentration :
    ∃ C : ℝ, 0 < C ∧ BoundedConcentrationContract C ∧ GaussianConcentrationContract C := by
  refine ⟨512, by norm_num, ?_, ?_⟩
  · intro Ω _ μ _ p r n _ U ξ hξ hind hξi hcenter η v hη hv hbound hvariance R hR hRind a s hs
    exact bounded_face_intrinsic_concentration_signed_faces μ U ξ hξ hind hξi hcenter hη hv
      hbound hvariance R hR hRind a hs
  · intro Ω _ μ _ p r _ V R hV hR hind U A hLaw a v s hv hs hvariance
    exact gaussian_intrinsic_concentration_signed_faces μ V R hV hR hind U A hLaw a hv hs hvariance

end

end RectangleCLT.Companion.SplitV4
