import RectangleCLTArxivV1.FaceCoordinates
import RectangleCLTCompanion.SplitV4.Printed.BoundedConcentration

/-!
# The bounded-sum assertion of Lemma 1

The original vectors are projected first. Their face envelope does not need
to control directions invisible to the faces, and no rank or covariance
nondegeneracy is imposed beyond the stated positive common face variance.
-/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators

/- The six transport/averaging steps below replay the archived printed
route, using its unique-gradient and threshold-perturbation C.1 input. -/

theorem coordinateBoundary_product_printed
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    (μ.prod ν).real {z | -s ≤ vectorFaceMaximum a ((∑ i, ξ i z.1) + R z.2) ∧
      vectorFaceMaximum a ((∑ i, ξ i z.1) + R z.2) ≤ s} ≤
      ((8 * s + 64 * η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ := by
  have hsum : Measurable (fun ω => ∑ i, ξ i ω) := Finset.measurable_sum _ (fun i _ => h.measurable i)
  have hW : Measurable (fun z : Ω × Γ => (∑ i, ξ i z.1) + R z.2) :=
    (hsum.comp measurable_fst).add (hR.comp measurable_snd)
  have hI := integrable_vectorBoundaryIndicator (μ.prod ν) _ hW a s
  rw [← integral_vectorBoundaryIndicator_eq_real (μ.prod ν) _ hW a s, integral_prod_symm _ hI]
  calc
    _ ≤ ∫ _γ : Γ, ((8 * s + 64 * η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ ∂ν := by
      apply integral_mono hI.integral_prod_right (integrable_const _)
      intro γ
      change (∫ ω, vectorBoundaryIndicator a s ((∑ i, ξ i ω) + R γ) ∂μ) ≤ _
      rw [integral_vectorBoundaryIndicator_eq_real μ _ (hsum.add_const (R γ)) a s]
      exact RectangleCLT.Companion.SplitV4.Printed.bounded_intrinsic_boundary_fixed_shift_printed μ ξ h hv hdiag a (R γ) hs
    _ = _ := by rw [integral_const]; simp only [measureReal_univ_eq_one, one_smul]

theorem coordinateLayer_product_printed
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    (μ.prod ν).real {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} ≤
      64 * ((s + η) / v * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ) := by
  have hη : 0 ≤ η := h.delta_nonneg
  have hI : 0 ≤ ∫ ω, ‖∑ i, ξ i ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  calc
    _ ≤ (μ.prod ν).real {z | -s ≤ vectorFaceMaximum a ((∑ i, ξ i z.1) + R z.2) ∧
      vectorFaceMaximum a ((∑ i, ξ i z.1) + R z.2) ≤ s} :=
      measureReal_mono (fun z hz => projectedFaceLayer_subset_closed_window a s hz)
    _ ≤ _ := coordinateBoundary_product_printed μ ξ h hv hdiag ν R hR a hs
    _ ≤ _ := by
      have hc : (8 * s + 64 * η) / v ≤ 64 * ((s + η) / v) := by
        calc
          _ ≤ (64 * (s + η)) / v := div_le_div_of_nonneg_right (by linarith) hv.le
          _ = _ := by ring
      apply (mul_le_mul_of_nonneg_right hc hI).trans_eq
      ring

theorem coordinateLayer_independent_printed {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (R : Ω → Vector p) (hR : Measurable R) (hRind : IndepFun (sumVector ξ) R μ)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s} ≤
      64 * ((s + η) / v * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ) := by
  have hid := independent_sum_shift_identDistrib μ ξ h.measurable R hR hRind
  have hset := measurableSet_projectedFaceLayer a s
  have hprob : μ {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s} =
      (μ.prod μ) {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} := by
    simpa only [Measure.map_apply_of_aemeasurable hid.aemeasurable_fst hset,
      Measure.map_apply_of_aemeasurable hid.aemeasurable_snd hset] using congrArg (fun ν => ν (projectedFaceLayer a s)) hid.map_eq
  change (μ {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s}).toReal ≤ _
  rw [hprob]
  exact coordinateLayer_product_printed μ ξ h hv hdiag μ R hR a hs

theorem coordinateLayer_product_log_printed
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    (μ.prod ν).real {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} ≤
      256 * ((s + η) * Real.sqrt (dimensionLog p / v)) := by
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hη : 0 ≤ η := h.delta_nonneg
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  let q := Real.sqrt (dimensionLog p / v)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hsη : 0 ≤ s + η := add_nonneg hs hη
  have hqq : q ^ 2 = dimensionLog p / v := Real.sq_sqrt (div_nonneg hL hv.le)
  have hLq : dimensionLog p = v * q ^ 2 := by
    apply (eq_div_iff (ne_of_gt hv)).mp at hqq
    nlinarith [hqq]
  have hsq : Real.sqrt v * Real.sqrt (dimensionLog p) = v * q := by
    have hsq₀ : Real.sqrt (dimensionLog p) = Real.sqrt v * q := by
      dsimp [q]
      rw [Real.sqrt_div hL]
      field_simp
    rw [hsq₀]
    nlinarith [Real.sq_sqrt hv.le]
  by_cases hsmall : η * q ≤ 1
  · have hnorm := h.integral_norm_sum_le_of_variance hp hv hdiag
    change (∫ ω, ‖∑ i, ξ i ω‖ ∂μ) ≤ _ at hnorm
    have hbudget : (∫ ω, ‖∑ i, ξ i ω‖ ∂μ) ≤ 4 * v * q := by
      rw [show 2 * Real.sqrt v * Real.sqrt (dimensionLog p) =
        2 * (Real.sqrt v * Real.sqrt (dimensionLog p)) by ring, hsq, hLq] at hnorm
      have hm := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hv.le hq)
      nlinarith
    have hbase := coordinateLayer_product_printed μ ξ h hv hdiag ν R hR a hs
    apply hbase.trans
    calc
      _ ≤ 64 * ((s + η) / v * (4 * v * q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbudget (div_nonneg hsη hv.le)) (by norm_num)
      _ = _ := by dsimp [q]; field_simp [ne_of_gt hv]; ring
  · have hlarge : 1 < (s + η) * q := by nlinarith [lt_of_not_ge hsmall]
    exact (measureReal_le_one (μ := μ.prod ν)).trans (by dsimp [q] at *; nlinarith)

theorem coordinateLayer_product_min_printed
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    (μ.prod ν).real {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} ≤
      256 * min 1 (min (((s + η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ)
        ((s + η) * Real.sqrt (dimensionLog p / v))) := by
  let P := (μ.prod ν).real {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s}
  have hη := h.delta_nonneg
  have hI : 0 ≤ ((s + η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ :=
    mul_nonneg (div_nonneg (add_nonneg hs hη) hv.le) (integral_nonneg (fun _ => norm_nonneg _))
  have h₁ : P ≤ 1 := measureReal_le_one
  have h₂ := coordinateLayer_product_printed μ ξ h hv hdiag ν R hR a hs
  have h₃ := coordinateLayer_product_log_printed μ ξ h hv hdiag ν R hR a hs
  have hd : P / 256 ≤ min 1 (min (((s + η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ)
      ((s + η) * Real.sqrt (dimensionLog p / v))) := by
    apply le_min
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
      linarith
    · apply le_min
      · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
        change P ≤ _ at h₂
        linarith
      · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
        simpa only [mul_comm] using h₃
  have hf := (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mp hd
  simpa only [mul_comm] using hf

theorem coordinateLayer_independent_min_printed {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (R : Ω → Vector p) (hR : Measurable R) (hRind : IndepFun (sumVector ξ) R μ)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s} ≤
      256 * min 1 (min (((s + η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ)
        ((s + η) * Real.sqrt (dimensionLog p / v))) := by
  have hid := independent_sum_shift_identDistrib μ ξ h.measurable R hR hRind
  have hset := measurableSet_projectedFaceLayer a s
  have hprob : μ {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s} =
      (μ.prod μ) {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} := by
    simpa only [Measure.map_apply_of_aemeasurable hid.aemeasurable_fst hset,
      Measure.map_apply_of_aemeasurable hid.aemeasurable_snd hset] using
      congrArg (fun ν => ν (projectedFaceLayer a s)) hid.map_eq
  change (μ {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s}).toReal ≤ _
  rw [hprob]
  exact coordinateLayer_product_min_printed μ ξ h hv hdiag μ R hR a hs

/-- The array of actual face projections of the bounded observations. -/
def projectedObservations {r m n : ℕ} {Ω : Type*} (U : Fin m → Fin r → ℝ)
    (X : Fin n → Ω → Fin r → ℝ) (i : Fin n) (ω : Ω) : Fin m → ℝ :=
  faceProjection U (X i ω)

theorem projectedObservations_sum {r m n : ℕ} {Ω : Type*}
    (U : Fin m → Fin r → ℝ) (X : Fin n → Ω → Fin r → ℝ) (ω : Ω) :
    (∑ i, projectedObservations U X i ω) = faceProjection U (sumVector X ω) :=
  (faceProjection_sum Finset.univ U (fun i => X i ω)).symm

/-- Centering is transported through each face projection using only the
integrability that is part of being a centered finite-dimensional vector. -/
theorem integral_faceProjection_zero {r m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (U : Fin m → Fin r → ℝ) (X : Ω → Fin r → ℝ)
    (hint : ∀ k, Integrable (fun ω => X ω k) μ)
    (hmean : ∀ k, (∫ ω, X ω k ∂μ) = 0) (j : Fin m) :
    (∫ ω, faceProjection U (X ω) j ∂μ) = 0 := by
  change (∫ ω, ∑ k, U j k * X ω k ∂μ) = 0
  rw [integral_finset_sum Finset.univ (fun k _ => (hint k).const_mul _)]
  simp only [integral_const_mul, hmean, mul_zero, Finset.sum_const_zero]

/-- The face-coordinate array satisfies exactly the archive's bounded
independent hypotheses, even when the face map has a nontrivial kernel. -/
theorem projectedObservations_boundedHypotheses {r m n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (U : Fin m → Fin r → ℝ)
    (X : Fin n → Ω → Fin r → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hint : ∀ i k, Integrable (fun ω => X i ω k) μ)
    (hmean : ∀ i k, (∫ ω, X i ω k ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceNorm U (X i ω) ≤ η) :
    BoundedIndependentHypotheses μ (projectedObservations U X) η := by
  refine ⟨?_, ?_, ?_, hbound, hη⟩
  · intro i
    exact (measurable_faceProjection U).comp (hmeas i)
  · exact hind.comp (fun _ => faceProjection U) (fun _ => measurable_faceProjection U)
  · intro i j
    exact integral_faceProjection_zero U (X i) (hint i) (hmean i) j

/-- Positive face variance rules out the vacuous empty observation array and
therefore forces the numerical face envelope to be nonnegative. -/
theorem faceEnvelope_nonneg_of_positive_variance {r m n : ℕ} [NeZero m]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin m → Fin r → ℝ) (X : Fin n → Ω → Fin r → ℝ) {η v : ℝ}
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceNorm U (X i ω) ≤ η) (hv : 0 < v)
    (hvariance : ∀ j, covariance μ (fun ω => faceProjection U (sumVector X ω)) j j = v) :
    0 ≤ η := by
  by_cases hn : n = 0
  · subst n
    have hh := hvariance (0 : Fin m)
    simp [sumVector, covariance, faceProjection] at hh
    linarith
  · let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    obtain ⟨ω, hω⟩ := (hbound i).exists
    exact (faceNorm_nonneg U (X i ω)).trans hω

/-- The generic face layer is exactly the pullback of the archived coordinate layer. -/
theorem mem_faceLayer_iff_projected {r m : ℕ} (U : Fin m → Fin r → ℝ)
    (a : Fin m → ℝ) (s : ℝ) (x : Fin r → ℝ) :
    x ∈ faceLayer U a s ↔
      faceProjection U x ∈ RectangleCLT.Companion.SplitV4.projectedFaceLayer a s := Iff.rfl

/-- The bounded intrinsic anti-concentration inequality in the printed face
coordinates, including arbitrary independent noise on the original space. -/
theorem boundedFaceLayer_intrinsic {r m n : ℕ} [NeZero m]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin m → Fin r → ℝ) (X : Fin n → Ω → Fin r → ℝ) {η v : ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hint : ∀ i k, Integrable (fun ω => X i ω k) μ)
    (hmean : ∀ i k, (∫ ω, X i ω k ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceNorm U (X i ω) ≤ η)
    (hv : 0 < v)
    (hvariance : ∀ j, covariance μ (fun ω => faceProjection U (sumVector X ω)) j j = v)
    (R : Ω → Fin r → ℝ) (hR : Measurable R) (hRind : IndepFun (sumVector X) R μ)
    (a : Fin m → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | sumVector X ω + R ω ∈ faceLayer U a s} ≤
      64 * ((s + η) / v * ∫ ω, faceNorm U (sumVector X ω) ∂μ) := by
  have hη := faceEnvelope_nonneg_of_positive_variance μ U X hbound hv hvariance
  have hproj := projectedObservations_boundedHypotheses μ U X hη hmeas hind hint hmean hbound
  have hsum : sumVector (projectedObservations U X) =
      (fun ω => faceProjection U (sumVector X ω)) := funext (projectedObservations_sum U X)
  have hdiag : ∀ j, covariance μ (sumVector (projectedObservations U X)) j j = v := by
    rw [hsum]
    exact hvariance
  have hind' : IndepFun (sumVector (projectedObservations U X))
      (fun ω => faceProjection U (R ω)) μ := by
    rw [hsum]
    exact hRind.comp (measurable_faceProjection U) (measurable_faceProjection U)
  have hh := coordinateLayer_independent_printed
    μ (projectedObservations U X) hproj hv hdiag (fun ω => faceProjection U (R ω))
    ((measurable_faceProjection U).comp hR) hind' a hs
  simp_rw [projectedObservations_sum, ← faceProjection_add] at hh
  exact hh

/-- Both intrinsic and logarithmic alternatives hold simultaneously. The
face count is displayed here; for rectangles it is `m = 2p`. -/
theorem boundedFaceLayer_min {r m n : ℕ} [NeZero m]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin m → Fin r → ℝ) (X : Fin n → Ω → Fin r → ℝ) {η v : ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hint : ∀ i k, Integrable (fun ω => X i ω k) μ)
    (hmean : ∀ i k, (∫ ω, X i ω k ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceNorm U (X i ω) ≤ η)
    (hv : 0 < v)
    (hvariance : ∀ j, covariance μ (fun ω => faceProjection U (sumVector X ω)) j j = v)
    (R : Ω → Fin r → ℝ) (hR : Measurable R) (hRind : IndepFun (sumVector X) R μ)
    (a : Fin m → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | sumVector X ω + R ω ∈ faceLayer U a s} ≤
      256 * min 1 (min (((s + η) / v) * ∫ ω, faceNorm U (sumVector X ω) ∂μ)
        ((s + η) * Real.sqrt (dimensionLog m / v))) := by
  have hη := faceEnvelope_nonneg_of_positive_variance μ U X hbound hv hvariance
  have hproj := projectedObservations_boundedHypotheses μ U X hη hmeas hind hint hmean hbound
  have hsum : sumVector (projectedObservations U X) =
      (fun ω => faceProjection U (sumVector X ω)) := funext (projectedObservations_sum U X)
  have hdiag : ∀ j, covariance μ (sumVector (projectedObservations U X)) j j = v := by
    rw [hsum]
    exact hvariance
  have hind' : IndepFun (sumVector (projectedObservations U X))
      (fun ω => faceProjection U (R ω)) μ := by
    rw [hsum]
    exact hRind.comp (measurable_faceProjection U) (measurable_faceProjection U)
  have hh := coordinateLayer_independent_min_printed
    μ (projectedObservations U X) hproj hv hdiag (fun ω => faceProjection U (R ω))
    ((measurable_faceProjection U).comp hR) hind' a hs
  simp_rw [projectedObservations_sum, ← faceProjection_add] at hh
  exact hh


/-- Passing from `p` coordinate pairs to `2p` faces changes the logarithmic
factor by at most an absolute constant, including `p = 1`. -/
theorem dimensionLog_double_le {p : ℕ} (hp : 1 ≤ p) :
    dimensionLog (2 * p) ≤ 2 * dimensionLog p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
  have heq : dimensionLog (2 * p) = Real.log 2 + dimensionLog p := by
    simp only [dimensionLog, Nat.cast_mul, Nat.cast_ofNat]
    rw [show Real.exp 1 * (2 * (p : ℝ)) = 2 * (Real.exp 1 * p) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hL := log_exp_mul_nat_ge_one hp
  change 1 ≤ dimensionLog p at hL
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hh
    exact hh
  rw [heq]
  linarith

theorem sqrt_dimensionLog_double_le {p : ℕ} (hp : 1 ≤ p) {v : ℝ} (hv : 0 < v) :
    Real.sqrt (dimensionLog (2 * p) / v) ≤ 2 * Real.sqrt (dimensionLog p / v) := by
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hdouble := dimensionLog_double_le hp
  have hh : dimensionLog (2 * p) / v ≤ 4 * (dimensionLog p / v) := by
    apply (div_le_iff₀ hv).mpr
    have hcancel : 4 * (dimensionLog p / v) * v = 4 * dimensionLog p := by field_simp
    rw [hcancel]
    linarith
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt (div_nonneg hL hv.le)]

/-- The bounded-sum half of the printed rectangle anti-concentration lemma.
The count is `2p`, while the logarithmic factor is the paper's `log(ep)`. -/
theorem boundedRectangleFaceLayer_min {r p n : ℕ} (hp : 1 ≤ p)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin (2 * p) → Fin r → ℝ) (X : Fin n → Ω → Fin r → ℝ) {η v : ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hint : ∀ i k, Integrable (fun ω => X i ω k) μ)
    (hmean : ∀ i k, (∫ ω, X i ω k ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceNorm U (X i ω) ≤ η)
    (hv : 0 < v)
    (hvariance : ∀ j, covariance μ (fun ω => faceProjection U (sumVector X ω)) j j = v)
    (R : Ω → Fin r → ℝ) (hR : Measurable R) (hRind : IndepFun (sumVector X) R μ)
    (a : Fin (2 * p) → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | sumVector X ω + R ω ∈ faceLayer U a s} ≤
      512 * min 1 (min (((s + η) / v) * ∫ ω, faceNorm U (sumVector X ω) ∂μ)
        ((s + η) * Real.sqrt (dimensionLog p / v))) := by
  letI : NeZero (2 * p) := ⟨Nat.mul_ne_zero (by decide) (by omega)⟩
  have hη := faceEnvelope_nonneg_of_positive_variance μ U X hbound hv hvariance
  let P := μ.real {ω | sumVector X ω + R ω ∈ faceLayer U a s}
  let I := ((s + η) / v) * ∫ ω, faceNorm U (sumVector X ω) ∂μ
  let J := (s + η) * Real.sqrt (dimensionLog p / v)
  have hI : 0 ≤ I := mul_nonneg (div_nonneg (add_nonneg hs hη) hv.le)
    (integral_nonneg (fun ω => faceNorm_nonneg U _))
  have hP₁ : P ≤ 1 := measureReal_le_one
  have hP₂ : P ≤ 512 * I := by
    have hh := boundedFaceLayer_intrinsic μ U X hmeas hind hint hmean hbound hv hvariance R hR hRind a hs
    change P ≤ 64 * I at hh
    linarith
  have hP₃ : P ≤ 512 * J := by
    have hh := boundedFaceLayer_min μ U X hmeas hind hint hmean hbound hv hvariance R hR hRind a hs
    have hj : P ≤ 256 * ((s + η) * Real.sqrt (dimensionLog (2 * p) / v)) :=
      hh.trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num))
    calc
      P ≤ _ := hj
      _ ≤ 256 * ((s + η) * (2 * Real.sqrt (dimensionLog p / v))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (sqrt_dimensionLog_double_le hp hv) (add_nonneg hs hη)) (by norm_num)
      _ = 512 * J := by dsimp [J]; ring
  have hh : P / 512 ≤ min 1 (min I J) := by
    apply le_min
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).mpr
      linarith
    · apply le_min
      · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).mpr
        simpa only [mul_comm] using hP₂
      · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).mpr
        simpa only [mul_comm] using hP₃
  have hh' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).mp hh
  simpa only [P, I, J, mul_comm] using hh'

end RectangleCLTArxivV1
