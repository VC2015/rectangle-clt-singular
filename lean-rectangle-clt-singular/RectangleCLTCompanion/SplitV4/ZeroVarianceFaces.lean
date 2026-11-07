import RectangleCLTCompanion.SplitV4.PolynomialFaceTransfer

/-!
# Deleting zero-variance faces

For an actual centered square-integrable vector and its exact Gaussian
covariance factor, a zero-variance linear form is zero almost surely under
both laws. A negative threshold on such a face gives probability zero under
both laws; nonnegative thresholds allow the face to be deleted exactly.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

variable {Ω : Type*} [MeasurableSpace Ω] {p m r : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem centered_linear_form_ae_zero_of_variance_zero
    (W : Ω → Vector p) (v : Vector p)
    (hL2 : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hc : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hv : dotProduct v ((covariance μ W).mulVec v) = 0) :
    ∀ᵐ ω ∂μ, dotProduct v (W ω) = 0 := by
  let M : Matrix (Fin 1) (Fin p) ℝ := fun _ => v
  have hm : (∫ ω, dotProduct v (W ω) ∂μ) = 0 := by
    unfold dotProduct
    rw [integral_finset_sum Finset.univ (fun j _ =>
      ((hL2 j).integrable (by norm_num)).const_mul _)]
    simp only [integral_const_mul, hc, mul_zero, Finset.sum_const_zero]
  have he : (fun ω => dotProduct v (W ω)) = ∑ j, (fun ω => v j * W ω j) := by
    funext ω
    simp only [dotProduct, Finset.sum_apply]
  have hi : MemLp (fun ω => dotProduct v (W ω)) 2 μ := by
    rw [he]
    exact memLp_finset_sum' Finset.univ (fun j _ => (hL2 j).const_mul _)
  have hcov := congrArg (fun S : Matrix (Fin 1) (Fin 1) ℝ => S 0 0)
    (covariance_mulVec_of_centered_memLp μ W M hL2 hc)
  have heq : (∫ ω, dotProduct v (W ω)^2 ∂μ) =
      dotProduct v ((covariance μ W).mulVec v) := by
    change (∫ ω, dotProduct v (W ω) * dotProduct v (W ω) ∂μ) -
      (∫ ω, dotProduct v (W ω) ∂μ) * (∫ ω, dotProduct v (W ω) ∂μ) =
        (M * covariance μ W * M.transpose) 0 0 at hcov
    have hr : (M * covariance μ W * M.transpose) 0 0 =
        dotProduct v ((covariance μ W).mulVec v) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, M, Matrix.mulVec,
        dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    simpa only [hm, mul_zero, sub_zero, hr, pow_two] using hcov
  have hz := (integral_eq_zero_iff_of_nonneg
    (fun ω => sq_nonneg (dotProduct v (W ω))) hi.integrable_sq).mp (heq.trans hv)
  filter_upwards [hz] with ω hω
  exact sq_eq_zero_iff.mp hω

theorem gaussian_linear_form_ae_zero_of_variance_zero
    (A : Matrix (Fin p) (Fin p) ℝ) (v : Vector p)
    (hv : dotProduct v ((A*A.transpose).mulVec v) = 0) :
    ∀ᵐ x ∂gaussianLaw A, dotProduct v x = 0 := by
  have hz : A.transpose.mulVec v = 0 := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at hv
    exact dotProduct_self_eq_zero.mp hv
  rw [gaussianLaw]
  apply (ae_map_iff (measurable_mulVec A).aemeasurable
    ((continuous_const.matrix_dotProduct continuous_id).measurable (measurableSet_singleton 0))).mpr
  apply ae_of_all
  intro x
  change dotProduct v (A.mulVec x) = 0
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hz, zero_dotProduct]

def retainedFaceNormals (ν : Matrix (Fin m) (Fin p) ℝ) (keep : Fin r → Fin m) :
    Matrix (Fin r) (Fin p) ℝ := fun β => ν (keep β)

theorem facePolyhedron_deleted_faces_iff
    (ν : Matrix (Fin m) (Fin p) ℝ) (keep : Fin r → Fin m)
    (a : Vector m) (x : Vector p)
    (hx : ∀ α, α ∉ Set.range keep → dotProduct (ν α) x = 0)
    (ha : ∀ α, α ∉ Set.range keep → 0 ≤ a α) :
    x ∈ facePolyhedron ν a ↔
      x ∈ facePolyhedron (retainedFaceNormals ν keep) (a ∘ keep) := by
  constructor
  · intro h β
    exact h (keep β)
  · intro h α
    by_cases hα : α ∈ Set.range keep
    · obtain ⟨β, rfl⟩ := hα
      exact h β
    · rw [hx α hα]
      exact ha α hα

theorem zero_variance_faces_ae_zero
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hL2 : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hc : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hA : A*A.transpose = covariance μ W)
    (ν : Matrix (Fin m) (Fin p) ℝ) (keep : Fin r → Fin m)
    (hzero : ∀ α, α ∉ Set.range keep →
      dotProduct (ν α) ((covariance μ W).mulVec (ν α)) = 0) :
    (∀ᵐ ω ∂μ, ∀ α, α ∉ Set.range keep → dotProduct (ν α) (W ω) = 0) ∧
    (∀ᵐ x ∂gaussianLaw A, ∀ α, α ∉ Set.range keep → dotProduct (ν α) x = 0) := by
  constructor
  · apply ae_all_iff.mpr
    intro α
    by_cases hα : α ∈ Set.range keep
    · exact ae_of_all _ fun _ hn => (hn hα).elim
    · filter_upwards [centered_linear_form_ae_zero_of_variance_zero W (ν α) hL2 hc
        (hzero α hα)] with ω hω
      exact fun _ => hω
  · apply ae_all_iff.mpr
    intro α
    by_cases hα : α ∈ Set.range keep
    · exact ae_of_all _ fun _ hn => (hn hα).elim
    · have hv : dotProduct (ν α) ((A*A.transpose).mulVec (ν α)) = 0 := by
        rw [hA]
        exact hzero α hα
      filter_upwards [gaussian_linear_form_ae_zero_of_variance_zero A (ν α) hv] with x hx
      exact fun _ => hx

/-- At nonnegative deleted thresholds, both original and Gaussian
polyhedron probabilities are exactly preserved. -/
theorem zero_variance_faces_probability_eq
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hL2 : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hc : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hA : A*A.transpose = covariance μ W)
    (ν : Matrix (Fin m) (Fin p) ℝ) (keep : Fin r → Fin m)
    (hzero : ∀ α, α ∉ Set.range keep →
      dotProduct (ν α) ((covariance μ W).mulVec (ν α)) = 0)
    (a : Vector m) (ha : ∀ α, α ∉ Set.range keep → 0 ≤ a α) :
    μ.real (W ⁻¹' facePolyhedron ν a) =
        μ.real (W ⁻¹' facePolyhedron (retainedFaceNormals ν keep) (a ∘ keep)) ∧
      (gaussianLaw A).real (facePolyhedron ν a) =
        (gaussianLaw A).real (facePolyhedron (retainedFaceNormals ν keep) (a ∘ keep)) := by
  obtain ⟨hw, hg⟩ := zero_variance_faces_ae_zero W A hL2 hc hA ν keep hzero
  constructor
  · apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hw] with ω hω
    exact propext (facePolyhedron_deleted_faces_iff ν keep a (W ω) hω ha)
  · apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hg] with x hx
    exact propext (facePolyhedron_deleted_faces_iff ν keep a x hx ha)

/-- A negative threshold on any deleted zero-variance face makes both
actual probabilities zero, including the Gaussian probability. -/
theorem zero_variance_faces_negative_threshold
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hL2 : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hc : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hA : A*A.transpose = covariance μ W)
    (ν : Matrix (Fin m) (Fin p) ℝ) (keep : Fin r → Fin m)
    (hzero : ∀ α, α ∉ Set.range keep →
      dotProduct (ν α) ((covariance μ W).mulVec (ν α)) = 0)
    (a : Vector m) (α : Fin m) (hα : α ∉ Set.range keep) (ha : a α < 0) :
    μ (W ⁻¹' facePolyhedron ν a) = 0 ∧ (gaussianLaw A) (facePolyhedron ν a) = 0 := by
  obtain ⟨hw, hg⟩ := zero_variance_faces_ae_zero W A hL2 hc hA ν keep hzero
  constructor
  · apply measure_zero_iff_ae_nmem.mpr
    filter_upwards [hw] with ω hω
    intro hx
    have hb := hx α
    rw [hω α hα] at hb
    exact (not_le_of_gt ha) hb
  · apply measure_zero_iff_ae_nmem.mpr
    filter_upwards [hg] with x hx
    intro hmem
    have hb := hmem α
    rw [hx α hα] at hb
    exact (not_le_of_gt ha) hb

theorem polyhedralDistance_le_delete_zero_variance_faces
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hL2 : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hc : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hA : A*A.transpose = covariance μ W)
    (ν : Matrix (Fin m) (Fin p) ℝ) (keep : Fin r → Fin m)
    (hzero : ∀ α, α ∉ Set.range keep →
      dotProduct (ν α) ((covariance μ W).mulVec (ν α)) = 0) :
    polyhedralDistance μ W A ν ≤ polyhedralDistance μ W A (retainedFaceNormals ν keep) := by
  apply csSup_le (show (Set.range (polyhedronError μ W A ν)).Nonempty from ⟨_, ⟨0, rfl⟩⟩)
  rintro e ⟨a, rfl⟩
  by_cases ha : ∀ α, α ∉ Set.range keep → 0 ≤ a α
  · obtain ⟨hw, hg⟩ := zero_variance_faces_probability_eq W A hL2 hc hA ν keep hzero a ha
    unfold polyhedronError
    rw [hw, hg]
    exact le_csSup (polyhedralErrors_bddAbove μ W A (retainedFaceNormals ν keep)) ⟨a ∘ keep, rfl⟩
  · push_neg at ha
    obtain ⟨α, hα, ha⟩ := ha
    obtain ⟨hw, hg⟩ := zero_variance_faces_negative_threshold W A hL2 hc hA ν keep hzero a α hα ha
    have he : polyhedronError μ W A ν a = 0 := by
      simp only [polyhedronError, measureReal_def, hw, hg, ENNReal.toReal_zero, sub_self, abs_zero]
    rw [he]
    exact (abs_nonneg _).trans
      (le_csSup (polyhedralErrors_bddAbove μ W A (retainedFaceNormals ν keep)) ⟨0, rfl⟩)

/-- Deletion is an equality of the actual suprema for every finite
subfamily. The retained indexing may be any injection. -/
theorem polyhedralDistance_delete_zero_variance_faces
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hL2 : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hc : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hA : A*A.transpose = covariance μ W)
    (ν : Matrix (Fin m) (Fin p) ℝ) (keep : Fin r → Fin m)
    (hkeep : Function.Injective keep)
    (hzero : ∀ α, α ∉ Set.range keep →
      dotProduct (ν α) ((covariance μ W).mulVec (ν α)) = 0) :
    polyhedralDistance μ W A ν = polyhedralDistance μ W A (retainedFaceNormals ν keep) := by
  apply le_antisymm (polyhedralDistance_le_delete_zero_variance_faces W A hL2 hc hA ν keep hzero)
  apply csSup_le (show (Set.range (polyhedronError μ W A (retainedFaceNormals ν keep))).Nonempty
    from ⟨_, ⟨0, rfl⟩⟩)
  rintro e ⟨b, rfl⟩
  let a : Vector m := Function.extend keep b 0
  have ha : ∀ α, α ∉ Set.range keep → 0 ≤ a α := by
    intro α hα
    change 0 ≤ Function.extend keep b 0 α
    rw [Function.extend_apply' (f := keep) b (0 : Vector m) α hα]
    rfl
  have he : a ∘ keep = b := funext (fun β => hkeep.extend_apply b (0 : Vector m) β)
  obtain ⟨hw, hg⟩ := zero_variance_faces_probability_eq W A hL2 hc hA ν keep hzero a ha
  have herr : polyhedronError μ W A ν a =
      polyhedronError μ W A (retainedFaceNormals ν keep) b := by
    unfold polyhedronError
    rw [hw, hg, he]
  rw [← herr]
  exact le_csSup (polyhedralErrors_bddAbove μ W A ν) ⟨a, rfl⟩

theorem polyhedralDistance_empty_faces
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin 0) (Fin p) ℝ) : polyhedralDistance μ W A ν = 0 := by
  have he (a : Vector 0) : polyhedronError μ W A ν a = 0 := by
    have hs : facePolyhedron ν a = Set.univ := by
      ext x
      simp only [facePolyhedron, Set.mem_setOf_eq, Set.mem_univ]
      exact ⟨fun _ => trivial, fun _ α => α.elim0⟩
    simp only [polyhedronError, hs, Set.preimage_univ, measureReal_univ_eq_one,
      sub_self, abs_zero]
  have hr : Set.range (polyhedronError μ W A ν) = {0} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact he a
    · intro hx
      refine ⟨0, ?_⟩
      simpa only [Set.mem_singleton_iff.mp hx] using he 0
  simp only [polyhedralDistance, hr, csSup_singleton]

theorem polyhedralDistance_zero_of_all_face_variances_zero
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hL2 : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hc : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hA : A*A.transpose = covariance μ W)
    (ν : Matrix (Fin m) (Fin p) ℝ)
    (hzero : ∀ α, dotProduct (ν α) ((covariance μ W).mulVec (ν α)) = 0) :
    polyhedralDistance μ W A ν = 0 := by
  rw [polyhedralDistance_delete_zero_variance_faces W A hL2 hc hA ν
    (Fin.elim0 : Fin 0 → Fin m) (by intro a; exact a.elim0)
    (fun α _ => hzero α)]
  exact polyhedralDistance_empty_faces W A _

/-- Polynomial Corollary 3 after deleting any zero-variance faces. The
remaining rate uses exactly their number and the safe scale `J² B`.
If no face remains, the preceding theorem gives distance zero instead. -/
theorem polynomialPolyhedralCLT_delete_zero_variance_faces
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (hr : 1 ≤ r) (hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) {q B : ℝ} (hq : 2 < q) (hB : 1 ≤ B)
    (h : PolynomialIndependentHypotheses μ X q B)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (normalizedObservationSum X))
    (ν : Matrix (Fin m) (Fin p) ℝ) (keep : Fin r → Fin m)
    (hzero : ∀ α, α ∉ Set.range keep → dotProduct (ν α)
      ((covariance μ (normalizedObservationSum X)).mulVec (ν α)) = 0)
    (σ : Vector r) (J : ℝ) (hσ : ∀ β, 0 < σ β)
    (hν : ∀ β, (∑ j, |ν (keep β) j|) ≤ J * σ β)
    (hvariance : ∀ β, dotProduct (ν (keep β))
      ((covariance μ (normalizedObservationSum X)).mulVec (ν (keep β))) = (σ β)^2) :
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤
      polynomialUniversalConstant q * min 1 (polynomialCombinedRate n r (J^2*B) q) := by
  have hL2 : ∀ j, MemLp (fun ω => normalizedObservationSum X ω j) 2 μ := by
    simpa only [sumVector_normalizedSummands] using
      memLp_sumVector_coordinate (normalizedSummands_coordinate_memLp_two h.coordinate_memLp_two)
  have hc : ∀ j, (∫ ω, normalizedObservationSum X ω j ∂μ) = 0 := by
    simpa only [sumVector_normalizedSummands] using
      integral_sumVector_coordinate_zero
        (fun i j => ((normalizedSummands_coordinate_memLp_two h.coordinate_memLp_two i j).integrable
          (by norm_num))) (normalizedSummands_centered h.centered)
  apply (polyhedralDistance_le_delete_zero_variance_faces
    (normalizedObservationSum X) A hL2 hc hA ν keep hzero).trans
  exact polynomialPolyhedralCLT μ hr hn X hq hB h A hA
    (retainedFaceNormals ν keep) σ J hσ hν hvariance

end
end RectangleCLT.Companion.SplitV4
