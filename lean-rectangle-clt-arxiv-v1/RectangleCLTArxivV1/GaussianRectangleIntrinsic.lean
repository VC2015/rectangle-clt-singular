import RectangleCLTArxivV1.ActiveFaceCoordinates
import RectangleCLTArxivV1.IntrinsicGaussianBoundary
import RectangleCLTArxivV1.GaussianWidthOrder

/-! Intrinsic Gaussian concentration for the actual signed faces of an
archived rectangle smoother. Missing faces and empty face systems are allowed. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT
open RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable section

theorem activeCoordinateNormals_covariance_diagonal {p : ℕ}
    (s : FaceSmoother p) (Q : Matrix (Fin p) (Fin p) ℝ) (v : ℝ)
    (hdiag : ∀ j, Q j j = v) (j : Fin s.faces.card) :
    dotProduct (activeCoordinateNormals s j) (Q.mulVec (activeCoordinateNormals s j)) = v := by
  classical
  unfold activeCoordinateNormals signedDirection
  cases hb : (activeFaceEquiv s j).1.2 <;>
    simp [signedVectors, Matrix.mulVec_neg, Matrix.mulVec_single, hdiag, single_dotProduct]

/-- The Gaussian intrinsic bound for any actual active rectangle face
system, bounded by the full Gaussian expected maximum. -/
theorem gaussianRectangleBoundary_intrinsic_fixed_shift {p : ℕ}
    (s : FaceSmoother p) (G : Matrix (Fin p) (Fin p) ℝ) (b : Vector p)
    {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hdiag : ∀ j, (G*G.transpose) j j = v) :
    (gaussianLaw G).real {x | x+b ∈ s.boundaryLayer d} ≤
      (2*d/v)*gaussianMaximumMean G := by
  by_cases he : s.faces = ∅
  · simp only [boundaryLayer_empty_of_faces_empty s he, Set.mem_empty_iff_false,
      Set.setOf_false, measureReal_empty]
    exact mul_nonneg (by positivity) (gaussianMaximumMean_nonneg G)
  · letI : NeZero s.faces.card := ⟨Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he)⟩
    have hvar := activeCoordinateNormals_covariance_diagonal s (G*G.transpose) v hdiag
    have hb := gaussianIntrinsicBoundary_fixed_shift (activeCoordinateNormals s) G
      (activeFaceOffsets s) b hv hd hvar
    have hevent : {x | x+b ∈ gaussianPolyhedronLayer (activeCoordinateNormals s)
        (activeFaceOffsets s) d} = {x | x+b ∈ s.boundaryLayer d} := by
      ext x
      exact (boundaryLayer_eq_activeFaceLayer s d (x+b)).symm
    rw [hevent] at hb
    apply hb.trans ((min_le_right _ _).trans ?_)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply integral_mono (integrable_gaussian_faceProjectionNorm (activeCoordinateNormals s) G)
      (gaussianLaw_integrable_norm G)
    intro x
    change ‖faceProjection (activeCoordinateNormals s) x‖ ≤ ‖x‖
    rw [activeCoordinateProjection_eq]
    exact activeFaceProjection_norm_le s x

/-- Arbitrary independent shift laws retain the Gaussian intrinsic
coefficient, without a shift moment assumption. -/
theorem gaussianRectangleBoundary_intrinsic_product
    {E : Type*} [MeasurableSpace E] {p : ℕ}
    (s : FaceSmoother p) (G : Matrix (Fin p) (Fin p) ℝ)
    (τ : Measure E) [IsProbabilityMeasure τ] (R : E → Vector p) (hR : Measurable R)
    (b : Vector p) {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hdiag : ∀ j, (G*G.transpose) j j = v) :
    ((gaussianLaw G).prod τ).real {z | (z.1+R z.2)+b ∈ s.boundaryLayer d} ≤
      (2*d/v)*gaussianMaximumMean G := by
  apply product_event_probability_le_of_sections (gaussianLaw G) τ _
    ((s.measurableSet_boundaryLayer d).preimage
      ((measurable_fst.add (hR.comp measurable_snd)).add_const b))
  intro e
  simpa only [add_assoc] using
    gaussianRectangleBoundary_intrinsic_fixed_shift s G (R e+b) hv hd hdiag

/-- The actual full Gaussian maximum with common variance `v` obeys the
Gaussian MGF maximum bound after variance normalization. -/
theorem gaussianMaximumMean_le_common_variance {p : ℕ} (hp : 1 ≤ p)
    (G : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (G*G.transpose) j j = v) :
    gaussianMaximumMean G ≤ 2*Real.sqrt (v*dimensionLog p) := by
  let B := Real.sqrt (1/v) • G
  have hunit (j : Fin p) : (B*B.transpose) j j = 1 := by
    dsimp [B]
    rw [sqrt_smul_factor_gram _ (by positivity)]
    simp only [Matrix.smul_apply, smul_eq_mul, hdiag]
    field_simp
  have hb := gaussianLaw_integral_norm_le hp B hunit
  change gaussianMaximumMean B ≤ _ at hb
  dsimp only [B] at hb
  rw [gaussianMaximumMean_smul, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at hb
  have he : gaussianMaximumMean G/Real.sqrt v ≤ 2*Real.sqrt (dimensionLog p) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hb
  have hh := (div_le_iff₀ (Real.sqrt_pos.mpr hv)).mp he
  rw [Real.sqrt_mul hv.le]
  nlinarith

/-- The actual intrinsic Gaussian rectangle coefficient is logarithmic. -/
theorem gaussianMaximumMean_intrinsic_coefficient_le {p : ℕ} (hp : 1 ≤ p)
    (G : Matrix (Fin p) (Fin p) ℝ) {v d : ℝ} (hv : 0 < v) (hd : 0 ≤ d)
    (hdiag : ∀ j, (G*G.transpose) j j = v) :
    (2*d/v)*gaussianMaximumMean G ≤ 4*d*Real.sqrt (dimensionLog p/v) := by
  have hm := gaussianMaximumMean_le_common_variance hp G hv hdiag
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
  rw [Real.sqrt_mul hv.le, Real.sqrt_div hL]
  field_simp
  ring_nf
  rw [Real.sq_sqrt hv.le]
  ring


/-- The direct Gaussian MGF route for an arbitrary actual rectangle. -/
theorem gaussianRectangleBoundary_fixed_shift_logarithmic {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (G : Matrix (Fin p) (Fin p) ℝ) (b : Vector p)
    {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hdiag : ∀ j, (G*G.transpose) j j = v) :
    (gaussianLaw G).real {x | x+b ∈ s.boundaryLayer d} ≤
      4*d*Real.sqrt (dimensionLog p/v) :=
  (gaussianRectangleBoundary_intrinsic_fixed_shift s G b hv hd hdiag).trans
    (gaussianMaximumMean_intrinsic_coefficient_le hp G hv hd.le hdiag)

/-- The rectangle logarithmic consequence uses the actual Gaussian MGF
maximum bound, retaining the direct intrinsic Gaussian proof. -/
theorem gaussianRectangleBoundary_product_logarithmic
    {E : Type*} [MeasurableSpace E] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (G : Matrix (Fin p) (Fin p) ℝ)
    (τ : Measure E) [IsProbabilityMeasure τ] (R : E → Vector p) (hR : Measurable R)
    (b : Vector p) {v d : ℝ} (hv : 0 < v) (hd : 0 < d)
    (hdiag : ∀ j, (G*G.transpose) j j = v) :
    ((gaussianLaw G).prod τ).real {z | (z.1+R z.2)+b ∈ s.boundaryLayer d} ≤
      4*d*Real.sqrt (dimensionLog p/v) := by
  exact (gaussianRectangleBoundary_intrinsic_product s G τ R hR b hv hd hdiag).trans
    (gaussianMaximumMean_intrinsic_coefficient_le hp G hv hd.le hdiag)

end
end RectangleCLTArxivV1
