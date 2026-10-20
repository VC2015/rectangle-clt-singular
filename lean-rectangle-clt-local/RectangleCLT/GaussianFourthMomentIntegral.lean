import RectangleCLT.GaussianFourthDetAssembly

/-! Actual Fubini identification between determinant-weighted Gaussian face
moments averaged over a measurable shift and the product-law tube moments. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

open GaussianTube

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

/-- The Gaussian kernel average is integrable under every measurable random
shift; its positive projection-polynomial envelope does not depend on the shift. -/
theorem integrable_gaussianSoftFaceMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (W : Ω → Vector p) (hW : Measurable W) {q : ℕ}
    (T : CompatibleFaceTuple p q) (k : ℕ) :
    Integrable (fun ω => s.gaussianSoftFaceMoment A (W ω) T.activeFaceSet k) μ := by
  have hi := integrable_softFace_projectionPolynomial_shift (μ := μ) T s A W hW hp k
  simpa only [gaussianSoftFaceMoment, projectionPolynomial, activeFaces, mul_comm] using
    hi.integral_prod_right

theorem integrable_faceMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (W : Ω → Vector p) (hW : Measurable W) {q : ℕ}
    (T : CompatibleFaceTuple p q) (k : ℕ) :
    Integrable (fun ω => faceMoment T s A (W ω) k) μ := by
  simpa only [s.faceMoment_eq_gaussianSoftFaceMoment] using
    (s.integrable_gaussianSoftFaceMoment_comp μ hp A W hW T k).const_mul
      ((T.gram (A * A.transpose)).det / s.bandwidth ^ q)

/-- Every finite determinant-weighted active-face sum is integrable under
an arbitrary measurable random shift. -/
theorem integrable_gaussianFaceMomentSum_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (W : Ω → Vector p) (hW : Measurable W) (q k : ℕ) :
    Integrable (fun ω => s.gaussianFaceMomentSum A (W ω) q k) μ := by
  classical
  exact integrable_finset_sum Finset.univ (fun T _ =>
    (s.integrable_gaussianSoftFaceMoment_comp μ hp A W hW T.val k).const_mul
      ((T.val.gram (A * A.transpose)).det))

theorem gaussianFaceMomentSum_div_eq_ordered_faceMoments
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q k : ℕ) :
    s.gaussianFaceMomentSum A x q k / s.bandwidth ^ q =
      ∑ T : OrderedFaceTuples s.faces q, faceMoment T.val s A x k := by
  classical
  unfold gaussianFaceMomentSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro T _
  rw [s.faceMoment_eq_gaussianSoftFaceMoment]
  ring

/-- The random-shift average of the actual Gaussian face-moment sum is the
ordered sum of genuine product-law shifted face moments. No probabilistic
concentration or comparison hypothesis is assumed. -/
theorem integral_gaussianFaceMomentSum_div_eq_shiftedFaceMoments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (W : Ω → Vector p) (hW : Measurable W) (q k : ℕ) :
    (∫ ω, s.gaussianFaceMomentSum A (W ω) q k ∂μ) / s.bandwidth ^ q =
      ∑ T : OrderedFaceTuples s.faces q, shiftedFaceMoment μ T.val s A W k := by
  classical
  calc
    _ = ∫ ω, s.gaussianFaceMomentSum A (W ω) q k / s.bandwidth ^ q ∂μ :=
      (integral_div _ _).symm
    _ = ∫ ω, ∑ T : OrderedFaceTuples s.faces q, faceMoment T.val s A (W ω) k ∂μ :=
      integral_congr_ae (ae_of_all _ (fun ω =>
        s.gaussianFaceMomentSum_div_eq_ordered_faceMoments A (W ω) q k))
    _ = ∑ T : OrderedFaceTuples s.faces q, ∫ ω, faceMoment T.val s A (W ω) k ∂μ :=
      integral_finset_sum Finset.univ (fun T _ => s.integrable_faceMoment_comp μ hp A W hW T.val k)
    _ = _ := Finset.sum_congr rfl (fun T _ => integral_faceMoment_shift_eq T.val s A W hW hp k)

end
end RectangleCLT.FaceSmoother
