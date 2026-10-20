import RectangleCLTCompanion.SignedSurfaceDyadic
import RectangleCLT.GaussianTubeDomination

/-! A single existing four-normal projection radius controls all singleton
and ridge directions. Its Gaussian moments already include family-size
counting, and its Lipschitz bound transfers source shells to output tails. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

/-- All unit active-span coordinates are controlled by the same radius,
without any inverse Gram eigenvalue bound. -/
theorem unit_active_span_coordinate_le {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hq0 : 0 < q) (hq : q ≤ 4) (u : EuclideanSpace ℝ (Fin p))
    (hu : u ∈ S.normalSpan A) (hun : ‖u‖ = 1) (z : Vector p) :
    |⟪u, projectionEuclideanVector z⟫_ℝ| ≤ fourFaceProjectionRadius A z := by
  simpa only [hun, one_mul] using
    S.abs_inner_normalSpan_le_projectionRadius A hq0 hq hu z

/-- A source shell stays in the corresponding output tail whenever the
physical displacement is at most one. Coefficient sizes are irrelevant. -/
theorem output_projection_tail_of_displacement {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (z d : Vector p) {R : ℝ}
    (hsource : R / 2 ≤ fourFaceProjectionRadius A z)
    (hd : ‖projectionEuclideanVector d‖ ≤ 1) :
    R / 2 - 1 ≤ fourFaceProjectionRadius A (z + d) := by
  have hh := fourFaceProjectionRadius_add_le A (z + d) (-d)
  have hneg : projectionEuclideanVector (-d) = -projectionEuclideanVector d := by
    ext j
    rfl
  rw [add_neg_cancel_right, hneg, norm_neg] at hh
  linarith

/-- Genuine polynomial moments of the common radius, with its finite
family-size count already discharged by the old Gaussian development. -/
theorem integrable_fourFaceProjectionRadius_moment {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (q : ℕ) :
    Integrable (fun z => (1 + fourFaceProjectionRadius A z) ^ q) (standardGaussian p) ∧
      (∫ z, (1 + fourFaceProjectionRadius A z) ^ q ∂standardGaussian p) ≤
        (Real.sqrt (dimensionLog p)) ^ q * Real.exp (8 + (4 * (q + 1 : ℝ)) ^ 2 / 2) := by
  let L := dimensionLog p
  let K := fourFaceProjectionRadius A
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (log_exp_mul_nat_ge_one hp)
  have hmoment := fourFaceProjectionRadius_weighted_moment_le hp A
    (M := Real.sqrt L) le_rfl q
  have hpoint (z : Vector p) : (1 + K z) ^ q ≤
      Real.exp (K z / Real.sqrt L) * (1 + K z) ^ q := by
    have he : 1 ≤ Real.exp (K z / Real.sqrt L) :=
      Real.one_le_exp_iff.mpr (div_nonneg (fourFaceProjectionRadius_nonneg A z)
        (Real.sqrt_nonneg _))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he
      (pow_nonneg (by linarith [fourFaceProjectionRadius_nonneg A z]) q)
  have hi : Integrable (fun z => (1 + K z) ^ q) (standardGaussian p) := by
    apply hmoment.1.mono'
      ((measurable_const.add (measurable_fourFaceProjectionRadius A)).pow_const q).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (pow_nonneg (by linarith [fourFaceProjectionRadius_nonneg A z]) q)]
      exact hpoint z
  exact ⟨hi, (integral_mono hi hmoment.1 hpoint).trans hmoment.2⟩

/-- The complete Gaussian shell series needed by the physical tube
argument. This holds for every covariance factor, including singular ones. -/
theorem fourFaceProjectionRadius_dyadic_tail_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {q : ℕ} (hq : 1 ≤ q) :
    (∑' n : ℕ, dyadicRadius n ^ q * (standardGaussian p).real
      {z | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A z}) ≤
      (2 * 2 ^ q) * (Real.sqrt (dimensionLog p)) ^ q *
        Real.exp (8 + (4 * (q + 1 : ℝ)) ^ 2 / 2) := by
  have hm := integrable_fourFaceProjectionRadius_moment hp A q
  have ht := tsum_dyadic_tail_masses_le (standardGaussian p) (fourFaceProjectionRadius A)
    (measurable_fourFaceProjectionRadius A) (fourFaceProjectionRadius_nonneg A) hq hm.1
  exact ht.trans ((mul_le_mul_of_nonneg_left hm.2 (by positivity)).trans_eq (by ring))

end
end RectangleCLT.Companion.SignedSurface
