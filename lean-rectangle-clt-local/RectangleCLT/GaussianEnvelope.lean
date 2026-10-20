import RectangleCLT.GaussianNormalMap
import RectangleCLT.BoundedEnvelopeShift

/-! Gaussian short-scale derivative envelopes for the actual smoother.
The covariance may be singular. A common positive coordinate variance is
handled by normalization, and arbitrary independent shifts require no moments.
These bounds do not assert the localized triple- or fourth-face estimates. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal

namespace RectangleCLT

theorem normalizedFactor_unit_diagonal {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) :
    ∀ j, ((Real.sqrt v)⁻¹ • A * ((Real.sqrt v)⁻¹ • A).transpose) j j = 1 := by
  intro j
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hs2 := Real.sq_sqrt hv.le
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_apply, smul_eq_mul, hdiag]
  field_simp [ne_of_gt hs]

theorem gaussianLaw_integral_exp_norm_scaled_variance_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (b : ℝ) :
    (∫ x : Vector p, Real.exp ((b / (Real.sqrt v * Real.sqrt (dimensionLog p))) * ‖x‖)
      ∂gaussianLaw A) ≤ Real.exp (1 + b ^ 2 / 2) := by
  let B := (Real.sqrt v)⁻¹ • A
  have hB := normalizedFactor_unit_diagonal A hv hdiag
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hmap (C : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
      (∫ x : Vector p, Real.exp (t * ‖x‖) ∂gaussianLaw C) =
        ∫ z : Vector p, Real.exp (t * ‖C.mulVec z‖) ∂standardGaussian p :=
    integral_map (measurable_mulVec C).aemeasurable
      (measurable_norm.const_mul t).exp.aestronglyMeasurable
  rw [hmap]
  calc
    _ = ∫ z : Vector p, Real.exp ((b / Real.sqrt (dimensionLog p)) * ‖B.mulVec z‖)
        ∂standardGaussian p := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        dsimp only [B]
        rw [Matrix.smul_mulVec_assoc, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hs)]
        congr 1
        ring
    _ = ∫ x : Vector p, Real.exp ((b / Real.sqrt (dimensionLog p)) * ‖x‖)
        ∂gaussianLaw B := (hmap B _).symm
    _ ≤ _ := gaussianLaw_integral_exp_norm_scaled_le hp B hB b

theorem rowGram_abs_le_variance {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : 0 < v) (hdiag : ∀ j, (A * A.transpose) j j = v) (j k : Fin p) :
    |(A * A.transpose) j k| ≤ v := by
  have hrow (i : Fin p) : (∑ r, A i r ^ 2) = v := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hdiag i
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r => A j r) (fun r => A k r)
  rw [hrow, hrow] at hcs
  have heq : (A * A.transpose) j k = ∑ r, A j r * A k r := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [heq]
  nlinarith [sq_abs (∑ r, A j r * A k r), abs_nonneg (∑ r, A j r * A k r)]

theorem FaceWeights.covarianceContraction_ge_scaled_F_theta {p : ℕ}
    (w : FaceWeights p) (Q : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, Q j j = v) (habs : ∀ j k, |Q j k| ≤ v) :
    v * (w.F * w.theta) ≤ w.covarianceContraction Q := by
  let Q₀ := v⁻¹ • Q
  have hdiag₀ : ∀ j, Q₀ j j = 1 := by
    intro j
    dsimp [Q₀]
    rw [hdiag, inv_mul_cancel₀ hv.ne']
  have habs₀ : ∀ j k, |Q₀ j k| ≤ 1 := by
    intro j k
    dsimp [Q₀]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hv)]
    calc
      _ ≤ v⁻¹ * v := mul_le_mul_of_nonneg_left (habs j k) (inv_nonneg.mpr hv.le)
      _ = 1 := inv_mul_cancel₀ hv.ne'
  have hscale : w.covarianceContraction Q₀ = v⁻¹ * w.covarianceContraction Q := by
    unfold FaceWeights.covarianceContraction
    simp only [Q₀, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hh := mul_le_mul_of_nonneg_left (w.covarianceContraction_ge_F_theta Q₀ hdiag₀ habs₀) hv.le
  simpa only [hscale, ← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul] using hh

theorem normalHessian_trace_ge_scaled_variance {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r z : Vector p) :
    v * (s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r))) / s.bandwidth ≤
      Matrix.trace (normalHessian s A r z) := by
  rw [normalHessian, Matrix.trace_mul_cycle, s.potentialCoordinateHessian_contraction]
  exact div_le_div_of_nonneg_right
    ((s.weights (A.mulVec z + r)).covarianceContraction_ge_scaled_F_theta
      (A * A.transpose) hv hdiag (rowGram_abs_le_variance A hv hdiag)) s.bandwidth_pos.le

namespace FaceSmoother

/-- The Gaussian smaller-envelope bound for any common positive coordinate
variance. It applies to singular covariance matrices and every fixed shift. -/
theorem gaussian_expected_variance_le_of_diagonal {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p) :
    (∫ x : Vector p, s.F (x + r) * (1 - s.F (x + r)) ∂gaussianLaw A) ≤
      Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p / v) := by
  let a := Real.sqrt (dimensionLog p)
  let d := Real.sqrt v
  let t := 1 / (d * a)
  let K := s.bandwidth * a / d
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL₀ : 0 ≤ dimensionLog p := by linarith
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hd : 0 < d := Real.sqrt_pos.mpr hv
  have hd2 : d ^ 2 = v := Real.sq_sqrt hv.le
  have ht : 0 ≤ t := (div_pos zero_lt_one (mul_pos hd ha)).le
  have hK : 0 < K := div_pos (mul_pos s.bandwidth_pos ha) hd
  have hcoeff : K * t * v / s.bandwidth = 1 := by
    dsimp [K, t]
    field_simp [ne_of_gt hd, ne_of_gt ha, ne_of_gt s.bandwidth_pos]
    nlinarith only [congrArg (fun u : ℝ => s.bandwidth * a * u) hd2]
  have hW : Measurable (fun z : Vector p => A.mulVec z + r) :=
    (measurable_mulVec A).add measurable_const
  have hvarint := s.integrable_smallerEnvelope _ hW (μ := standardGaussian p)
  have hJint := (normalMap_integral_abs_det_le_exp_norm hp s A r ht).1
  have hpwise (z : Vector p) :
      s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r)) ≤
        K * |(fderiv ℝ (normalMap s A r t) z).det| := by
    have hh : t * (v * (s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r))) / s.bandwidth) ≤
        |(fderiv ℝ (normalMap s A r t) z).det| := by
      calc
        _ ≤ t * Matrix.trace (normalHessian s A r z) :=
          mul_le_mul_of_nonneg_left (normalHessian_trace_ge_scaled_variance s A hv hdiag r z) ht
        _ ≤ (1 + t • normalHessian s A r z).det :=
          posSemidef_mul_trace_le_det_one_add (normalHessian_posSemidef s A r z) ht
        _ ≤ _ := by rw [normalMap_fderiv_det]; exact le_abs_self _
    calc
      _ = (K * t * v / s.bandwidth) *
          (s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r))) := by rw [hcoeff, one_mul]
      _ = K * (t * (v * (s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r))) / s.bandwidth)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hh hK.le
  have hJbound : (∫ z, |(fderiv ℝ (normalMap s A r t) z).det| ∂standardGaussian p) ≤
      Real.exp (3 / 2 : ℝ) := by
    have hh := (normalMap_integral_abs_det_le_exp_norm hp s A r ht).2.trans
      (gaussianLaw_integral_exp_norm_scaled_variance_le hp A hv hdiag (1 : ℝ))
    convert hh using 1
    norm_num
  have hmap : (∫ x : Vector p, s.F (x + r) * (1 - s.F (x + r)) ∂gaussianLaw A) =
      ∫ z : Vector p, s.F (A.mulVec z + r) * (1 - s.F (A.mulVec z + r))
        ∂standardGaussian p := by
    apply integral_map (measurable_mulVec A).aemeasurable
    have hF : Measurable (fun x : Vector p => s.F (x + r)) :=
      s.continuous_F.measurable.comp (measurable_id.add measurable_const)
    exact (hF.mul (measurable_const.sub hF)).aestronglyMeasurable
  rw [hmap]
  calc
    _ ≤ ∫ z : Vector p, K * |(fderiv ℝ (normalMap s A r t) z).det| ∂standardGaussian p :=
      integral_mono hvarint (hJint.const_mul _) hpwise
    _ = K * (∫ z, |(fderiv ℝ (normalMap s A r t) z).det| ∂standardGaussian p) := integral_const_mul _ _
    _ ≤ K * Real.exp (3 / 2 : ℝ) := mul_le_mul_of_nonneg_left hJbound hK.le
    _ = _ := by rw [Real.sqrt_div hL₀]; dsimp [K, a, d]; ring

/-- The same estimate after an arbitrary independent measurable shift.
The shift law needs no integrability or tail assumption. -/
theorem gaussian_expected_variance_independent_shift_le
    {E : Type*} [MeasurableSpace E] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (ν : Measure E) [IsProbabilityMeasure ν] (R : E → Vector p) (hR : Measurable R) :
    (∫ z : Vector p × E, s.F (z.1 + R z.2) * (1 - s.F (z.1 + R z.2))
      ∂(gaussianLaw A).prod ν) ≤
      Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p / v) := by
  have hW : Measurable (fun z : Vector p × E => z.1 + R z.2) :=
    measurable_fst.add (hR.comp measurable_snd)
  have hi := s.integrable_smallerEnvelope _ hW (μ := (gaussianLaw A).prod ν)
  rw [integral_prod_symm _ hi]
  calc
    _ ≤ ∫ _r : E, Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p / v) ∂ν :=
      integral_mono_ae hi.integral_prod_right (integrable_const _)
        (ae_of_all _ (fun r => s.gaussian_expected_variance_le_of_diagonal hp A hv hdiag (R r)))
    _ = _ := by simp

/-- Uniform covariance range used by the Gaussian half of the interpolation
path. The factor depends only on the fixed lower bound one half. -/
theorem gaussian_expected_variance_le_of_half_diagonal {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 1 / 2 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p) :
    (∫ x : Vector p, s.F (x + r) * (1 - s.F (x + r)) ∂gaussianLaw A) ≤
      Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (2 * dimensionLog p) := by
  have hvpos : 0 < v := by linarith
  have hL : 0 ≤ dimensionLog p := (by norm_num : (0 : ℝ) ≤ 1).trans
    (log_exp_mul_nat_ge_one hp)
  apply (s.gaussian_expected_variance_le_of_diagonal hp A hvpos hdiag r).trans
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _)
    (mul_nonneg (Real.exp_nonneg _) s.bandwidth_pos.le)
  apply (div_le_iff₀ hvpos).mpr
  have hh := mul_le_mul_of_nonneg_left hv hL
  nlinarith

/-- Gaussian short-scale averaging of the summed entrywise third-derivative
majorants. Each entry controls every shift within the bandwidth cube. -/
theorem gaussian_integral_sum_thirdLocalMajorant_le {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p) :
    (∫ x : Vector p, ∑ j, ∑ k, ∑ l, s.thirdLocalMajorant (x + r) j k l ∂gaussianLaw A) ≤
      (13 * (Real.exp 2) ^ 4 * Real.exp (3 / 2 : ℝ)) *
        Real.sqrt (dimensionLog p / v) / s.bandwidth ^ 2 := by
  have hh := s.integral_sum_thirdLocalMajorant_le (fun x : Vector p => x + r)
    (measurable_id.add measurable_const)
    (s.gaussian_expected_variance_le_of_diagonal hp A hv hdiag r)
  convert hh using 1
  field_simp [ne_of_gt s.bandwidth_pos]
  ring

/-- Gaussian short-scale averaging of the summed entrywise fourth-derivative
majorants. This is the short-cap estimate, without a face-density assertion. -/
theorem gaussian_integral_sum_fourthLocalMajorant_le {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p) :
    (∫ x : Vector p, ∑ j, ∑ k, ∑ l, ∑ m,
      s.fourthLocalMajorant (x + r) j k l m ∂gaussianLaw A) ≤
      (75 * (Real.exp 2) ^ 5 * Real.exp (3 / 2 : ℝ)) *
        Real.sqrt (dimensionLog p / v) / s.bandwidth ^ 3 := by
  have hh := s.integral_sum_fourthLocalMajorant_le (fun x : Vector p => x + r)
    (measurable_id.add measurable_const)
    (s.gaussian_expected_variance_le_of_diagonal hp A hv hdiag r)
  convert hh using 1
  field_simp [ne_of_gt s.bandwidth_pos]
  ring

/-- Third-order Gaussian short-cap averaging after an arbitrary independent
shift, with actual product integration over that shift law. -/
theorem gaussian_integral_sum_thirdLocalMajorant_independent_shift_le
    {E : Type*} [MeasurableSpace E] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (ν : Measure E) [IsProbabilityMeasure ν] (R : E → Vector p) (hR : Measurable R) :
    (∫ z : Vector p × E, ∑ j, ∑ k, ∑ l,
      s.thirdLocalMajorant (z.1 + R z.2) j k l ∂(gaussianLaw A).prod ν) ≤
      (13 * (Real.exp 2) ^ 4 * Real.exp (3 / 2 : ℝ)) *
        Real.sqrt (dimensionLog p / v) / s.bandwidth ^ 2 := by
  have hh := s.integral_sum_thirdLocalMajorant_le (fun z : Vector p × E => z.1 + R z.2)
    (measurable_fst.add (hR.comp measurable_snd))
    (s.gaussian_expected_variance_independent_shift_le hp A hv hdiag ν R hR)
  convert hh using 1
  field_simp [ne_of_gt s.bandwidth_pos]
  ring

/-- Fourth-order Gaussian short-cap averaging after an arbitrary independent
shift. The statement does not assume a long-cap concentration oracle. -/
theorem gaussian_integral_sum_fourthLocalMajorant_independent_shift_le
    {E : Type*} [MeasurableSpace E] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (ν : Measure E) [IsProbabilityMeasure ν] (R : E → Vector p) (hR : Measurable R) :
    (∫ z : Vector p × E, ∑ j, ∑ k, ∑ l, ∑ m,
      s.fourthLocalMajorant (z.1 + R z.2) j k l m ∂(gaussianLaw A).prod ν) ≤
      (75 * (Real.exp 2) ^ 5 * Real.exp (3 / 2 : ℝ)) *
        Real.sqrt (dimensionLog p / v) / s.bandwidth ^ 3 := by
  have hh := s.integral_sum_fourthLocalMajorant_le (fun z : Vector p × E => z.1 + R z.2)
    (measurable_fst.add (hR.comp measurable_snd))
    (s.gaussian_expected_variance_independent_shift_le hp A hv hdiag ν R hR)
  convert hh using 1
  field_simp [ne_of_gt s.bandwidth_pos]
  ring

end FaceSmoother

end RectangleCLT
