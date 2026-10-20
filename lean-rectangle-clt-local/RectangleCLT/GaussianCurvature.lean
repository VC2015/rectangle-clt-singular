import RectangleCLT.GaussianStein
import RectangleCLT.GaussianMaximum
import RectangleCLT.LocalCovariance
import RectangleCLT.SmootherConvolution

/-! Expected curvature at a concrete Gaussian vector, including singular
covariances. All integration-by-parts test functions are supplied by the
actual rectangle potential. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT
namespace FaceWeights

variable {p : ℕ} (w : FaceWeights p)

theorem abs_v_le_one (j : Fin p) : |w.v j| ≤ 1 :=
  (Finset.single_le_sum (fun k _ => abs_nonneg (w.v k))
    (Finset.mem_univ j)).trans w.sum_abs_v_le_one

theorem coordinateMass_le_one (j : Fin p) : w.coordinateMass j ≤ 1 := by
  calc
    _ ≤ ∑ k, w.coordinateMass k := Finset.single_le_sum
      (fun k _ => w.coordinateMass_nonneg k) (Finset.mem_univ j)
    _ = w.theta := w.sum_coordinateMass
    _ ≤ 1 := w.theta_lt_one.le

theorem abs_covarianceEntry_le_two (j k : Fin p) :
    |w.covarianceEntry j k| ≤ 2 := by
  have hdiag : |w.diagonalMass j k| ≤ 1 := by
    unfold diagonalMass
    split_ifs
    · simpa only [abs_of_nonneg (w.coordinateMass_nonneg j)] using w.coordinateMass_le_one j
    · norm_num
  calc
    _ ≤ |w.diagonalMass j k| + |w.v j * w.v k| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add hdiag (by
      rw [abs_mul]
      calc
        _ ≤ 1 * |w.v k| := mul_le_mul_of_nonneg_right (w.abs_v_le_one j) (abs_nonneg _)
        _ ≤ 1 := by simpa only [one_mul] using w.abs_v_le_one k)
    _ = 2 := by norm_num

theorem covarianceEntry_mul_sum (j : Fin p) (y : Vector p) :
    (∑ k, y k * w.covarianceEntry j k) =
      w.coordinateMass j * y j - w.v j * w.directionalMean y := by
  classical
  simp only [covarianceEntry, mul_sub, Finset.sum_sub_distrib]
  have hdiag : (∑ k, y k * w.diagonalMass j k) = w.coordinateMass j * y j := by
    simp [diagonalMass, mul_comm]
  rw [hdiag, w.directionalMean_eq, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => by ring)

end FaceWeights

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem continuous_potentialHessian (j k : Fin p) :
    Continuous (fun x => s.potentialCoordinateHessian x j k) := by
  simp_rw [s.potentialCoordinateHessian_eq]
  exact ((s.continuous_diagonalMass j k).sub
    ((s.continuous_v j).mul (s.continuous_v k))).div_const s.bandwidth

theorem continuous_kappa : Continuous s.kappa := by
  change Continuous (fun x => (1 - s.F x) - ∑ j, (s.weights x).v j ^ 2)
  exact (continuous_const.sub s.continuous_F).sub
    (continuous_finset_sum _ (fun j _ => (s.continuous_v j).pow 2))

theorem abs_potentialHessian_le (x : Vector p) (j k : Fin p) :
    |s.potentialCoordinateHessian x j k| ≤ 2 / s.bandwidth := by
  rw [s.potentialCoordinateHessian_eq, abs_div, abs_of_pos s.bandwidth_pos]
  exact div_le_div_of_nonneg_right ((s.weights x).abs_covarianceEntry_le_two j k)
    s.bandwidth_pos.le

/-- The prescribed Hessian is the actual derivative of the potential gradient
along every line, not merely an algebraic surrogate for that derivative. -/
theorem hasDerivAt_v_line_hessian (x y : Vector p) (j : Fin p) :
    HasDerivAt (fun t : ℝ => s.v (x + t • y) j)
      (∑ k, y k * s.potentialCoordinateHessian x j k) 0 := by
  have hsum : (∑ k, y k * s.potentialCoordinateHessian x j k) =
      ((s.weights x).coordinateMass j * y j -
        (s.weights x).v j * (s.weights x).directionalMean y) / s.bandwidth := by
    simp_rw [s.potentialCoordinateHessian_eq, ← mul_div_assoc]
    rw [← Finset.sum_div, (s.weights x).covarianceEntry_mul_sum]
  rw [hsum]
  simpa only [line, Pi.add_apply, Pi.smul_apply, smul_eq_mul, line_zero] using
    s.hasDerivAt_v_coordinate_line x y j 0

/-- Actual Gaussian integration by parts for a shifted potential gradient.
The identities hold for every matrix factor, including singular factors. -/
theorem gaussian_potential_coordinate_stein (A : Matrix (Fin p) (Fin p) ℝ)
    (r : Vector p) (j : Fin p) :
    (∫ x, x j * s.v (x + r) j ∂gaussianLaw A) =
      ∑ k, (A * A.transpose) j k *
        ∫ x, s.potentialCoordinateHessian (x + r) j k ∂gaussianLaw A := by
  apply gaussianLaw_stein A j
  · intro x a
    convert s.hasDerivAt_v_line_hessian (x + r) (fun k => A k a) j using 1
    funext t
    congr 1
    exact add_right_comm x (t • (fun k => A k a)) r
  · exact ((s.continuous_v j).comp (continuous_id.add continuous_const)).measurable
  · intro k
    exact ((s.continuous_potentialHessian j k).comp
      (continuous_id.add continuous_const)).measurable
  · exact ⟨1, fun x => (s.weights (x + r)).abs_v_le_one j⟩
  · exact ⟨2 / s.bandwidth, fun x k => s.abs_potentialHessian_le (x + r) j k⟩

private theorem integrable_gaussian_potentialHessian (A : Matrix (Fin p) (Fin p) ℝ)
    (r : Vector p) (j k : Fin p) :
    Integrable (fun x => s.potentialCoordinateHessian (x + r) j k) (gaussianLaw A) := by
  apply (integrable_const (2 / s.bandwidth)).mono'
    (((s.continuous_potentialHessian j k).comp
      (continuous_id.add continuous_const)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun x => by
    simpa only [Real.norm_eq_abs] using s.abs_potentialHessian_le (x + r) j k)

private theorem integrable_gaussian_coordinate_v (A : Matrix (Fin p) (Fin p) ℝ)
    (r : Vector p) (j : Fin p) :
    Integrable (fun x => x j * s.v (x + r) j) (gaussianLaw A) := by
  have h := (gaussianLaw_integrable_coordinate A j).bdd_mul
    (((s.continuous_v j).comp
      (continuous_id.add continuous_const)).measurable.aestronglyMeasurable)
    ⟨1, fun x => by
      simpa only [Real.norm_eq_abs] using (s.weights (x + r)).abs_v_le_one j⟩
  simpa only [mul_comm] using h

theorem integrable_gaussian_kappa (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) :
    Integrable (fun x => s.kappa (x + r)) (gaussianLaw A) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((s.continuous_kappa.comp
      (continuous_id.add continuous_const)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun x => by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, kappa,
      abs_of_nonneg (s.weights (x + r)).kappa_nonneg] using
      (s.weights (x + r)).kappa_le_one)

theorem coordinate_dot_v_le_norm (x y : Vector p) :
    (∑ j, x j * s.v y j) ≤ ‖x‖ := by
  calc
    _ ≤ ∑ j, |x j| * |s.v y j| := Finset.sum_le_sum (fun j _ => by
      simpa only [abs_mul] using le_abs_self (x j * s.v y j))
    _ ≤ ∑ j, ‖x‖ * |s.v y j| := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j) (abs_nonneg _))
    _ = ‖x‖ * ∑ j, |s.v y j| := by rw [Finset.mul_sum]
    _ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left (s.weights y).sum_abs_v_le_one (norm_nonneg _)
    _ = ‖x‖ := mul_one _

/-- Gaussian expected curvature controlled by the expected maximum norm.
The only nondegeneracy used is the pairwise correlation gap. -/
theorem gaussian_expected_kappa_le_norm (A : Matrix (Fin p) (Fin p) ℝ)
    (r : Vector p) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∫ x, s.kappa (x + r) ∂gaussianLaw A) ≤
      s.bandwidth / pairGap (A * A.transpose) *
        ∫ x : Vector p, ‖x‖ ∂gaussianLaw A := by
  classical
  let Q := A * A.transpose
  have hH (j k : Fin p) := s.integrable_gaussian_potentialHessian A r j k
  have hcontractint : Integrable
      (fun x => ∑ j, ∑ k, Q j k * s.potentialCoordinateHessian (x + r) j k)
      (gaussianLaw A) := integrable_finset_sum Finset.univ
    (fun j _ => integrable_finset_sum Finset.univ (fun k _ => (hH j k).const_mul (Q j k)))
  have hcontractpoint (x : Vector p) :
      (pairGap Q / s.bandwidth) * s.kappa (x + r) ≤
        ∑ j, ∑ k, Q j k * s.potentialCoordinateHessian (x + r) j k := by
    simp_rw [s.potentialCoordinateHessian_eq, ← mul_div_assoc]
    simp_rw [← Finset.sum_div]
    calc
      _ = (pairGap Q * (s.weights (x + r)).kappa) / s.bandwidth := by
        change (pairGap Q / s.bandwidth) * (s.weights (x + r)).kappa = _
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        ((s.weights (x + r)).covarianceContraction_ge_pairGap Q hdiag) s.bandwidth_pos.le
  have hintegrated :
      (pairGap Q / s.bandwidth) * (∫ x, s.kappa (x + r) ∂gaussianLaw A) ≤
        ∫ x, ∑ j, ∑ k, Q j k * s.potentialCoordinateHessian (x + r) j k
          ∂gaussianLaw A := by
    rw [← integral_const_mul]
    exact integral_mono_ae ((s.integrable_gaussian_kappa A r).const_mul _) hcontractint
      (ae_of_all _ hcontractpoint)
  have hdotint : Integrable (fun x => ∑ j, x j * s.v (x + r) j) (gaussianLaw A) :=
    integrable_finset_sum Finset.univ (fun j _ => s.integrable_gaussian_coordinate_v A r j)
  have hstein :
      (∫ x, ∑ j, ∑ k, Q j k * s.potentialCoordinateHessian (x + r) j k
        ∂gaussianLaw A) = ∫ x, ∑ j, x j * s.v (x + r) j ∂gaussianLaw A := by
    rw [integral_finset_sum Finset.univ
      (fun j _ => integrable_finset_sum Finset.univ (fun k _ => (hH j k).const_mul (Q j k))),
      integral_finset_sum Finset.univ (fun j _ => s.integrable_gaussian_coordinate_v A r j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum Finset.univ (fun k _ => (hH j k).const_mul (Q j k))]
    simp only [integral_const_mul]
    exact (s.gaussian_potential_coordinate_stein A r j).symm
  rw [hstein] at hintegrated
  have hnorm := integral_mono_ae hdotint (gaussianLaw_integrable_norm A)
    (ae_of_all _ (fun x => s.coordinate_dot_v_le_norm x (x + r)))
  have hbound := hintegrated.trans hnorm
  calc
    _ = (s.bandwidth / pairGap Q) *
        ((pairGap Q / s.bandwidth) * ∫ x, s.kappa (x + r) ∂gaussianLaw A) := by
      field_simp [ne_of_gt hc, ne_of_gt s.bandwidth_pos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (div_nonneg s.bandwidth_pos.le hc.le)

/-- The Gaussian endpoint curvature estimate with the explicit constant two,
valid even when the covariance matrix is singular. -/
theorem gaussian_expected_kappa_le (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (r : Vector p) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∫ x, s.kappa (x + r) ∂gaussianLaw A) ≤
      2 * s.bandwidth * Real.sqrt (dimensionLog p) / pairGap (A * A.transpose) := by
  calc
    _ ≤ s.bandwidth / pairGap (A * A.transpose) *
        ∫ x : Vector p, ‖x‖ ∂gaussianLaw A := s.gaussian_expected_kappa_le_norm A r hdiag hc
    _ ≤ s.bandwidth / pairGap (A * A.transpose) *
        (2 * Real.sqrt (dimensionLog p)) :=
      mul_le_mul_of_nonneg_left (gaussianLaw_integral_norm_le hp A hdiag)
        (div_nonneg s.bandwidth_pos.le hc.le)
    _ = _ := by ring

/-- The same estimate for an arbitrary independent shift, represented by its
own probability law. No moment assumption on the shift is needed. -/
theorem gaussian_expected_kappa_independent_shift_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∫ z : Vector p × Vector p, s.kappa (z.1 + z.2) ∂(gaussianLaw A).prod ν) ≤
      2 * s.bandwidth * Real.sqrt (dimensionLog p) / pairGap (A * A.transpose) := by
  have hint : Integrable (fun z : Vector p × Vector p => s.kappa (z.1 + z.2))
      ((gaussianLaw A).prod ν) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((s.continuous_kappa.comp
        (continuous_fst.add continuous_snd)).measurable.aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      simpa only [Function.comp_apply, Real.norm_eq_abs, kappa,
        abs_of_nonneg (s.weights (z.1 + z.2)).kappa_nonneg] using
        (s.weights (z.1 + z.2)).kappa_le_one)
  rw [integral_prod_symm _ hint]
  calc
    _ ≤ ∫ _r : Vector p, 2 * s.bandwidth * Real.sqrt (dimensionLog p) /
        pairGap (A * A.transpose) ∂ν :=
      integral_mono_ae hint.integral_prod_right (integrable_const _)
        (ae_of_all _ (fun r => s.gaussian_expected_kappa_le hp A r hdiag hc))
    _ = _ := by simp

private theorem gaussian_curvature_indicator_measurable : Measurable s.indicator := by
  classical
  have hclosed : IsClosed {x : Vector p | s.Inside x} := by
    have hset : {x : Vector p | s.Inside x} =
        ⋂ f : Face p, ⋂ _hf : f ∈ s.faces, {x | s.faceScore f x ≤ 0} := by
      ext x
      simp only [Set.mem_setOf_eq, Inside, Set.mem_iInter]
    rw [hset]
    exact isClosed_iInter (fun f => isClosed_iInter
      (fun _hf => isClosed_le (s.continuous_faceScore f) continuous_const))
  exact Measurable.ite hclosed.measurableSet measurable_const measurable_const

/-- The actual Gaussian smoothing endpoint error for the closed rectangle,
including missing faces, with explicit constant four. -/
theorem gaussian_smoothing_error_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) :
    (∫ x, |s.F (x + r) - s.indicator (x + r)| ∂gaussianLaw A) ≤
      4 * s.bandwidth * Real.sqrt (dimensionLog p) / pairGap (A * A.transpose) := by
  have hshift : Measurable (fun x : Vector p => x + r) :=
    (continuous_id.add continuous_const).measurable
  have herrmeas : AEStronglyMeasurable
      (fun x => |s.F (x + r) - s.indicator (x + r)|) (gaussianLaw A) :=
    (((s.continuous_F.measurable.comp hshift).sub
      (s.gaussian_curvature_indicator_measurable.comp hshift)).abs).aestronglyMeasurable
  have herrint : Integrable
      (fun x => |s.F (x + r) - s.indicator (x + r)|) (gaussianLaw A) := by
    apply ((s.integrable_gaussian_kappa A r).const_mul 2).mono' herrmeas
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs, abs_abs] using s.endpoint_error (x + r))
  have herr : (∫ x, |s.F (x + r) - s.indicator (x + r)| ∂gaussianLaw A) ≤
      2 * ∫ x, s.kappa (x + r) ∂gaussianLaw A := by
    rw [← integral_const_mul]
    exact integral_mono_ae herrint ((s.integrable_gaussian_kappa A r).const_mul 2)
      (ae_of_all _ (fun x => s.endpoint_error (x + r)))
  calc
    _ ≤ 2 * ∫ x, s.kappa (x + r) ∂gaussianLaw A := herr
    _ ≤ 2 * (2 * s.bandwidth * Real.sqrt (dimensionLog p) /
        pairGap (A * A.transpose)) :=
      mul_le_mul_of_nonneg_left (s.gaussian_expected_kappa_le hp A r hdiag hc) (by norm_num)
    _ = _ := by ring

end FaceSmoother
end RectangleCLT
