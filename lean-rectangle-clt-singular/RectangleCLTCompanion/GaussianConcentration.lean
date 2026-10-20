import RectangleCLT.GaussianEnvelope
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Gaussian rectangle shells without a covariance gap

The Gaussian covariance may be singular. A finite-bandwidth calibration,
rather than a limiting argument, converts the proved smaller-envelope bound
into concentration of the actual sharp rectangle boundary layer.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- Differentiating a common translation of all face offsets. -/
theorem hasDerivAt_shiftOffsets_F (x : Vector p) (t : ℝ) :
    HasDerivAt (fun u => (s.shiftOffsets u).F x)
      ((s.shiftOffsets t).F x * (1 - (s.shiftOffsets t).F x) / s.bandwidth) t := by
  have hden : 1 + Real.exp (-t / s.bandwidth) * (s.weights x).T ≠ 0 := by
    have h := ((s.shiftOffsets t).weights x).denominator_pos
    rw [s.shiftOffsets_T] at h
    exact h.ne'
  simp_rw [s.shiftOffsets_F]
  convert (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_const t (1 : ℝ)).add
      ((((hasDerivAt_id t).neg.div_const s.bandwidth).exp).mul_const (s.weights x).T))
    hden using 1
  field_simp
  ring

/-- Common offset translation increases the rational rectangle smoother. -/
theorem shiftOffsets_F_mono (x : Vector p) {a b : ℝ} (hab : a ≤ b) :
    (s.shiftOffsets a).F x ≤ (s.shiftOffsets b).F x := by
  have hT := (s.weights x).T_nonneg
  rw [s.shiftOffsets_F, s.shiftOffsets_F]
  apply one_div_le_one_div_of_le
    (by positivity : 0 < 1 + Real.exp (-b / s.bandwidth) * (s.weights x).T)
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ (s.weights x).T_nonneg
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by linarith) s.bandwidth_pos.le)

private theorem integrable_shiftOffsets_F
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] (r : Vector p) (t : ℝ) :
    Integrable (fun x => (s.shiftOffsets t).F (x + r)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((s.shiftOffsets t).continuous_F.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => (s.shiftOffsets t).norm_F_le_one (x + r))

/-- The derivative of an actual translated-smoother expectation. The
dominating function is the integrable constant `1 / bandwidth`. -/
theorem hasDerivAt_integral_shiftOffsets_F
    (μ : Measure (Vector p)) [IsProbabilityMeasure μ] (r : Vector p) (t : ℝ) :
    HasDerivAt (fun u => ∫ x, (s.shiftOffsets u).F (x + r) ∂μ)
      (∫ x, (s.shiftOffsets t).F (x + r) *
        (1 - (s.shiftOffsets t).F (x + r)) / s.bandwidth ∂μ) t := by
  have hm (u : ℝ) : Measurable (fun x => (s.shiftOffsets u).F (x + r)) :=
    (s.shiftOffsets u).continuous_F.measurable.comp (measurable_id.add measurable_const)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (bound := fun _ => 1 / s.bandwidth) (ε := 1)
    (F := fun u x => (s.shiftOffsets u).F (x + r))
    (F' := fun u x => (s.shiftOffsets u).F (x + r) *
      (1 - (s.shiftOffsets u).F (x + r)) / s.bandwidth)
    (x₀ := t) (by norm_num)
    (Filter.Eventually.of_forall (fun u => (hm u).aestronglyMeasurable))
    (s.integrable_shiftOffsets_F μ r t)
    (((hm t).mul (measurable_const.sub (hm t))).div_const _).aestronglyMeasurable
    (ae_of_all μ (fun x u _ => by
      have hF₀ := (s.shiftOffsets u).F_pos (x + r)
      have hF₁ := (s.shiftOffsets u).F_le_one (x + r)
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (mul_nonneg hF₀.le (by linarith)) s.bandwidth_pos.le)]
      apply div_le_div_of_nonneg_right _ s.bandwidth_pos.le
      nlinarith [sq_nonneg ((s.shiftOffsets u).F (x + r))]))
    (integrable_const _)
    (ae_of_all μ (fun x u _ => s.hasDerivAt_shiftOffsets_F (x + r) u))
  exact h.2

/-- The expected smoother is Lipschitz in the common face threshold, with
no separation or invertibility assumption on the actual Gaussian covariance. -/
theorem gaussian_integral_shiftOffsets_F_sub_le {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ x, (s.shiftOffsets b).F (x + r) ∂gaussianLaw A) -
      (∫ x, (s.shiftOffsets a).F (x + r) ∂gaussianLaw A) ≤
      Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p / v) * (b - a) := by
  let P : ℝ → ℝ := fun u => ∫ x, (s.shiftOffsets u).F (x + r) ∂gaussianLaw A
  let D : ℝ → ℝ := fun u => ∫ x, (s.shiftOffsets u).F (x + r) *
    (1 - (s.shiftOffsets u).F (x + r)) / s.bandwidth ∂gaussianLaw A
  let K := Real.exp (3 / 2 : ℝ) * Real.sqrt (dimensionLog p / v)
  have hd (u : ℝ) : HasDerivAt P (D u) u :=
    s.hasDerivAt_integral_shiftOffsets_F (gaussianLaw A) r u
  have hb (u : ℝ) : D u ≤ K := by
    dsimp [D, K]
    rw [integral_div]
    apply (div_le_iff₀ s.bandwidth_pos).mpr
    convert (s.shiftOffsets u).gaussian_expected_variance_le_of_diagonal hp A hv hdiag r
      using 1
    simp only [shiftOffsets]
    ring
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab
    (fun u _ => (hd u).continuousAt.continuousWithinAt)
    (fun u _ => (hd u).hasDerivWithinAt)
    continuousOn_const.integrableOn_Icc (fun u _ => hb u)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh

private theorem shiftOffsets_F_gap_on_boundary
    (hp : 1 ≤ p) {d : ℝ}
    (hcal : 4 * (p : ℝ) + 1 ≤ d / s.bandwidth)
    (x : Vector p) (hx : x ∈ s.boundaryLayer d) :
    1 / 3 ≤ (s.shiftOffsets (2 * d)).F x - (s.shiftOffsets (-2 * d)).F x := by
  classical
  obtain ⟨hout, hin⟩ := (s.mem_boundaryLayer_iff_score d x).mp hx
  push_neg at hin
  obtain ⟨f, hf, hscore⟩ := hin
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have he : 4 * (p : ℝ) + 2 ≤ Real.exp (d / s.bandwidth) := by
    linarith [Real.add_one_le_exp (d / s.bandwidth)]
  have he₀ := Real.exp_pos (d / s.bandwidth)
  have hup : ((s.shiftOffsets (2 * d)).weights x).T ≤ 1 / 2 := by
    calc
      _ ≤ ∑ _f : Face p, Real.exp (-d / s.bandwidth) := by
        apply Finset.sum_le_sum
        intro g _
        by_cases hg : g ∈ s.faces
        · simp only [weights, shiftOffsets, hg, ↓reduceIte]
          apply Real.exp_le_exp.mpr
          apply div_le_div_of_nonneg_right _ s.bandwidth_pos.le
          have hh := hout g hg
          change normalDot g x - (s.offsets g + 2 * d) ≤ -d
          unfold faceScore at hh
          linarith
        · simp only [weights, shiftOffsets, hg, ↓reduceIte]
          exact (Real.exp_pos _).le
      _ = (2 * (p : ℝ)) / Real.exp (d / s.bandwidth) := by
        rw [show -d / s.bandwidth = -(d / s.bandwidth) by ring, Real.exp_neg]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,
          div_eq_mul_inv]
        ring
      _ ≤ 1 / 2 := by
        apply (div_le_iff₀ he₀).mpr
        linarith
  have hlow : 2 ≤ ((s.shiftOffsets (-2 * d)).weights x).T := by
    calc
      _ ≤ Real.exp (d / s.bandwidth) := by linarith
      _ ≤ ((s.shiftOffsets (-2 * d)).weights x).weight f := by
        simp only [weights, shiftOffsets, hf, ↓reduceIte]
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ s.bandwidth_pos.le
        unfold faceScore at hscore
        change d ≤ normalDot f x - (s.offsets f + -2 * d)
        linarith
      _ ≤ _ := ((s.shiftOffsets (-2 * d)).weights x).weight_le_T f
  have hplus : 2 / 3 ≤ (s.shiftOffsets (2 * d)).F x := by
    change 2 / 3 ≤ 1 / (1 + ((s.shiftOffsets (2 * d)).weights x).T)
    apply (le_div_iff₀ ((s.shiftOffsets (2 * d)).weights x).denominator_pos).mpr
    linarith
  have hminus : (s.shiftOffsets (-2 * d)).F x ≤ 1 / 3 := by
    change 1 / (1 + ((s.shiftOffsets (-2 * d)).weights x).T) ≤ 1 / 3
    apply (div_le_iff₀ ((s.shiftOffsets (-2 * d)).weights x).denominator_pos).mpr
    linarith
  linarith

/-- The actual Gaussian probability of a sharp rectangle shell. Every
coordinate has the same positive variance, but the covariance factor may
have any rank. No pair-gap or local determinant assumption is used. -/
theorem gaussian_boundary_probability_le {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v d : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p) (hd : 0 < d) :
    (gaussianLaw A).real {x | x + r ∈ s.boundaryLayer d} ≤
      12 * Real.exp (3 / 2 : ℝ) * d * Real.sqrt (dimensionLog p / v) := by
  let h := d / (4 * (p : ℝ) + 1)
  have hh : 0 < h := div_pos hd (by positivity)
  let t : FaceSmoother p := {s with bandwidth := h, bandwidth_pos := hh}
  have hcal : 4 * (p : ℝ) + 1 ≤ d / t.bandwidth := by
    change 4 * (p : ℝ) + 1 ≤ d / (d / (4 * (p : ℝ) + 1))
    have hK : 4 * (p : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hd.ne', hK]
  have hboundary : t.boundaryLayer d = s.boundaryLayer d := rfl
  let E : Set (Vector p) := {x | x + r ∈ s.boundaryLayer d}
  have hE : MeasurableSet E :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add measurable_const)
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) (gaussianLaw A) :=
    (integrable_const (1 : ℝ)).indicator hE
  have hdif : Integrable (fun x => 3 *
      ((t.shiftOffsets (2 * d)).F (x + r) - (t.shiftOffsets (-2 * d)).F (x + r)))
      (gaussianLaw A) :=
    ((t.integrable_shiftOffsets_F (gaussianLaw A) r _).sub
      (t.integrable_shiftOffsets_F (gaussianLaw A) r _)).const_mul _
  have hpoint (x : Vector p) : E.indicator (fun _ => (1 : ℝ)) x ≤
      3 * ((t.shiftOffsets (2 * d)).F (x + r) -
        (t.shiftOffsets (-2 * d)).F (x + r)) := by
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      have hb := t.shiftOffsets_F_gap_on_boundary hp hcal (x + r)
        (by simpa only [hboundary] using hx)
      linarith
    · rw [Set.indicator_of_not_mem hx]
      have hm := t.shiftOffsets_F_mono (x + r) (by linarith : -2 * d ≤ 2 * d)
      linarith
  have hb := integral_mono hi hdif hpoint
  rw [integral_indicator_const (1 : ℝ) hE, integral_const_mul,
    integral_sub (t.integrable_shiftOffsets_F (gaussianLaw A) r _)
      (t.integrable_shiftOffsets_F (gaussianLaw A) r _)] at hb
  simp only [smul_eq_mul, mul_one] at hb
  have hlip := t.gaussian_integral_shiftOffsets_F_sub_le hp A hv hdiag r
    (by linarith : -2 * d ≤ 2 * d)
  have hs := hb.trans (mul_le_mul_of_nonneg_left hlip (by norm_num : (0 : ℝ) ≤ 3))
  convert hs using 1
  ring

/-- The same sharp Gaussian shell estimate after an arbitrary independent
measurable shift. Its law needs no moment assumptions. -/
theorem gaussian_boundary_probability_independent_shift_le
    {E : Type*} [MeasurableSpace E] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {v d : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (ν : Measure E) [IsProbabilityMeasure ν]
    (R : E → Vector p) (hR : Measurable R) (hd : 0 < d) :
    ((gaussianLaw A).prod ν).real {z | z.1 + R z.2 ∈ s.boundaryLayer d} ≤
      12 * Real.exp (3 / 2 : ℝ) * d * Real.sqrt (dimensionLog p / v) :=
  s.boundary_probability_independent_shift_le (gaussianLaw A) ν id measurable_id R hR d _
    (fun r => s.gaussian_boundary_probability_le hp A hv hdiag r hd)

end RectangleCLT.FaceSmoother
