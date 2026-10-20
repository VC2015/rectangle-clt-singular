import RectangleCLTCompanion.MatrixReduction
import RectangleCLT.GaussianProjectionMaximum

/-!
# Gaussian weighted means and entropy

The estimates here concern actual integrals. The Cameron--Martin identity
is proved from the explicit product Gaussian density and translation of
Lebesgue measure. No independence of rotated Gaussian coordinates is assumed.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

/-- Weighted Jensen's exponential inequality, using its supporting tangent
line. All integrability requirements are explicit. -/
theorem weighted_exp_mean_le
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (w f : Ω → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : Integrable w ν)
    (hwf : Integrable (fun x => w x * f x) ν)
    (hwe : Integrable (fun x => w x * Real.exp (f x)) ν)
    (hp : 0 < ∫ x, w x ∂ν) :
    (∫ x, w x ∂ν) * Real.exp ((∫ x, w x * f x ∂ν) / (∫ x, w x ∂ν)) ≤
      ∫ x, w x * Real.exp (f x) ∂ν := by
  let m := (∫ x, w x * f x ∂ν) / (∫ x, w x ∂ν)
  have hm : m * (∫ x, w x ∂ν) = ∫ x, w x * f x ∂ν := by
    dsimp [m]
    field_simp
  have hpoint (x : Ω) : Real.exp m *
      ((w x + w x * f x) - m * w x) ≤ w x * Real.exp (f x) := by
    calc
      _ = (w x * Real.exp m) * (1 + (f x - m)) := by ring
      _ ≤ (w x * Real.exp m) * Real.exp (f x - m) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (f x - m)])
          (mul_nonneg (hw0 x) (Real.exp_nonneg _))
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hh := integral_mono (((hw.add hwf).sub (hw.const_mul m)).const_mul (Real.exp m))
    hwe hpoint
  have hsub := integral_sub (hw.add hwf) (hw.const_mul m)
  have hadd := integral_add hw hwf
  simp only [Pi.add_apply, Pi.sub_apply] at hsub hadd
  rw [integral_const_mul] at hh
  simp only [Pi.add_apply, Pi.sub_apply] at hh
  rw [hsub, hadd, integral_const_mul, hm] at hh
  simpa only [add_sub_cancel_right, mul_comm] using hh

/-- Actual Gaussian exponential tilting by a deterministic vector. -/
theorem gaussian_exponential_translation {r : ℕ} (b : Vector r → ℝ) (t : Vector r) :
    (∫ z, b z * Real.exp (faceDot t z) ∂standardGaussian r) =
      Real.exp (vectorNormSq t / 2) * ∫ z, b (z + t) ∂standardGaussian r := by
  rw [standardGaussian_integral_density_mul, standardGaussian_integral_density_mul]
  have hpoint (z : Vector r) :
      standardGaussianDensity r z * (b z * Real.exp (faceDot t z)) =
        Real.exp (vectorNormSq t / 2) *
          (standardGaussianDensity r (z - t) * b z) := by
    have ht := standardGaussianDensity_translate z (-t)
    have hd : faceDot (-t) z = -faceDot t z := by
      simp only [faceDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    have hn : vectorNormSq (-t) = vectorNormSq t := by
      simp only [vectorNormSq, Pi.neg_apply, neg_sq]
    rw [hd, hn] at ht
    have heq : Real.exp (vectorNormSq t / 2) * Real.exp
        (- -faceDot t z - vectorNormSq t / 2) = Real.exp (faceDot t z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [sub_eq_add_neg, ht]
    rw [← heq]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  congr 1
  have htrans := integral_add_right_eq_self (μ := volume)
    (fun z : Vector r => standardGaussianDensity r (z - t) * b z) t
  simpa only [add_sub_cancel_right] using htrans.symm

/-- A reference weight depending only on a face coordinate is invariant
under exponential tilts in orthogonal directions. -/
theorem gaussian_one_face_exponential {r : ℕ}
    (β : ℝ → ℝ) (u t : Vector r) (hortho : faceDot u t = 0) :
    (∫ z, β (faceDot u z) * Real.exp (faceDot t z) ∂standardGaussian r) =
      Real.exp (vectorNormSq t / 2) * ∫ z, β (faceDot u z) ∂standardGaussian r := by
  rw [gaussian_exponential_translation]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    change β (faceDot u (z + t)) = β (faceDot u z)
    have hd : faceDot u (z + t) = faceDot u z + faceDot u t := by
      simp only [faceDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [hd, hortho, add_zero]

theorem gaussian_integrable_weighted_linear {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1) (t : Vector r) :
    Integrable (fun z => w z * faceDot t z) (standardGaussian r) := by
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    (standardGaussian_integrable_weighted_coordinate w hw hb j).const_mul (t j))
  convert hi using 1
  funext z
  simp only [faceDot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gaussian_integrable_weighted_linear_sq {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1) (t : Vector r) :
    Integrable (fun z => w z * (faceDot t z) ^ 2) (standardGaussian r) := by
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      (standardGaussian_integrable_weighted_product w hw hb j k).const_mul (t j * t k)))
  convert hi using 1
  funext z
  simp only [faceDot, pow_two, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_congr rfl fun k _ => by ring

theorem weighted_linear_integral_eq_mean {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1)
    (hp : weightMass (standardGaussian r) w ≠ 0) (t : Vector r) :
    (∫ z, w z * faceDot t z ∂standardGaussian r) =
      weightMass (standardGaussian r) w * faceDot t (weightMean (standardGaussian r) id w) := by
  have hfun : (fun z => w z * faceDot t z) =
      fun z => ∑ j, t j * (z j * w z) := by
    funext z
    simp only [faceDot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfun, integral_finset_sum _ (fun j _ =>
    (standardGaussian_integrable_weighted_coordinate w hw hb j).const_mul (t j))]
  simp only [integral_const_mul, faceDot, weightMean, id_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp

/-- Weighted Cauchy--Schwarz for a scalar coordinate, proved by integrating
the nonnegative centered square. -/
theorem weighted_mean_sq_le_second
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (w f : Ω → ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : Integrable w ν)
    (hwf : Integrable (fun x => w x * f x) ν)
    (hwf2 : Integrable (fun x => w x * (f x) ^ 2) ν)
    (hp : 0 < ∫ x, w x ∂ν) :
    (∫ x, w x ∂ν) * ((∫ x, w x * f x ∂ν) / (∫ x, w x ∂ν)) ^ 2 ≤
      ∫ x, w x * (f x) ^ 2 ∂ν := by
  let m := (∫ x, w x * f x ∂ν) / (∫ x, w x ∂ν)
  have hm : (∫ x, w x * f x ∂ν) = m * (∫ x, w x ∂ν) := by
    dsimp [m]
    field_simp
  have hpoint (x : Ω) : w x * (f x - m) ^ 2 =
      (w x * (f x) ^ 2 - (2 * m) * (w x * f x)) + m ^ 2 * w x := by ring
  have hnon : 0 ≤ ∫ x, w x * (f x - m) ^ 2 ∂ν :=
    integral_nonneg fun x => mul_nonneg (hw0 x) (sq_nonneg _)
  simp_rw [hpoint] at hnon
  have hadd := integral_add (hwf2.sub (hwf.const_mul (2 * m))) (hw.const_mul (m ^ 2))
  have hsub := integral_sub hwf2 (hwf.const_mul (2 * m))
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul, integral_const_mul, hm] at hnon
  change (∫ x, w x ∂ν) * m ^ 2 ≤ _
  nlinarith only [hnon]

def tangentMean {r : ℕ} (u m : Vector r) : Vector r := m - faceDot u m • u

theorem tangentMean_orthogonal {r : ℕ} (u m : Vector r) (hu : vectorNormSq u = 1) :
    faceDot u (tangentMean u m) = 0 := by
  simp only [tangentMean, faceDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib]
  have heq : (∑ j, u j * ((∑ k, u k * m k) * u j)) =
      (∑ k, u k * m k) * vectorNormSq u := by
    simp only [vectorNormSq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [heq, hu]
  ring

theorem tangentMean_dot_mean {r : ℕ} (u m : Vector r) :
    faceDot (tangentMean u m) m = vectorNormSq m - (faceDot u m) ^ 2 := by
  simp only [tangentMean, faceDot, vectorNormSq, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  have hsqsum : (∑ j, ((∑ k, u k * m k) * u j) * m j) =
      (∑ k, u k * m k) ^ 2 := by
    rw [pow_two, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsqsum]
  simp only [pow_two]

theorem tangentMean_normSq {r : ℕ} (u m : Vector r) (hu : vectorNormSq u = 1) :
    vectorNormSq (tangentMean u m) = vectorNormSq m - (faceDot u m) ^ 2 := by
  have heq (a : ℝ) : vectorNormSq (m - a • u) =
      vectorNormSq m - 2 * a * faceDot u m + a ^ 2 * vectorNormSq u := by
    calc
      _ = ∑ j, ((m j) ^ 2 - 2 * a * (u j * m j) + a ^ 2 * (u j) ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := by simp only [vectorNormSq, faceDot, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum]
  rw [tangentMean, heq, hu]
  ring

/-- The paper's Gaussian mean/entropy estimate for an actual bounded
weight dominated by a function of one unit face coordinate. -/
theorem gaussian_mean_relative_to_one_face {r : ℕ}
    (u : Vector r) (hu : vectorNormSq u = 1)
    (β : ℝ → ℝ) (hβ : Measurable β) (hβb : ∀ a, 0 ≤ β a ∧ β a ≤ 1)
    (w : Vector r → ℝ) (hw : Measurable w)
    (hwb : ∀ z, 0 ≤ w z ∧ w z ≤ β (faceDot u z))
    (hp : 0 < weightMass (standardGaussian r) w) :
    weightMass (standardGaussian r) w * vectorNormSq (weightMean (standardGaussian r) id w) ≤
      (∫ z, w z * (faceDot u z) ^ 2 ∂standardGaussian r) +
        2 * weightMass (standardGaussian r) w *
          Real.log ((∫ z, β (faceDot u z) ∂standardGaussian r) /
            weightMass (standardGaussian r) w) := by
  let μ := weightMean (standardGaussian r) id w
  let t := tangentMean u μ
  let p := weightMass (standardGaussian r) w
  let b : Vector r → ℝ := fun z => β (faceDot u z)
  let pb := ∫ z, b z ∂standardGaussian r
  have hw0 : ∀ z, 0 ≤ w z := fun z => (hwb z).1
  have hbound : ∀ z, |w z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (hw0 z)]
    exact (hwb z).2.trans (hβb _).2
  have hb : Measurable b := hβ.comp (Finset.measurable_sum _
    (fun j _ => measurable_const.mul (measurable_pi_apply j)))
  have hbb : ∀ z, |b z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (hβb _).1]
    exact (hβb _).2
  have hwi := standardGaussian_integrable_bounded_weight w hw hbound
  have hbi := standardGaussian_integrable_bounded_weight b hb hbb
  have hppb : p ≤ pb := integral_mono hwi hbi fun z => (hwb z).2
  have hpb : 0 < pb := hp.trans_le hppb
  have hexp : Integrable (fun z => Real.exp (faceDot t z)) (standardGaussian r) := by
    simpa only [one_mul, faceDot] using integrable_exp_linearProjection t 1
  have hwexp := hexp.bdd_mul hw.aestronglyMeasurable ⟨1, fun z => by
    simpa only [Real.norm_eq_abs] using hbound z⟩
  have hbexp := hexp.bdd_mul hb.aestronglyMeasurable ⟨1, fun z => by
    simpa only [Real.norm_eq_abs] using hbb z⟩
  have hJ := weighted_exp_mean_le (standardGaussian r) w (faceDot t) hw0 hwi
    (gaussian_integrable_weighted_linear w hw hbound t) hwexp hp
  rw [weighted_linear_integral_eq_mean w hw hbound hp.ne'] at hJ
  change p * Real.exp ((p * faceDot t μ) / p) ≤ _ at hJ
  rw [mul_div_cancel_left₀ _ hp.ne'] at hJ
  have horth : faceDot u t = 0 := tangentMean_orthogonal u μ hu
  have hnormal : faceDot t μ = vectorNormSq t := by
    rw [tangentMean_dot_mean u μ, tangentMean_normSq u μ hu]
  have hI : p * Real.exp (vectorNormSq t) ≤ pb * Real.exp (vectorNormSq t / 2) := by
    calc
      _ = p * Real.exp (faceDot t μ) := by rw [hnormal]
      _ ≤ ∫ z, w z * Real.exp (faceDot t z) ∂standardGaussian r := hJ
      _ ≤ ∫ z, b z * Real.exp (faceDot t z) ∂standardGaussian r :=
        integral_mono hwexp hbexp fun z =>
          mul_le_mul_of_nonneg_right (hwb z).2 (Real.exp_nonneg _)
      _ = _ := by rw [gaussian_one_face_exponential β u t horth]; ring
  have hexpHalf : Real.exp (vectorNormSq t / 2) ≤ pb / p := by
    apply (le_div_iff₀ hp).mpr
    apply (mul_le_mul_right (Real.exp_pos (vectorNormSq t / 2))).mp
    have heq : Real.exp (vectorNormSq t) =
        Real.exp (vectorNormSq t / 2) * Real.exp (vectorNormSq t / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hI
    convert hI using 1
    ring
  have hlog : vectorNormSq t ≤ 2 * Real.log (pb / p) := by
    have hh := (Real.le_log_iff_exp_le (div_pos hpb hp)).mpr hexpHalf
    linarith
  have hsecond := weighted_mean_sq_le_second (standardGaussian r) w (faceDot u)
    hw0 hwi (gaussian_integrable_weighted_linear w hw hbound u)
    (gaussian_integrable_weighted_linear_sq w hw hbound u) hp
  rw [weighted_linear_integral_eq_mean w hw hbound hp.ne'] at hsecond
  change p * ((p * faceDot u μ) / p) ^ 2 ≤ _ at hsecond
  rw [mul_div_cancel_left₀ _ hp.ne'] at hsecond
  have hscale := mul_le_mul_of_nonneg_left hlog hp.le
  change p * vectorNormSq t ≤ p * (2 * Real.log (pb / p)) at hscale
  change p * vectorNormSq μ ≤ (∫ z, w z * (faceDot u z) ^ 2 ∂standardGaussian r) +
    2 * p * Real.log (pb / p)
  change p * (faceDot u μ) ^ 2 ≤ _ at hsecond
  calc
    _ = p * (faceDot u μ) ^ 2 + p * vectorNormSq t := by
      dsimp only [t]
      rw [tangentMean_normSq u μ hu]
      ring
    _ ≤ (∫ z, w z * (faceDot u z) ^ 2 ∂standardGaussian r) +
        p * (2 * Real.log (pb / p)) := add_le_add hsecond hscale
    _ = _ := by ring

end

end RectangleCLT.Companion
