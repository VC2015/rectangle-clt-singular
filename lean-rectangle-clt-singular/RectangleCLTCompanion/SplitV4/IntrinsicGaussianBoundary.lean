import RectangleCLTCompanion.GaussianEntropy
import RectangleCLT.GaussianStein
import RectangleCLT.GaussianTriple
import RectangleCLTCompanion.SplitV4.GaussianMaximumLimits

/-! Actual smooth-maximum geometry and Gaussian integration by parts for the
intrinsic Gaussian boundary estimate. The rows are allowed to repeat and their
Gram matrix may be singular. The unit-row condition is the Euclidean sum of
squares; it is not the ambient supremum norm on `Vector`.
-/

open MeasureTheory
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {m r : ℕ} [NeZero m]

def gaussianFacePartition (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) : ℝ :=
  ∑ α, Real.exp (β * (faceDot (w α) x - a α))

def gaussianFaceWeight (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) (α : Fin m) : ℝ :=
  Real.exp (β * (faceDot (w α) x - a α)) / gaussianFacePartition w a β x

def smoothGaussianFaceMaximum (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) : ℝ :=
  Real.log (gaussianFacePartition w a β x) / β

def smoothGaussianFaceGradient (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) : Vector r :=
  fun j => ∑ α, gaussianFaceWeight w a β x α * w α j

def smoothGaussianFaceHessian (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) (j k : Fin r) : ℝ :=
  β * ((∑ α, gaussianFaceWeight w a β x α * w α j * w α k) -
    smoothGaussianFaceGradient w a β x j * smoothGaussianFaceGradient w a β x k)

theorem gaussianFacePartition_pos (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) : 0 < gaussianFacePartition w a β x := by
  exact Finset.sum_pos (fun α _ => Real.exp_pos _) Finset.univ_nonempty

theorem gaussianFaceWeight_nonneg (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) (α : Fin m) : 0 ≤ gaussianFaceWeight w a β x α :=
  div_nonneg (Real.exp_nonneg _) (gaussianFacePartition_pos w a β x).le

theorem gaussianFaceWeight_sum (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) : ∑ α, gaussianFaceWeight w a β x α = 1 := by
  simp only [gaussianFaceWeight, ← Finset.sum_div]
  exact div_self (gaussianFacePartition_pos w a β x).ne'

theorem continuous_gaussianFacePartition (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) : Continuous (gaussianFacePartition w a β) := by
  unfold gaussianFacePartition faceDot
  fun_prop

theorem continuous_gaussianFaceWeight (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (α : Fin m) : Continuous (fun x => gaussianFaceWeight w a β x α) := by
  apply Continuous.div _ (continuous_gaussianFacePartition w a β)
    (fun x => (gaussianFacePartition_pos w a β x).ne')
  unfold faceDot
  fun_prop

theorem continuous_smoothGaussianFaceMaximum (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) : Continuous (smoothGaussianFaceMaximum w a β) := by
  exact ((continuous_gaussianFacePartition w a β).log
    (fun x => (gaussianFacePartition_pos w a β x).ne')).div_const β

theorem continuous_smoothGaussianFaceGradient (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (j : Fin r) : Continuous (fun x => smoothGaussianFaceGradient w a β x j) := by
  exact continuous_finset_sum _ (fun α _ =>
    (continuous_gaussianFaceWeight w a β α).mul continuous_const)

theorem continuous_smoothGaussianFaceHessian (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (j k : Fin r) : Continuous (fun x => smoothGaussianFaceHessian w a β x j k) := by
  exact continuous_const.mul ((continuous_finset_sum _ (fun α _ =>
    ((continuous_gaussianFaceWeight w a β α).mul continuous_const).mul continuous_const)).sub
      ((continuous_smoothGaussianFaceGradient w a β j).mul
        (continuous_smoothGaussianFaceGradient w a β k)))

theorem gaussianFacePartition_hasDerivAt (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) (j : Fin r) :
    HasDerivAt (fun t => gaussianFacePartition w a β (Function.update x j t))
      (β * gaussianFacePartition w a β x * smoothGaussianFaceGradient w a β x j) (x j) := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun α _ =>
    (((hasDerivAt_faceDot_update (w α) x j).sub_const (a α)).const_mul β).exp)
  convert hd using 1
  simp only [Function.update_eq_self, smoothGaussianFaceGradient, gaussianFaceWeight,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  field_simp [(gaussianFacePartition_pos w a β x).ne']
  <;> ring

theorem smoothGaussianFaceMaximum_hasDerivAt (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (hβ : β ≠ 0) (x : Vector r) (j : Fin r) :
    HasDerivAt (fun t => smoothGaussianFaceMaximum w a β (Function.update x j t))
      (smoothGaussianFaceGradient w a β x j) (x j) := by
  have hd := ((gaussianFacePartition_hasDerivAt w a β x j).log
    (gaussianFacePartition_pos w a β (Function.update x j (x j))).ne').div_const β
  convert hd using 1
  simp only [Function.update_eq_self]
  field_simp [(gaussianFacePartition_pos w a β x).ne', hβ]
  <;> ring

theorem gaussianFaceWeight_hasDerivAt (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) (α : Fin m) (j : Fin r) :
    HasDerivAt (fun t => gaussianFaceWeight w a β (Function.update x j t) α)
      (β * gaussianFaceWeight w a β x α *
        (w α j - smoothGaussianFaceGradient w a β x j)) (x j) := by
  have hd := ((((hasDerivAt_faceDot_update (w α) x j).sub_const (a α)).const_mul β).exp).div
    (gaussianFacePartition_hasDerivAt w a β x j)
      (gaussianFacePartition_pos w a β (Function.update x j (x j))).ne'
  convert hd using 1
  simp only [Function.update_eq_self, gaussianFaceWeight]
  field_simp [(gaussianFacePartition_pos w a β x).ne']
  <;> ring

theorem smoothGaussianFaceGradient_hasDerivAt (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) (j k : Fin r) :
    HasDerivAt (fun t => smoothGaussianFaceGradient w a β (Function.update x k t) j)
      (smoothGaussianFaceHessian w a β x j k) (x k) := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun α _ =>
    (gaussianFaceWeight_hasDerivAt w a β x α k).mul_const (w α j))
  convert hd using 1
  have he : (∑ α, β * gaussianFaceWeight w a β x α *
      (w α k - smoothGaussianFaceGradient w a β x k) * w α j) =
      β * (∑ α, gaussianFaceWeight w a β x α * w α j * w α k) -
        (β * smoothGaussianFaceGradient w a β x k) *
          (∑ α, gaussianFaceWeight w a β x α * w α j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  rw [he]
  change β * (_ - smoothGaussianFaceGradient w a β x j *
    smoothGaussianFaceGradient w a β x k) = _
  change _ = β * _ - (β * smoothGaussianFaceGradient w a β x k) *
    smoothGaussianFaceGradient w a β x j
  ring

/-- Weighted coordinate variance, proved by expanding the centered square. -/
theorem simplex_weighted_variance (p z : Fin m → ℝ) (hp : ∑ α, p α = 1) :
    (∑ α, p α * (z α - ∑ γ, p γ * z γ) ^ 2) =
      (∑ α, p α * z α ^ 2) - (∑ α, p α * z α) ^ 2 := by
  let M := ∑ γ, p γ * z γ
  have hx : (∑ α, p α * (z α - M) ^ 2) =
      (∑ α, p α * z α ^ 2) - (2 * M) * (∑ α, p α * z α) +
        M ^ 2 * (∑ α, p α) := by
    calc
      _ = ∑ α, ((p α * z α ^ 2 - (2 * M) * (p α * z α)) + M ^ 2 * p α) :=
        Finset.sum_congr rfl (fun α _ => by ring)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hx, hp]
  dsimp only [M]
  ring

theorem smoothGaussianFaceGradient_normSq_le_one
    (w : Fin m → Vector r) (a : Fin m → ℝ) (β : ℝ) (x : Vector r)
    (hw : ∀ α, vectorNormSq (w α) = 1) :
    vectorNormSq (smoothGaussianFaceGradient w a β x) ≤ 1 := by
  have hc (j : Fin r) := simplex_weighted_variance
    (gaussianFaceWeight w a β x) (fun α => w α j) (gaussianFaceWeight_sum w a β x)
  have hn (j : Fin r) :
      (smoothGaussianFaceGradient w a β x j) ^ 2 ≤
        ∑ α, gaussianFaceWeight w a β x α * (w α j) ^ 2 := by
    have hh : 0 ≤ ∑ α, gaussianFaceWeight w a β x α *
        (w α j - ∑ γ, gaussianFaceWeight w a β x γ * w γ j) ^ 2 :=
      Finset.sum_nonneg (fun α (_ : α ∈ Finset.univ) =>
        mul_nonneg (gaussianFaceWeight_nonneg w a β x α) (sq_nonneg _))
    rw [hc j] at hh
    exact sub_nonneg.mp hh
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hn j)
  have he : (∑ j, ∑ α, gaussianFaceWeight w a β x α * (w α j) ^ 2) = 1 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    change (∑ α, gaussianFaceWeight w a β x α * vectorNormSq (w α)) = 1
    simp_rw [hw, mul_one]
    exact gaussianFaceWeight_sum w a β x
  rwa [he] at hh

theorem smoothGaussianFaceHessian_trace
    (w : Fin m → Vector r) (a : Fin m → ℝ) (β : ℝ) (x : Vector r)
    (hw : ∀ α, vectorNormSq (w α) = 1) :
    (∑ j, smoothGaussianFaceHessian w a β x j j) =
      β * (1 - vectorNormSq (smoothGaussianFaceGradient w a β x)) := by
  have he : (∑ j, ∑ α, gaussianFaceWeight w a β x α * (w α j) ^ 2) = 1 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    change (∑ α, gaussianFaceWeight w a β x α * vectorNormSq (w α)) = 1
    simp_rw [hw, mul_one]
    exact gaussianFaceWeight_sum w a β x
  simp only [smoothGaussianFaceHessian, ← mul_assoc, ← pow_two,
    ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hp (α : Fin m) (j : Fin r) : gaussianFaceWeight w a β x α * w α j * w α j =
      gaussianFaceWeight w a β x α * (w α j) ^ 2 := by ring
  simp_rw [hp]
  rw [he]
  rfl

theorem smoothGaussianFaceHessian_trace_nonneg
    (w : Fin m → Vector r) (a : Fin m → ℝ) (β : ℝ) (hβ : 0 ≤ β) (x : Vector r)
    (hw : ∀ α, vectorNormSq (w α) = 1) :
    0 ≤ ∑ j, smoothGaussianFaceHessian w a β x j j := by
  rw [smoothGaussianFaceHessian_trace w a β x hw]
  exact mul_nonneg hβ (sub_nonneg.mpr (smoothGaussianFaceGradient_normSq_le_one w a β x hw))

theorem coordinate_sq_le_vectorNormSq (z : Vector r) (j : Fin r) :
    (z j) ^ 2 ≤ vectorNormSq z :=
  Finset.single_le_sum (fun k _ => sq_nonneg (z k)) (Finset.mem_univ j)

theorem unit_face_coordinate_abs_le_one (w : Vector r)
    (hw : vectorNormSq w = 1) (j : Fin r) : |w j| ≤ 1 := by
  apply (sq_le_one_iff_abs_le_one _).mp
  exact (coordinate_sq_le_vectorNormSq w j).trans_eq hw

theorem smoothGaussianFaceGradient_coordinate_abs_le_one
    (w : Fin m → Vector r) (a : Fin m → ℝ) (β : ℝ) (x : Vector r)
    (hw : ∀ α, vectorNormSq (w α) = 1) (j : Fin r) :
    |smoothGaussianFaceGradient w a β x j| ≤ 1 := by
  apply (sq_le_one_iff_abs_le_one _).mp
  exact (coordinate_sq_le_vectorNormSq _ j).trans
    (smoothGaussianFaceGradient_normSq_le_one w a β x hw)

theorem smoothGaussianFaceHessian_coordinate_abs_le
    (w : Fin m → Vector r) (a : Fin m → ℝ) (β : ℝ) (x : Vector r)
    (hw : ∀ α, vectorNormSq (w α) = 1) (j k : Fin r) :
    |smoothGaussianFaceHessian w a β x j k| ≤ 2 * |β| := by
  have hf : |∑ α, gaussianFaceWeight w a β x α * w α j * w α k| ≤ 1 := by
    calc
      _ ≤ ∑ α, |gaussianFaceWeight w a β x α * w α j * w α k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ α, gaussianFaceWeight w a β x α := by
        apply Finset.sum_le_sum
        intro α _
        rw [abs_mul, abs_mul, abs_of_nonneg (gaussianFaceWeight_nonneg w a β x α)]
        calc
          _ ≤ gaussianFaceWeight w a β x α * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left
              (unit_face_coordinate_abs_le_one (w α) (hw α) j)
              (gaussianFaceWeight_nonneg w a β x α))
              (unit_face_coordinate_abs_le_one (w α) (hw α) k)
              (abs_nonneg _) (by simpa only [mul_one] using gaussianFaceWeight_nonneg w a β x α)
          _ = _ := by ring
      _ = 1 := gaussianFaceWeight_sum w a β x
  have hg : |smoothGaussianFaceGradient w a β x j *
      smoothGaussianFaceGradient w a β x k| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul
      (smoothGaussianFaceGradient_coordinate_abs_le_one w a β x hw j)
      (smoothGaussianFaceGradient_coordinate_abs_le_one w a β x hw k)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  rw [smoothGaussianFaceHessian, abs_mul]
  have hs := (abs_sub _ _).trans (add_le_add hf hg)
  nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg β)]

/-- The positive part of the largest unshifted Gaussian face projection.
No opposite-pair assumption is built into this definition. -/
def positiveGaussianFaceMaximum (w : Fin m → Vector r) (x : Vector r) : ℝ :=
  max 0 ((Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty
    (fun α => faceDot (w α) x))

theorem positiveGaussianFaceMaximum_nonneg (w : Fin m → Vector r) (x : Vector r) :
    0 ≤ positiveGaussianFaceMaximum w x := le_max_left _ _

theorem faceDot_le_positiveGaussianFaceMaximum (w : Fin m → Vector r)
    (x : Vector r) (α : Fin m) :
    faceDot (w α) x ≤ positiveGaussianFaceMaximum w x :=
  (Finset.le_sup' (fun α => faceDot (w α) x) (Finset.mem_univ α)).trans (le_max_right _ _)

theorem continuous_positiveGaussianFaceMaximum (w : Fin m → Vector r) :
    Continuous (positiveGaussianFaceMaximum w) := by
  apply continuous_const.max
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro α _
  unfold faceDot
  fun_prop

theorem positiveGaussianFaceMaximum_le_sum_abs (w : Fin m → Vector r) (x : Vector r) :
    positiveGaussianFaceMaximum w x ≤ ∑ α, |faceDot (w α) x| := by
  apply max_le (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  apply Finset.sup'_le
  intro α _
  exact (le_abs_self _).trans
    (Finset.single_le_sum (fun γ _ => abs_nonneg (faceDot (w γ) x)) (Finset.mem_univ α))

theorem integrable_positiveGaussianFaceMaximum (w : Fin m → Vector r) :
    Integrable (positiveGaussianFaceMaximum w) (standardGaussian r) := by
  apply (integrable_finset_sum Finset.univ (fun α _ =>
    (standardGaussian_integrable_faceDot (w α)).abs)).mono'
      (continuous_positiveGaussianFaceMaximum w).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveGaussianFaceMaximum_nonneg w x)]
    exact positiveGaussianFaceMaximum_le_sum_abs w x)

theorem smoothGaussianFaceGradient_dot (w : Fin m → Vector r)
    (a : Fin m → ℝ) (β : ℝ) (x : Vector r) :
    faceDot (smoothGaussianFaceGradient w a β x) x =
      ∑ α, gaussianFaceWeight w a β x α * faceDot (w α) x := by
  simp only [faceDot, smoothGaussianFaceGradient, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem smoothGaussianFaceGradient_dot_le_positiveMaximum
    (w : Fin m → Vector r) (a : Fin m → ℝ) (β : ℝ) (x : Vector r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    t * faceDot (smoothGaussianFaceGradient w a β x) x ≤ positiveGaussianFaceMaximum w x := by
  have hh : faceDot (smoothGaussianFaceGradient w a β x) x ≤
      positiveGaussianFaceMaximum w x := by
    rw [smoothGaussianFaceGradient_dot]
    calc
      _ ≤ ∑ α, gaussianFaceWeight w a β x α * positiveGaussianFaceMaximum w x :=
        Finset.sum_le_sum (fun α _ => mul_le_mul_of_nonneg_left
          (faceDot_le_positiveGaussianFaceMaximum w x α)
          (gaussianFaceWeight_nonneg w a β x α))
      _ = _ := by rw [← Finset.sum_mul, gaussianFaceWeight_sum, one_mul]
  exact (mul_le_mul_of_nonneg_left hh ht.1).trans
    ((mul_le_mul_of_nonneg_right ht.2 (positiveGaussianFaceMaximum_nonneg w x)).trans_eq
      (one_mul _))

private theorem gaussian_integrable_of_continuous_bounded (f : Vector r → ℝ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) :
    Integrable f (standardGaussian r) :=
  (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hC)

/-- The actual coordinatewise Gaussian integration by parts for the smooth
maximum. All the derivative and integrability obligations are discharged by
the finite softmax formulas and the bounded `C¹` test. -/
theorem smoothGaussianFaceMaximum_stein
    (w : Fin m → Vector r) (a : Fin m → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hw : ∀ α, vectorNormSq (w α) = 1)
    (ψ dψ : ℝ → ℝ) (hψ : ∀ t, HasDerivAt ψ (dψ t) t)
    (hdψ : Continuous dψ) (hψb : ∀ t, 0 ≤ ψ t ∧ ψ t ≤ 1)
    (D : ℝ) (hdψb : ∀ t, |dψ t| ≤ D) :
    (∫ x, dψ (smoothGaussianFaceMaximum w a β x) *
        vectorNormSq (smoothGaussianFaceGradient w a β x) +
      ψ (smoothGaussianFaceMaximum w a β x) *
        (∑ j, smoothGaussianFaceHessian w a β x j j) ∂standardGaussian r) =
    ∫ x, ψ (smoothGaussianFaceMaximum w a β x) *
      faceDot (smoothGaussianFaceGradient w a β x) x ∂standardGaussian r := by
  let F := smoothGaussianFaceMaximum w a β
  let g := smoothGaussianFaceGradient w a β
  let H := smoothGaussianFaceHessian w a β
  have hFc : Continuous F := continuous_smoothGaussianFaceMaximum w a β
  have hgc (j : Fin r) : Continuous (fun x => g x j) :=
    continuous_smoothGaussianFaceGradient w a β j
  have hHc (j : Fin r) : Continuous (fun x => H x j j) :=
    continuous_smoothGaussianFaceHessian w a β j j
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr (fun t => (hψ t).continuousAt)
  have hψabs (t : ℝ) : |ψ t| ≤ 1 :=
    (abs_of_nonneg (hψb t).1).trans_le (hψb t).2
  have hgabs (x : Vector r) (j : Fin r) : |g x j| ≤ 1 :=
    smoothGaussianFaceGradient_coordinate_abs_le_one w a β x hw j
  have hgb (j : Fin r) (x : Vector r) : |ψ (F x) * g x j| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hψabs (F x)) (hgabs x j)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hDb (j : Fin r) (x : Vector r) :
      |dψ (F x) * (g x j) ^ 2 + ψ (F x) * H x j j| ≤ D + 2 * |β| := by
    have hg2 : |(g x j) ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (hgabs x j)
    have hD0 : 0 ≤ D := (abs_nonneg (dψ 0)).trans (hdψb 0)
    calc
      _ ≤ |dψ (F x) * (g x j) ^ 2| + |ψ (F x) * H x j j| := abs_add _ _
      _ ≤ D * 1 + 1 * (2 * |β|) := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_mul (hdψb (F x)) hg2 (abs_nonneg _) hD0)
          (mul_le_mul (hψabs (F x))
            (smoothGaussianFaceHessian_coordinate_abs_le w a β x hw j j)
            (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      _ = _ := by ring
  have hDc (j : Fin r) : Continuous
      (fun x => dψ (F x) * (g x j) ^ 2 + ψ (F x) * H x j j) :=
    ((hdψ.comp hFc).mul ((hgc j).pow 2)).add ((hψc.comp hFc).mul (hHc j))
  have hdi (j : Fin r) : Integrable
      (fun x => dψ (F x) * (g x j) ^ 2 + ψ (F x) * H x j j) (standardGaussian r) :=
    gaussian_integrable_of_continuous_bounded _ (hDc j) _ (hDb j)
  have hxgi (j : Fin r) : Integrable (fun x => x j * (ψ (F x) * g x j))
      (standardGaussian r) := by
    simpa only [mul_comm] using (standardGaussian_integrable_coordinate r j).bdd_mul
      (((hψc.comp hFc).mul (hgc j)).aestronglyMeasurable)
      ⟨1, fun x => by simpa only [Real.norm_eq_abs] using hgb j x⟩
  have hstein (j : Fin r) :
      (∫ x, x j * (ψ (F x) * g x j) ∂standardGaussian r) =
      ∫ x, dψ (F x) * (g x j) ^ 2 + ψ (F x) * H x j j ∂standardGaussian r := by
    apply standardGaussian_coordinate_stein j _
      ((hψc.comp hFc).mul (hgc j)).measurable (hDc j).measurable
      ⟨1, hgb j⟩ ⟨D + 2 * |β|, hDb j⟩
    intro x
    have hp := (hψ (smoothGaussianFaceMaximum w a β (Function.update x j (x j)))).comp (x j)
      (smoothGaussianFaceMaximum_hasDerivAt w a β hβ x j)
    have hd := hp.mul (smoothGaussianFaceGradient_hasDerivAt w a β x j j)
    convert hd using 1 <;> dsimp only [F, g, H, Function.comp_apply] <;>
      simp only [Function.update_eq_self] <;> ring
  calc
    _ = ∫ x, ∑ j, (dψ (F x) * (g x j) ^ 2 + ψ (F x) * H x j j)
        ∂standardGaussian r := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        simp only [vectorNormSq, Finset.mul_sum, Finset.sum_add_distrib, F, g, H])
    _ = ∑ j, ∫ x, dψ (F x) * (g x j) ^ 2 + ψ (F x) * H x j j
        ∂standardGaussian r := integral_finset_sum _ (fun j _ => hdi j)
    _ = ∑ j, ∫ x, x j * (ψ (F x) * g x j) ∂standardGaussian r :=
      Finset.sum_congr rfl (fun j _ => (hstein j).symm)
    _ = ∫ x, ∑ j, x j * (ψ (F x) * g x j) ∂standardGaussian r :=
      (integral_finset_sum _ (fun j _ => hxgi j)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        simp only [faceDot, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring))

/-- The exact intrinsic smooth-test inequality. Its right hand side retains
the actual positive expected maximum, with coefficient one. -/
theorem smoothGaussianFaceMaximum_test_bound
    (w : Fin m → Vector r) (a : Fin m → ℝ) (β : ℝ) (hβ : 0 < β)
    (hw : ∀ α, vectorNormSq (w α) = 1)
    (ψ dψ : ℝ → ℝ) (hψ : ∀ t, HasDerivAt ψ (dψ t) t)
    (hdψ : Continuous dψ) (hψb : ∀ t, 0 ≤ ψ t ∧ ψ t ≤ 1)
    (D : ℝ) (hdψb : ∀ t, |dψ t| ≤ D) :
    (∫ x, dψ (smoothGaussianFaceMaximum w a β x) *
      vectorNormSq (smoothGaussianFaceGradient w a β x) ∂standardGaussian r) ≤
      ∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r := by
  let F := smoothGaussianFaceMaximum w a β
  let g := smoothGaussianFaceGradient w a β
  have hψc : Continuous ψ := continuous_iff_continuousAt.mpr (fun t => (hψ t).continuousAt)
  have hleftc : Continuous (fun x => dψ (F x) * vectorNormSq (g x)) := by
    apply (hdψ.comp (continuous_smoothGaussianFaceMaximum w a β)).mul
    apply continuous_finset_sum
    intro j _
    exact (continuous_smoothGaussianFaceGradient w a β j).pow 2
  have hleftb (x : Vector r) : |dψ (F x) * vectorNormSq (g x)| ≤ D := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ vectorNormSq (g x) from
      Finset.sum_nonneg (fun j _ => sq_nonneg _))]
    have hD0 : 0 ≤ D := (abs_nonneg (dψ 0)).trans (hdψb 0)
    exact (mul_le_mul (hdψb (F x))
      (smoothGaussianFaceGradient_normSq_le_one w a β x hw)
      (Finset.sum_nonneg (fun j _ => sq_nonneg _)) hD0).trans_eq (mul_one D)
  have hlefti := gaussian_integrable_of_continuous_bounded _ hleftc D hleftb
  have hcorr (x : Vector r) : 0 ≤ ψ (F x) *
      (∑ j, smoothGaussianFaceHessian w a β x j j) :=
    mul_nonneg (hψb (F x)).1 (smoothGaussianFaceHessian_trace_nonneg w a β hβ.le x hw)
  have hcorrc : Continuous (fun x => ψ (F x) *
      (∑ j, smoothGaussianFaceHessian w a β x j j)) :=
    (hψc.comp (continuous_smoothGaussianFaceMaximum w a β)).mul
      (continuous_finset_sum _ (fun j _ => continuous_smoothGaussianFaceHessian w a β j j))
  have hcorrb (x : Vector r) : |ψ (F x) *
      (∑ j, smoothGaussianFaceHessian w a β x j j)| ≤ (r : ℝ) * (2 * |β|) := by
    rw [abs_mul]
    calc
      _ ≤ 1 * (∑ j, |smoothGaussianFaceHessian w a β x j j|) :=
        mul_le_mul ((abs_of_nonneg (hψb (F x)).1).trans_le (hψb (F x)).2)
          (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _) (by norm_num)
      _ ≤ _ := by
        simp only [one_mul]
        simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
          smoothGaussianFaceHessian_coordinate_abs_le w a β x hw j j)
  have hcorri := gaussian_integrable_of_continuous_bounded _ hcorrc _ hcorrb
  have hrighi : Integrable (fun x => ψ (F x) * faceDot (g x) x) (standardGaussian r) := by
    have hi := integrable_finset_sum Finset.univ (fun j _ =>
      (standardGaussian_integrable_coordinate r j).bdd_mul
        (((hψc.comp (continuous_smoothGaussianFaceMaximum w a β)).mul
          (continuous_smoothGaussianFaceGradient w a β j)).aestronglyMeasurable)
        ⟨1, fun x => by
          rw [Real.norm_eq_abs, abs_mul]
          exact (mul_le_mul ((abs_of_nonneg (hψb (F x)).1).trans_le (hψb (F x)).2)
            (smoothGaussianFaceGradient_coordinate_abs_le_one w a β x hw j)
            (abs_nonneg _) (by norm_num)).trans_eq (one_mul (1 : ℝ))⟩)
    convert hi using 1
    funext x
    simp only [faceDot, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by dsimp only [F, g, Function.comp_apply]; ring)
  calc
    _ ≤ (∫ x, dψ (F x) * vectorNormSq (g x) ∂standardGaussian r) +
        ∫ x, ψ (F x) * (∑ j, smoothGaussianFaceHessian w a β x j j)
          ∂standardGaussian r := le_add_of_nonneg_right (integral_nonneg hcorr)
    _ = ∫ x, ψ (F x) * faceDot (g x) x ∂standardGaussian r := by
      rw [← integral_add hlefti hcorri]
      exact smoothGaussianFaceMaximum_stein w a β hβ.ne' hw ψ dψ hψ hdψ hψb D hdψb
    _ ≤ _ := integral_mono hrighi (integrable_positiveGaussianFaceMaximum w)
      (fun x => smoothGaussianFaceGradient_dot_le_positiveMaximum w a β x (ψ (F x)) (hψb _))

theorem gaussianFacePartition_lower (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) :
    Real.exp (β * gaussianAffineMaximum w a x) ≤ gaussianFacePartition w a β x := by
  rw [activeGaussianBranch_attains]
  exact Finset.single_le_sum (fun α _ => Real.exp_nonneg
    (β * (faceDot (w α) x - a α))) (Finset.mem_univ (activeGaussianBranch w a x))

theorem gaussianFacePartition_upper (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (x : Vector r) :
    gaussianFacePartition w a β x ≤ (m : ℝ) * Real.exp (β * gaussianAffineMaximum w a x) := by
  calc
    _ ≤ ∑ _α : Fin m, Real.exp (β * gaussianAffineMaximum w a x) :=
      Finset.sum_le_sum (fun α _ => Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (affineBranch_le_gaussianAffineMaximum w a x α) hβ))
    _ = _ := by simp

/-- Uniform log-sum-exp error, including arbitrary repeated rows. -/
theorem smoothGaussianFaceMaximum_bounds (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (hβ : 0 < β) (x : Vector r) :
    gaussianAffineMaximum w a x ≤ smoothGaussianFaceMaximum w a β x ∧
      smoothGaussianFaceMaximum w a β x ≤ gaussianAffineMaximum w a x + Real.log m / β := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  constructor
  · apply (le_div_iff₀ hβ).mpr
    have hh := Real.log_le_log (Real.exp_pos _) (gaussianFacePartition_lower w a β x)
    simpa only [Real.log_exp, mul_comm] using hh
  · apply (div_le_iff₀ hβ).mpr
    have hh := Real.log_le_log (gaussianFacePartition_pos w a β x)
      (gaussianFacePartition_upper w a β hβ.le x)
    rw [Real.log_mul hm.ne' (Real.exp_pos _).ne', Real.log_exp] at hh
    nlinarith [div_mul_cancel₀ (Real.log (m : ℝ)) hβ.ne']

theorem gaussianFaceWeight_le_exp_gap (w : Fin m → Vector r) (a : Fin m → ℝ)
    (β : ℝ) (x : Vector r) (α : Fin m) :
    gaussianFaceWeight w a β x α ≤
      Real.exp (β * ((faceDot (w α) x - a α) - gaussianAffineMaximum w a x)) := by
  calc
    _ ≤ Real.exp (β * (faceDot (w α) x - a α)) /
        Real.exp (β * gaussianAffineMaximum w a x) :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _)
        (Real.exp_pos _) (gaussianFacePartition_lower w a β x)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

theorem smoothGaussianFaceMaximum_tendsto (w : Fin m → Vector r)
    (a : Fin m → ℝ) (x : Vector r) :
    Filter.Tendsto (fun β : ℝ => smoothGaussianFaceMaximum w a β x)
      Filter.atTop (𝓝 (gaussianAffineMaximum w a x)) := by
  have ht : Filter.Tendsto (fun β : ℝ => gaussianAffineMaximum w a x + Real.log m / β)
      Filter.atTop (𝓝 (gaussianAffineMaximum w a x)) := by
    have hc : Filter.Tendsto (fun _β : ℝ => gaussianAffineMaximum w a x)
        Filter.atTop (𝓝 (gaussianAffineMaximum w a x)) := tendsto_const_nhds
    have hd : Filter.Tendsto (fun β : ℝ => Real.log m / β) Filter.atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Filter.tendsto_id
    simpa only [add_zero] using hc.add hd
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact (Filter.eventually_gt_atTop (0 : ℝ)).mono
      (fun β hβ => (smoothGaussianFaceMaximum_bounds w a β hβ x).1)
  · exact (Filter.eventually_gt_atTop (0 : ℝ)).mono
      (fun β hβ => (smoothGaussianFaceMaximum_bounds w a β hβ x).2)

theorem gaussianFaceWeight_tendsto_zero_of_inactive
    (w : Fin m → Vector r) (a : Fin m → ℝ) (x : Vector r) (α : Fin m)
    (hα : faceDot (w α) x - a α < gaussianAffineMaximum w a x) :
    Filter.Tendsto (fun β : ℝ => gaussianFaceWeight w a β x α)
      Filter.atTop (𝓝 0) := by
  have hg := Real.tendsto_exp_atBot.comp
    (Filter.tendsto_id.atTop_mul_const_of_neg (sub_neg.mpr hα))
  exact squeeze_zero (fun β => gaussianFaceWeight_nonneg w a β x α)
    (fun β => gaussianFaceWeight_le_exp_gap w a β x α) hg

theorem smoothGaussianFaceGradient_sub_active
    (w : Fin m → Vector r) (a : Fin m → ℝ) (β : ℝ) (x : Vector r)
    (α : Fin m) (j : Fin r) :
    smoothGaussianFaceGradient w a β x j - w α j =
      ∑ γ, gaussianFaceWeight w a β x γ * (w γ j - w α j) := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    gaussianFaceWeight_sum, one_mul, smoothGaussianFaceGradient]

/-- At a point where ties can only occur between identical normal rows,
the smooth gradient converges to an actual active unit normal. This avoids
any artificial covariance gap and permits repeated rows outright. -/
theorem smoothGaussianFaceGradient_tendsto_active
    (w : Fin m → Vector r) (a : Fin m → ℝ) (x : Vector r)
    (hties : ∀ α γ, w α ≠ w γ →
      faceDot (w α) x - a α ≠ faceDot (w γ) x - a γ) (j : Fin r) :
    Filter.Tendsto (fun β : ℝ => smoothGaussianFaceGradient w a β x j)
      Filter.atTop (𝓝 (w (activeGaussianBranch w a x) j)) := by
  let α := activeGaussianBranch w a x
  have hlim (γ : Fin m) : Filter.Tendsto
      (fun β : ℝ => gaussianFaceWeight w a β x γ * (w γ j - w α j))
      Filter.atTop (𝓝 0) := by
    by_cases he : w γ = w α
    · simp only [he, sub_self, mul_zero]
      exact tendsto_const_nhds
    · have hg : faceDot (w γ) x - a γ < gaussianAffineMaximum w a x := by
        apply lt_of_le_of_ne (affineBranch_le_gaussianAffineMaximum w a x γ)
        rw [activeGaussianBranch_attains]
        exact hties γ α he
      simpa only [zero_mul] using
        (gaussianFaceWeight_tendsto_zero_of_inactive w a x γ hg).mul_const (w γ j - w α j)
  have hs := tendsto_finset_sum Finset.univ (fun γ _ => hlim γ)
  simp only [Finset.sum_const_zero] at hs
  have he (β : ℝ) := smoothGaussianFaceGradient_sub_active w a β x α j
  have hd : Filter.Tendsto (fun β : ℝ => smoothGaussianFaceGradient w a β x j - w α j)
      Filter.atTop (𝓝 0) := hs.congr (fun β => (he β).symm)
  simpa only [sub_add_cancel, zero_add] using hd.add_const (w α j)

theorem smoothGaussianFaceGradient_normSq_tendsto_one
    (w : Fin m → Vector r) (a : Fin m → ℝ) (x : Vector r)
    (hw : ∀ α, vectorNormSq (w α) = 1)
    (hties : ∀ α γ, w α ≠ w γ →
      faceDot (w α) x - a α ≠ faceDot (w γ) x - a γ) :
    Filter.Tendsto (fun β : ℝ => vectorNormSq (smoothGaussianFaceGradient w a β x))
      Filter.atTop (𝓝 1) := by
  have hh := tendsto_finset_sum Finset.univ (fun j _ =>
    (smoothGaussianFaceGradient_tendsto_active w a x hties j).pow 2)
  change Filter.Tendsto (fun β : ℝ => vectorNormSq (smoothGaussianFaceGradient w a β x))
    Filter.atTop (𝓝 (vectorNormSq (w (activeGaussianBranch w a x)))) at hh
  rwa [hw] at hh

theorem positiveGaussianFaceMaximum_le_projection_norm
    (w : Fin m → Vector r) (x : Vector r) :
    positiveGaussianFaceMaximum w x ≤ ‖linearProjectionFamily w x‖ := by
  apply max_le (norm_nonneg _)
  apply Finset.sup'_le
  intro α _
  exact (le_abs_self _).trans (by
    simpa only [linearProjectionFamily, faceDot, Real.norm_eq_abs] using
      norm_le_pi_norm (linearProjectionFamily w x) α)

theorem integrable_gaussian_projection_norm (w : Fin m → Vector r) :
    Integrable (fun x => ‖linearProjectionFamily w x‖) (standardGaussian r) := by
  apply (integrable_finset_sum Finset.univ (fun α _ =>
    (standardGaussian_integrable_faceDot (w α)).abs)).mono'
      (measurable_linearProjectionFamily w).norm.aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun α _ =>
      abs_nonneg (faceDot (w α) x)))).mpr
    intro α
    exact Finset.single_le_sum (fun γ _ => abs_nonneg (faceDot (w γ) x)) (Finset.mem_univ α))

theorem integral_positiveGaussianFaceMaximum_le_projection_norm
    (w : Fin m → Vector r) :
    (∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r) ≤
      ∫ x, ‖linearProjectionFamily w x‖ ∂standardGaussian r :=
  integral_mono (integrable_positiveGaussianFaceMaximum w) (integrable_gaussian_projection_norm w)
    (positiveGaussianFaceMaximum_le_projection_norm w)

theorem exp_positiveGaussianFaceMaximum_le (w : Fin m → Vector r)
    (t : ℝ) (x : Vector r) :
    Real.exp (t * positiveGaussianFaceMaximum w x) ≤
      1 + ∑ α, Real.exp (t * faceDot (w α) x) := by
  by_cases h : ((Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty
      (fun α => faceDot (w α) x)) ≤ 0
  · rw [positiveGaussianFaceMaximum, max_eq_left h, mul_zero, Real.exp_zero]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun α _ => Real.exp_nonneg _))
  · rw [positiveGaussianFaceMaximum, max_eq_right (le_of_lt (lt_of_not_ge h))]
    obtain ⟨α, _, hα⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin m)))
      Finset.univ_nonempty (fun α => faceDot (w α) x)
    rw [hα]
    exact (Finset.single_le_sum (fun γ _ => Real.exp_nonneg (t * faceDot (w γ) x))
      (Finset.mem_univ α)).trans (le_add_of_nonneg_left (by norm_num))

theorem integrable_exp_positiveGaussianFaceMaximum (w : Fin m → Vector r) (t : ℝ) :
    Integrable (fun x => Real.exp (t * positiveGaussianFaceMaximum w x)) (standardGaussian r) := by
  apply ((integrable_const (1 : ℝ)).add (integrable_finset_sum Finset.univ
    (fun α _ => integrable_exp_linearProjection (w α) t))).mono'
      (Real.continuous_exp.comp ((continuous_const : Continuous (fun _ : Vector r => t)).mul
        (continuous_positiveGaussianFaceMaximum w))).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    change ‖Real.exp (t * positiveGaussianFaceMaximum w x)‖ ≤
      1 + ∑ α, Real.exp (t * faceDot (w α) x)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_positiveGaussianFaceMaximum_le w t x)

theorem integral_exp_positiveGaussianFaceMaximum_le (w : Fin m → Vector r)
    (hw : ∀ α, vectorNormSq (w α) = 1) (t : ℝ) :
    (∫ x, Real.exp (t * positiveGaussianFaceMaximum w x) ∂standardGaussian r) ≤
      ((m : ℝ) + 1) * Real.exp (t ^ 2 / 2) := by
  have hi (α : Fin m) : Integrable (fun x => Real.exp (t * faceDot (w α) x))
      (standardGaussian r) := integrable_exp_linearProjection (w α) t
  calc
    _ ≤ ∫ x, 1 + ∑ α, Real.exp (t * faceDot (w α) x) ∂standardGaussian r :=
      integral_mono (integrable_exp_positiveGaussianFaceMaximum w t)
        ((integrable_const (1 : ℝ)).add (integrable_finset_sum Finset.univ (fun α _ => hi α)))
        (exp_positiveGaussianFaceMaximum_le w t)
    _ = 1 + (m : ℝ) * Real.exp (t ^ 2 / 2) := by
      rw [integral_add (integrable_const (1 : ℝ))
        (integrable_finset_sum Finset.univ (fun α _ => hi α)),
        integral_finset_sum _ (fun α _ => hi α)]
      have hg (α : Fin m) : (∫ x, Real.exp (t * faceDot (w α) x) ∂standardGaussian r) =
          Real.exp (t ^ 2 / 2) := by
        change ProbabilityTheory.mgf (faceDot (w α)) (standardGaussian r) t = _
        unfold faceDot
        rw [standardGaussian_mgf_linearProjection]
        change Real.exp (t ^ 2 * vectorNormSq (w α) / 2) = _
        rw [hw, mul_one]
      simp_rw [hg]
      simp
    _ ≤ _ := by
      have he : 1 ≤ Real.exp (t ^ 2 / 2) := Real.one_le_exp (by positivity)
      nlinarith

/-- The logarithmic intrinsic maximum estimate has the exact
`sqrt (2 log (m+1))` constant and needs no independence between faces. -/
theorem integral_positiveGaussianFaceMaximum_le_sqrt_log
    (w : Fin m → Vector r) (hw : ∀ α, vectorNormSq (w α) = 1) :
    (∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r) ≤
      Real.sqrt (2 * Real.log ((m : ℝ) + 1)) := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hlog : 0 < Real.log ((m : ℝ) + 1) := Real.log_pos (by linarith)
  let t := Real.sqrt (2 * Real.log ((m : ℝ) + 1))
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t ^ 2 = 2 * Real.log ((m : ℝ) + 1) := Real.sq_sqrt (by positivity)
  have hj := exp_integral_le_integral_exp
    ((integrable_positiveGaussianFaceMaximum w).const_mul t)
    (integrable_exp_positiveGaussianFaceMaximum w t)
  rw [integral_const_mul] at hj
  have hb := hj.trans (integral_exp_positiveGaussianFaceMaximum_le w hw t)
  have he : ((m : ℝ) + 1) * Real.exp (t ^ 2 / 2) =
      Real.exp (2 * Real.log ((m : ℝ) + 1)) := by
    rw [ht2]
    have hp : 0 < (m : ℝ) + 1 := by positivity
    rw [show 2 * Real.log ((m : ℝ) + 1) / 2 = Real.log ((m : ℝ) + 1) by ring]
    conv_lhs => lhs; rw [← Real.exp_log hp]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hb
  have hh := Real.exp_le_exp.mp hb
  nlinarith

/-- Dominated convergence removes the smooth maximum. The domination is
the actual test derivative bound, since the soft gradient has norm at most
one. Hyperplane nullity supplies the full-measure gradient limit. -/
theorem gaussianAffineMaximum_test_bound
    (w : Fin m → Vector r) (a : Fin m → ℝ)
    (hw : ∀ α, vectorNormSq (w α) = 1)
    (ψ dψ : ℝ → ℝ) (hψ : ∀ t, HasDerivAt ψ (dψ t) t)
    (hdψ : Continuous dψ) (hψb : ∀ t, 0 ≤ ψ t ∧ ψ t ≤ 1)
    (D : ℝ) (hdψb : ∀ t, |dψ t| ≤ D) :
    (∫ x, dψ (gaussianAffineMaximum w a x) ∂standardGaussian r) ≤
      ∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r := by
  let H (β : ℝ) (x : Vector r) := dψ (smoothGaussianFaceMaximum w a β x) *
    vectorNormSq (smoothGaussianFaceGradient w a β x)
  have hHc (β : ℝ) : Continuous (H β) := by
    apply (hdψ.comp (continuous_smoothGaussianFaceMaximum w a β)).mul
    exact continuous_finset_sum _ (fun j _ =>
      (continuous_smoothGaussianFaceGradient w a β j).pow 2)
  have hHb (β : ℝ) (x : Vector r) : |H β x| ≤ D := by
    have hn : 0 ≤ vectorNormSq (smoothGaussianFaceGradient w a β x) :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    dsimp only [H]
    rw [abs_mul, abs_of_nonneg hn]
    exact (mul_le_mul (hdψb _)
      (smoothGaussianFaceGradient_normSq_le_one w a β x hw) hn
      ((abs_nonneg (dψ 0)).trans (hdψb 0))).trans_eq (mul_one D)
  have hlim : ∀ᵐ x ∂standardGaussian r, Filter.Tendsto (fun β : ℝ => H β x)
      Filter.atTop (𝓝 (dψ (gaussianAffineMaximum w a x))) := by
    filter_upwards [gaussian_affine_branches_ae_distinct_rows_ne w a] with x hx
    have hf := (hdψ.tendsto (gaussianAffineMaximum w a x)).comp
      (smoothGaussianFaceMaximum_tendsto w a x)
    simpa only [mul_one] using hf.mul
      (smoothGaussianFaceGradient_normSq_tendsto_one w a x hw hx)
  have hI := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussian r) (F := H)
    (f := fun x => dψ (gaussianAffineMaximum w a x)) (fun _ => D)
    (Filter.Eventually.of_forall (fun β => (hHc β).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun β => ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hHb β x))) (integrable_const D) hlim
  exact le_of_tendsto hI ((Filter.eventually_gt_atTop (0 : ℝ)).mono
    (fun β hβ => smoothGaussianFaceMaximum_test_bound w a β hβ hw ψ dψ hψ hdψ hψb D hdψb))

/-- The full intrinsic Gaussian boundary inequality, with the exact
coefficient two. Covariance singularity, repeated normal rows, and arbitrary
thresholds are all allowed. The slightly stronger closed shell is bounded. -/
theorem intrinsicGaussianBoundary
    (w : Fin m → Vector r) (a : Fin m → ℝ)
    (hw : ∀ α, vectorNormSq (w α) = 1) {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian r).real {x | -s ≤ gaussianAffineMaximum w a x ∧
      gaussianAffineMaximum w a x ≤ s} ≤
      (2 * s) * ∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r := by
  have ht := centered_interval_probability_le_of_smooth_tests (standardGaussian r)
    (gaussianAffineMaximum w a) (continuous_gaussianAffineMaximum w a).measurable
    (∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r)
    (fun ψ dψ hψ hdψ _ hψb hb => by
      obtain ⟨D, hD⟩ := hb
      exact gaussianAffineMaximum_test_bound w a hw ψ dψ hψ hdψ hψb D hD)
    (t := 0) hs
  simpa only [zero_sub, zero_add, Set.preimage_setOf_eq, Set.mem_Icc] using ht

theorem intrinsicGaussianBoundary_absoluteMaximum
    (w : Fin m → Vector r) (a : Fin m → ℝ)
    (hw : ∀ α, vectorNormSq (w α) = 1) {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian r).real {x | -s ≤ gaussianAffineMaximum w a x ∧
      gaussianAffineMaximum w a x ≤ s} ≤
      (2 * s) * ∫ x, ‖linearProjectionFamily w x‖ ∂standardGaussian r :=
  (intrinsicGaussianBoundary w a hw hs).trans
    (mul_le_mul_of_nonneg_left (integral_positiveGaussianFaceMaximum_le_projection_norm w)
      (by positivity))

theorem intrinsicGaussianBoundary_logarithmic
    (w : Fin m → Vector r) (a : Fin m → ℝ)
    (hw : ∀ α, vectorNormSq (w α) = 1) {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian r).real {x | -s ≤ gaussianAffineMaximum w a x ∧
      gaussianAffineMaximum w a x ≤ s} ≤
      (2 * s) * Real.sqrt (2 * Real.log ((m : ℝ) + 1)) :=
  (intrinsicGaussianBoundary w a hw hs).trans
    (mul_le_mul_of_nonneg_left (integral_positiveGaussianFaceMaximum_le_sqrt_log w hw)
      (by positivity))

/-- The manuscript's half-open shell follows from the proved closed-shell
bound; no endpoint-mass premise is needed. -/
theorem intrinsicGaussianBoundary_Ioc
    (w : Fin m → Vector r) (a : Fin m → ℝ)
    (hw : ∀ α, vectorNormSq (w α) = 1) {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian r).real {x | -s < gaussianAffineMaximum w a x ∧
      gaussianAffineMaximum w a x ≤ s} ≤
      (2 * s) * ∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r := by
  have hsub : {x | -s < gaussianAffineMaximum w a x ∧ gaussianAffineMaximum w a x ≤ s} ⊆
      {x | -s ≤ gaussianAffineMaximum w a x ∧ gaussianAffineMaximum w a x ≤ s} :=
    fun _ hx => ⟨hx.1.le, hx.2⟩
  exact (measureReal_mono hsub).trans (intrinsicGaussianBoundary w a hw hs)

theorem intrinsicGaussianBoundary_min_one
    (w : Fin m → Vector r) (a : Fin m → ℝ)
    (hw : ∀ α, vectorNormSq (w α) = 1) {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian r).real {x | -s ≤ gaussianAffineMaximum w a x ∧
      gaussianAffineMaximum w a x ≤ s} ≤
      min 1 ((2 * s) * ∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r) := by
  exact le_min (measureReal_le_one) (intrinsicGaussianBoundary w a hw hs)

end

end RectangleCLT.Companion.SplitV4
