import RectangleCLTArxivV1.IntrinsicBoundedConcentration
import RectangleCLTArxivV1.GaussianC1Statement

/-! Lemma 1 for an arbitrary nonempty face family with at most `2p` faces. -/
namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT
open scoped BigOperators

set_option autoImplicit false

theorem dimensionLog_faces_le {m p : ℕ} [NeZero m] (hm : m ≤ 2 * p) :
    dimensionLog m ≤ dimensionLog (2 * p) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (NeZero.pos m)
  have hmp : (m : ℝ) ≤ (2 * p : ℕ) := by exact_mod_cast hm
  unfold dimensionLog
  apply Real.log_le_log (mul_pos (Real.exp_pos _) hm0)
  exact mul_le_mul_of_nonneg_left hmp (Real.exp_pos _).le

/-- The bounded half of Lemma 1. Only the face projections are bounded;
unobserved directions need no envelope or spectral lower bound. -/
theorem lemma_1_bounded_model {r m p n : ℕ} [NeZero m] (hp : 1 ≤ p) (hm : m ≤ 2 * p)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Fin m → Fin r → ℝ) (X : Fin n → Ω → Fin r → ℝ) {η v : ℝ}
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hint : ∀ i k, Integrable (fun ω => X i ω k) μ)
    (hmean : ∀ i k, (∫ ω, X i ω k ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceNorm U (X i ω) ≤ η)
    (hv : 0 < v)
    (hvariance : ∀ j, covariance μ (fun ω => faceProjection U (sumVector X ω)) j j = v)
    (R : Ω → Fin r → ℝ) (hR : Measurable R) (hRind : IndepFun (sumVector X) R μ)
    (a : Fin m → ℝ) {s : ℝ} (hs : 0 < s) :
    μ.real {ω | sumVector X ω + R ω ∈ faceLayer U a s} ≤
      512 * min 1 (min (((s + η) / v) * ∫ ω, faceNorm U (sumVector X ω) ∂μ)
        ((s + η) * Real.sqrt (dimensionLog p / v))) := by
  have hη := faceEnvelope_nonneg_of_positive_variance μ U X hbound hv hvariance
  let P := μ.real {ω | sumVector X ω + R ω ∈ faceLayer U a s}
  let I := ((s + η) / v) * ∫ ω, faceNorm U (sumVector X ω) ∂μ
  let J := (s + η) * Real.sqrt (dimensionLog p / v)
  have hP1 : P ≤ 1 := measureReal_le_one
  have hP2 : P ≤ 512 * I := by
    have hh := boundedFaceLayer_intrinsic μ U X hmeas hind hint hmean hbound hv hvariance R hR hRind a hs.le
    change P ≤ 64 * I at hh
    have hI : 0 ≤ I := mul_nonneg (div_nonneg (add_nonneg hs.le hη) hv.le)
      (integral_nonneg (fun ω => faceNorm_nonneg U _))
    linarith
  have hroot : Real.sqrt (dimensionLog m / v) ≤ 2 * Real.sqrt (dimensionLog p / v) :=
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (dimensionLog_faces_le hm) hv.le)).trans
      (sqrt_dimensionLog_double_le hp hv)
  have hP3 : P ≤ 512 * J := by
    have hh := boundedFaceLayer_min μ U X hmeas hind hint hmean hbound hv hvariance R hR hRind a hs.le
    have hj : P ≤ 256 * ((s + η) * Real.sqrt (dimensionLog m / v)) :=
      hh.trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num))
    calc
      P ≤ _ := hj
      _ ≤ 256 * ((s + η) * (2 * Real.sqrt (dimensionLog p / v))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hroot (add_nonneg hs.le hη)) (by norm_num)
      _ = 512 * J := by dsimp [J]; ring
  have hh : P / 512 ≤ min 1 (min I J) := by
    apply le_min
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).mpr
      linarith
    · apply le_min
      · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).mpr
        simpa only [mul_comm] using hP2
      · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).mpr
        simpa only [mul_comm] using hP3
  have hh' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 512)).mp hh
  simpa only [mul_comm] using hh'

end RectangleCLTArxivV1
