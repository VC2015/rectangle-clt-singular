import RectangleCLTArxivV1.CapWeightMassProduct
import RectangleCLT.BoundedIndependentScaling

/-! Deterministic variance normalization for the general lower-variance
constant in Supplemental Lemma G.1. No upper covariance bound is needed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def capVarianceScale (c : ℝ) : ℝ := (Real.sqrt (2*c))⁻¹

theorem capVarianceScale_pos {c : ℝ} (hc : 0 < c) : 0 < capVarianceScale c := by
  unfold capVarianceScale
  positivity

theorem capVarianceScale_sq_mul {c : ℝ} (hc : 0 < c) :
    (capVarianceScale c)^2*c = 1/2 := by
  unfold capVarianceScale
  have hs : (Real.sqrt (2*c))^2 = 2*c := Real.sq_sqrt (by positivity)
  have hn := (Real.sqrt_pos.mpr (by positivity : 0 < 2*c)).ne'
  rw [inv_pow,hs]
  field_simp
  ring

theorem capMixedValue_smul {Ω : Type*} {p r n : ℕ}
    (X : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin r) ℝ) (a : ℝ)
    (z : Ω × Vector r) :
    capMixedValue (fun i ω => a • X i ω) (a • A) z = a • capMixedValue X A z := by
  unfold capMixedValue
  rw [sumVector_smul,Matrix.smul_mulVec_assoc,smul_add]

theorem capMixedCovariance_smul {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin p) (Fin r) ℝ) (a : ℝ) :
    capMixedCovariance μ (fun i ω => a • X i ω) (a • A) = a^2 • capMixedCovariance μ X A := by
  unfold capMixedCovariance
  rw [hdata.covariance_sum_smul,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  simp only [pow_two,smul_add]

theorem cap_scaled_interval_iff (a z x h : ℝ) (ha : 0 < a) :
    |a*z-a*x| ≤ a*h ↔ |z-x| ≤ h := by
  rw [← mul_sub,abs_mul,abs_of_pos ha,mul_le_mul_left ha]

/-- General positive lower variance, in actual projected coordinates. -/
theorem cap_one_projection_small_interval_of_lower_variance
    {Ω : Type*} [MeasurableSpace Ω] {r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {c h : ℝ} (hc : 0 < c)
    (hvar : c ≤ capMixedCovariance μ X A 0 0)
    (hh : 0 < h) (hband : δ ≤ h) (x : ℝ) :
    (μ.prod (standardGaussian r)).real {z | |capMixedValue X A z 0-x| ≤ h} ≤
      8*capVarianceScale c*h*Real.sqrt (Real.pi/capGaussianExponent) := by
  let a := capVarianceScale c
  have ha : 0 < a := capVarianceScale_pos hc
  have hd := hdata.smul_of_nonneg a ha.le
  have hvar' : (1/2 : ℝ) ≤ capMixedCovariance μ (fun i ω => a • X i ω) (a • A) 0 0 := by
    rw [capMixedCovariance_smul hdata]
    change (1/2 : ℝ) ≤ a^2*capMixedCovariance μ X A 0 0
    have he : a^2*c=1/2 := capVarianceScale_sq_mul hc
    nlinarith [mul_le_mul_of_nonneg_left hvar (sq_nonneg a)]
  have hp := cap_one_projection_small_interval hd (a • A) hvar' (mul_pos ha hh)
    (mul_le_mul_of_nonneg_left hband ha.le) (a*x)
  have he : {z | |capMixedValue (fun i ω => a • X i ω) (a • A) z 0-a*x| ≤ a*h} =
      {z | |capMixedValue X A z 0-x| ≤ h} := by
    ext z
    simp only [Set.mem_setOf_eq,capMixedValue_smul,Pi.smul_apply,smul_eq_mul]
    exact cap_scaled_interval_iff a _ x h ha
  rw [he] at hp
  exact hp.trans_eq (by dsimp [a]; ring)

/-- General positive lower variance for the two-face small box. -/
theorem cap_two_projection_small_box_of_lower_variance
    {Ω : Type*} [MeasurableSpace Ω] {r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {c v ρ h : ℝ} (hc : 0 < c)
    (hv : c ≤ v) (hρ : ρ^2 < 1)
    (hcov : capMixedCovariance μ X A = !![v,v*ρ;v*ρ,v])
    (hh : 0 < h) (hband : 2*δ ≤ h) (x y : ℝ) :
    (μ.prod (standardGaussian r)).real {z |
      |capMixedValue X A z 0-x| ≤ h ∧ |capMixedValue X A z 1-y| ≤ h} ≤
      16*Real.pi^3*(capVarianceScale c)^2*h^2/Real.sqrt (1-ρ^2) := by
  let a := capVarianceScale c
  have ha : 0 < a := capVarianceScale_pos hc
  have hd := hdata.smul_of_nonneg a ha.le
  have hv' : (1/2 : ℝ) ≤ a^2*v := by
    have he : a^2*c=1/2 := capVarianceScale_sq_mul hc
    nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg a)]
  have hcov' : capMixedCovariance μ (fun i ω => a • X i ω) (a • A) =
      !![a^2*v,(a^2*v)*ρ;(a^2*v)*ρ,a^2*v] := by
    rw [capMixedCovariance_smul hdata,hcov]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply,smul_eq_mul] <;> ring
  have hband' : 2*(a*δ) ≤ a*h := by nlinarith [mul_le_mul_of_nonneg_left hband ha.le]
  have hp := cap_two_projection_small_box hd (a • A) hv' hρ hcov' (mul_pos ha hh) hband' (a*x) (a*y)
  have he : {z | |capMixedValue (fun i ω => a • X i ω) (a • A) z 0-a*x| ≤ a*h ∧
      |capMixedValue (fun i ω => a • X i ω) (a • A) z 1-a*y| ≤ a*h} =
      {z | |capMixedValue X A z 0-x| ≤ h ∧ |capMixedValue X A z 1-y| ≤ h} := by
    ext z
    simp only [Set.mem_setOf_eq,capMixedValue_smul,Pi.smul_apply,smul_eq_mul]
    exact and_congr (cap_scaled_interval_iff a _ x h ha) (cap_scaled_interval_iff a _ y h ha)
  rw [he] at hp
  exact hp.trans_eq (by dsimp [a]; ring)

/-- The general-lower-variance single logistic mass, uniform in thresholds
and deterministic translations. -/
theorem cap_one_face_tuple_mass_of_lower_variance
    {Ω : Type*} [MeasurableSpace Ω] {r n m p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {c h : ℝ} (hc : 0 < c)
    (hvar : c ≤ capMixedCovariance μ X A 0 0)
    (hh : 0 < h) (hband : δ ≤ h)
    (U : Fin m → Vector p) (a : Vector m) (j : Fin m)
    (Y : Ω × Vector r → Vector p) (hY : Measurable Y) (b : ℝ)
    (hproj : ∀ z, faceDot (U j) (Y z) = capMixedValue X A z 0+b) :
    (∫ z, logisticTupleWeight U a h ![j] (Y z) ∂μ.prod (standardGaussian r)) ≤
      16*Real.exp (1/2)*capVarianceScale c*h*Real.sqrt (Real.pi/capGaussianExponent) := by
  have hscale := (capVarianceScale_pos hc).le
  have hp := integral_logistic_single_le_of_intervals (μ.prod (standardGaussian r)) U a hh
    (by positivity : 0 ≤ 8*capVarianceScale c*h*Real.sqrt (Real.pi/capGaussianExponent)) Y hY j (fun t => by
      have he : {z | |faceDot (U j) (Y z)-t| ≤ h} = {z | |capMixedValue X A z 0-(t-b)| ≤ h} := by
        ext z
        simp only [Set.mem_setOf_eq,hproj]
        have he : capMixedValue X A z 0+b-t = capMixedValue X A z 0-(t-b) := by ring
        rw [he]
      rw [he]
      exact cap_one_projection_small_interval_of_lower_variance hdata A hc hvar hh hband (t-b))
  exact hp.trans_eq (by ring)

/-- The general-lower-variance pair logistic mass, uniform in thresholds
and deterministic translations. -/
theorem cap_two_face_tuple_mass_of_lower_variance
    {Ω : Type*} [MeasurableSpace Ω] {r n m p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {c v ρ h : ℝ} (hc : 0 < c)
    (hv : c ≤ v) (hρ : ρ^2 < 1)
    (hcov : capMixedCovariance μ X A = !![v,v*ρ;v*ρ,v])
    (hh : 0 < h) (hband : 2*δ ≤ h)
    (U : Fin m → Vector p) (a : Vector m) (j k : Fin m)
    (Y : Ω × Vector r → Vector p) (hY : Measurable Y) (b₀ b₁ : ℝ)
    (hproj₀ : ∀ z, faceDot (U j) (Y z) = capMixedValue X A z 0+b₀)
    (hproj₁ : ∀ z, faceDot (U k) (Y z) = capMixedValue X A z 1+b₁) :
    (∫ z, logisticTupleWeight U a h ![j,k] (Y z) ∂μ.prod (standardGaussian r)) ≤
      64*Real.exp 1*Real.pi^3*(capVarianceScale c)^2*h^2/Real.sqrt (1-ρ^2) := by
  have hp := integral_logistic_pair_le_of_boxes (μ.prod (standardGaussian r)) U a hh
    (by positivity : 0 ≤ 16*Real.pi^3*(capVarianceScale c)^2*h^2/Real.sqrt (1-ρ^2)) Y hY j k (fun s t => by
      have he : {z | |faceDot (U j) (Y z)-s| ≤ h ∧ |faceDot (U k) (Y z)-t| ≤ h} =
          {z | |capMixedValue X A z 0-(s-b₀)| ≤ h ∧ |capMixedValue X A z 1-(t-b₁)| ≤ h} := by
        ext z
        simp only [Set.mem_setOf_eq,hproj₀,hproj₁]
        have he0 : capMixedValue X A z 0+b₀-s = capMixedValue X A z 0-(s-b₀) := by ring
        have he1 : capMixedValue X A z 1+b₁-t = capMixedValue X A z 1-(t-b₁) := by ring
        rw [he0,he1]
      rw [he]
      exact cap_two_projection_small_box_of_lower_variance hdata A hc hv hρ hcov hh hband (s-b₀) (t-b₁))
  exact hp.trans_eq (by ring)

end
end RectangleCLTArxivV1
