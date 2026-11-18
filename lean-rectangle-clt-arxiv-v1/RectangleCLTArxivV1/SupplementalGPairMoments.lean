import RectangleCLTArxivV1.SupplementalGGeometry

/-! Copy averaging of the angular pair coefficient. The two arrays may be
dependent and need only their genuine quadratic moment budgets. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_abs_mul_le_squares (a b : ℝ) : |a*b| ≤ (a^2+b^2)/2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a|-|b|),sq_abs a,sq_abs b]

theorem cap_integrable_abs_faceDot_mul
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ} (μ : Measure Ω)
    (Z W : Ω → Vector r) (hZm : Measurable Z) (hWm : Measurable W)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j*Z ω k) μ)
    (hW : ∀ j k, Integrable (fun ω => W ω j*W ω k) μ) (e : Vector r) :
    Integrable (fun ω => |faceDot e (Z ω)*faceDot e (W ω)|) μ := by
  have hi := ((integrable_faceDot_sq μ Z hZ e).add (integrable_faceDot_sq μ W hW e)).div_const 2
  have hm : Measurable (fun ω => |faceDot e (Z ω)*faceDot e (W ω)|) := by unfold faceDot; fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs,abs_abs]
    exact cap_abs_mul_le_squares _ _)

theorem cap_sum_integral_abs_faceDot_mul_le
    {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ} (μ : Measure Ω)
    (Z W : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i)) (hWm : ∀ i, Measurable (W i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hW : ∀ i j k, Integrable (fun ω => W i ω j*W i ω k) μ)
    {K : ℝ}
    (hbZ : ∀ e : Vector r, ∑ i, ∫ ω, (faceDot e (Z i ω))^2 ∂μ ≤ K*vectorNormSq e)
    (hbW : ∀ e : Vector r, ∑ i, ∫ ω, (faceDot e (W i ω))^2 ∂μ ≤ K*vectorNormSq e)
    (e : Vector r) (he : vectorNormSq e = 1) :
    (∑ i, ∫ ω, |faceDot e (Z i ω)*faceDot e (W i ω)| ∂μ) ≤ K := by
  have ht (i : Fin n) : (∫ ω, |faceDot e (Z i ω)*faceDot e (W i ω)| ∂μ) ≤
      ((∫ ω, (faceDot e (Z i ω))^2 ∂μ)+(∫ ω, (faceDot e (W i ω))^2 ∂μ))/2 := by
    have hZi := integrable_faceDot_sq μ (Z i) (hZ i) e
    have hWi := integrable_faceDot_sq μ (W i) (hW i) e
    have hi := integral_mono (cap_integrable_abs_faceDot_mul μ (Z i) (W i) (hZm i) (hWm i) (hZ i) (hW i) e)
      ((hZi.add hWi).div_const 2) (fun ω => cap_abs_mul_le_squares _ _)
    simp only [Pi.add_apply] at hi
    simpa only [integral_div,integral_add hZi hWi] using hi
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ht i)
  rw [← Finset.sum_div,Finset.sum_add_distrib] at hs
  have h1 := hbZ e
  have h2 := hbW e
  rw [he,mul_one] at h1 h2
  linarith

/-- Angular cancellation after actual copy expectation. This estimate holds
for all three copy patterns because no independence of Z and W is needed. -/
theorem cap_pair_coefficient_integral_abs_le
    {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ} (μ : Measure Ω)
    (Z W : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i)) (hWm : ∀ i, Measurable (W i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hW : ∀ i j k, Integrable (fun ω => W i ω j*W i ω k) μ)
    {K : ℝ}
    (hbZ : ∀ e : Vector r, ∑ i, ∫ ω, (faceDot e (Z i ω))^2 ∂μ ≤ K*vectorNormSq e)
    (hbW : ∀ e : Vector r, ∑ i, ∫ ω, (faceDot e (W i ω))^2 ∂μ ≤ K*vectorNormSq e)
    (u v : Vector r) (hu : vectorNormSq u = 1) (hv : vectorNormSq v = 1)
    (hρ : |dotProduct u v| < 1) :
    (∑ i, ∫ ω, |capPairCoefficient u v (Z i ω) (W i ω)| ∂μ) ≤
      4*K*(1-|dotProduct u v|) := by
  let q := capAngularDirection u v
  let c := 1-|dotProduct u v|
  have hc : 0 ≤ c := by dsimp only [c]; linarith
  have hq : vectorNormSq q = 1 := capAngularDirection_unit u v hu hv hρ
  let P (e : Vector r) (i : Fin n) (ω : Ω) := |faceDot e (Z i ω)*faceDot e (W i ω)|
  have hPi (e : Vector r) (i : Fin n) : Integrable (P e i) μ :=
    cap_integrable_abs_faceDot_mul μ (Z i) (W i) (hZm i) (hWm i) (hZ i) (hW i) e
  have hp (i : Fin n) (ω : Ω) : |capPairCoefficient u v (Z i ω) (W i ω)| ≤
      c*(P u i ω+P v i ω+2*P q i ω) := by
    rw [capPairCoefficient_angular_identity u v (Z i ω) (W i ω) hρ,abs_mul,abs_mul]
    have hsign : |capSign (dotProduct u v)| = 1 := by unfold capSign; split <;> norm_num
    rw [hsign,one_mul,abs_of_nonneg hc]
    apply mul_le_mul_of_nonneg_left _ hc
    have h1 := abs_sub (dotProduct u (Z i ω)*dotProduct u (W i ω)+
      dotProduct v (Z i ω)*dotProduct v (W i ω)) (2*dotProduct q (Z i ω)*dotProduct q (W i ω))
    have h2 := abs_add (dotProduct u (Z i ω)*dotProduct u (W i ω))
      (dotProduct v (Z i ω)*dotProduct v (W i ω))
    change |dotProduct u (Z i ω)*dotProduct u (W i ω)+dotProduct v (Z i ω)*dotProduct v (W i ω)-
      2*dotProduct q (Z i ω)*dotProduct q (W i ω)| ≤ _
    dsimp only [P]
    simp only [faceDot,dotProduct,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h1 h2 ⊢
    linarith
  have hBi (i : Fin n) : Integrable (fun ω => |capPairCoefficient u v (Z i ω) (W i ω)|) μ := by
    have hm : Measurable (fun ω => |capPairCoefficient u v (Z i ω) (W i ω)|) := by
      unfold capPairCoefficient dotProduct; fun_prop
    apply ((((hPi u i).add (hPi v i)).add ((hPi q i).const_mul 2)).const_mul c).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by rw [Real.norm_eq_abs,abs_abs]; exact hp i ω)
  have ht (i : Fin n) : (∫ ω, |capPairCoefficient u v (Z i ω) (W i ω)| ∂μ) ≤
      c*((∫ ω, P u i ω ∂μ)+(∫ ω, P v i ω ∂μ)+2*(∫ ω, P q i ω ∂μ)) := by
    have hi := integral_mono (hBi i)
      ((((hPi u i).add (hPi v i)).add ((hPi q i).const_mul 2)).const_mul c) (hp i)
    have hsplit : (∫ ω, P u i ω+P v i ω+2*P q i ω ∂μ) =
        (∫ ω, P u i ω ∂μ)+(∫ ω, P v i ω ∂μ)+2*(∫ ω, P q i ω ∂μ) := by
      calc
        _ = (∫ ω, P u i ω+P v i ω ∂μ)+(∫ ω, 2*P q i ω ∂μ) :=
          integral_add ((hPi u i).add (hPi v i)) ((hPi q i).const_mul 2)
        _ = _ := by rw [integral_add (hPi u i) (hPi v i),integral_const_mul]
    rw [integral_const_mul] at hi
    exact hi.trans_eq (congrArg (fun a => c*a) hsplit)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ht i)
  simp only [← Finset.mul_sum,Finset.sum_add_distrib] at hs
  have h1 := cap_sum_integral_abs_faceDot_mul_le μ Z W hZm hWm hZ hW hbZ hbW u hu
  have h2 := cap_sum_integral_abs_faceDot_mul_le μ Z W hZm hWm hZ hW hbZ hbW v hv
  have h3 := cap_sum_integral_abs_faceDot_mul_le μ Z W hZm hWm hZ hW hbZ hbW q hq
  dsimp only [P] at hs
  dsimp only [c] at hc hs
  nlinarith

end
end RectangleCLTArxivV1
