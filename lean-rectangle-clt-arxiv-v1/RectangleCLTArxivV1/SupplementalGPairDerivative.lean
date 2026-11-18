import RectangleCLTArxivV1.SupplementalGDecomposition

/-! The positive-weight small-angle branch uses the actual second
directional derivative, with the original pair weight retained. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def capSoftFaceSecond {p : ℕ} (s : FaceSmoother p) (S : Finset (Face p))
    (y x : Vector p) : ℝ :=
  s.softFaceWeight S x/s.bandwidth^2*
    (((∑ f ∈ S, normalDot f y)-((S.card : ℝ)+1)*(s.weights x).directionalMean y)^2-
      ((S.card : ℝ)+1)*(s.weights x).directionalCovariance y)

theorem capSoftFaceSecond_is_derivative {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (x y : Vector p) (t : ℝ) :
    HasDerivAt (fun a => s.softFaceDirectional S y (line x y a))
      (capSoftFaceSecond s S y (line x y t)) t := by
  have hW := (s.hasDerivAt_softFaceWeight_line S x y t).div_const s.bandwidth
  have hM := (s.hasDerivAt_directionalMean_line x y t).const_mul ((S.card : ℝ)+1)
  have hL := (hasDerivAt_const t (∑ f ∈ S, normalDot f y)).sub hM
  convert hW.mul hL using 1
  dsimp only [softFaceDirectional,capSoftFaceSecond]
  ring

theorem cap_directionalCovariance_le {p : ℕ} (w : FaceWeights p)
    (y : Vector p) {δ : ℝ} (_hδ : 0 ≤ δ) (hy : ‖y‖ ≤ δ) :
    w.directionalCovariance y ≤ δ^2 := by
  have hf (f : Face p) : normalDot f y^2 ≤ δ^2 := by
    have ha := abs_normalDot_le_of_norm_le f hy
    have ht := pow_le_pow_left₀ (abs_nonneg (normalDot f y)) ha 2
    simpa only [sq_abs] using ht
  have hsum : w.directionalSecondMoment y ≤ δ^2 := by
    unfold FaceWeights.directionalSecondMoment
    calc
      _ ≤ ∑ f, w.pi f*δ^2 := Finset.sum_le_sum (fun f _ =>
        mul_le_mul_of_nonneg_left (hf f) (w.pi_nonneg f))
      _ = w.theta*δ^2 := by rw [← Finset.sum_mul,w.sum_pi]
      _ ≤ δ^2 := by nlinarith [w.theta_lt_one]
  unfold FaceWeights.directionalCovariance
  nlinarith [sq_nonneg (w.directionalMean y)]

/-- A two-face second derivative costs only 28δ²/h² times its actual
positive weight. No division by an angle occurs in this branch. -/
theorem capSoftFaceSecond_abs_le {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (hcard : S.card ≤ 2) (x y : Vector p)
    {δ : ℝ} (hδ : 0 ≤ δ) (hy : ‖y‖ ≤ δ) :
    |capSoftFaceSecond s S y x| ≤ 28*δ^2/s.bandwidth^2*s.softFaceWeight S x := by
  let c : ℝ := (S.card : ℝ)+1
  let L := (∑ f ∈ S, normalDot f y)-c*(s.weights x).directionalMean y
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hc3 : c ≤ 3 := by dsimp only [c]; exact_mod_cast (show S.card+1≤3 by omega)
  have hM := ((s.weights x).abs_directionalMean_le_norm y).trans hy
  have hsum : |∑ f ∈ S, normalDot f y| ≤ (S.card : ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun f _ => abs_normalDot_le_of_norm_le f hy)).trans_eq
    simp
  have hL : |L| ≤ 5*δ := by
    dsimp only [L]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_of_nonneg hc0]
    have ht := mul_le_mul_of_nonneg_left hM hc0
    have hc : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcard
    nlinarith
  have hV0 := (s.weights x).directionalCovariance_nonneg y
  have hV := cap_directionalCovariance_le (s.weights x) y hδ hy
  have hB : |L^2-c*(s.weights x).directionalCovariance y| ≤ 28*δ^2 := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (sq_nonneg L),abs_mul,abs_of_nonneg hc0,abs_of_nonneg hV0]
    have hL2 : L^2 ≤ 25*δ^2 := by
      have ht := pow_le_pow_left₀ (abs_nonneg L) hL 2
      simpa only [sq_abs,mul_pow,show (5 : ℝ)^2=25 by norm_num] using ht
    nlinarith [mul_le_mul_of_nonneg_left hV hc0]
  unfold capSoftFaceSecond
  change |s.softFaceWeight S x/s.bandwidth^2*(L^2-c*(s.weights x).directionalCovariance y)| ≤ _
  rw [abs_mul,abs_of_nonneg (div_nonneg (s.softFaceWeight_nonneg S x) (sq_nonneg s.bandwidth))]
  apply (mul_le_mul_of_nonneg_left hB (div_nonneg (s.softFaceWeight_nonneg S x) (sq_nonneg s.bandwidth))).trans_eq
  ring

theorem cap_softFaceWeight_shift_le {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (x : Vector p) {v : Vector p} {R : ℝ} (hv : ‖v‖ ≤ R) :
    s.softFaceWeight S (x+v) ≤
      Real.exp (((2*S.card+1 : ℕ) : ℝ)*R/s.bandwidth)*s.softFaceWeight S x := by
  have hp : (∏ f ∈ S, s.pi (x+v) f) ≤ ∏ f ∈ S, (Real.exp (2*R/s.bandwidth)*s.pi x f) := by
    apply Finset.prod_le_prod
    · intro f _; exact (s.weights (x+v)).pi_nonneg f
    · intro f _; exact s.pi_shift_le x hv f
  have ht := mul_le_mul (s.F_shift_le x hv) hp
    (Finset.prod_nonneg (fun f _ => (s.weights (x+v)).pi_nonneg f))
    (mul_nonneg (Real.exp_pos _).le (s.F_pos x).le)
  apply ht.trans_eq
  simp only [Finset.prod_mul_distrib,Finset.prod_const]
  change (Real.exp (R/s.bandwidth)*s.F x)*(Real.exp (2*R/s.bandwidth)^S.card*
    (∏ f ∈ S, s.pi x f)) = _
  rw [← Real.exp_nat_mul,show (S.card : ℝ)*(2*R/s.bandwidth) = (2*S.card : ℕ)*R/s.bandwidth by push_cast; ring]
  rw [show Real.exp (R/s.bandwidth)*s.F x*(Real.exp ((2*S.card : ℕ)*R/s.bandwidth)*
      (∏ f ∈ S, s.pi x f)) =
      (Real.exp (R/s.bandwidth)*Real.exp ((2*S.card : ℕ)*R/s.bandwidth))*
        (s.F x*∏ f ∈ S, s.pi x f) by ring,← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The pair second derivative remains bounded by the weight at the common
base after a bounded copy-dependent displacement. -/
theorem capSoftFaceSecond_shift_abs_le {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (hcard : S.card ≤ 2) (x y : Vector p)
    {δ R : ℝ} (hδ : 0 ≤ δ) (hy : ‖y‖ ≤ δ) {v : Vector p} (hv : ‖v‖ ≤ R) :
    |capSoftFaceSecond s S y (x+v)| ≤
      (28*δ^2/s.bandwidth^2*Real.exp (5*R/s.bandwidth))*s.softFaceWeight S x := by
  have hR : 0 ≤ R := (norm_nonneg v).trans hv
  have hc : ((2*S.card+1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast (show 2*S.card+1≤5 by omega)
  have he : Real.exp (((2*S.card+1 : ℕ) : ℝ)*R/s.bandwidth) ≤ Real.exp (5*R/s.bandwidth) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hR) s.bandwidth_pos.le)
  calc
    _ ≤ 28*δ^2/s.bandwidth^2*s.softFaceWeight S (x+v) := capSoftFaceSecond_abs_le s S hcard (x+v) y hδ hy
    _ ≤ 28*δ^2/s.bandwidth^2*(Real.exp (((2*S.card+1 : ℕ) : ℝ)*R/s.bandwidth)*s.softFaceWeight S x) :=
      mul_le_mul_of_nonneg_left (cap_softFaceWeight_shift_le s S x hv) (by positivity)
    _ ≤ 28*δ^2/s.bandwidth^2*(Real.exp (5*R/s.bandwidth)*s.softFaceWeight S x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (s.softFaceWeight_nonneg S x)) (by positivity)
    _ = _ := by ring

end
end RectangleCLTArxivV1
