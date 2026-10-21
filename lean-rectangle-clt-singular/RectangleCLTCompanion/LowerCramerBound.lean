import RectangleCLTCompanion.LowerLogEsscherTail
import RectangleCLTCompanion.LowerInverseTilt

/-! A proved moderate-tail estimate for the actual skewed two-point
construction. In particular, no relative-tail estimate is a hypothesis. -/

open MeasureTheory ProbabilityTheory Set

namespace RectangleCLT.Companion

noncomputable section

def lowerCramerSmallConstant : ℝ := 100 * Real.exp 4 + 4 * lowerRelativeTailConstant

def lowerCramerRemainderConstant : ℝ :=
  lowerInverseRemainderConstant + 4 * lowerRelativeTailConstant + 32 * Real.exp 4

theorem lowerCramerSmallConstant_pos : 0 < lowerCramerSmallConstant := by
  unfold lowerCramerSmallConstant
  have hK := lowerRelativeTailConstant_pos
  positivity

theorem lowerCramerRemainderConstant_pos : 0 < lowerCramerRemainderConstant := by
  unfold lowerCramerRemainderConstant
  have hC := lowerInverseRemainderConstant_pos
  have hK := lowerRelativeTailConstant_pos
  positivity

theorem lowerTiltRoot_tailParameter_geometry {B u t : ℝ} (hB : 1 ≤ B) (hu : 0 < u)
    (hsmall : 100 * Real.exp 4 * (B * u) ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) (2*u)) (hroot : lowerTiltMean B t = u)
    {n : ℕ} (hn : 1 ≤ n) :
    (Real.sqrt n * u) / 2 ≤ lowerTiltedTailParameter B t n ∧
      |lowerTiltedTailParameter B t n - Real.sqrt n * u| /
        min (lowerTiltedTailParameter B t n) (Real.sqrt n * u) ≤ 32 * Real.exp 4 * (B * u) := by
  have hBp : 0 < B := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt := Real.sqrt_pos.mpr hnpos
  have hx : 0 < Real.sqrt n * u := mul_pos hsqrt hu
  have hdiff := mul_le_mul_of_nonneg_left
    (lowerTiltMean_root_sqrtVariance hB hu.le hsmall ht hroot) hsqrt.le
  have hdiff' : |lowerTiltedTailParameter B t n - Real.sqrt n * u| ≤
      (16 * Real.exp 4 * (B * u)) * (Real.sqrt n * u) := by
    calc
      _ = Real.sqrt n * |t * Real.sqrt (lowerTiltVariance B t) - u| := by
        have hh : lowerTiltedTailParameter B t n - Real.sqrt n * u =
            Real.sqrt n * (t * Real.sqrt (lowerTiltVariance B t) - u) := by
          unfold lowerTiltedTailParameter
          ring
        rw [hh, abs_mul, abs_of_pos hsqrt]
      _ ≤ Real.sqrt n * (16 * Real.exp 4 * B * u ^ 2) := hdiff
      _ = _ := by ring
  have hcoef : 16 * Real.exp 4 * (B * u) ≤ 1 / 2 := by
    have hBu : 0 ≤ B*u := mul_nonneg hBp.le hu.le
    nlinarith
  have hslow : (Real.sqrt n * u) / 2 ≤ lowerTiltedTailParameter B t n := by
    have hh := (abs_le.mp hdiff').1
    have hm := mul_le_mul_of_nonneg_right hcoef hx.le
    linarith
  refine ⟨hslow, ?_⟩
  have hmin : (Real.sqrt n * u) / 2 ≤
      min (lowerTiltedTailParameter B t n) (Real.sqrt n * u) :=
    le_min hslow (by linarith)
  apply (div_le_iff₀ ((half_pos hx).trans_le hmin)).mpr
  calc
    _ ≤ (16 * Real.exp 4 * (B * u)) * (Real.sqrt n * u) := hdiff'
    _ = (32 * Real.exp 4 * (B * u)) * ((Real.sqrt n * u) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmin (by positivity)

/-- The exact cubic coefficient is `n(B-B⁻¹)u³/6`; the explicit
remainder has the two scales `Bu` and `nB²u⁴`. -/
theorem lowerTwoPoint_cramer_bound {B u : ℝ} (hB : 1 ≤ B) (hu : 0 < u)
    {n : ℕ} (hn : 1 ≤ n) (hx : 2 ≤ Real.sqrt n * u)
    (hsmall : lowerCramerSmallConstant * (B * u) ≤ 1) :
    |Real.log ((lowerScalarArrayLaw B n).real
        {z | n * u < lowerScalarSum z} / standardNormalUpperTail (Real.sqrt n * u)) -
      n * (B - B⁻¹) * u ^ 3 / 6| ≤
        lowerCramerRemainderConstant * (B * u + n * B ^ 2 * u ^ 4) := by
  have hBp : 0 < B := by linarith
  have hBu : 0 ≤ B*u := mul_nonneg hBp.le hu.le
  have hK := lowerRelativeTailConstant_pos
  have hsmall' : 100 * Real.exp 4 * (B*u) ≤ 1 := by
    unfold lowerCramerSmallConstant at hsmall
    nlinarith [mul_nonneg hK.le hBu]
  have hsmallK : 4 * lowerRelativeTailConstant * (B*u) ≤ 1 := by
    unfold lowerCramerSmallConstant at hsmall
    nlinarith [mul_nonneg (Real.exp_pos (4 : ℝ)).le hBu]
  let t := lowerInverseTilt B u
  have hspec := lowerInverseTilt_spec hB hu.le hsmall'
  have ht := hspec.1
  have hroot := hspec.2
  have htpos := lowerTiltMean_root_pos hB hu ht.1 hroot
  have hgeom := lowerTiltRoot_tailParameter_geometry hB hu hsmall' ht hroot hn
  have hs : 1 ≤ lowerTiltedTailParameter B t n := by linarith [hgeom.1]
  have hBEsmall : lowerRelativeTailConstant * (B*t) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hK.le hBp.le)
    nlinarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hxpos : 0 < Real.sqrt n*u := by linarith
  have htail := lower_log_esscher_tail_error hB hn htpos hxpos hs hBEsmall
  rw [hroot] at htail
  have htail' : |Real.log ((lowerScalarArrayLaw B n).real {z | n*u < lowerScalarSum z} /
      standardNormalUpperTail (Real.sqrt n*u)) -
      (n * cgf id (lowerTwoPointLaw B) t - t*(n*u) + (Real.sqrt n*u)^2/2)| ≤
      (4 * lowerRelativeTailConstant + 32 * Real.exp 4) * (B*u) := by
    have hh := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ 2*lowerRelativeTailConstant*B)
    exact htail.trans (by nlinarith [hgeom.2])
  have hleg := mul_le_mul_of_nonneg_left
    (lowerTiltMean_root_cgf hB hu.le hsmall' ht hroot) hnpos.le
  have hx2 : (Real.sqrt n*u)^2 = n*u^2 := by rw [mul_pow, Real.sq_sqrt hnpos.le]
  have hleg' : |(n * cgf id (lowerTwoPointLaw B) t - t*(n*u) +
      (Real.sqrt n*u)^2/2) - n*(B-B⁻¹)*u^3/6| ≤
      lowerInverseRemainderConstant * (n*B^2*u^4) := by
    have hid : (n * cgf id (lowerTwoPointLaw B) t - t*(n*u) +
        (Real.sqrt n*u)^2/2) - n*(B-B⁻¹)*u^3/6 =
        n * (cgf id (lowerTwoPointLaw B) t - t*u + u^2/2 - (B-B⁻¹)*u^3/6) := by
      rw [hx2]
      ring
    rw [hid, abs_mul, abs_of_pos hnpos]
    exact hleg.trans_eq (by ring)
  have hsum := (abs_add
    (Real.log ((lowerScalarArrayLaw B n).real {z | n*u < lowerScalarSum z} /
      standardNormalUpperTail (Real.sqrt n*u)) -
      (n * cgf id (lowerTwoPointLaw B) t - t*(n*u) + (Real.sqrt n*u)^2/2))
    ((n * cgf id (lowerTwoPointLaw B) t - t*(n*u) + (Real.sqrt n*u)^2/2) -
      n*(B-B⁻¹)*u^3/6)).trans (add_le_add htail' hleg')
  have hsum' : |Real.log ((lowerScalarArrayLaw B n).real {z | n*u < lowerScalarSum z} /
      standardNormalUpperTail (Real.sqrt n*u)) - n*(B-B⁻¹)*u^3/6| ≤
      (4*lowerRelativeTailConstant+32*Real.exp 4)*(B*u) +
        lowerInverseRemainderConstant*(n*B^2*u^4) := by
    convert hsum using 1 <;> congr 1 <;> ring
  apply hsum'.trans
  unfold lowerCramerRemainderConstant
  have hL := lowerInverseRemainderConstant_pos
  have hquartic : 0 ≤ (n : ℝ)*B^2*u^4 := by positivity
  nlinarith [mul_nonneg hL.le hBu,
    mul_nonneg (by positivity : 0 ≤ 4*lowerRelativeTailConstant+32*Real.exp 4) hquartic]

theorem lowerTwoPoint_cramer_tail_pos {B u : ℝ} (hB : 1 ≤ B) (hu : 0 < u)
    {n : ℕ} (hn : 1 ≤ n) (hx : 2 ≤ Real.sqrt n * u)
    (hsmall : lowerCramerSmallConstant * (B * u) ≤ 1) :
    0 < (lowerScalarArrayLaw B n).real {z | n * u < lowerScalarSum z} := by
  have hBp : 0 < B := by linarith
  have hBu : 0 ≤ B*u := mul_nonneg hBp.le hu.le
  have hK := lowerRelativeTailConstant_pos
  have hsmall' : 100 * Real.exp 4 * (B*u) ≤ 1 := by
    unfold lowerCramerSmallConstant at hsmall
    nlinarith [mul_nonneg hK.le hBu]
  have hsmallK : 4 * lowerRelativeTailConstant * (B*u) ≤ 1 := by
    unfold lowerCramerSmallConstant at hsmall
    nlinarith [mul_nonneg (Real.exp_pos (4 : ℝ)).le hBu]
  let t := lowerInverseTilt B u
  have hspec := lowerInverseTilt_spec hB hu.le hsmall'
  have ht := hspec.1
  have hroot := hspec.2
  have htpos := lowerTiltMean_root_pos hB hu ht.1 hroot
  have hgeom := lowerTiltRoot_tailParameter_geometry hB hu hsmall' ht hroot hn
  have hs : 1 ≤ lowerTiltedTailParameter B t n := by linarith [hgeom.1]
  have hBEsmall : lowerRelativeTailConstant * (B*t) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left ht.2 (mul_nonneg hK.le hBp.le)
    nlinarith
  have hE := (lowerTiltedTailExpectation_log_error hB hn htpos hs hBEsmall).1
  have hq := lowerScalarArrayLaw_strict_tail_standardized hB t hn
  rw [hroot] at hq
  rw [hq]
  exact mul_pos (Real.exp_pos _) hE

end

end RectangleCLT.Companion
