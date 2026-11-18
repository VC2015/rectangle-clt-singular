import RectangleCLTArxivV1.LowerSparseWidthScales
import RectangleCLTCompanion.SplitV4.Printed.PolynomialRegimes

/-! The coordinate fourth-moment term is negligible in the stated sparse regime. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lowerSparse_width_rate_le_twice_of_coordinate {n p : ℕ} {q B g : ℝ}
    (hp : 1 ≤ p) (hg : 0 ≤ g)
    (hcoord : polynomialCoordinateRate n p B ≤ polynomialSparseRate n p B q) :
    polynomialFourthWidthRate n p B q g ≤ 2*lowerSparseIntrinsicRate n (dimensionLog p) q B g := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hC : Real.sqrt (dimensionLog p)*(B^(1/2 : ℝ)*dimensionLog p^(3/4 : ℝ)/(n : ℝ)^(1/4 : ℝ)) =
      polynomialCoordinateRate n p B := by
    unfold polynomialCoordinateRate
    rw [Real.sqrt_eq_rpow]
    have he : dimensionLog p^(1/2 : ℝ)*dimensionLog p^(3/4 : ℝ) = dimensionLog p^(5/4 : ℝ) := by
      rw [← Real.rpow_add hL]
      norm_num
    calc
      _ = B^(1/2 : ℝ)*(dimensionLog p^(1/2 : ℝ)*dimensionLog p^(3/4 : ℝ))/(n : ℝ)^(1/4 : ℝ) := by ring
      _ = _ := by rw [he]
  have hS : Real.sqrt (dimensionLog p)*(B*dimensionLog p^(1-1/q)/
      ((n : ℝ)^(1/2-1/q)*Real.log (Real.exp 1+lowerSparseIntrinsicK n (dimensionLog p) q B)^(1-1/q))) =
      polynomialSparseRate n p B q := by
    unfold polynomialSparseRate polynomialSparseParameter lowerSparseIntrinsicK
    rw [Real.sqrt_eq_rpow]
    have he : dimensionLog p^(1/2 : ℝ)*dimensionLog p^(1-1/q) = dimensionLog p^(3/2-1/q) := by
      rw [← Real.rpow_add hL]
      congr 1
      ring
    calc
      _ = B*(dimensionLog p^(1/2 : ℝ)*dimensionLog p^(1-1/q))/
        ((n : ℝ)^(1/2-1/q)*Real.log (Real.exp 1+B*((n : ℝ)/dimensionLog p)^(2/q-1/2))^(1-1/q)) := by ring
      _ = _ := by rw [he]
  have hnew := (mul_le_mul_left (Real.sqrt_pos.mpr hL)).mp (show
      Real.sqrt (dimensionLog p)*(B^(1/2 : ℝ)*dimensionLog p^(3/4 : ℝ)/(n : ℝ)^(1/4 : ℝ)) ≤
      Real.sqrt (dimensionLog p)*(B*dimensionLog p^(1-1/q)/
        ((n : ℝ)^(1/2-1/q)*Real.log (Real.exp 1+lowerSparseIntrinsicK n (dimensionLog p) q B)^(1-1/q))) from by
    rw [hC,hS]
    exact hcoord)
  have hh := mul_le_mul_of_nonneg_left (add_le_add_right hnew
    (B*dimensionLog p^(1-1/q)/((n : ℝ)^(1/2-1/q)*
      Real.log (Real.exp 1+lowerSparseIntrinsicK n (dimensionLog p) q B)^(1-1/q)))) hg
  unfold polynomialFourthWidthRate lowerSparseIntrinsicRate lowerSparseIntrinsicK at *
  convert hh using 1 <;> ring

theorem eventually_lowerSparse_width_rate_le_twice {q : ℝ} {B g : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : ∀ n, 1 ≤ p n) (hg : ∀ n, 0 ≤ g n)
    (hK : Tendsto (fun n => lowerSparseIntrinsicK n (dimensionLog (p n)) q (B n)) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, polynomialFourthWidthRate n (p n) (B n) q (g n) ≤
      2*lowerSparseIntrinsicRate n (dimensionLog (p n)) q (B n) (g n) := by
  have hratio := Printed.sqrt_div_bennett_log_tendsto_atTop (1-1/q) hK
  filter_upwards [hratio.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1] with n hnRatio hn
  have hBpos : 0 < B n := by linarith [hB n]
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < dimensionLog (p n) := zero_lt_one.trans_le (log_exp_mul_nat_ge_one (hp n))
  have hCoordpos : 0 < polynomialCoordinateRate n (p n) (B n) := by
    unfold polynomialCoordinateRate
    positivity
  have he := Printed.polynomialSparseRate_div_coordinateRate hn (hp n) (q := q) hBpos
  have hratio' : 1 ≤ polynomialSparseRate n (p n) (B n) q/polynomialCoordinateRate n (p n) (B n) := by
    rw [he]
    exact hnRatio
  exact lowerSparse_width_rate_le_twice_of_coordinate (hp n) (hg n) ((one_le_div hCoordpos).mp hratio')

end
end RectangleCLTArxivV1
