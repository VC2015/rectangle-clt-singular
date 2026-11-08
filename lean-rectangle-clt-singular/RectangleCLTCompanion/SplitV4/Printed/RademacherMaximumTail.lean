import RectangleCLTCompanion.SplitV4.Printed.RademacherMaximum

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem familyRademacher_mgf {n : ℕ} (t : ℝ) :
    mgf (familyRademacherScalarSum (n := n)) (familySignLaw n) t =
      Real.cosh (t / Real.sqrt n) ^ n := by
  have hind : iIndepFun (rademacherIncrements (n := n)) (familySignLaw n) :=
    (familyPi_iIndepFun (fun _ : Fin n => familyBernoulli familyHalf)).comp
      (fun _ b => (1 / Real.sqrt n) * familySign b) (fun _ => measurable_of_finite _)
  have hsum : (familyRademacherScalarSum (n := n)) = ∑ i : Fin n, rademacherIncrements i := by
    funext z
    simp only [Finset.sum_apply, familyRademacherScalarSum, rademacherIncrements, Finset.mul_sum]
  have hcoord (i : Fin n) : mgf (rademacherIncrements i) (familySignLaw n) t =
      Real.cosh (t / Real.sqrt n) := by
    unfold mgf rademacherIncrements
    change (∫ z : FamilySigns n, Real.exp (t * ((1 / Real.sqrt n) * familySign (z i)))
      ∂Measure.pi (fun _ : Fin n => familyBernoulli familyHalf)) = _
    rw [integral_familyBooleanPi familyHalf i (fun b => Real.exp (t * ((1 / Real.sqrt n) * familySign b))),
      integral_familyBernoulli]
    simp [familyHalf, familySign, Real.cosh_eq, div_eq_mul_inv]
    ring
  rw [hsum]
  have hh := hind.mgf_sum (fun _ => measurable_of_finite _) Finset.univ (t := t)
  rw [hh]
  simp only [hcoord, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem familyRademacher_mgf_le {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    mgf (familyRademacherScalarSum (n := n)) (familySignLaw n) t ≤ Real.exp (t ^ 2 / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sqrt_pos.mpr hn0
  rw [familyRademacher_mgf]
  calc
    _ ≤ Real.exp ((t / Real.sqrt n) ^ 2 / 2) ^ n :=
      pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) n
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [div_pow, Real.sq_sqrt hn0.le]
      field_simp
      ring

theorem familyRademacherUpperTail_subgaussian {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : 0 ≤ x) :
    familyRademacherUpperTail n x ≤ Real.exp (-x ^ 2 / 2) := by
  have hh := measure_ge_le_exp_mul_mgf (μ := familySignLaw n)
    (X := familyRademacherScalarSum) x hx
    (integrable_family_finite _ (fun z => Real.exp (x * familyRademacherScalarSum z)))
  calc
    _ ≤ (familySignLaw n).real {z | x ≤ familyRademacherScalarSum z} :=
      measureReal_mono (fun z hz => (show x < familyRademacherScalarSum z from hz).le)
    _ ≤ _ := hh
    _ ≤ Real.exp (-x * x) * Real.exp (x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (familyRademacher_mgf_le hn x) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem standardNormalUpperTail_subgaussian {x : ℝ} (hx : 0 ≤ x) :
    standardNormalUpperTail x ≤ Real.exp (-x ^ 2 / 2) := by
  have hweight : Integrable (lowerStrictTailWeight x) (gaussianReal 0 1) := by
    apply (integrable_const (1 : ℝ)).mono' (lowerStrictTailWeight_measurable x).aestronglyMeasurable
    exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (lowerStrictTailWeight_nonneg x y)]
      exact lowerStrictTailWeight_le_one hx y)
  have hi := integral_mono hweight
    (integrable_const (1 : ℝ)) (lowerStrictTailWeight_le_one hx)
  rw [← normalWeightedTail_eq_integral] at hi
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi
  exact (standardNormalUpperTail_eq_exp_mul_weighted x).le.trans
    (mul_le_of_le_one_right (Real.exp_pos _).le hi)

theorem familyRademacherMaximum_outer_error {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      2 * (m : ℝ) * Real.exp (-x ^ 2 / 2) := by
  have hu0 : 0 ≤ familyRademacherCDF n x := measureReal_nonneg
  have hu1 : familyRademacherCDF n x ≤ 1 := measureReal_le_one
  have hv0 := standardNormalCDF_nonneg x
  have hv1 := standardNormalCDF_le_one x
  have hh := probability_power_difference hu0 hu1 hv0 hv1 m
  have hscalar : |familyRademacherCDF n x - standardNormalCDF x| ≤
      2 * Real.exp (-x ^ 2 / 2) := by
    rw [familyRademacherCDF_eq_one_sub]
    have htail : 0 ≤ standardNormalUpperTail x := measureReal_nonneg
    have hRtail : 0 ≤ familyRademacherUpperTail n x := measureReal_nonneg
    have he : 1 - familyRademacherUpperTail n x - standardNormalCDF x =
        standardNormalUpperTail x - familyRademacherUpperTail n x := by
      rw [standardNormalUpperTail_eq_one_sub]
      ring
    rw [he]
    exact (abs_sub_le_iff.mpr ⟨by linarith [standardNormalUpperTail_subgaussian hx],
      by linarith [familyRademacherUpperTail_subgaussian hn hx]⟩)
  rw [familyRademacherMaximum_cdf, normalMaximumCDF]
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg m : (0 : ℝ) ≤ m)])

end
end RectangleCLT.Companion.SplitV4.Printed
