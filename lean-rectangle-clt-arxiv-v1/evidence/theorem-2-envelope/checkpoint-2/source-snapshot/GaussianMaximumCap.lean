import RectangleCLTArxivV1.GaussianWidthOrder

/-! The MGF maximum estimate with an upper bound on marginal variances,
including zero and singular Gaussian covariance matrices. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open scoped BigOperators

private theorem gaussianLaw_integral_exp_norm_le_of_diagonal_le_one {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j ≤ 1) (t : ℝ) :
    (∫ x : Vector p, Real.exp (t * ‖x‖) ∂gaussianLaw A) ≤
      (2 * (p : ℝ)) * Real.exp (t ^ 2 / 2) := by
  have hi (j : Fin p) : Integrable
      (fun x : Vector p => Real.exp (t * x j) + Real.exp (-t * x j)) (gaussianLaw A) :=
    (gaussianLaw_integrable_exp_coordinate A j t).add
      (gaussianLaw_integrable_exp_coordinate A j (-t))
  calc
    _ ≤ ∫ x : Vector p, ∑ j, (Real.exp (t * x j) + Real.exp (-t * x j)) ∂gaussianLaw A :=
      integral_mono (gaussianLaw_integrable_exp_norm hp A t)
        (integrable_finset_sum Finset.univ fun j _ => hi j)
        (fun x => exp_mul_norm_le_sum hp x t)
    _ = ∑ j : Fin p, (Real.exp (t ^ 2 * (A * A.transpose) j j / 2) +
        Real.exp (t ^ 2 * (A * A.transpose) j j / 2)) := by
      rw [integral_finset_sum Finset.univ fun j _ => hi j]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_add (gaussianLaw_integrable_exp_coordinate A j t)
        (gaussianLaw_integrable_exp_coordinate A j (-t))]
      change mgf (fun x : Vector p => x j) (gaussianLaw A) t +
        mgf (fun x : Vector p => x j) (gaussianLaw A) (-t) = _
      rw [gaussianLaw_mgf_coordinate, gaussianLaw_mgf_coordinate]
      simp only [neg_sq]
    _ ≤ ∑ _j : Fin p, (Real.exp (t ^ 2 / 2) + Real.exp (t ^ 2 / 2)) := by
      apply Finset.sum_le_sum
      intro j _
      have he : Real.exp (t ^ 2 * (A * A.transpose) j j / 2) ≤ Real.exp (t ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left (hdiag j) (sq_nonneg t)]
      exact add_le_add he he
    _ = _ := by simp; ring

private theorem gaussianMaximumMean_le_of_diagonal_le_one {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j ≤ 1) :
    gaussianMaximumMean A ≤ 2 * Real.sqrt (dimensionLog p) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ dimensionLog p := by linarith
  let t := Real.sqrt (dimensionLog p)
  have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
  have ht2 : t ^ 2 = dimensionLog p := Real.sq_sqrt hL0
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hcard : 2 * (p : ℝ) ≤ Real.exp (dimensionLog p) := by
    rw [dimensionLog, Real.exp_log (mul_pos (Real.exp_pos _) hpR)]
    exact mul_le_mul_of_nonneg_right htwo hpR.le
  have hj := exp_integral_le_integral_exp
    ((gaussianLaw_integrable_norm A).const_mul t)
    (gaussianLaw_integrable_exp_norm hp A t)
  rw [integral_const_mul] at hj
  have he : Real.exp (t * (∫ x : Vector p, ‖x‖ ∂gaussianLaw A)) ≤
      Real.exp (2 * dimensionLog p) := by
    calc
      _ ≤ ∫ x : Vector p, Real.exp (t * ‖x‖) ∂gaussianLaw A := hj
      _ ≤ (2 * (p : ℝ)) * Real.exp (t ^ 2 / 2) :=
        gaussianLaw_integral_exp_norm_le_of_diagonal_le_one hp A hdiag t
      _ ≤ Real.exp (dimensionLog p) * Real.exp (dimensionLog p) := by
        apply mul_le_mul hcard
        · exact Real.exp_le_exp.mpr (by rw [ht2]; linarith)
        · exact Real.exp_nonneg _
        · exact Real.exp_nonneg _
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlog := Real.exp_le_exp.mp he
  change (∫ x : Vector p, ‖x‖ ∂gaussianLaw A) ≤ 2 * t
  nlinarith

/-- Upper marginal variances alone bound the actual Gaussian width. -/
theorem gaussianMaximumMean_le_of_diagonal_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j ≤ v) :
    gaussianMaximumMean A ≤ 2 * Real.sqrt (v * dimensionLog p) := by
  by_cases hv0 : v = 0
  · have hA : A = 0 := by
      ext j k
      have hs : (∑ l, A j l ^ 2) ≤ 0 := by
        simpa only [hv0, Matrix.mul_apply, Matrix.transpose_apply, ← pow_two] using hdiag j
      have hk : A j k ^ 2 ≤ 0 := (Finset.single_le_sum
        (fun l _ => sq_nonneg (A j l)) (Finset.mem_univ k)).trans hs
      simpa only [Matrix.zero_apply] using (sq_eq_zero_iff.mp (le_antisymm hk (sq_nonneg _)))
    have hz : gaussianMaximumMean (0 : Matrix (Fin p) (Fin p) ℝ) = 0 := by
      simpa only [zero_smul, abs_zero, zero_mul] using gaussianMaximumMean_smul 0 A
    simp only [hv0, hA, hz, zero_mul, Real.sqrt_zero, mul_zero, le_refl]
  · have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    let B := Real.sqrt (1 / v) • A
    have hunit (j : Fin p) : (B * B.transpose) j j ≤ 1 := by
      dsimp [B]
      rw [sqrt_smul_factor_gram _ (by positivity)]
      simp only [Matrix.smul_apply, smul_eq_mul]
      have hh : (A * A.transpose) j j / v ≤ 1 :=
        (div_le_iff₀ hvp).mpr (by simpa only [one_mul] using hdiag j)
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hh
    have hb := gaussianMaximumMean_le_of_diagonal_le_one hp B hunit
    dsimp only [B] at hb
    rw [gaussianMaximumMean_smul, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one] at hb
    have he : gaussianMaximumMean A / Real.sqrt v ≤ 2 * Real.sqrt (dimensionLog p) := by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hb
    have hh := (div_le_iff₀ (Real.sqrt_pos.mpr hvp)).mp he
    rw [Real.sqrt_mul hv]
    nlinarith

end RectangleCLTArxivV1
