import RectangleCLT.GaussianMoments
import RectangleCLT.Optimization

/-! Exponential moments and the expected maximum coordinate of the concrete
Gaussian pushforward law. No nonsingularity hypothesis is needed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal

namespace RectangleCLT

theorem standardGaussian_mgf_coordinate (p : ℕ) (j : Fin p) (t : ℝ) :
    mgf (fun x : Vector p => x j) (standardGaussian p) t = Real.exp (t ^ 2 / 2) := by
  rw [← mgf_id_map (measurable_pi_apply j).aemeasurable,
    standardGaussian_map_eval, standardRealGaussian_mgf]

theorem standardGaussian_mgf_mulVec_coordinate {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) (t : ℝ) :
    mgf (fun x : Vector p => A.mulVec x j) (standardGaussian p) t =
      Real.exp (t ^ 2 * (A * A.transpose) j j / 2) := by
  classical
  have hind : iIndepFun (fun i (x : Vector p) => A j i * x i)
      (standardGaussian p) :=
    (standardGaussian_iIndepFun p).comp (fun i u => A j i * u)
      (fun i => measurable_const.mul measurable_id)
  have hmeas (i : Fin p) : Measurable (fun x : Vector p => A j i * x i) :=
    measurable_const.mul (measurable_pi_apply i)
  have hfun : (fun x : Vector p => A.mulVec x j) =
      ∑ i ∈ Finset.univ, fun x : Vector p => A j i * x i := by
    funext x
    simp [Matrix.mulVec, dotProduct]
  rw [hfun]
  rw [hind.mgf_sum hmeas]
  have hscalar (i : Fin p) :
      mgf (fun x : Vector p => A j i * x i) (standardGaussian p) t =
        Real.exp ((A j i * t) ^ 2 / 2) := by
    change mgf ((A j i) • (fun x : Vector p => x i)) (standardGaussian p) t = _
    rw [mgf_smul_left, standardGaussian_mgf_coordinate]
  simp_rw [hscalar]
  rw [← Real.exp_sum]
  congr 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gaussianLaw_mgf_coordinate {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) (t : ℝ) :
    mgf (fun x : Vector p => x j) (gaussianLaw A) t =
      Real.exp (t ^ 2 * (A * A.transpose) j j / 2) := by
  change (∫ x : Vector p, Real.exp (t * x j) ∂(standardGaussian p).map A.mulVec) = _
  rw [integral_map (measurable_mulVec A).aemeasurable
    ((measurable_pi_apply j).const_mul t).exp.aestronglyMeasurable]
  exact standardGaussian_mgf_mulVec_coordinate A j t

theorem gaussianLaw_integrable_exp_coordinate {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) (t : ℝ) :
    Integrable (fun x : Vector p => Real.exp (t * x j)) (gaussianLaw A) := by
  exact mgf_pos_iff.mp (by rw [gaussianLaw_mgf_coordinate]; positivity)

theorem norm_le_sum_abs_coordinate {p : ℕ} (x : Vector p) :
    ‖x‖ ≤ ∑ j, |x j| := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg (x j))).mpr
  intro j
  simpa only [Real.norm_eq_abs] using
    Finset.single_le_sum (fun i _ => abs_nonneg (x i)) (Finset.mem_univ j)

theorem gaussianLaw_integrable_norm {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun x : Vector p => ‖x‖) (gaussianLaw A) := by
  have hi := integrable_finset_sum Finset.univ
    (fun j _ => (gaussianLaw_integrable_coordinate A j).norm)
  apply hi.mono' measurable_norm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs, abs_norm] using norm_le_sum_abs_coordinate x

/-- Pointwise exponential domination by the two signed coordinate lists. -/
theorem exp_mul_norm_le_sum {p : ℕ} (hp : 1 ≤ p) (x : Vector p) (t : ℝ) :
    Real.exp (t * ‖x‖) ≤ ∑ j, (Real.exp (t * x j) + Real.exp (-t * x j)) := by
  classical
  have hn : (Finset.univ : Finset (Fin p)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => |x j|) hn
  have hnorm : ‖x‖ = |x j| := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i =>
        by simpa only [Real.norm_eq_abs] using hmax i (Finset.mem_univ i)
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  rw [hnorm]
  have hcoord : Real.exp (t * |x j|) ≤
      Real.exp (t * x j) + Real.exp (-t * x j) := by
    by_cases hx : 0 ≤ x j
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge hx), mul_neg, ← neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  exact hcoord.trans (Finset.single_le_sum
    (fun i _ => add_nonneg (Real.exp_nonneg (t * x i)) (Real.exp_nonneg (-t * x i))) hj)

theorem gaussianLaw_integrable_exp_norm {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) :
    Integrable (fun x : Vector p => Real.exp (t * ‖x‖)) (gaussianLaw A) := by
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    (gaussianLaw_integrable_exp_coordinate A j t).add
      (gaussianLaw_integrable_exp_coordinate A j (-t)))
  apply hi.mono' (measurable_norm.const_mul t).exp.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_mul_norm_le_sum hp x t

theorem gaussianLaw_integral_exp_norm_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (t : ℝ) :
    (∫ x : Vector p, Real.exp (t * ‖x‖) ∂gaussianLaw A) ≤
      (2 * (p : ℝ)) * Real.exp (t ^ 2 / 2) := by
  have hi (j : Fin p) : Integrable
      (fun x : Vector p => Real.exp (t * x j) + Real.exp (-t * x j)) (gaussianLaw A) :=
    (gaussianLaw_integrable_exp_coordinate A j t).add
      (gaussianLaw_integrable_exp_coordinate A j (-t))
  calc
    _ ≤ ∫ x : Vector p, ∑ j, (Real.exp (t * x j) + Real.exp (-t * x j))
        ∂gaussianLaw A :=
      integral_mono (gaussianLaw_integrable_exp_norm hp A t)
        (integrable_finset_sum Finset.univ fun j _ => hi j)
        (fun x => exp_mul_norm_le_sum hp x t)
    _ = ∑ j : Fin p, (Real.exp (t ^ 2 / 2) + Real.exp (t ^ 2 / 2)) := by
      rw [integral_finset_sum Finset.univ fun j _ => hi j]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_add (gaussianLaw_integrable_exp_coordinate A j t)
        (gaussianLaw_integrable_exp_coordinate A j (-t))]
      change mgf (fun x : Vector p => x j) (gaussianLaw A) t +
        mgf (fun x : Vector p => x j) (gaussianLaw A) (-t) = _
      rw [gaussianLaw_mgf_coordinate, gaussianLaw_mgf_coordinate, hdiag]
      simp only [mul_one, neg_sq]
    _ = _ := by simp; ring

/-- Jensen's exponential inequality from the supporting tangent line. -/
theorem exp_integral_le_integral_exp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hexp : Integrable (fun x => Real.exp (f x)) μ) :
    Real.exp (∫ x, f x ∂μ) ≤ ∫ x, Real.exp (f x) ∂μ := by
  let m := ∫ x, f x ∂μ
  have hsub : Integrable (fun x => f x - m) μ := hf.sub (integrable_const m)
  have hi : Integrable (fun x => Real.exp m * (1 + (f x - m))) μ :=
    ((integrable_const (1 : ℝ)).add hsub).const_mul _
  have hpoint (x : Ω) : Real.exp m * (1 + (f x - m)) ≤ Real.exp (f x) := by
    calc
      _ ≤ Real.exp m * Real.exp (f x - m) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (f x - m)])
          (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hh := integral_mono hi hexp hpoint
  simpa only [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hsub,
    integral_sub hf (integrable_const m), integral_const, measureReal_univ_eq_one,
    one_smul, m, sub_self, add_zero, mul_one] using hh

/-- A dimension-dependent expected maximum bound for the actual Gaussian
law. Unit coordinate variances suffice; its covariance may be singular. -/
theorem gaussianLaw_integral_norm_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) :
    (∫ x : Vector p, ‖x‖ ∂gaussianLaw A) ≤ 2 * Real.sqrt (dimensionLog p) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ dimensionLog p := by linarith
  let t := Real.sqrt (dimensionLog p)
  have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
  have ht2 : t ^ 2 = dimensionLog p := Real.sq_sqrt hL0
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    norm_num at hh ⊢
    exact hh
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
        gaussianLaw_integral_exp_norm_le hp A hdiag t
      _ ≤ Real.exp (dimensionLog p) * Real.exp (dimensionLog p) := by
        apply mul_le_mul hcard
        · exact Real.exp_le_exp.mpr (by rw [ht2]; linarith)
        · exact Real.exp_nonneg _
        · exact Real.exp_nonneg _
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hlog := Real.exp_le_exp.mp he
  change (∫ x : Vector p, ‖x‖ ∂gaussianLaw A) ≤ 2 * t
  nlinarith

end RectangleCLT
