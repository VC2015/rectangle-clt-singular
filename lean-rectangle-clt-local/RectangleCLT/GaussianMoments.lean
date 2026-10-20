import RectangleCLT.Statement
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Integration

/-! Actual moments of the concrete Gaussian laws used by this project.
The covariance conclusion will not require an invertible Gaussian factor. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal

namespace RectangleCLT

theorem standardRealGaussian_mgf (t : ℝ) :
    mgf id (gaussianReal 0 1) t = Real.exp (t ^ 2 / 2) := by
  simpa using mgf_gaussianReal (p := gaussianReal 0 1) (X := id)
    (μ := 0) (v := 1) (by simp) t

theorem standardRealGaussian_integrableExpSet :
    integrableExpSet id (gaussianReal 0 1) = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  exact mgf_pos_iff.mp (by rw [standardRealGaussian_mgf]; positivity)

private theorem standardRealGaussian_mem_interior (t : ℝ) :
    t ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
  rw [standardRealGaussian_integrableExpSet, interior_univ]
  trivial

theorem standardRealGaussian_integrable_pow (m : ℕ) :
    Integrable (fun x : ℝ => x ^ m) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet
    (standardRealGaussian_mem_interior 0) m

theorem standardRealGaussian_memLp (q : ℝ≥0) :
    MemLp (id : ℝ → ℝ) q (gaussianReal 0 1) :=
  memLp_of_mem_interior_integrableExpSet (standardRealGaussian_mem_interior 0) q

private theorem hasDerivAt_standardRealGaussian_mgf (t : ℝ) :
    HasDerivAt (mgf id (gaussianReal 0 1)) (t * Real.exp (t ^ 2 / 2)) t := by
  rw [show mgf id (gaussianReal 0 1) = (fun t => Real.exp (t ^ 2 / 2)) from
    funext standardRealGaussian_mgf]
  convert ((((hasDerivAt_id t).pow 2).div_const 2).exp) using 1
  dsimp
  ring

theorem standardRealGaussian_integral :
    (∫ x : ℝ, x ∂gaussianReal 0 1) = 0 := by
  have hmoment := hasDerivAt_mgf (standardRealGaussian_mem_interior 0)
  have hunique := (hasDerivAt_standardRealGaussian_mgf 0).unique hmoment
  simpa using hunique.symm

theorem standardRealGaussian_integral_sq :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  have hderiv : deriv (mgf id (gaussianReal 0 1)) =
      (fun t => t * Real.exp (t ^ 2 / 2)) :=
    funext (fun t => (hasDerivAt_standardRealGaussian_mgf t).deriv)
  have hmoment := iteratedDeriv_mgf_zero (standardRealGaussian_mem_interior 0) 2
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv] at hmoment
  have hd : HasDerivAt (fun t : ℝ => t * Real.exp (t ^ 2 / 2)) 1 0 := by
    convert (hasDerivAt_id (0 : ℝ)).mul
      ((((hasDerivAt_id (0 : ℝ)).pow 2).div_const 2).exp) using 1
    norm_num
  rw [hd.deriv] at hmoment
  simpa using hmoment.symm

/-- Each coordinate of the product law has the specified scalar normal law. -/
theorem standardGaussian_map_eval (p : ℕ) (j : Fin p) :
    (standardGaussian p).map (fun x => x j) = gaussianReal 0 1 := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply j) hs]
  have hset : (fun x : Vector p => x j) ⁻¹' s =
      Set.pi Set.univ (fun i => if i = j then s else Set.univ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hx i
      by_cases hi : i = j
      · subst i; simpa using hx
      · simp [hi]
    · intro hx
      simpa using hx j
  rw [hset]
  change Measure.pi (fun _ : Fin p => gaussianReal 0 1) _ = _
  rw [Measure.pi_pi]
  simp [apply_ite, measure_univ]

theorem standardGaussian_integrable_coordinate_pow (p : ℕ) (j : Fin p) (m : ℕ) :
    Integrable (fun x : Vector p => x j ^ m) (standardGaussian p) := by
  have hscalar : Integrable (fun t : ℝ => t ^ m)
      ((standardGaussian p).map (fun x => x j)) := by
    rw [standardGaussian_map_eval]
    exact standardRealGaussian_integrable_pow m
  exact (integrable_map_measure
    (measurable_id.pow_const m).aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable).mp hscalar

theorem standardGaussian_memLp_coordinate (p : ℕ) (j : Fin p) (q : ℝ≥0) :
    MemLp (fun x : Vector p => x j) q (standardGaussian p) := by
  have hscalar : MemLp (id : ℝ → ℝ) q
      ((standardGaussian p).map (fun x => x j)) := by
    rw [standardGaussian_map_eval]
    exact standardRealGaussian_memLp q
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (measurable_pi_apply j).aemeasurable).mp hscalar

theorem standardGaussian_integrable_coordinate (p : ℕ) (j : Fin p) :
    Integrable (fun x : Vector p => x j) (standardGaussian p) := by
  simpa only [pow_one] using standardGaussian_integrable_coordinate_pow p j 1

theorem standardGaussian_integral_coordinate (p : ℕ) (j : Fin p) :
    (∫ x : Vector p, x j ∂standardGaussian p) = 0 := by
  have hmap := integral_map (μ := standardGaussian p) (measurable_pi_apply j).aemeasurable
    (f := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable
  rw [standardGaussian_map_eval] at hmap
  exact hmap.symm.trans standardRealGaussian_integral

theorem standardGaussian_integral_coordinate_sq (p : ℕ) (j : Fin p) :
    (∫ x : Vector p, x j ^ 2 ∂standardGaussian p) = 1 := by
  have hmap := integral_map (μ := standardGaussian p)
    (measurable_pi_apply j).aemeasurable
    (f := fun t : ℝ => t ^ 2) (measurable_id.pow_const 2).aestronglyMeasurable
  rw [standardGaussian_map_eval] at hmap
  exact hmap.symm.trans standardRealGaussian_integral_sq

/-- Independence here concerns coordinates of the product Gaussian itself. -/
theorem standardGaussian_iIndepFun (p : ℕ) :
    iIndepFun (fun j (x : Vector p) => x j) (standardGaussian p) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_pi_apply j).aemeasurable)).mpr
  change (standardGaussian p).map id = _
  rw [Measure.map_id]
  simp only [standardGaussian_map_eval]
  rfl

theorem standardGaussian_integrable_coordinate_product (p : ℕ) (j k : Fin p) :
    Integrable (fun x : Vector p => x j * x k) (standardGaussian p) := by
  haveI : ENNReal.HolderTriple (2 : ENNReal) 2 1 :=
    ⟨by simpa only [inv_one] using ENNReal.inv_two_add_inv_two⟩
  have hj : MemLp (fun x : Vector p => x j) (2 : ENNReal) (standardGaussian p) := by
    simpa using standardGaussian_memLp_coordinate p j 2
  have hk : MemLp (fun x : Vector p => x k) (2 : ENNReal) (standardGaussian p) := by
    simpa using standardGaussian_memLp_coordinate p k 2
  exact hj.integrable_mul hk

/-- The actual cross moments of the product Gaussian, including its diagonal. -/
theorem standardGaussian_integral_coordinate_product (p : ℕ) (j k : Fin p) :
    (∫ x : Vector p, x j * x k ∂standardGaussian p) = if j = k then 1 else 0 := by
  classical
  by_cases hjk : j = k
  · subst k
    simpa only [if_true, sq] using standardGaussian_integral_coordinate_sq p j
  · rw [if_neg hjk]
    have hi := (standardGaussian_iIndepFun p).indepFun hjk
    calc
      _ = (∫ x : Vector p, x j ∂standardGaussian p) *
          (∫ x : Vector p, x k ∂standardGaussian p) :=
        hi.integral_mul_of_integrable (standardGaussian_integrable_coordinate p j)
          (standardGaussian_integrable_coordinate p k)
      _ = 0 := by rw [standardGaussian_integral_coordinate, zero_mul]

/-- Finite linear combinations of Gaussian coordinates have every finite
`L^q` moment, without any rank condition on the matrix. -/
theorem standardGaussian_memLp_mulVec_coordinate {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) (q : ℝ≥0) :
    MemLp (fun x : Vector p => A.mulVec x j) q (standardGaussian p) := by
  change MemLp (fun x : Vector p => ∑ i, A j i * x i) q (standardGaussian p)
  exact memLp_finset_sum Finset.univ
    (fun i _ => (standardGaussian_memLp_coordinate p i q).const_mul (A j i))

theorem standardGaussian_integrable_mulVec_coordinate {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    Integrable (fun x : Vector p => A.mulVec x j) (standardGaussian p) := by
  change Integrable (fun x : Vector p => ∑ i, A j i * x i) (standardGaussian p)
  exact integrable_finset_sum Finset.univ
    (fun i _ => (standardGaussian_integrable_coordinate p i).const_mul (A j i))

theorem standardGaussian_integrable_mulVec_product {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) :
    Integrable (fun x : Vector p => A.mulVec x j * A.mulVec x k)
      (standardGaussian p) := by
  haveI : ENNReal.HolderTriple (2 : ENNReal) 2 1 :=
    ⟨by simpa only [inv_one] using ENNReal.inv_two_add_inv_two⟩
  have hj : MemLp (fun x : Vector p => A.mulVec x j) (2 : ENNReal)
      (standardGaussian p) := by
    simpa using standardGaussian_memLp_mulVec_coordinate A j 2
  have hk : MemLp (fun x : Vector p => A.mulVec x k) (2 : ENNReal)
      (standardGaussian p) := by
    simpa using standardGaussian_memLp_mulVec_coordinate A k 2
  exact hj.integrable_mul hk

theorem standardGaussian_integral_mulVec_coordinate {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    (∫ x : Vector p, A.mulVec x j ∂standardGaussian p) = 0 := by
  change (∫ x : Vector p, ∑ i, A j i * x i ∂standardGaussian p) = 0
  rw [integral_finset_sum Finset.univ
    (fun i _ => (standardGaussian_integrable_coordinate p i).const_mul (A j i))]
  simp only [integral_const_mul, standardGaussian_integral_coordinate, mul_zero,
    Finset.sum_const_zero]

theorem standardGaussian_integral_mulVec_product {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) :
    (∫ x : Vector p, A.mulVec x j * A.mulVec x k ∂standardGaussian p) =
      (A * A.transpose) j k := by
  classical
  have hprod (x : Vector p) : A.mulVec x j * A.mulVec x k =
      ∑ r, ∑ s, (A j r * A k s) * (x r * x s) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hint (r s : Fin p) : Integrable
      (fun x : Vector p => (A j r * A k s) * (x r * x s)) (standardGaussian p) :=
    (standardGaussian_integrable_coordinate_product p r s).const_mul _
  calc
    _ = ∫ x : Vector p, ∑ r, ∑ s, (A j r * A k s) * (x r * x s)
        ∂standardGaussian p := integral_congr_ae (ae_of_all _ hprod)
    _ = ∑ r, ∑ s, ∫ x : Vector p, (A j r * A k s) * (x r * x s)
        ∂standardGaussian p := by
      rw [integral_finset_sum Finset.univ
        (fun r _ => integrable_finset_sum Finset.univ (fun s _ => hint r s))]
      apply Finset.sum_congr rfl
      intro r _
      exact integral_finset_sum Finset.univ (fun s _ => hint r s)
    _ = ∑ r, A j r * A k r := by
      simp_rw [integral_const_mul, standardGaussian_integral_coordinate_product]
      simp
    _ = _ := by simp only [Matrix.mul_apply, Matrix.transpose_apply]

/-- Coordinate integrability for the actual pushforward law. -/
theorem gaussianLaw_integrable_coordinate {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    Integrable (fun x : Vector p => x j) (gaussianLaw A) := by
  unfold gaussianLaw
  exact (integrable_map_measure (measurable_pi_apply j).aestronglyMeasurable
    (measurable_mulVec A).aemeasurable).mpr
      (standardGaussian_integrable_mulVec_coordinate A j)

theorem gaussianLaw_integrable_coordinate_product {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) :
    Integrable (fun x : Vector p => x j * x k) (gaussianLaw A) := by
  unfold gaussianLaw
  exact (integrable_map_measure
    ((measurable_pi_apply j).mul (measurable_pi_apply k)).aestronglyMeasurable
    (measurable_mulVec A).aemeasurable).mpr
      (standardGaussian_integrable_mulVec_product A j k)

theorem gaussianLaw_integral_coordinate {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    (∫ x : Vector p, x j ∂gaussianLaw A) = 0 := by
  unfold gaussianLaw
  rw [integral_map (measurable_mulVec A).aemeasurable
    (measurable_pi_apply j).aestronglyMeasurable]
  exact standardGaussian_integral_mulVec_coordinate A j

theorem gaussianLaw_integral_coordinate_product {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) :
    (∫ x : Vector p, x j * x k ∂gaussianLaw A) = (A * A.transpose) j k := by
  unfold gaussianLaw
  rw [integral_map (measurable_mulVec A).aemeasurable
    ((measurable_pi_apply j).mul (measurable_pi_apply k)).aestronglyMeasurable]
  exact standardGaussian_integral_mulVec_product A j k

/-- The concrete Gaussian pushforward really has the required covariance,
also for singular matrices and in dimension zero. -/
theorem covariance_gaussianLaw {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    covariance (gaussianLaw A) id = A * A.transpose := by
  ext j k
  simp only [covariance, id_eq, gaussianLaw_integral_coordinate_product,
    gaussianLaw_integral_coordinate, zero_mul, sub_zero]

end RectangleCLT
