import RectangleCLT.GaussianComparisonLaw
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Ring

/-!
# Exact finite splitting of a possibly singular Gaussian component

This uses the explicit Fourier transform of the concrete Gaussian law.
The argument is an equality of laws, not an invocation of a central limit
theorem.  A finite array of sufficiently small Gaussian increments can
therefore be truncated before applying the bounded theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

/-- The actual product law of independent Gaussian increments. -/
def gaussianComponentArrayLaw {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (N : ℕ) :
    Measure (Fin N → Vector p) :=
  Measure.pi (fun _ : Fin N => gaussianLaw B)

instance gaussianComponentArrayLaw_isProbability {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (N : ℕ) :
    IsProbabilityMeasure (gaussianComponentArrayLaw B N) := by
  refine ⟨?_⟩
  simp only [gaussianComponentArrayLaw, Measure.pi_univ, measure_univ, Finset.prod_const_one]

theorem gaussianComponentArrayLaw_map_eval {p N : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (i : Fin N) :
    (gaussianComponentArrayLaw B N).map (fun z => z i) = gaussianLaw B := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have hset : (fun z : Fin N → Vector p => z i) ⁻¹' s =
      Set.pi Set.univ (fun j => if j = i then s else Set.univ) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hz j
      by_cases hj : j = i
      · subst j; simpa using hz
      · simp [hj]
    · intro hz
      simpa using hz i
  rw [hset]
  change Measure.pi (fun _ : Fin N => gaussianLaw B) _ = _
  rw [Measure.pi_pi]
  simp [apply_ite, measure_univ]

theorem gaussianComponentArray_iIndepFun {p N : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) :
    iIndepFun (fun i (z : Fin N → Vector p) => z i)
      (gaussianComponentArrayLaw B N) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  change (gaussianComponentArrayLaw B N).map id = _
  rw [Measure.map_id]
  simp only [gaussianComponentArrayLaw_map_eval]
  rfl

/-- A finite sum with its deterministic increment scale. -/
def gaussianComponentSum {p N : ℕ} (a : ℝ)
    (z : Fin N → Vector p) : Vector p :=
  a • ∑ i, z i

theorem measurable_gaussianComponentSum {p N : ℕ} (a : ℝ) :
    Measurable (gaussianComponentSum (p := p) (N := N) a) := by
  unfold gaussianComponentSum
  fun_prop

theorem vectorFourier_gaussianComponentSum {p N : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (a : ℝ) (t : Vector p) :
    vectorFourier ((gaussianComponentArrayLaw B N).map
      (gaussianComponentSum a)) t =
      Complex.exp (-(((N : ℝ) * a ^ 2 *
        dotProduct t ((B * B.transpose).mulVec t) : ℝ) : ℂ) / 2) := by
  classical
  letI : MeasureSpace (Vector p) := ⟨gaussianLaw B⟩
  letI : IsProbabilityMeasure (volume : Measure (Vector p)) := by
    change IsProbabilityMeasure (gaussianLaw B)
    infer_instance
  have hkernel (z : Fin N → Vector p) :
      vectorFourierKernel t (gaussianComponentSum a z) =
        ∏ i, vectorFourierKernel (a • t) (z i) := by
    unfold vectorFourierKernel gaussianComponentSum
    rw [← Complex.exp_sum]
    congr 1
    have hdot : dotProduct (∑ i, z i) t = ∑ i, dotProduct (z i) t := by
      simp only [dotProduct, Finset.sum_apply, Finset.sum_mul]
      exact Finset.sum_comm
    simp only [smul_dotProduct, dotProduct_smul, hdot,
      Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul,
      Finset.mul_sum, Finset.sum_mul]
  unfold vectorFourier
  rw [integral_map (measurable_gaussianComponentSum a).aemeasurable
    (measurable_vectorFourierKernel t).aestronglyMeasurable]
  simp_rw [hkernel]
  change (∫ z : Fin N → Vector p,
    ∏ i, vectorFourierKernel (a • t) (z i)) = _
  rw [integral_fintype_prod_eq_pow]
  simp only [Fintype.card_fin]
  change vectorFourier (gaussianLaw B) (a • t) ^ N = _
  rw [vectorFourier_gaussianLaw, ← Complex.exp_nat_mul]
  congr 1
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  ring

/-- Exact splitting, with no nonsingularity condition on `B`. -/
theorem gaussianComponentSum_law {p N : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) {a : ℝ}
    (hscale : (N : ℝ) * a ^ 2 = 1) :
    (gaussianComponentArrayLaw B N).map (gaussianComponentSum a) =
      gaussianLaw B := by
  apply measure_eq_of_vectorFourier_eq
  intro t
  rw [vectorFourier_gaussianComponentSum, hscale, one_mul,
    vectorFourier_gaussianLaw]

/-- Integer powers suffice for the approximation: `k^6` increments of
scale `k^-3` have exactly the original Gaussian covariance. -/
theorem gaussianComponentSum_law_sixth {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    (gaussianComponentArrayLaw B (k ^ 6)).map
      (gaussianComponentSum ((k : ℝ) ^ 3)⁻¹) = gaussianLaw B := by
  apply gaussianComponentSum_law
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  push_cast
  field_simp [hk'] <;> ring

/-- The concrete centered Gaussian law is invariant under negation. -/
theorem gaussianComponentLaw_map_neg {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) :
    (gaussianLaw B).map (fun x : Vector p => -x) = gaussianLaw B := by
  calc
    _ = gaussianLaw (-B) := by
      unfold gaussianLaw
      rw [Measure.map_map measurable_neg (measurable_mulVec B)]
      congr 1
      funext x
      simp only [Function.comp_apply, Matrix.neg_mulVec]
    _ = gaussianLaw B := gaussianLaw_eq_of_factor_covariance (by simp)

/-- Every measurable odd observable has zero Gaussian integral.  The
Bochner integral convention makes integrability unnecessary for this
identity; subsequent moment bounds establish integrability where used. -/
theorem gaussianComponent_integral_odd {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) {f : Vector p → ℝ}
    (hf : Measurable f) (hodd : ∀ x, f (-x) = -f x) :
    (∫ x, f x ∂gaussianLaw B) = 0 := by
  have hmap := integral_map (μ := gaussianLaw B) measurable_neg.aemeasurable
    hf.aestronglyMeasurable
  rw [gaussianComponentLaw_map_neg B] at hmap
  have heq : (fun x : Vector p => f (-x)) = (fun x => -f x) := funext hodd
  rw [heq, integral_neg] at hmap
  linarith

end

end RectangleCLT
