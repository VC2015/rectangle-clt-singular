import RectangleCLTArxivV1.SupplementalGScoreRestoration
import RectangleCLT.GaussianStein
import RectangleCLTCompanion.SignedSurfaceGaussianSection

/-! Actual Gaussian nuclear moments of the second and third Hermite
matrices. The third-order estimate follows from trace duality and scalar
Gaussian moments, without an assumed matrix remainder estimate. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_standardRealGaussian_integral_fourth :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  have hderiv (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert (hasDerivAt_id x).pow 3 using 1
    norm_num
  have hmul : (fun x : ℝ => x * x ^ 3) = (fun x => x ^ 4) := by
    funext x
    ring
  have hs := standardRealGaussian_stein_of_integrable hderiv
    (standardRealGaussian_integrable_pow 3)
    ((standardRealGaussian_integrable_pow 2).const_mul 3)
    (by rw [hmul]; exact standardRealGaussian_integrable_pow 4)
  rw [hmul, integral_const_mul, standardRealGaussian_integral_sq, mul_one] at hs
  exact hs

theorem cap_standardGaussian_integral_coordinate_fourth {r : ℕ} (j : Fin r) :
    (∫ g : Vector r, g j ^ 4 ∂standardGaussian r) = 3 := by
  have hmap := integral_map (μ := standardGaussian r)
    (measurable_pi_apply j).aemeasurable
    (f := fun t : ℝ => t ^ 4) (measurable_id.pow_const 4).aestronglyMeasurable
  rw [standardGaussian_map_eval] at hmap
  exact hmap.symm.trans cap_standardRealGaussian_integral_fourth

private theorem cap_abs_trace_unit_le_dimension {r : ℕ}
    {B : Matrix (Fin r) (Fin r) ℝ} (hB : symmetricTraceUnitBall B) :
    |Matrix.trace B| ≤ (r : ℝ) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ j, |B j j|) ≤ ∑ _j : Fin r, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hB.2.2 j j)
    _ = r := by simp

private theorem cap_abs_trace_secondHermite {r : ℕ}
    {B : Matrix (Fin r) (Fin r) ℝ} (hB : symmetricTraceUnitBall B) (g : Vector r) :
    |Matrix.trace (B * (rankOne g - 1))| ≤ vectorNormSq g + r := by
  rw [Matrix.mul_sub, Matrix.trace_sub, trace_mul_rankOne, Matrix.mul_one]
  exact (abs_sub _ _).trans (add_le_add (hB.2.1 g) (cap_abs_trace_unit_le_dimension hB))

theorem capSecondHermite_nuclear_le {r : ℕ} (g : Vector r) :
    symmetricNuclearNorm (rankOne g - 1) ≤ vectorNormSq g + r := by
  apply csSup_le (symmetricTrace_values_nonempty _)
  rintro t ⟨B, hB, rfl⟩
  exact (le_abs_self _).trans (cap_abs_trace_secondHermite hB g)

private theorem cap_vectorNormSq_parallelogram {r : ℕ} (u g : Vector r) :
    vectorNormSq (u + g) + vectorNormSq (u - g) =
      2 * (vectorNormSq u + vectorNormSq g) := by
  unfold vectorNormSq
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem cap_abs_trace_cross {r : ℕ}
    {B : Matrix (Fin r) (Fin r) ℝ} (hB : symmetricTraceUnitBall B) (u g : Vector r) :
    |Matrix.trace (B * (Matrix.vecMulVec u g + Matrix.vecMulVec g u))| ≤
      vectorNormSq u + vectorNormSq g := by
  have hid : Matrix.vecMulVec u g + Matrix.vecMulVec g u =
      (1 / 2 : ℝ) • (rankOne (u + g) - rankOne (u - g)) := by
    ext j k
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
      Matrix.sub_apply, rankOne, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hid, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Matrix.mul_sub, Matrix.trace_sub,
    trace_mul_rankOne, trace_mul_rankOne]
  have hh := (abs_sub _ _).trans (add_le_add (hB.2.1 (u + g)) (hB.2.1 (u - g)))
  have hs := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [cap_vectorNormSq_parallelogram] at hs
  linarith only [hs]

theorem capThirdHermite_nuclear_le {r : ℕ} (u g : Vector r) :
    symmetricNuclearNorm (capThirdHermiteMatrix u g) ≤
      |faceDot u g| * (vectorNormSq g + r) + vectorNormSq u + vectorNormSq g := by
  have hid : capThirdHermiteMatrix u g =
      faceDot u g • (rankOne g - 1) - (Matrix.vecMulVec u g + Matrix.vecMulVec g u) := by
    ext j k
    simp only [capThirdHermiteMatrix, Matrix.sub_apply, Matrix.smul_apply,
      rankOne, Matrix.one_apply, Matrix.add_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  apply csSup_le (symmetricTrace_values_nonempty _)
  rintro t ⟨B, hB, rfl⟩
  apply (le_abs_self _).trans
  rw [hid, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  calc
    _ ≤ |faceDot u g| * |Matrix.trace (B * (rankOne g - 1))| +
        |Matrix.trace (B * (Matrix.vecMulVec u g + Matrix.vecMulVec g u))| := by
      simpa only [abs_mul] using abs_sub
        (faceDot u g * Matrix.trace (B * (rankOne g - 1)))
        (Matrix.trace (B * (Matrix.vecMulVec u g + Matrix.vecMulVec g u)))
    _ ≤ |faceDot u g| * (vectorNormSq g + r) + (vectorNormSq u + vectorNormSq g) :=
      add_le_add (mul_le_mul_of_nonneg_left (cap_abs_trace_secondHermite hB g) (abs_nonneg _))
        (cap_abs_trace_cross hB u g)
    _ = _ := by ring

theorem capThirdHermiteMatrix_nuclear_integrable {r : ℕ} (u : Vector r) :
    Integrable (fun g => symmetricNuclearNorm (capThirdHermiteMatrix u g)) (standardGaussian r) := by
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => (capThirdHermiteMatrix_integrable u k j).abs))
  have hc : Continuous (fun g : Vector r => capThirdHermiteMatrix u g) := by
    unfold capThirdHermiteMatrix faceDot
    fun_prop
  apply hi.mono' (continuous_symmetricNuclearNorm.comp hc).measurable.aestronglyMeasurable
  apply ae_of_all
  intro g
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (symmetricNuclearNorm_nonneg _)]
  exact symmetricNuclearNorm_le_entrySum _

theorem capSecondHermite_nuclear_integrable (r : ℕ) :
    Integrable (fun g : Vector r => symmetricNuclearNorm (rankOne g - 1)) (standardGaussian r) := by
  have hi := (SignedSurface.standardGaussian_integrable_vectorNormSq r).add (integrable_const (r : ℝ))
  have hc : Continuous (fun g : Vector r => rankOne g - (1 : Matrix (Fin r) (Fin r) ℝ)) := by
    unfold rankOne
    fun_prop
  apply hi.mono' (continuous_symmetricNuclearNorm.comp hc).measurable.aestronglyMeasurable
  apply ae_of_all
  intro g
  simp only [Function.comp_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (symmetricNuclearNorm_nonneg _)]
  exact capSecondHermite_nuclear_le g

theorem capSecondHermite_integral_nuclear_le (r : ℕ) :
    (∫ g : Vector r, symmetricNuclearNorm (rankOne g - 1) ∂standardGaussian r) ≤ 2 * r := by
  have hh := integral_mono (capSecondHermite_nuclear_integrable r)
    ((SignedSurface.standardGaussian_integrable_vectorNormSq r).add (integrable_const (r : ℝ)))
    (capSecondHermite_nuclear_le (r := r))
  simp only [Pi.add_apply] at hh
  rw [integral_add (SignedSurface.standardGaussian_integrable_vectorNormSq r) (integrable_const (r : ℝ)),
    SignedSurface.standardGaussian_integral_vectorNormSq] at hh
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hh
  linarith only [hh]

/-- The actual third-Hermite nuclear moment has linear dimension cost.
The proof only needs the unit direction and the scalar fourth moment. -/
theorem capThirdHermite_integral_nuclear_le {r : ℕ} (u : Vector r)
    (hr : 1 ≤ r) (hu : vectorNormSq u = 1) :
    (∫ g : Vector r, symmetricNuclearNorm (capThirdHermiteMatrix u g)
      ∂standardGaussian r) ≤ 5 * r := by
  let P : Fin r → Vector r → ℝ := fun j g => (faceDot u g ^ 2 + g j ^ 4) / 2
  let Q : Vector r → ℝ := fun g => (1 + faceDot u g ^ 2) / 2
  let S : Vector r → ℝ := fun g => ∑ j, P j g
  let F : Vector r → ℝ := fun g => S g + (r : ℝ) * Q g + 1 + vectorNormSq g
  have hiP (j : Fin r) : Integrable (P j) (standardGaussian r) :=
    ((SignedSurface.standardGaussian_integrable_faceDot_sq u).add
      (standardGaussian_integrable_coordinate_pow r j 4)).div_const 2
  have hiQ : Integrable Q (standardGaussian r) :=
    ((integrable_const 1).add (SignedSurface.standardGaussian_integrable_faceDot_sq u)).div_const 2
  have hiS : Integrable S (standardGaussian r) := integrable_finset_sum Finset.univ (fun j _ => hiP j)
  have hiF : Integrable F (standardGaussian r) :=
    (((hiS.add (hiQ.const_mul (r : ℝ))).add (integrable_const 1)).add
      (SignedSurface.standardGaussian_integrable_vectorNormSq r))
  have hP (j : Fin r) : (∫ g, P j g ∂standardGaussian r) = 2 := by
    dsimp only [P]
    rw [integral_div, integral_add (SignedSurface.standardGaussian_integrable_faceDot_sq u)
      (standardGaussian_integrable_coordinate_pow r j 4),
      SignedSurface.standardGaussian_integral_faceDot_sq, hu,
      cap_standardGaussian_integral_coordinate_fourth]
    norm_num
  have hQ : (∫ g, Q g ∂standardGaussian r) = 1 := by
    dsimp only [Q]
    rw [integral_div, integral_add (integrable_const 1)
      (SignedSurface.standardGaussian_integrable_faceDot_sq u),
      SignedSurface.standardGaussian_integral_faceDot_sq, hu]
    norm_num
  have hS : (∫ g, S g ∂standardGaussian r) = 2 * r := by
    dsimp only [S]
    rw [integral_finset_sum Finset.univ (fun j _ => hiP j)]
    simp only [hP, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hF : (∫ g, F g ∂standardGaussian r) = 4 * r + 1 := by
    dsimp only [F]
    have he₁ := integral_add hiS (hiQ.const_mul (r : ℝ))
    have he₂ := integral_add (hiS.add (hiQ.const_mul (r : ℝ))) (integrable_const 1)
    have he₃ := integral_add ((hiS.add (hiQ.const_mul (r : ℝ))).add (integrable_const 1))
      (SignedSurface.standardGaussian_integrable_vectorNormSq r)
    simp only [Pi.add_apply] at he₁ he₂ he₃
    rw [he₃, he₂, he₁, integral_const_mul, hS, hQ,
      SignedSurface.standardGaussian_integral_vectorNormSq]
    simp
    ring
  have hpoint (g : Vector r) : symmetricNuclearNorm (capThirdHermiteMatrix u g) ≤ F g := by
    have hyoung (j : Fin r) : |faceDot u g| * g j ^ 2 ≤ P j g := by
      dsimp only [P]
      nlinarith [sq_nonneg (|faceDot u g| - g j ^ 2), sq_abs (faceDot u g)]
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) => hyoung j)
    rw [← Finset.mul_sum] at hsum
    change |faceDot u g| * vectorNormSq g ≤ S g at hsum
    have hy : |faceDot u g| ≤ Q g := by
      dsimp only [Q]
      nlinarith [sq_nonneg (|faceDot u g| - 1), sq_abs (faceDot u g)]
    have hyr := mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    have hb := capThirdHermite_nuclear_le u g
    rw [hu] at hb
    dsimp only [F]
    nlinarith only [hsum, hyr, hb]
  have hh := integral_mono (capThirdHermiteMatrix_nuclear_integrable u) hiF hpoint
  rw [hF] at hh
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  linarith

end
end RectangleCLTArxivV1
