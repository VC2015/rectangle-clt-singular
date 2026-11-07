import RectangleCLTCompanion.SplitV4.LogisticNormalRegularization
import RectangleCLTCompanion.SplitV4.SymmetricNuclearNorm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual Gaussian dominated-convergence and Fatou steps for B.4.
These are limit implications, not a replacement for the separate quantitative
B.5 bound on the linearly independent padded systems.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- Conditional Gaussian second-score entries converge under bounded
pointwise-convergent actual weights. All domination follows from genuine
Gaussian second moments. -/
theorem weightedScore_entry_tendsto_of_bounded_weights {r : ℕ}
    (w : ℕ → Vector r → ℝ) (w₀ : Vector r → ℝ)
    (hw : ∀ n, Measurable (w n)) (hwb : ∀ n g, |w n g| ≤ 1)
    (hlim : ∀ g, Tendsto (fun n => w n g) atTop (𝓝 (w₀ g))) (j l : Fin r) :
    Tendsto (fun n => weightedScore (standardGaussian r) id (w n) j l) atTop
      (𝓝 (weightedScore (standardGaussian r) id w₀ j l)) := by
  let P (g : Vector r) := g j * g l - if j = l then 1 else 0
  have hPi : Integrable P (standardGaussian r) :=
    (standardGaussian_integrable_coordinate_product r j l).sub (integrable_const _)
  apply tendsto_integral_of_dominated_convergence (fun g => |P g|)
  · intro n
    exact ((show Measurable P by unfold P; fun_prop).mul (hw n)).aestronglyMeasurable
  · exact hPi.abs
  · intro n
    exact ae_of_all _ (fun g => by
      change ‖P g * w n g‖ ≤ |P g|
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (hwb n g) (abs_nonneg _)).trans_eq (mul_one _))
  · exact ae_of_all _ (fun g => (hlim g).const_mul (P g))

/-- Fatou's lemma with a uniform integral budget. The limiting function's
integrability is explicit, while nonnegativity and convergence are actual
pointwise statements; no desired quantitative conclusion is a premise. -/
theorem integral_nonnegative_limit_le_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : ℕ → Ω → ℝ) (f₀ : Ω → ℝ)
    (hfi : ∀ n, Integrable (f n) μ) (hf₀i : Integrable f₀ μ)
    (hf0 : ∀ n ω, 0 ≤ f n ω) (hf₀0 : ∀ ω, 0 ≤ f₀ ω)
    (hlim : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (f₀ ω)))
    {B : ℝ} (hB : ∀ n, (∫ ω, f n ω ∂μ) ≤ B) : (∫ ω, f₀ ω ∂μ) ≤ B := by
  have hB0 : 0 ≤ B := (integral_nonneg (hf0 0)).trans (hB 0)
  have hENN (ω : Ω) : Tendsto (fun n => ENNReal.ofReal (f n ω)) atTop (𝓝 (ENNReal.ofReal (f₀ ω))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hlim ω)
  have hlin : (∫⁻ ω, ENNReal.ofReal (f₀ ω) ∂μ) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂μ :=
        lintegral_congr_ae (ae_of_all _ (fun ω => (hENN ω).liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => (hfi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ _ := by
        have hh : ∀ n, (∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ) ≤ ENNReal.ofReal B := by
          intro n
          rw [← ofReal_integral_eq_lintegral_ofReal (hfi n) (ae_of_all _ (hf0 n))]
          exact ENNReal.ofReal_le_ofReal (hB n)
        simpa only [liminf_const] using liminf_le_liminf (f := (atTop : Filter ℕ)) (Eventually.of_forall hh)
  rw [← ofReal_integral_eq_lintegral_ofReal hf₀i (ae_of_all _ hf₀0)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hB0).mp hlin

def firstGaussianBlock {r s : ℕ} (g : Vector (r + s)) : Vector r :=
  fun j => g (Fin.castAdd s j)

def firstGaussianBlockMatrix (r s : ℕ) : Matrix (Fin r) (Fin (r + s)) ℝ :=
  fun j => Fin.append (Pi.single j 1) 0

theorem firstGaussianBlockMatrix_mulVec (r s : ℕ) (g : Vector (r + s)) :
    (firstGaussianBlockMatrix r s).mulVec g = firstGaussianBlock g := by
  funext j
  simp [firstGaussianBlockMatrix, firstGaussianBlock, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
    Pi.single_apply]

theorem firstGaussianBlockMatrix_gram (r s : ℕ) :
    firstGaussianBlockMatrix r s * (firstGaussianBlockMatrix r s).transpose = 1 := by
  ext j k
  simp [firstGaussianBlockMatrix, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_add,
    Pi.single_apply, Matrix.one_apply, eq_comm]

/-- The retained original Gaussian block has its actual standard Gaussian
law, including zero-dimensional and singular-factor cases. -/
theorem firstGaussianBlock_law (r s : ℕ) :
    (standardGaussian (r + s)).map (firstGaussianBlock (r := r) (s := s)) = standardGaussian r := by
  have hfac := rectangularGaussianLaw_eq_gaussianLaw (firstGaussianBlockMatrix r s)
    (1 : Matrix (Fin r) (Fin r) ℝ) (by simpa using firstGaussianBlockMatrix_gram r s)
  have hI : gaussianLaw (1 : Matrix (Fin r) (Fin r) ℝ) = standardGaussian r := by
    unfold gaussianLaw
    have he : (1 : Matrix (Fin r) (Fin r) ℝ).mulVec = id := by funext x; simp
    rw [he, Measure.map_id]
  have he : (firstGaussianBlockMatrix r s).mulVec = firstGaussianBlock :=
    funext (firstGaussianBlockMatrix_mulVec r s)
  simpa only [rectangularGaussianLaw, he, hI] using hfac

/-- The upper-left score of a weight depending only on the original block
is exactly the original score, rather than a surrogate Gaussian matrix. -/
theorem weightedScore_firstGaussianBlock {r s : ℕ} (w : Vector r → ℝ) (hw : Measurable w) :
    (weightedScore (standardGaussian (r + s)) id (fun g => w (firstGaussianBlock g))).submatrix
      (Fin.castAdd s) (Fin.castAdd s) = weightedScore (standardGaussian r) id w := by
  have hfst : Measurable (firstGaussianBlock (r := r) (s := s)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (Fin.castAdd s j))
  ext j l
  have hm : Measurable (fun g : Vector r => (g j * g l - if j = l then 1 else 0) * w g) :=
    (((measurable_pi_apply j).mul (measurable_pi_apply l)).sub_const _).mul hw
  have he := integral_map (μ := standardGaussian (r + s)) hfst.aemeasurable hm.aestronglyMeasurable
  rw [firstGaussianBlock_law] at he
  simpa only [weightedScore, Matrix.submatrix_apply, id_eq, firstGaussianBlock,
    Fin.castAdd_inj] using he.symm

end

end RectangleCLT.Companion.SplitV4
