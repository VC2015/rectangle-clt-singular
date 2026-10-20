import RectangleCLTCompanion.SelectorMeanBound
import RectangleCLTCompanion.RestorationMatrixBound

/-! Averaging the actual selector matrix reduction. Only the signed trace
estimate remains an explicit analytic premise here; covariance contraction,
mean-energy estimates, and integrability are supplied by proved theorems. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {p r q : ℕ}

/-- The actual score entries are measurable in an arbitrary measurable base. -/
theorem measurable_selectorGaussianScore_entry (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (α : Fin q → Face p) (j l : Fin r) :
    Measurable (fun ω => selectorGaussianScore s A V α ω j l) := by
  have hx : Measurable (fun z : Ω × Vector r => A.mulVec z.2 + V z.1) :=
    (((continuous_const.matrix_mulVec continuous_id).measurable).comp measurable_snd).add
      (hV.comp measurable_fst)
  have hw := (continuous_selectorWeight s α).measurable.comp hx
  have hm : Measurable (fun z : Ω × Vector r =>
      (z.2 j * z.2 l - if j = l then 1 else 0) *
        selectorWeight s α (A.mulVec z.2 + V z.1)) :=
    ((((measurable_pi_apply j).comp measurable_snd).mul
      ((measurable_pi_apply l).comp measurable_snd)).sub_const _).mul hw
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace Ω] in
/-- A uniform bound used solely for integrability, with no covariance rank
restriction and no requirement that a selector have positive mass. -/
theorem norm_selectorGaussianScore_diagonal_le_two (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (α : Fin q → Face p) (ω : Ω) (j : Fin r) :
    ‖selectorGaussianScore s A V α ω j j‖ ≤ 2 := by
  change ‖∫ g : Vector r, (g j * g j - if j = j then 1 else 0) *
    selectorWeight s α (A.mulVec g + V ω) ∂standardGaussian r‖ ≤ 2
  simp only [↓reduceIte]
  have hquad : Integrable (fun g : Vector r => (g j) ^ 2) (standardGaussian r) := by
    simpa only [pow_two] using standardGaussian_integrable_coordinate_product r j j
  have hi : Integrable (fun g : Vector r => (g j) ^ 2 + 1) (standardGaussian r) :=
    hquad.add (integrable_const 1)
  have hh := norm_integral_le_of_norm_le
    (f := fun g : Vector r => (g j * g j - 1) *
      selectorWeight s α (A.mulVec g + V ω)) hi (ae_of_all _ (fun g : Vector r => by
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (selectorWeight_nonneg s α _)]
    calc
      _ ≤ |g j * g j - 1| := mul_le_of_le_one_right (abs_nonneg _)
        (selectorWeight_le_one s α _)
      _ ≤ (g j) ^ 2 + 1 := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg (g j)]))
  have he : (∫ g : Vector r, (g j) ^ 2 + 1 ∂standardGaussian r) = 2 := by
    rw [integral_add hquad (integrable_const 1),
      standardGaussian_integral_coordinate_sq]
    norm_num
  exact hh.trans_eq he

theorem integrable_selectorGaussianScore_trace (ν : Measure Ω) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (α : Fin q → Face p) :
    Integrable (fun ω => Matrix.trace (selectorGaussianScore s A V α ω)) ν := by
  apply integrable_finset_sum
  intro j _
  exact (integrable_const (2 : ℝ)).mono'
    (measurable_selectorGaussianScore_entry s A V hV α j j).aestronglyMeasurable
    (ae_of_all _ (fun ω => norm_selectorGaussianScore_diagonal_le_two s A V α ω j))

theorem measurable_sum_abs_trace_selectorGaussianScore
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (hV : Measurable V)
    (B : (Fin q → Face p) → Ω → Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ α j l, Measurable (fun ω => B α ω j l)) :
    Measurable (fun ω => ∑ α, |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)|) := by
  classical
  apply Finset.measurable_sum
  intro α _
  apply Measurable.abs
  change Measurable (fun ω => ∑ j, ∑ l, B α ω j l * selectorGaussianScore s A V α ω l j)
  exact Finset.measurable_sum _ (fun j _ =>
    Finset.measurable_sum _ (fun l _ =>
      (hB α j l).mul (measurable_selectorGaussianScore_entry s A V hV α l j)))

/-- Matrices need only a quadratic-form bound. No entry bound or symmetry
is assumed; uncontrolled skew parts disappear in the actual trace pairing. -/
theorem integrable_sum_abs_trace_selectorGaussianScore
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (hV : Measurable V)
    (B : (Fin q → Face p) → Ω → Matrix (Fin r) (Fin r) ℝ) {b : ℝ}
    (hBm : ∀ α j l, Measurable (fun ω => B α ω j l))
    (hB : ∀ α ω u, |matrixQuadratic (B α ω) u| ≤ b * vectorNormSq u) :
    Integrable (fun ω => ∑ α, |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)|) ν := by
  classical
  have hE : Integrable (fun ω => ∑ α : Fin q → Face p,
      weightMass (standardGaussian r) (fun g => selectorWeight s α (A.mulVec g + V ω)) *
        vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α (A.mulVec g + V ω)))) ν := by
    apply integrable_finset_sum
    intro α _
    have hx : Measurable (fun z : Ω × Vector r => A.mulVec z.2 + V z.1) :=
      (((continuous_const.matrix_mulVec continuous_id).measurable).comp measurable_snd).add
      (hV.comp measurable_fst)
    exact integrable_gaussian_weighted_mean_energy ν _
      ((continuous_selectorWeight s α).measurable.comp hx)
      (fun ω g => ⟨selectorWeight_nonneg s α _, selectorWeight_le_one s α _⟩)
  have hT : Integrable (fun ω => ∑ α : Fin q → Face p,
      Matrix.trace (selectorGaussianScore s A V α ω)) ν :=
    integrable_finset_sum Finset.univ (fun α _ =>
      integrable_selectorGaussianScore_trace ν s A V hV α)
  apply (((hE.const_mul 2).sub hT).const_mul b).mono'
    (measurable_sum_abs_trace_selectorGaussianScore s A V hV B hBm).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    simpa only [selectorGaussianScore, selectorTupleWeight, selectorWeight] using
      sum_selectorWeight_trace_reduction s Finset.univ A (V ω) (fun α => B α ω)
        (fun α _ => hB α ω)

/-- Averaged matrix reduction with a genuine signed-trace premise. -/
theorem integral_sum_abs_trace_selectorGaussianScore_le
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (hV : Measurable V)
    (B : (Fin q → Face p) → Ω → Matrix (Fin r) (Fin r) ℝ) {b K T : ℝ}
    (hb : 0 ≤ b) (hBm : ∀ α j l, Measurable (fun ω => B α ω j l))
    (hB : ∀ α ω u, |matrixQuadratic (B α ω) u| ≤ b * vectorNormSq u)
    (hmean : (∫ ω, ∑ α : Fin q → Face p,
      weightMass (standardGaussian r) (fun g => selectorWeight s α (A.mulVec g + V ω)) *
        vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α (A.mulVec g + V ω))) ∂ν) ≤ K)
    (htrace : -(∫ ω, ∑ α : Fin q → Face p,
      Matrix.trace (selectorGaussianScore s A V α ω) ∂ν) ≤ T) :
    (∫ ω, ∑ α, |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)| ∂ν) ≤
      b * (2 * K + T) := by
  classical
  have hE : Integrable (fun ω => ∑ α : Fin q → Face p,
      weightMass (standardGaussian r) (fun g => selectorWeight s α (A.mulVec g + V ω)) *
        vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α (A.mulVec g + V ω)))) ν := by
    apply integrable_finset_sum
    intro α _
    have hx : Measurable (fun z : Ω × Vector r => A.mulVec z.2 + V z.1) :=
      (((continuous_const.matrix_mulVec continuous_id).measurable).comp measurable_snd).add
      (hV.comp measurable_fst)
    exact integrable_gaussian_weighted_mean_energy ν _
      ((continuous_selectorWeight s α).measurable.comp hx)
      (fun ω g => ⟨selectorWeight_nonneg s α _, selectorWeight_le_one s α _⟩)
  have hT : Integrable (fun ω => ∑ α : Fin q → Face p,
      Matrix.trace (selectorGaussianScore s A V α ω)) ν :=
    integrable_finset_sum Finset.univ (fun α _ =>
      integrable_selectorGaussianScore_trace ν s A V hV α)
  have hpoint (ω : Ω) := sum_selectorWeight_trace_reduction s Finset.univ A (V ω)
    (fun α => B α ω) (fun α _ => hB α ω)
  have hh := integral_mono (integrable_sum_abs_trace_selectorGaussianScore ν s A V hV B hBm hB)
    (((hE.const_mul 2).sub hT).const_mul b) (fun ω => by
      simpa only [selectorGaussianScore, selectorTupleWeight, selectorWeight] using hpoint ω)
  simp only [Pi.sub_apply] at hh
  rw [integral_const_mul, integral_sub (hE.const_mul 2) hT, integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith) hb)

/-- An explicit constant absorbing the linear order factor in the proved
mean-energy estimate together with an exponential signed-trace estimate. -/
def selectorMatrixConstant (D : ℝ) : ℝ := 2 * (Real.exp (13 / 2 : ℝ) + 8) + 2 + D

theorem one_le_selectorMatrixConstant {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ selectorMatrixConstant D := by
  unfold selectorMatrixConstant
  linarith [Real.exp_nonneg (13 / 2 : ℝ)]

private theorem selector_order_constant_le {D : ℝ} (hD : 0 ≤ D) (q : ℕ) :
    2 * (Real.exp (13 / 2 : ℝ) + 8) * (q : ℝ) + D ^ (q + 1) ≤
      selectorMatrixConstant D ^ (q + 1) := by
  let a : ℝ := 2 * (Real.exp (13 / 2 : ℝ) + 8) + 2
  have ha : 2 ≤ a := by dsimp [a]; linarith [Real.exp_nonneg (13 / 2 : ℝ)]
  have hq : (q : ℝ) ≤ (2 : ℝ) ^ q := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, div_one] using Nat.cast_le_pow_div_sub (show (1 : ℝ) < 2 by norm_num) q
  have hqa : (q : ℝ) ≤ a ^ q := hq.trans (pow_le_pow_left₀ (by norm_num) ha q)
  have hlin : 2 * (Real.exp (13 / 2 : ℝ) + 8) * (q : ℝ) ≤ a ^ (q + 1) := by
    calc
      _ ≤ a * (q : ℝ) := mul_le_mul_of_nonneg_right (by dsimp [a]; linarith)
        (Nat.cast_nonneg q)
      _ ≤ a * a ^ q := mul_le_mul_of_nonneg_left hqa (by linarith)
      _ = _ := by rw [pow_succ]; ring
  exact (add_le_add_right hlin _).trans
    (by simpa [selectorMatrixConstant, a] using
      pow_add_pow_le (show 0 ≤ a by linarith) hD (show q + 1 ≠ 0 by omega))

/-- Conditional analytic closure of the actual averaged matrix estimate.
The signed trace bound is displayed explicitly and is instantiated by the
separate signed surface argument. The mean bound is proved from the actual
transition-mass estimate. -/
theorem averagedSelectorMatrixEstimate_of_signed_trace_bound
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) {h M D : ℝ}
    (hM : 0 < M) (hD : 0 ≤ D) (hbound : TransitionMassBound ν V h M)
    (s : FaceSmoother p) (hs : s.bandwidth = h) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin r) ℝ) (hunit : ∀ j, vectorNormSq (A j) = 1) (σ : ℝ)
    (htrace : ∀ q : ℕ, 1 ≤ q →
      -(∫ ω, ∑ α : Fin q → Face p,
        Matrix.trace (selectorGaussianScore s (σ • A) V α ω) ∂ν) ≤
          D ^ (q + 1) * (M * dimensionLog p)) :
    AveragedSelectorMatrixEstimate s ν (σ • A) V
      (selectorMatrixConstant D) (M * dimensionLog p) := by
  classical
  intro q hq b hb B hBm hB
  refine ⟨integrable_sum_abs_trace_selectorGaussianScore ν s (σ • A) V hV B hBm hB, ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have hm := integral_selectorMeanEnergy_le (k := k) ν V hV hM hbound s hs hp A hunit σ
  have ht := htrace (k + 1) (by omega)
  have hh := integral_sum_abs_trace_selectorGaussianScore_le ν s (σ • A) V hV B hb hBm hB hm ht
  have hL : 0 ≤ M * dimensionLog p := mul_nonneg hM.le
    (zero_le_one.trans (log_exp_mul_nat_ge_one hp))
  calc
    _ ≤ b * (2 * ((Real.exp (13 / 2 : ℝ) + 8) * (k + 1 : ℝ) * M * dimensionLog p) +
        D ^ (k + 1 + 1) * (M * dimensionLog p)) := hh
    _ = b * ((2 * (Real.exp (13 / 2 : ℝ) + 8) * ((k + 1 : ℕ) : ℝ) +
        D ^ (k + 1 + 1)) * (M * dimensionLog p)) := by push_cast; ring
    _ ≤ b * (selectorMatrixConstant D ^ (k + 1 + 1) * (M * dimensionLog p)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (selector_order_constant_le hD (k + 1)) hL) hb
    _ = _ := by ring

end
end RectangleCLT.Companion
