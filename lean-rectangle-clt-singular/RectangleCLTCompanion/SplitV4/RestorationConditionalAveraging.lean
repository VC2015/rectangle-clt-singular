import RectangleCLTCompanion.SplitV4.RestorationConditionalBudgets
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import RectangleCLTCompanion.RestorationIntegration

/-! Conditional averaging at the common base in Lemma B.2. Almost-sure
operator budgets are converted to measurable coefficient versions, and
actual conditional expectation is pulled through H-measurable weights.
No concentration of a conditional law is used. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem matrixQuadratic_bound_of_rational {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (b : ℝ)
    (hbound : ∀ q : Fin r → ℚ,
      |matrixQuadratic B (fun j => (q j : ℝ))| ≤ b * vectorNormSq (fun j => (q j : ℝ))) :
    ∀ u : Vector r, |matrixQuadratic B u| ≤ b * vectorNormSq u := by
  let e : (Fin r → ℚ) → Vector r := fun q j => (q j : ℝ)
  have hd : DenseRange e := DenseRange.piMap (fun _ : Fin r => Rat.denseRange_cast)
  have hl : Continuous (fun u : Vector r => |matrixQuadratic B u|) := by
    apply Continuous.abs
    unfold matrixQuadratic
    exact continuous_finset_sum _ (fun j _ => continuous_finset_sum _
      (fun k _ => ((continuous_apply j).mul continuous_const).mul (continuous_apply k)))
  have hr : Continuous (fun u : Vector r => b * vectorNormSq u) := by
    apply continuous_const.mul
    exact continuous_finset_sum _ (fun j _ => (continuous_apply j).pow 2)
  have hc := isClosed_le hl hr
  have hsub : Set.range e ⊆ {u | |matrixQuadratic B u| ≤ b * vectorNormSq u} := by
    rintro _ ⟨q, rfl⟩
    exact hbound q
  exact fun u => (hc.closure_subset_iff.mpr hsub) (hd u)

def restorationCoefficientBudgetSet {Ω : Type*} {r : ℕ}
    (B : Ω → Matrix (Fin r) (Fin r) ℝ) (b : ℝ) : Set Ω :=
  {ω | ∀ q : Fin r → ℚ,
    |matrixQuadratic (B ω) (fun j => (q j : ℝ))| ≤ b * vectorNormSq (fun j => (q j : ℝ))}

theorem measurableSet_restorationCoefficientBudgetSet {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (B : Ω → Matrix (Fin r) (Fin r) ℝ) (b : ℝ)
    (hB : ∀ j k, Measurable (fun ω => B ω j k)) :
    MeasurableSet (restorationCoefficientBudgetSet B b) := by
  unfold restorationCoefficientBudgetSet
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro q
  apply measurableSet_le _ measurable_const
  apply Measurable.abs
  unfold matrixQuadratic
  exact Finset.measurable_sum _ (fun j _ => Finset.measurable_sum _
    (fun k _ => ((hB j k).const_mul (q j : ℝ)).mul_const (q k : ℝ)))

def boundedRestorationCoefficientVersion {Ω : Type*} {r : ℕ}
    (B : Ω → Matrix (Fin r) (Fin r) ℝ) (b : ℝ) (ω : Ω) : Matrix (Fin r) (Fin r) ℝ := by
  classical
  exact if ω ∈ restorationCoefficientBudgetSet B b then B ω else 0

theorem measurable_boundedRestorationCoefficientVersion_entry
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (B : Ω → Matrix (Fin r) (Fin r) ℝ) (b : ℝ)
    (hB : ∀ j k, Measurable (fun ω => B ω j k)) (j k : Fin r) :
    Measurable (fun ω => boundedRestorationCoefficientVersion B b ω j k) := by
  classical
  have hf : (fun ω => boundedRestorationCoefficientVersion B b ω j k) =
      (fun ω => if ω ∈ restorationCoefficientBudgetSet B b then B ω j k else 0) := by
    funext ω
    unfold boundedRestorationCoefficientVersion
    split_ifs <;> rfl
  rw [hf]
  exact Measurable.ite (measurableSet_restorationCoefficientBudgetSet B b hB) (hB j k) measurable_const

theorem boundedRestorationCoefficientVersion_quadratic
    {Ω : Type*} {r : ℕ} (B : Ω → Matrix (Fin r) (Fin r) ℝ) {b : ℝ} (hb : 0 ≤ b)
    (ω : Ω) (u : Vector r) :
    |matrixQuadratic (boundedRestorationCoefficientVersion B b ω) u| ≤ b * vectorNormSq u := by
  classical
  unfold boundedRestorationCoefficientVersion
  split_ifs with hω
  · exact matrixQuadratic_bound_of_rational _ _ hω u
  · simp only [matrixQuadratic, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, abs_zero]
    exact mul_nonneg hb (Finset.sum_nonneg (fun j _ => sq_nonneg (u j)))

theorem boundedRestorationCoefficientVersion_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ} (μ : Measure Ω)
    (B : Ω → Matrix (Fin r) (Fin r) ℝ) (b : ℝ)
    (hB : ∀ᵐ ω ∂μ, ∀ u, |matrixQuadratic (B ω) u| ≤ b * vectorNormSq u) :
    boundedRestorationCoefficientVersion B b =ᵐ[μ] B := by
  classical
  filter_upwards [hB] with ω hω
  exact if_pos (fun q : Fin r → ℚ => hω (fun j => (q j : ℝ)))

/-- The checked averaged matrix estimate accepts genuine almost-sure
conditional coefficient budgets after choosing equal measurable versions.
This does not strengthen concentration to a conditional-law assertion. -/
theorem averagedSelectorMatrixEstimate_ae_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r : ℕ}
    (s : FaceSmoother p) (ν : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) {C T : ℝ} (hmatrix : AveragedSelectorMatrixEstimate s ν A V C T)
    (q : ℕ) (hq : 1 ≤ q) {b : ℝ} (hb : 0 ≤ b)
    (B : (Fin q → Face p) → Ω → Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ α j k, Measurable (fun ω => B α ω j k))
    (hbudget : ∀ α, ∀ᵐ ω ∂ν, ∀ u, |matrixQuadratic (B α ω) u| ≤ b * vectorNormSq u) :
    Integrable (fun ω => ∑ α, |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)|) ν ∧
    (∫ ω, ∑ α, |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)| ∂ν) ≤
      b * C ^ (q + 1) * T := by
  let B' := fun α => boundedRestorationCoefficientVersion (B α) b
  have he (α : Fin q → Face p) : B' α =ᵐ[ν] B α :=
    boundedRestorationCoefficientVersion_ae_eq ν _ b (hbudget α)
  have hsum : (fun ω => ∑ α, |Matrix.trace (B' α ω * selectorGaussianScore s A V α ω)|) =ᵐ[ν]
      (fun ω => ∑ α, |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)|) := by
    filter_upwards [ae_all_iff.mpr he] with ω hω
    exact Finset.sum_congr rfl (fun α _ => by rw [hω α])
  have hm := hmatrix q hq b hb B'
    (fun α j k => measurable_boundedRestorationCoefficientVersion_entry _ b (hB α) j k)
    (fun α ω u => boundedRestorationCoefficientVersion_quadratic _ hb ω u)
  exact ⟨hm.1.congr hsum, (integral_congr_ae hsum).symm.trans_le hm.2⟩

/-- Exact common-base averaging: an H-measurable weight pulls through
the actual conditional expectation. Both original integrals are genuine. -/
theorem integral_mul_condExp_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ) (F G : Ω → ℝ)
    (hF : Integrable F μ) (hG : StronglyMeasurable[H] G)
    (hFG : Integrable (fun ω => F ω * G ω) μ) :
    Integrable (fun ω => (μ[F|H]) ω * G ω) μ ∧
    (∫ ω, F ω * G ω ∂μ) = ∫ ω, (μ[F|H]) ω * G ω ∂μ := by
  have he := condExp_mul_of_stronglyMeasurable_right hG hFG hF
  refine ⟨integrable_condExp.congr he, ?_⟩
  calc
    _ = ∫ ω, (μ[(fun z => F z * G z)|H]) ω ∂μ := (integral_condExp hH).symm
    _ = _ := integral_congr_ae he

/-- The operator coefficient can be conditionally averaged before its
trace pairing with the common-base matrix weight. No trace budget or rank
factor is introduced, and both integrands are genuinely integrable. -/
theorem integral_trace_conditionalMatrixAverage_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (B M : Ω → Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ j k, Integrable (fun ω => B ω j k) μ)
    (hM : ∀ j k, StronglyMeasurable[H] (fun ω => M ω j k))
    (hBM : ∀ j k, Integrable (fun ω => B ω j k * M ω k j) μ) :
    Integrable (fun ω => Matrix.trace (B ω * M ω)) μ ∧
    Integrable (fun ω => Matrix.trace (conditionalMatrixAverage (mΩ := mΩ) μ H B ω * M ω)) μ ∧
    (∫ ω, Matrix.trace (B ω * M ω) ∂μ) =
      ∫ ω, Matrix.trace (conditionalMatrixAverage (mΩ := mΩ) μ H B ω * M ω) ∂μ := by
  have he (j k : Fin r) := integral_mul_condExp_eq (mΩ := mΩ) μ H hH
    (fun ω => B ω j k) (fun ω => M ω k j) (hB j k) (hM k j) (hBM j k)
  have hCM (j k : Fin r) : Integrable
      (fun ω => conditionalMatrixAverage (mΩ := mΩ) μ H B ω j k * M ω k j) μ := (he j k).1
  have hiB : Integrable (fun ω => Matrix.trace (B ω * M ω)) μ := by
    simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] using
      integrable_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ (fun k _ => hBM j k))
  have hiC : Integrable (fun ω => Matrix.trace (conditionalMatrixAverage (mΩ := mΩ) μ H B ω * M ω)) μ := by
    simpa only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply] using
      integrable_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ (fun k _ => hCM j k))
  refine ⟨hiB, hiC, ?_⟩
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ (fun k _ => hBM j k)),
    integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ (fun k _ => hCM j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => hBM j k),
    integral_finset_sum Finset.univ (fun k _ => hCM j k)]
  exact Finset.sum_congr rfl (fun k _ => (he j k).2)

theorem stronglyMeasurable_selectorGaussianScore_entry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r q : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : Measurable V) (α : Fin q → Face p) (j k : Fin r) :
    StronglyMeasurable (fun ω => selectorGaussianScore s A V α ω j k) := by
  have hA : Measurable A.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hU : Measurable (fun z : Vector r × Ω => A.mulVec z.1 + V z.2) :=
    (hA.comp measurable_fst).add (hV.comp measurable_snd)
  have hw := measurable_selectorTupleWeight_comp s α _ hU
  have hp : Measurable (fun z : Vector r × Ω => z.1 j * z.1 k - if j = k then (1 : ℝ) else 0) :=
    (((measurable_pi_apply j).comp measurable_fst).mul
      ((measurable_pi_apply k).comp measurable_fst)).sub measurable_const
  change StronglyMeasurable (fun ω => ∫ g : Vector r,
    (g j * g k - if j = k then (1 : ℝ) else 0) * selectorTupleWeight s α (A.mulVec g + V ω) ∂standardGaussian r)
  exact (hp.mul hw).stronglyMeasurable.integral_prod_left'

def gaussianScoreEntryBudget (r : ℕ) (j k : Fin r) : ℝ :=
  ∫ g : Vector r, |g j * g k - if j = k then (1 : ℝ) else 0| ∂standardGaussian r

theorem abs_selectorGaussianScore_entry_le {Ω : Type*} [MeasurableSpace Ω] {p r q : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (α : Fin q → Face p) (ω : Ω) (j k : Fin r) :
    |selectorGaussianScore s A V α ω j k| ≤ gaussianScoreEntryBudget r j k := by
  let w : Vector r → ℝ := fun g => selectorTupleWeight s α (A.mulVec g + V ω)
  have hw : Measurable w := measurable_selectorTupleWeight_comp s α _
    ((continuous_const.matrix_mulVec continuous_id).measurable.add_const (V ω))
  have hwb (g : Vector r) : |w g| ≤ 1 := by
    rw [abs_of_nonneg (selectorTupleWeight_nonneg s α _)]
    exact selectorTupleWeight_le_one s α _
  have hi := (standardGaussian_integrable_weighted_product w hw hwb j k).sub
    ((standardGaussian_integrable_bounded_weight w hw hwb).const_mul (if j = k then 1 else 0))
  have hpoly := (standardGaussian_integrable_coordinate_product r j k).sub
    (integrable_const (μ := standardGaussian r) (if j = k then (1 : ℝ) else 0))
  change |∫ g, (g j * g k - if j = k then (1 : ℝ) else 0) * w g ∂standardGaussian r| ≤ _
  apply abs_integral_le_integral_abs.trans
  have hi' : Integrable (fun g => (g j * g k - if j = k then (1 : ℝ) else 0) * w g) (standardGaussian r) := by
    convert hi using 1
    funext g
    simp only [Pi.sub_apply]
    ring
  apply integral_mono hi'.abs hpoly.abs
  intro g
  change |(g j * g k - if j = k then (1 : ℝ) else 0) * w g| ≤
    |g j * g k - if j = k then (1 : ℝ) else 0|
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (hwb g) (abs_nonneg _)).trans_eq (mul_one _)

/-- One complete restoration-series matrix order, averaged against the
unconditional common base. Its operator coefficient is the genuine
conditional expectation, with all moment products justified. -/
theorem conditional_restoration_matrix_order_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {C T : ℝ}
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ A V C T)
    (q : ℕ) (hq : 1 ≤ q) {b : ℝ} (hb : 0 ≤ b)
    (B : (Fin q → Face p) → Ω → Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ α j k, Integrable (fun ω => B α ω j k) μ)
    (hbudget : ∀ α, ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H (B α) ω) u| ≤ b * vectorNormSq u) :
    Integrable (fun ω => ∑ α, Matrix.trace (B α ω * selectorGaussianScore s A V α ω)) μ ∧
    |∫ ω, ∑ α, Matrix.trace (B α ω * selectorGaussianScore s A V α ω) ∂μ| ≤
      b * C ^ (q + 1) * T := by
  have hscoreH (α : Fin q → Face p) (j k : Fin r) :
      StronglyMeasurable[H] (fun ω => selectorGaussianScore s A V α ω j k) :=
    stronglyMeasurable_selectorGaussianScore_entry (mΩ := H) s A V hV α j k
  have hprod (α : Fin q → Face p) (j k : Fin r) : Integrable
      (fun ω => B α ω j k * selectorGaussianScore s A V α ω k j) μ := by
    have hi := (hB α j k).bdd_mul' ((hscoreH α k j).mono hH).aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs]
        exact abs_selectorGaussianScore_entry_le s A V α ω k j))
    simpa only [mul_comm] using hi
  have he (α : Fin q → Face p) := integral_trace_conditionalMatrixAverage_eq (mΩ := mΩ)
    μ H hH (B α) (fun ω => selectorGaussianScore s A V α ω) (hB α) (hscoreH α) (hprod α)
  have hmC (α : Fin q → Face p) (j k : Fin r) : @Measurable Ω ℝ mΩ inferInstance
      (fun ω => conditionalMatrixAverage (mΩ := mΩ) μ H (B α) ω j k) := by
    exact (stronglyMeasurable_condExp.mono hH).measurable
  have hmat := averagedSelectorMatrixEstimate_ae_bound (mΩ := mΩ) s μ A V hmatrix q hq hb
    (fun α => conditionalMatrixAverage (mΩ := mΩ) μ H (B α)) hmC hbudget
  have hiB := integrable_finset_sum Finset.univ (fun α _ => (he α).1)
  have hiC := integrable_finset_sum Finset.univ (fun α _ => (he α).2.1)
  refine ⟨hiB, ?_⟩
  have hEq : (∫ ω, ∑ α, Matrix.trace (B α ω * selectorGaussianScore s A V α ω) ∂μ) =
      ∫ ω, ∑ α, Matrix.trace (conditionalMatrixAverage (mΩ := mΩ) μ H (B α) ω * selectorGaussianScore s A V α ω) ∂μ := by
    rw [integral_finset_sum Finset.univ (fun α _ => (he α).1),
      integral_finset_sum Finset.univ (fun α _ => (he α).2.1)]
    exact Finset.sum_congr rfl (fun α _ => (he α).2.2)
  rw [hEq]
  apply abs_integral_le_integral_abs.trans
  exact (integral_mono hiC.abs hmat.1 (fun ω => Finset.abs_sum_le_sum_abs _ _)).trans hmat.2

end

end RectangleCLT.Companion.SplitV4
