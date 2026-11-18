import RectangleCLTArxivV1.SupplementalGScoreRestoration
import RectangleCLTCompanion.SplitV4.RestorationConditionalAveraging

/-! The common-base signed cubic matrices and conditional trace step in
Appendix H. Quantitative geometric matrix sums remain explicit inputs;
the genuine conditional expectation and all integrability are proved. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The signed Gaussian cubic matrix. The unit normal is independent of
the evaluation matrix, so replacing A by σA does not rescale H3. -/
def hFourthCubicGaussianScore {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (U : Face p → Vector r) (V : Ω → Vector p) (α : Fin (K+1) → Face p)
    (ω : Ω) : Matrix (Fin r) (Fin r) ℝ :=
  fun j k => ∫ g, capThirdHermiteMatrix (U (α 0)) g j k*
    selectorTupleWeight s α (A.mulVec g+V ω) ∂standardGaussian r

theorem hFourthCubicGaussianScore_integrable_entry {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (U : Face p → Vector r) (V : Ω → Vector p) (α : Fin (K+1) → Face p)
    (ω : Ω) (j k : Fin r) :
    Integrable (fun g => capThirdHermiteMatrix (U (α 0)) g j k*
      selectorTupleWeight s α (A.mulVec g+V ω)) (standardGaussian r) := by
  have hw : Measurable (fun g : Vector r => selectorTupleWeight s α (A.mulVec g+V ω)) :=
    measurable_selectorTupleWeight_comp s α _
      ((continuous_const.matrix_mulVec continuous_id).measurable.add_const (V ω))
  have hi := (capThirdHermiteMatrix_integrable (U (α 0)) j k).bdd_mul'
    hw.aestronglyMeasurable
    (ae_of_all (standardGaussian r) (fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (selectorTupleWeight_nonneg s α _)]
      exact selectorTupleWeight_le_one s α _))
  simpa only [mul_comm] using hi

theorem stronglyMeasurable_hFourthCubicGaussianScore_entry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (U : Face p → Vector r) (V : Ω → Vector p) (hV : Measurable V)
    (α : Fin (K+1) → Face p) (j k : Fin r) :
    StronglyMeasurable (fun ω => hFourthCubicGaussianScore s A U V α ω j k) := by
  have hpoint : Measurable (fun z : Vector r × Ω => A.mulVec z.1+V z.2) :=
    ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_fst).add
      (hV.comp measurable_snd)
  have hpoly : Measurable (fun z : Vector r × Ω =>
      capThirdHermiteMatrix (U (α 0)) z.1 j k) := by
    unfold capThirdHermiteMatrix faceDot
    fun_prop
  exact (hpoly.mul (measurable_selectorTupleWeight_comp s α _ hpoint)).stronglyMeasurable.integral_prod_left'

theorem abs_hFourthCubicGaussianScore_entry_le {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (U : Face p → Vector r) (V : Ω → Vector p) (α : Fin (K+1) → Face p)
    (ω : Ω) (j k : Fin r) :
    |hFourthCubicGaussianScore s A U V α ω j k| ≤
      ∫ g, |capThirdHermiteMatrix (U (α 0)) g j k| ∂standardGaussian r := by
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (hFourthCubicGaussianScore_integrable_entry s A U V α ω j k).abs
    (capThirdHermiteMatrix_integrable _ j k).abs
  intro g
  dsimp only
  rw [abs_mul,abs_of_nonneg (selectorTupleWeight_nonneg s α _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (selectorTupleWeight_le_one s α _)

theorem hFourthCubicGaussianScore_isHermitian {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (U : Face p → Vector r) (V : Ω → Vector p) (α : Fin (K+1) → Face p) (ω : Ω) :
    (hFourthCubicGaussianScore s A U V α ω).IsHermitian := by
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  ext j k
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    have hs := congrFun (congrFun (capThirdHermiteMatrix_symmetric (U (α 0)) g) j) k
    change capThirdHermiteMatrix (U (α 0)) g k j=capThirdHermiteMatrix (U (α 0)) g j k at hs
    rw [hs])

/-- Coarse finite entry envelopes justify nuclear integrability; they are
not used in the final rank-free estimate. -/
theorem hFourth_integrable_nuclear_of_entry_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : Ω → Matrix (Fin r) (Fin r) ℝ)
    (hM : ∀ j k, Measurable (fun ω => M ω j k))
    (D : Fin r → Fin r → ℝ) (hD : ∀ ω j k, |M ω j k| ≤ D j k) :
    Integrable (fun ω => symmetricNuclearNorm (M ω)) μ := by
  have hm : Measurable (fun ω => fun j k => M ω j k) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (hM j))
  have hn : Continuous (fun M : Fin r → Fin r → ℝ => symmetricNuclearNorm M) :=
    continuous_symmetricNuclearNorm
  apply (integrable_const (μ := μ) (∑ j, ∑ k, D k j)).mono'
    (hn.measurable.comp hm).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (symmetricNuclearNorm_nonneg _)]
    exact (symmetricNuclearNorm_le_entrySum _).trans
      (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hD ω k j))))

theorem hFourthCubicGaussianScore_nuclear_integrable
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : Measurable V) (α : Fin (K+1) → Face p) :
    Integrable (fun ω => symmetricNuclearNorm (hFourthCubicGaussianScore s A U V α ω)) μ :=
  hFourth_integrable_nuclear_of_entry_bounds μ _
    (fun j k => (stronglyMeasurable_hFourthCubicGaussianScore_entry s A U V hV α j k).measurable)
    _ (fun ω j k => abs_hFourthCubicGaussianScore_entry_le s A U V α ω j k)

/-- A general finite family of actual common-base matrices can be paired
with the genuine conditional coefficient before taking a nuclear norm.
The only quantitative supplier is the displayed unconditional nuclear sum. -/
theorem hFourth_conditional_matrix_sum_bound
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] {r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (M B : ι → Ω → Matrix (Fin r) (Fin r) ℝ)
    (hM : ∀ a j k, StronglyMeasurable[H] (fun ω => M a ω j k))
    (hMsym : ∀ a ω, (M a ω).IsHermitian)
    (D : ι → Fin r → Fin r → ℝ) (hD : ∀ a ω j k, |M a ω j k| ≤ D a j k)
    (hB : ∀ a j k, Integrable (fun ω => B a ω j k) μ)
    {b T : ℝ} (hb : 0 ≤ b)
    (hbudget : ∀ a, ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H (B a) ω) u| ≤ b*vectorNormSq u)
    (hsupplier : (∫ ω, ∑ a, symmetricNuclearNorm (M a ω) ∂μ) ≤ T) :
    Integrable (fun ω => ∑ a, Matrix.trace (B a ω*M a ω)) μ ∧
      |∫ ω, ∑ a, Matrix.trace (B a ω*M a ω) ∂μ| ≤ b*T := by
  classical
  letI : MeasurableSpace Ω := mΩ
  have hprod (a : ι) (j k : Fin r) : Integrable
      (fun ω => B a ω j k*M a ω k j) μ := by
    simpa only [mul_comm] using (hB a j k).bdd_mul' ((hM a k j).mono hH).aestronglyMeasurable
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact hD a ω k j))
  have he (a : ι) := integral_trace_conditionalMatrixAverage_eq (mΩ := mΩ)
    μ H hH (B a) (M a) (hB a) (hM a) (hprod a)
  have hiB := integrable_finset_sum Finset.univ (fun a _ => (he a).1)
  have hiC := integrable_finset_sum Finset.univ (fun a _ => (he a).2.1)
  have hiN := integrable_finset_sum Finset.univ (fun a _ =>
    hFourth_integrable_nuclear_of_entry_bounds (mΩ := mΩ) μ (M a)
      (fun j k => ((hM a j k).mono hH).measurable) (D a) (hD a))
  have heq : (∫ ω, ∑ a, Matrix.trace (B a ω*M a ω) ∂μ)=
      ∫ ω, ∑ a, Matrix.trace (conditionalMatrixAverage (mΩ := mΩ) μ H (B a) ω*M a ω) ∂μ := by
    rw [integral_finset_sum _ (fun a _ => (he a).1),
      integral_finset_sum _ (fun a _ => (he a).2.1)]
    exact Finset.sum_congr rfl (fun a _ => (he a).2.2)
  refine ⟨hiB, ?_⟩
  rw [heq]
  apply abs_integral_le_integral_abs.trans
  have hpoint : ∀ᵐ ω ∂μ,
      |∑ a, Matrix.trace (conditionalMatrixAverage (mΩ := mΩ) μ H (B a) ω*M a ω)| ≤
        b*∑ a, symmetricNuclearNorm (M a ω) := by
    filter_upwards [ae_all_iff.mpr hbudget] with ω hω
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ =>
      abs_trace_mul_le_nuclear_of_quadratic _ _ (hMsym a ω) (hω a))
  calc
    _ ≤ ∫ ω, b*∑ a, symmetricNuclearNorm (M a ω) ∂μ :=
      integral_mono_ae hiC.abs (hiN.const_mul b) hpoint
    _ = b*∫ ω, ∑ a, symmetricNuclearNorm (M a ω) ∂μ := integral_const_mul _ _
    _ ≤ b*T := mul_le_mul_of_nonneg_left hsupplier hb

end
end RectangleCLTArxivV1
