import RectangleCLTCompanion.SplitV4.SymmetricNuclearNorm
import RectangleCLTCompanion.SelectorMatrixBound
import RectangleCLTCompanion.SignedSurfaceScoreExpansion
import RectangleCLTCompanion.GammaMixture

/-! Genuine nuclear-norm reductions for the actual logistic selector
matrices in Appendix B.4. Quantitative closure here displays its signed
aggregate-trace input explicitly; it is not the completed B.4 theorem until
the separate averaged hard-threshold estimate discharges that input.
-/

open MeasureTheory Set
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {p r k : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Actual Gaussian score matrices are real symmetric; their nuclear norm
therefore equals the sum of absolute eigenvalues proved in the support file. -/
theorem weightedScore_isHermitian (w : Vector r → ℝ) :
    (weightedScore (standardGaussian r) id w).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext j l
  unfold weightedScore
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    simp only [Matrix.transpose_apply, id_eq]
    by_cases h : j = l
    · subst l; rfl
    · simp only [if_neg h, if_neg (Ne.symm h)]
      ring)

theorem selectorGaussianScore_isHermitian (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (α : Fin k → Face p) (ω : Ω) : (selectorGaussianScore s A V α ω).IsHermitian :=
  weightedScore_isHermitian _

/-- The actual nuclear norm, rather than a named trace-duality premise,
is bounded by mean energy minus the signed score trace. Checked Prékopa
covariance contraction is already part of the selector reduction used here. -/
theorem selectorWeight_nuclear_reduction (s : FaceSmoother p)
    (α : Fin k → Face p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    symmetricNuclearNorm (weightedScore (standardGaussian r) id
      (fun g => selectorWeight s α (A.mulVec g + v))) ≤
      2 * weightMass (standardGaussian r) (fun g => selectorWeight s α (A.mulVec g + v)) *
        vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α (A.mulVec g + v))) -
      Matrix.trace (weightedScore (standardGaussian r) id
        (fun g => selectorWeight s α (A.mulVec g + v))) := by
  apply csSup_le (symmetricTrace_values_nonempty _)
  rintro t ⟨B, hB, rfl⟩
  have hh := selectorWeight_trace_reduction s α A v B (b := 1)
    (fun z => by simpa only [one_mul] using hB.2.1 z)
  exact (le_abs_self _).trans (by simpa only [one_mul] using hh)

theorem sum_selectorWeight_nuclear_reduction (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    (∑ α : Fin k → Face p, symmetricNuclearNorm (weightedScore (standardGaussian r) id
      (fun g => selectorWeight s α (A.mulVec g + v)))) ≤
      2 * (∑ α : Fin k → Face p,
        weightMass (standardGaussian r) (fun g => selectorWeight s α (A.mulVec g + v)) *
          vectorNormSq (weightMean (standardGaussian r) id
            (fun g => selectorWeight s α (A.mulVec g + v)))) -
        ∑ α : Fin k → Face p, Matrix.trace (weightedScore (standardGaussian r) id
          (fun g => selectorWeight s α (A.mulVec g + v))) := by
  have hh := Finset.sum_le_sum (fun (α : Fin k → Face p) (_ : α ∈ Finset.univ) =>
    selectorWeight_nuclear_reduction s α A v)
  simpa only [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc] using hh

theorem measurable_selectorGaussianScore_nuclear (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (α : Fin k → Face p) : Measurable (fun ω => symmetricNuclearNorm (selectorGaussianScore s A V α ω)) := by
  have hc : Continuous (fun M : Fin r → Fin r → ℝ => symmetricNuclearNorm M) :=
    continuous_symmetricNuclearNorm
  have hm : Measurable (fun ω => fun j l => selectorGaussianScore s A V α ω j l) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _
      (fun l => measurable_selectorGaussianScore_entry s A V hV α j l))
  exact hc.measurable.comp hm

theorem integrable_selector_mean_energy_sum (ν : Measure Ω) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) :
    Integrable (fun ω => ∑ α : Fin k → Face p,
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

theorem integrable_selector_signed_trace_sum (ν : Measure Ω) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) :
    Integrable (fun ω => ∑ α : Fin k → Face p, Matrix.trace (selectorGaussianScore s A V α ω)) ν :=
  integrable_finset_sum Finset.univ (fun α _ => integrable_selectorGaussianScore_trace ν s A V hV α)

theorem integrable_selector_nuclear_sum (ν : Measure Ω) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) :
    Integrable (fun ω => ∑ α : Fin k → Face p, symmetricNuclearNorm (selectorGaussianScore s A V α ω)) ν := by
  apply (((integrable_selector_mean_energy_sum ν s A V hV).const_mul 2).sub
    (integrable_selector_signed_trace_sum ν s A V hV)).mono'
    (Finset.measurable_sum _ (fun α _ => measurable_selectorGaussianScore_nuclear s A V hV α)).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun α _ => symmetricNuclearNorm_nonneg _))]
    simpa only [selectorGaussianScore, selectorTupleWeight, selectorWeight] using
      sum_selectorWeight_nuclear_reduction (k := k) s A (V ω))

/-- The complete matrix reduction under displayed mean and signed trace
budgets. In particular, the signed trace is summed before any absolute value
is taken; it is never replaced by a sum of absolute traces. -/
theorem integral_selector_nuclear_sum_le (ν : Measure Ω) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) {K T : ℝ}
    (hmean : (∫ ω, ∑ α : Fin k → Face p,
      weightMass (standardGaussian r) (fun g => selectorWeight s α (A.mulVec g + V ω)) *
        vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α (A.mulVec g + V ω))) ∂ν) ≤ K)
    (htrace : -(∫ ω, ∑ α : Fin k → Face p,
      Matrix.trace (selectorGaussianScore s A V α ω) ∂ν) ≤ T) :
    (∫ ω, ∑ α : Fin k → Face p, symmetricNuclearNorm (selectorGaussianScore s A V α ω) ∂ν) ≤
      2 * K + T := by
  have hE := integrable_selector_mean_energy_sum (k := k) ν s A V hV
  have hT := integrable_selector_signed_trace_sum (k := k) ν s A V hV
  have hh := integral_mono (integrable_selector_nuclear_sum ν s A V hV)
    ((hE.const_mul 2).sub hT) (fun ω => by
      simpa only [selectorGaussianScore, selectorTupleWeight, selectorWeight] using
        sum_selectorWeight_nuclear_reduction (k := k) s A (V ω))
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (hE.const_mul 2) hT, integral_const_mul] at hh
  linarith

/-- The ordered selector sum is exactly the single signed radial score
with weight `F θ^k`. This is the cancellation needed for the Gamma bridge. -/
theorem logistic_signed_trace_aggregate (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (k : ℕ) :
    (∑ α : Fin k → Face p, Matrix.trace (weightedScore (standardGaussian r) id
      (fun g => selectorWeight s α (A.mulVec g + v)))) =
      ∫ g, (vectorNormSq g - (r : ℝ)) *
        (s.F (A.mulVec g + v) * s.theta (A.mulVec g + v) ^ k) ∂standardGaussian r :=
  SignedSurface.sum_selectorWeight_trace_eq_gaussianSelectorTrace s A v k

theorem logistic_matrix_order_constant_le {D : ℝ} (hD : 0 ≤ D) (q : ℕ) :
    2 * (Real.exp (13 / 2 : ℝ) + 8) * (q : ℝ) + D ^ (q + 1) ≤
      selectorMatrixConstant D ^ (q + 1) := by
  let a : ℝ := 2 * (Real.exp (13 / 2 : ℝ) + 8) + 2
  have ha : 2 ≤ a := by dsimp only [a]; linarith [Real.exp_nonneg (13 / 2 : ℝ)]
  have hq : (q : ℝ) ≤ (2 : ℝ) ^ q := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, div_one] using
      Nat.cast_le_pow_div_sub (show (1 : ℝ) < 2 by norm_num) q
  have hqa : (q : ℝ) ≤ a ^ q := hq.trans (pow_le_pow_left₀ (by norm_num) ha q)
  have hlin : 2 * (Real.exp (13 / 2 : ℝ) + 8) * (q : ℝ) ≤ a ^ (q + 1) := by
    calc
      _ ≤ a * (q : ℝ) := mul_le_mul_of_nonneg_right (by dsimp [a]; linarith) (Nat.cast_nonneg q)
      _ ≤ a * a ^ q := mul_le_mul_of_nonneg_left hqa (by linarith)
      _ = _ := by rw [pow_succ]; ring
  exact (add_le_add_right hlin _).trans (by
    simpa only [selectorMatrixConstant, a] using
      pow_add_pow_le (show 0 ≤ a by linarith) hD (show q + 1 ≠ 0 by omega))

/-- Quantitative nuclear-norm closure of the genuine selector reduction.
Its transition and signed aggregate-trace budgets are explicit inputs, to be
discharged from the paper's base concentration and the separate B.5 theorem.
This theorem does not assume individual absolute score-trace estimates. -/
theorem logisticMatrixEstimate_of_transition_and_signed_trace
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) {h M D : ℝ}
    (hM : 0 < M) (hD : 0 ≤ D) (hbound : TransitionMassBound ν V h M)
    (s : FaceSmoother p) (hs : s.bandwidth = h) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin r) ℝ) (hunit : ∀ j, vectorNormSq (A j) = 1) (σ : ℝ)
    (htrace : ∀ q : ℕ, 1 ≤ q →
      -(∫ ω, ∑ α : Fin q → Face p,
        Matrix.trace (selectorGaussianScore s (σ • A) V α ω) ∂ν) ≤
          D ^ (q + 1) * (M * dimensionLog p))
    (q : ℕ) (hq : 1 ≤ q) :
    (∫ ω, ∑ α : Fin q → Face p,
      symmetricNuclearNorm (selectorGaussianScore s (σ • A) V α ω) ∂ν) ≤
      selectorMatrixConstant D ^ (q + 1) * (M * dimensionLog p) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have hm := integral_selectorMeanEnergy_le (k := k) ν V hV hM hbound s hs hp A hunit σ
  have ht := htrace (k + 1) (by omega)
  have hh := integral_selector_nuclear_sum_le ν s (σ • A) V hV hm ht
  have hL : 0 ≤ M * dimensionLog p :=
    mul_nonneg hM.le (zero_le_one.trans (log_exp_mul_nat_ge_one hp))
  calc
    _ ≤ 2 * ((Real.exp (13 / 2 : ℝ) + 8) * (k + 1 : ℝ) * M * dimensionLog p) +
        D ^ (k + 1 + 1) * (M * dimensionLog p) := hh
    _ = (2 * (Real.exp (13 / 2 : ℝ) + 8) * ((k + 1 : ℕ) : ℝ) +
        D ^ (k + 1 + 1)) * (M * dimensionLog p) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (logistic_matrix_order_constant_le hD (k + 1)) hL

/-- Every finite normal family is represented by activating only the upper
coordinate faces after the exact face projection. Negative coordinate faces
are omitted; no opposite-pair property of the normals is required here. -/
def upperFaceSmoother {m : ℕ} (a : Vector m) (h : ℝ) (hh : 0 < h) : FaceSmoother m where
  faces := Finset.univ.filter (fun f => f.2 = true)
  offsets := fun f => a f.1
  bandwidth := h
  bandwidth_pos := hh

def logisticNullWeight {m r : ℕ} (u : Fin m → Vector r) (a : Vector m) (h : ℝ) (x : Vector r) : ℝ :=
  1 / (1 + ∑ j, Real.exp ((faceDot (u j) x - a j) / h))

def logisticFaceWeight {m r : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h : ℝ) (x : Vector r) (j : Fin m) : ℝ :=
  Real.exp ((faceDot (u j) x - a j) / h) * logisticNullWeight u a h x

def logisticTupleWeight {m r k : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h : ℝ) (α : Fin k → Fin m) (x : Vector r) : ℝ :=
  logisticNullWeight u a h x * ∏ i, logisticFaceWeight u a h x (α i)

theorem upperFaceSmoother_total {m r : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h : ℝ) (hh : 0 < h) (x : Vector r) :
    (((upperFaceSmoother a h hh).weights (Matrix.mulVec u x)).T) =
      ∑ j, Real.exp ((faceDot (u j) x - a j) / h) := by
  simp [FaceWeights.T, FaceSmoother.weights, upperFaceSmoother,
    Fintype.sum_prod_type, Fintype.sum_bool, FaceSmoother.faceScore,
    FaceSmoother.normalDot, Matrix.mulVec, dotProduct, faceDot]

theorem upperFaceSmoother_F {m r : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h : ℝ) (hh : 0 < h) (x : Vector r) :
    (upperFaceSmoother a h hh).F (Matrix.mulVec u x) = logisticNullWeight u a h x := by
  change 1 / (1 + _) = _
  rw [upperFaceSmoother_total]
  rfl

theorem upperFaceSmoother_pi {m r : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h : ℝ) (hh : 0 < h) (x : Vector r) (j : Fin m) :
    (upperFaceSmoother a h hh).pi (Matrix.mulVec u x) (j, true) = logisticFaceWeight u a h x j := by
  change (((upperFaceSmoother a h hh).weights (Matrix.mulVec u x)).weight (j, true)) /
    (1 + ((upperFaceSmoother a h hh).weights (Matrix.mulVec u x)).T) = _
  rw [upperFaceSmoother_total]
  simp [FaceSmoother.weights, upperFaceSmoother, Finset.mem_filter, Finset.mem_univ,
    FaceSmoother.faceScore, FaceSmoother.normalDot,
    logisticFaceWeight, logisticNullWeight, Matrix.mulVec, dotProduct, faceDot,
    div_eq_mul_inv, one_mul]

theorem upperFaceSmoother_selectorWeight {m r k : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h : ℝ) (hh : 0 < h) (α : Fin k → Fin m) (x : Vector r) :
    selectorWeight (upperFaceSmoother a h hh) (fun i => (α i, true)) (Matrix.mulVec u x) =
      logisticTupleWeight u a h α x := by
  simp only [selectorWeight, upperFaceSmoother_F, upperFaceSmoother_pi, logisticTupleWeight]

/-- Exact Gamma-mixture reconstruction for any genuine integrable signed
test. In particular, this applies to the radial Gaussian score before any
absolute value is taken. The clock law and all Fubini hypotheses are actual.
-/
theorem gammaMixture_integral_signed_test
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (P : Ω → ℝ) (hP : Integrable P μ) (s : FaceSmoother p) (a : ℕ) :
    (∫ ω, P ω * s.F (V ω) ^ (a + 1) ∂μ) =
      ∫ e, ∫ ω, {ω | (s.randomRectangle e).Inside (V ω)}.indicator P ω
        ∂μ ∂gammaRectangleLaw p a := by
  let E : Set (Ω × (ℝ × (Face p → ℝ))) :=
    {z | (s.randomRectangle z.2).Inside (V z.1)}
  have hE : MeasurableSet E := by
    simp only [E, FaceSmoother.Inside, FaceSmoother.faceScore, FaceSmoother.randomRectangle,
      setOf_forall]
    apply MeasurableSet.iInter
    intro f
    apply MeasurableSet.iInter
    intro _hf
    apply measurableSet_le
    · have hlog : Measurable (fun z : Ω × (ℝ × (Face p → ℝ)) => Real.log (z.2.2 f / z.2.1)) := by
        fun_prop
      exact ((FaceSmoother.continuous_normalDot f).measurable.comp (hV.comp measurable_fst)).sub
        (measurable_const.add (measurable_const.mul hlog))
    · exact measurable_const
  let I : Ω × (ℝ × (Face p → ℝ)) → ℝ := E.indicator (fun z => P z.1)
  have hiP : Integrable (fun z : Ω × (ℝ × (Face p → ℝ)) => P z.1)
      (μ.prod (gammaRectangleLaw p a)) := by
    simpa only [mul_one] using hP.mul_prod (integrable_const (1 : ℝ))
  have hi : Integrable I (μ.prod (gammaRectangleLaw p a)) := hiP.indicator hE
  have hinner (ω : Ω) : (∫ e, I (ω, e) ∂gammaRectangleLaw p a) =
      P ω * s.F (V ω) ^ (a + 1) := by
    change (∫ e, {e | (s.randomRectangle e).Inside (V ω)}.indicator
      (fun _ => P ω) e ∂gammaRectangleLaw p a) = _
    have hS : MeasurableSet {e | (s.randomRectangle e).Inside (V ω)} :=
      hE.preimage (measurable_const.prodMk measurable_id)
    rw [integral_indicator_const (P ω) hS, smul_eq_mul,
      ← s.F_pow_eq_gamma_randomRectangle_probability]
    ring
  calc
    _ = ∫ ω, ∫ e, I (ω, e) ∂gammaRectangleLaw p a ∂μ :=
      integral_congr_ae (ae_of_all _ (fun ω => (hinner ω).symm))
    _ = ∫ e, ∫ ω, I (ω, e) ∂μ ∂gammaRectangleLaw p a := integral_integral_swap hi
    _ = _ := rfl

def logisticGaussianScore {m r k : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h σ : ℝ) (α : Fin k → Fin m) (x : Vector r) : Matrix (Fin r) (Fin r) ℝ :=
  weightedScore (standardGaussian r) id (fun g => logisticTupleWeight u a h α (x + σ • g))

theorem logisticGaussianScore_eq_upper_selector {m r k : ℕ} (u : Fin m → Vector r)
    (a : Vector m) (h : ℝ) (hh : 0 < h) (σ : ℝ) (α : Fin k → Fin m) (x : Vector r) :
    logisticGaussianScore u a h σ α x =
      selectorGaussianScore (upperFaceSmoother a h hh) (σ • u)
        (Matrix.mulVec u) (fun i => (α i, true)) x := by
  unfold logisticGaussianScore selectorGaussianScore
  apply congrArg (fun w : Vector r → ℝ => weightedScore (standardGaussian r) id w)
  funext g
  change logisticTupleWeight u a h α (x + σ • g) =
    selectorWeight (upperFaceSmoother a h hh) (fun i => (α i, true))
      (Matrix.mulVec (σ • u) g + Matrix.mulVec u x)
  rw [← upperFaceSmoother_selectorWeight u a h hh α]
  congr 1
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.smul_mulVec_assoc]
  exact add_comm _ _

theorem sum_upper_tuples_le_all_faces {m k : ℕ}
    (f : (Fin k → Face m) → ℝ) (hf : ∀ α, 0 ≤ f α) :
    (∑ α : Fin k → Fin m, f (fun i => (α i, true))) ≤ ∑ β : Fin k → Face m, f β := by
  let e : (Fin k → Fin m) → (Fin k → Face m) := fun α i => (α i, true)
  have he : Function.Injective e := by
    intro α β h
    funext i
    exact congrArg Prod.fst (congrFun h i)
  calc
    _ = ∑ β ∈ Finset.univ.image e, f β := by
      symm
      exact Finset.sum_image (fun _ _ _ _ h => he h)
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg hf

set_option maxHeartbeats 800000 in
theorem logisticGaussianScore_nuclear_sum_le_upper_selector {m r k : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h : ℝ) (hh : 0 < h) (σ : ℝ) (x : Vector r) :
    (∑ α : Fin k → Fin m, symmetricNuclearNorm (logisticGaussianScore u a h σ α x)) ≤
      ∑ β : Fin k → Face m, symmetricNuclearNorm
        (selectorGaussianScore (upperFaceSmoother a h hh) (σ • u) (Matrix.mulVec u) β x) := by
  calc
    _ = ∑ α : Fin k → Fin m, symmetricNuclearNorm
        (selectorGaussianScore (upperFaceSmoother a h hh) (σ • u) (Matrix.mulVec u)
          (fun i => (α i, true)) x) := by
      exact Finset.sum_congr rfl (fun α _ => congrArg
        (fun M : Matrix (Fin r) (Fin r) ℝ => symmetricNuclearNorm M)
        (logisticGaussianScore_eq_upper_selector u a h hh σ α x))
    _ ≤ _ := sum_upper_tuples_le_all_faces (m := m) (k := k)
      (fun β : Fin k → Face m => symmetricNuclearNorm
        (selectorGaussianScore (upperFaceSmoother a h hh) (σ • u) (Matrix.mulVec u) β x))
      (fun β => symmetricNuclearNorm_nonneg
        (selectorGaussianScore (upperFaceSmoother a h hh) (σ • u) (Matrix.mulVec u) β x))

end

end RectangleCLT.Companion.SplitV4
