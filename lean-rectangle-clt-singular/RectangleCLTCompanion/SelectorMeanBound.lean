import RectangleCLTCompanion.SelectorConcentration
import RectangleCLTCompanion.SelectorProjectionMoment

/-! Averaged mean-energy bounds for actual Gaussian selector tuples. Shared
transition mass controls both selector and one-face reference masses, so the
entropy estimate contains no logarithm of the smoothing bandwidth. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

theorem integral_massEntropy_le_common_caps
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (p b : Ω → ℝ) (hp : Measurable p) (hb : Measurable b)
    (hp0 : ∀ ω, 0 ≤ p ω) (hpb : ∀ ω, p ω ≤ b ω)
    (hpi : Integrable p ν) (hbi : Integrable b ν)
    {M N : ℝ} (hM : 0 < M) (hN : 1 ≤ N)
    (hpcap : (∫ ω, p ω ∂ν) ≤ M) (hbcap : (∫ ω, b ω ∂ν) ≤ N * M) :
    (∫ ω, massEntropy (p ω) (b ω) ∂ν) ≤ M * (2 + Real.log N) := by
  by_cases hz : (∫ ω, p ω ∂ν) = 0
  · have hpz := (integral_eq_zero_iff_of_nonneg hp0 hpi).mp hz
    have he : (∫ ω, massEntropy (p ω) (b ω) ∂ν) = 0 := by
      have hzero : (fun ω => massEntropy (p ω) (b ω)) =ᵐ[ν] 0 := by
        filter_upwards [hpz] with ω hω
        simp only [massEntropy, hω, zero_mul, Pi.zero_apply]
      rw [integral_congr_ae hzero]
      simp only [Pi.zero_apply, integral_zero]
    rw [he]
    exact mul_nonneg hM.le (by linarith [Real.log_nonneg hN])
  · have hP : 0 < ∫ ω, p ω ∂ν :=
      lt_of_le_of_ne (integral_nonneg hp0) (Ne.symm hz)
    calc
      _ ≤ massEntropy (∫ ω, p ω ∂ν) (∫ ω, b ω ∂ν) :=
        integral_massEntropy_le ν p b hp hb hp0 hpb hpi hbi hP
      _ ≤ M * (1 * (1 + Real.log N) + 1) :=
        massEntropy_le_common_scale hP.le (integral_mono hpi hbi hpb) hM
          (le_refl 1) hN (by simpa only [one_mul] using hpcap)
          (by simpa only [one_mul] using hbcap)
      _ = _ := by ring

variable {p r k : ℕ}

def selectorFamilyMass (s : FaceSmoother p) (S : Finset (Fin (k + 1) → Face p))
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (v : Vector p) : ℝ :=
  ∑ α ∈ S, weightMass (standardGaussian r)
    (fun g => selectorWeight s α ((σ • A).mulVec g + v))

def selectorFamilyReferenceMass (s : FaceSmoother p) (S : Finset (Fin (k + 1) → Face p))
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (v : Vector p) : ℝ :=
  ∑ α ∈ S, ∫ g, oneFaceReference s (α 0) ((σ • A).mulVec g + v) ∂standardGaussian r

def selectorFamilyMeanEnergy (s : FaceSmoother p) (S : Finset (Fin (k + 1) → Face p))
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (v : Vector p) : ℝ :=
  ∑ α ∈ S, weightMass (standardGaussian r)
    (fun g => selectorWeight s α ((σ • A).mulVec g + v)) *
    vectorNormSq (weightMean (standardGaussian r) id
      (fun g => selectorWeight s α ((σ • A).mulVec g + v)))

def selectorFamilyNormalEnergy (s : FaceSmoother p) (S : Finset (Fin (k + 1) → Face p))
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (v : Vector p) : ℝ :=
  ∫ g, ∑ α ∈ S, selectorWeight s α ((σ • A).mulVec g + v) *
    (faceDot (selectorFaceNormal A (α 0)) g) ^ 2 ∂standardGaussian r

private theorem measurable_gaussian_base
    {Ω : Type*} [MeasurableSpace Ω] (V : Ω → Vector p) (hV : Measurable V)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) :
    Measurable (fun z : Ω × Vector r => (σ • A).mulVec z.2 + V z.1) :=
  (((continuous_const.matrix_mulVec continuous_id).measurable).comp measurable_snd).add
    (hV.comp measurable_fst)

private theorem integrable_selector_joint
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (α : Fin (k + 1) → Face p) :
    Integrable (fun z : Ω × Vector r => selectorWeight s α ((σ • A).mulVec z.2 + V z.1))
      (ν.prod (standardGaussian r)) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((continuous_selectorWeight s α).measurable.comp
      (measurable_gaussian_base V hV A σ)).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (selectorWeight_nonneg s α _)]
    exact selectorWeight_le_one s α _

private theorem continuous_oneFaceReference (s : FaceSmoother p) (f : Face p) :
    Continuous (oneFaceReference s f) := by
  unfold oneFaceReference
  have he := Real.continuous_exp.comp ((s.continuous_faceScore f).div_const s.bandwidth)
  exact he.div ((continuous_const.add he).pow 2) (fun x => by positivity)

private theorem integrable_reference_joint
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (f : Face p) :
    Integrable (fun z : Ω × Vector r => oneFaceReference s f ((σ • A).mulVec z.2 + V z.1))
      (ν.prod (standardGaussian r)) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((continuous_oneFaceReference s f).measurable.comp
      (measurable_gaussian_base V hV A σ)).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (oneFaceReference_bounds s f _).1]
    exact (oneFaceReference_bounds s f _).2

private theorem integrable_unit_test {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (f : Ω → ℝ) (hf : Measurable f)
    (hb : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) : Integrable f ν := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb ω).1]
    exact (hb ω).2

private theorem family_mass_properties
    {Ω ι : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (V : Ω → Vector p) (hV : Measurable V)
    (S : Finset ι) (f : ι → Vector p → ℝ)
    (hf : ∀ α ∈ S, Continuous (f α))
    (hb : ∀ α ∈ S, ∀ x, 0 ≤ f α x ∧ f α x ≤ 1)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) :
    Measurable (fun ω => ∑ α ∈ S, ∫ g, f α ((σ • A).mulVec g + V ω) ∂standardGaussian r) ∧
    Integrable (fun ω => ∑ α ∈ S, ∫ g, f α ((σ • A).mulVec g + V ω) ∂standardGaussian r) ν ∧
    (∫ ω, (∑ α ∈ S, ∫ g, f α ((σ • A).mulVec g + V ω) ∂standardGaussian r) ∂ν) =
      ∫ g, (∫ ω, ∑ α ∈ S, f α ((σ • A).mulVec g + V ω) ∂ν) ∂standardGaussian r := by
  have hm (α : ι) (hα : α ∈ S) :
      Measurable (fun z : Ω × Vector r => f α ((σ • A).mulVec z.2 + V z.1)) :=
    (hf α hα).measurable.comp (measurable_gaussian_base V hV A σ)
  have hi (α : ι) (hα : α ∈ S) :
      Integrable (fun z : Ω × Vector r => f α ((σ • A).mulVec z.2 + V z.1))
        (ν.prod (standardGaussian r)) :=
    integrable_unit_test _ _ (hm α hα) (fun z => hb α hα _)
  have hsum : Integrable (fun z : Ω × Vector r => ∑ α ∈ S,
      f α ((σ • A).mulVec z.2 + V z.1)) (ν.prod (standardGaussian r)) :=
    integrable_finset_sum S hi
  have heq (ω : Ω) : (∑ α ∈ S, ∫ g, f α ((σ • A).mulVec g + V ω) ∂standardGaussian r) =
      ∫ g, ∑ α ∈ S, f α ((σ • A).mulVec g + V ω) ∂standardGaussian r := by
    symm
    apply integral_finset_sum
    intro α hα
    exact integrable_unit_test _ _ ((hf α hα).measurable.comp
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const).measurable)
      (fun _g => hb α hα _)
  refine ⟨Finset.measurable_sum S (fun α hα =>
    (hm α hα).stronglyMeasurable.integral_prod_right'.measurable), ?_, ?_⟩
  · simpa only [heq] using hsum.integral_prod_left
  · simp_rw [heq]
    exact integral_integral_swap (f := fun ω g => ∑ α ∈ S,
      f α ((σ • A).mulVec g + V ω)) hsum

theorem selectorFamilyMass_nonneg (s : FaceSmoother p)
    (S : Finset (Fin (k + 1) → Face p)) (A : Matrix (Fin p) (Fin r) ℝ)
    (σ : ℝ) (v : Vector p) : 0 ≤ selectorFamilyMass s S A σ v :=
  Finset.sum_nonneg (fun α _ => integral_nonneg (fun _g => selectorWeight_nonneg s α _))

theorem selectorFamilyMass_le_reference (s : FaceSmoother p)
    (S : Finset (Fin (k + 1) → Face p)) (A : Matrix (Fin p) (Fin r) ℝ)
    (σ : ℝ) (v : Vector p) :
    selectorFamilyMass s S A σ v ≤ selectorFamilyReferenceMass s S A σ v := by
  apply Finset.sum_le_sum
  intro α _
  exact integral_mono (selectorWeight_affine_moments s α (σ • A) v).1
    (integrable_oneFaceReference (standardGaussian r) s (α 0)
      (fun g => (σ • A).mulVec g + v)
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const).measurable)
    (fun g => selectorWeight_le_oneFaceReference s α _)

theorem TransitionMassBound.selectorFamily
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {V : Ω → Vector p} (hV : Measurable V) {h M : ℝ}
    (hbound : TransitionMassBound ν V h M) (s : FaceSmoother p) (hs : s.bandwidth = h)
    (S : Finset (Fin (k + 1) → Face p)) (z : Vector p) :
    (∫ ω, ∑ α ∈ S, selectorWeight s α (V ω + z) ∂ν) ≤ M := by
  have hi (α : Fin (k + 1) → Face p) :
      Integrable (fun ω => selectorWeight s α (V ω + z)) ν :=
    integrable_unit_test _ _ ((continuous_selectorWeight s α).measurable.comp (hV.add_const z))
      (fun ω => ⟨selectorWeight_nonneg s α _, selectorWeight_le_one s α _⟩)
  exact (integral_mono (integrable_finset_sum S (fun α _ => hi α))
    (integrable_finset_sum Finset.univ (fun α _ => hi α))
    (fun ω => Finset.sum_le_univ_sum_of_nonneg (fun α => selectorWeight_nonneg s α _))).trans
    (hbound.selectorSum hV s hs k z)

theorem integral_selectorFamilyMass_le
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) {h M : ℝ}
    (hbound : TransitionMassBound ν V h M) (s : FaceSmoother p) (hs : s.bandwidth = h)
    (S : Finset (Fin (k + 1) → Face p)) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) :
    (∫ ω, selectorFamilyMass s S A σ (V ω) ∂ν) ≤ M := by
  have hp := family_mass_properties ν V hV S (selectorWeight s)
    (fun α _ => continuous_selectorWeight s α)
    (fun α _ x => ⟨selectorWeight_nonneg s α x, selectorWeight_le_one s α x⟩) A σ
  change (∫ ω, ∑ α ∈ S, ∫ g, selectorWeight s α ((σ • A).mulVec g + V ω)
    ∂standardGaussian r ∂ν) ≤ M
  rw [hp.2.2]
  have hi := (integrable_finset_sum S (fun α _ => integrable_selector_joint ν V hV s A σ α)).integral_prod_right
  calc
    _ ≤ ∫ _g : Vector r, M ∂standardGaussian r := integral_mono hi (integrable_const _) (fun g => by
      simpa only [add_comm] using hbound.selectorFamily hV s hs S ((σ • A).mulVec g))
    _ = M := by simp

theorem integral_selectorFamilyReferenceMass_le
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) {h M : ℝ}
    (hbound : TransitionMassBound ν V h M) (s : FaceSmoother p) (hs : s.bandwidth = h)
    (S : Finset (Fin (k + 1) → Face p)) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) :
    (∫ ω, selectorFamilyReferenceMass s S A σ (V ω) ∂ν) ≤ S.card * M := by
  have hp := family_mass_properties ν V hV S (fun α => oneFaceReference s (α 0))
    (fun α _ => continuous_oneFaceReference s (α 0))
    (fun α _ x => oneFaceReference_bounds s (α 0) x) A σ
  change (∫ ω, ∑ α ∈ S, ∫ g, oneFaceReference s (α 0) ((σ • A).mulVec g + V ω)
    ∂standardGaussian r ∂ν) ≤ _
  rw [hp.2.2]
  have hi := (integrable_finset_sum S (fun α _ => integrable_reference_joint ν V hV s A σ (α 0))).integral_prod_right
  calc
    _ ≤ ∫ _g : Vector r, (S.card : ℝ) * M ∂standardGaussian r := by
      apply integral_mono hi (integrable_const _)
      intro g
      change (∫ ω, ∑ α ∈ S, oneFaceReference s (α 0) ((σ • A).mulVec g + V ω) ∂ν) ≤
        (S.card : ℝ) * M
      rw [integral_finset_sum S (fun α _ => integrable_oneFaceReference ν s (α 0)
        (fun ω => (σ • A).mulVec g + V ω) (measurable_const.add hV))]
      calc
        _ ≤ ∑ _α ∈ S, M := Finset.sum_le_sum (fun α _ => by
          simpa only [add_comm] using hbound.oneFace s hs (α 0) ((σ • A).mulVec g))
        _ = _ := by simp
    _ = _ := by simp

private theorem integrable_normal_joint
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) (s : FaceSmoother p)
    (S : Finset (Fin (k + 1) → Face p)) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ)
    (R : Vector r → ℝ)
    (hRi : Integrable (fun g => (R g) ^ 2) (standardGaussian r))
    (hdom : ∀ (f : Face p) g, (faceDot (selectorFaceNormal A f) g) ^ 2 ≤ (R g) ^ 2) :
    Integrable (fun z : Ω × Vector r => ∑ α ∈ S,
      selectorWeight s α ((σ • A).mulVec z.2 + V z.1) *
        (faceDot (selectorFaceNormal A (α 0)) z.2) ^ 2) (ν.prod (standardGaussian r)) := by
  have hRi' : Integrable (fun z : Ω × Vector r => (R z.2) ^ 2)
      (ν.prod (standardGaussian r)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) (μ := ν)).mul_prod hRi
  have hi (α : Fin (k + 1) → Face p) :
      Integrable (fun z : Ω × Vector r => selectorWeight s α ((σ • A).mulVec z.2 + V z.1) *
        (faceDot (selectorFaceNormal A (α 0)) z.2) ^ 2) (ν.prod (standardGaussian r)) := by
    have hm : Measurable (fun z : Ω × Vector r =>
        (faceDot (selectorFaceNormal A (α 0)) z.2) ^ 2) := by
      unfold faceDot
      fun_prop
    apply hRi'.mono' ((((continuous_selectorWeight s α).measurable.comp
      (measurable_gaussian_base V hV A σ)).mul hm).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      dsimp only [Function.comp_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (selectorWeight_nonneg s α _) (sq_nonneg _))]
      exact (mul_le_of_le_one_left (sq_nonneg _) (selectorWeight_le_one s α _)).trans (hdom _ _)
  exact integrable_finset_sum S (fun α _ => hi α)

theorem integrable_selectorFamilyNormalEnergy
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) (s : FaceSmoother p)
    (S : Finset (Fin (k + 1) → Face p)) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ)
    (R : Vector r → ℝ)
    (hRi : Integrable (fun g => (R g) ^ 2) (standardGaussian r))
    (hdom : ∀ (f : Face p) g, (faceDot (selectorFaceNormal A f) g) ^ 2 ≤ (R g) ^ 2) :
    Integrable (fun ω => selectorFamilyNormalEnergy s S A σ (V ω)) ν :=
  (integrable_normal_joint ν V hV s S A σ R hRi hdom).integral_prod_left

theorem integral_selectorFamilyNormalEnergy_le
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) {h M : ℝ}
    (hbound : TransitionMassBound ν V h M) (s : FaceSmoother p) (hs : s.bandwidth = h)
    (S : Finset (Fin (k + 1) → Face p)) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ)
    (R : Vector r → ℝ)
    (hRi : Integrable (fun g => (R g) ^ 2) (standardGaussian r))
    (hdom : ∀ (f : Face p) g, (faceDot (selectorFaceNormal A f) g) ^ 2 ≤ (R g) ^ 2) :
    (∫ ω, selectorFamilyNormalEnergy s S A σ (V ω) ∂ν) ≤
      M * (∫ g, (R g) ^ 2 ∂standardGaussian r) := by
  have hsum := integrable_normal_joint ν V hV s S A σ R hRi hdom
  change (∫ ω, (∫ g, ∑ α ∈ S, selectorWeight s α ((σ • A).mulVec g + V ω) *
    (faceDot (selectorFaceNormal A (α 0)) g) ^ 2 ∂standardGaussian r) ∂ν) ≤ _
  rw [integral_integral_swap (f := fun ω g => ∑ α ∈ S,
    selectorWeight s α ((σ • A).mulVec g + V ω) *
      (faceDot (selectorFaceNormal A (α 0)) g) ^ 2) hsum]
  have hh := integral_mono_ae hsum.integral_prod_right (hRi.const_mul M) ?_
  · simpa only [integral_const_mul] using hh
  · filter_upwards [hsum.prod_left_ae] with g hg
    have hmass : Integrable (fun ω => ∑ α ∈ S,
        selectorWeight s α ((σ • A).mulVec g + V ω)) ν :=
      integrable_finset_sum S (fun α _ => integrable_unit_test _ _
        ((continuous_selectorWeight s α).measurable.comp (measurable_const.add hV))
        (fun ω => ⟨selectorWeight_nonneg s α _, selectorWeight_le_one s α _⟩))
    have hpoint (ω : Ω) : (∑ α ∈ S, selectorWeight s α ((σ • A).mulVec g + V ω) *
        (faceDot (selectorFaceNormal A (α 0)) g) ^ 2) ≤
        (∑ α ∈ S, selectorWeight s α ((σ • A).mulVec g + V ω)) * (R g) ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun α _ =>
        mul_le_mul_of_nonneg_left (hdom _ _) (selectorWeight_nonneg s α _))
    calc
      _ ≤ (∫ ω, ∑ α ∈ S, selectorWeight s α ((σ • A).mulVec g + V ω) ∂ν) * (R g) ^ 2 := by
        simpa only [integral_mul_const] using integral_mono hg (hmass.mul_const _) hpoint
      _ ≤ M * (R g) ^ 2 := mul_le_mul_of_nonneg_right
        (by simpa only [add_comm] using hbound.selectorFamily hV s hs S ((σ • A).mulVec g))
        (sq_nonneg _)

theorem integrable_selectorFamilyMeanEnergy
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) (s : FaceSmoother p)
    (S : Finset (Fin (k + 1) → Face p)) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) :
    Integrable (fun ω => selectorFamilyMeanEnergy s S A σ (V ω)) ν := by
  apply integrable_finset_sum
  intro α _
  exact integrable_gaussian_weighted_mean_energy ν
    (fun ω g => selectorWeight s α ((σ • A).mulVec g + V ω))
    ((continuous_selectorWeight s α).measurable.comp (measurable_gaussian_base V hV A σ))
    (fun ω g => ⟨selectorWeight_nonneg s α _, selectorWeight_le_one s α _⟩)

/-- Actual averaged entropy and first-normal-energy control. This statement
keeps the finite family cardinality explicit and allows vanishing averaged
selector mass. -/
theorem integral_selectorFamilyMeanEnergy_le_entropy
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) {h M : ℝ} (hM : 0 < M)
    (hbound : TransitionMassBound ν V h M) (s : FaceSmoother p) (hs : s.bandwidth = h)
    (S : Finset (Fin (k + 1) → Face p)) (hS : S.Nonempty)
    (hactive : ∀ α ∈ S, ∀ i, α i ∈ s.faces)
    (A : Matrix (Fin p) (Fin r) ℝ) (hunit : ∀ j, vectorNormSq (A j) = 1) (σ : ℝ)
    (R : Vector r → ℝ)
    (hRi : Integrable (fun g => (R g) ^ 2) (standardGaussian r))
    (hdom : ∀ (f : Face p) g, (faceDot (selectorFaceNormal A f) g) ^ 2 ≤ (R g) ^ 2) :
    (∫ ω, selectorFamilyMeanEnergy s S A σ (V ω) ∂ν) ≤
      M * (∫ g, (R g) ^ 2 ∂standardGaussian r) +
        2 * M * (2 + Real.log (S.card : ℝ)) := by
  have hp := family_mass_properties ν V hV S (selectorWeight s)
    (fun α _ => continuous_selectorWeight s α)
    (fun α _ x => ⟨selectorWeight_nonneg s α x, selectorWeight_le_one s α x⟩) A σ
  have hb := family_mass_properties ν V hV S (fun α => oneFaceReference s (α 0))
    (fun α _ => continuous_oneFaceReference s (α 0))
    (fun α _ x => oneFaceReference_bounds s (α 0) x) A σ
  have hent := integral_massEntropy_le_common_caps ν
    (fun ω => selectorFamilyMass s S A σ (V ω))
    (fun ω => selectorFamilyReferenceMass s S A σ (V ω)) hp.1 hb.1
    (fun ω => selectorFamilyMass_nonneg s S A σ (V ω))
    (fun ω => selectorFamilyMass_le_reference s S A σ (V ω)) hp.2.1 hb.2.1 hM
    (by exact_mod_cast hS.card_pos)
    (integral_selectorFamilyMass_le ν V hV hbound s hs S A σ)
    (integral_selectorFamilyReferenceMass_le ν V hV hbound s hs S A σ)
  have he := integrable_massEntropy ν
    (fun ω => selectorFamilyMass s S A σ (V ω))
    (fun ω => selectorFamilyReferenceMass s S A σ (V ω)) hp.1 hb.1
    (fun ω => selectorFamilyMass_nonneg s S A σ (V ω))
    (fun ω => selectorFamilyMass_le_reference s S A σ (V ω)) hb.2.1
  have hn := integrable_selectorFamilyNormalEnergy ν V hV s S A σ R hRi hdom
  have hm := integrable_selectorFamilyMeanEnergy ν V hV s S A σ
  have hpoint (ω : Ω) : selectorFamilyMeanEnergy s S A σ (V ω) ≤
      selectorFamilyNormalEnergy s S A σ (V ω) +
        2 * massEntropy (selectorFamilyMass s S A σ (V ω))
          (selectorFamilyReferenceMass s S A σ (V ω)) := by
    simpa only [selectorFamilyMeanEnergy, selectorFamilyNormalEnergy,
      selectorFamilyMass, selectorFamilyReferenceMass, oneFaceReferenceProfile_eq,
      ← Matrix.smul_mulVec_assoc] using
      selector_family_means_le_entropy s S hS hactive A hunit (V ω) σ
  have hh := integral_mono hm (hn.add (he.const_mul 2)) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hn (he.const_mul 2), integral_const_mul] at hh
  have hncap := integral_selectorFamilyNormalEnergy_le ν V hV hbound s hs S A σ R hRi hdom
  nlinarith

/-- The averaged Gaussian mean-energy bound for every actual active tuple
family. The constant is explicit and independent of both covariance rank
and smoothing bandwidth. -/
theorem integral_selectorFamilyMeanEnergy_le
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) {h M : ℝ} (hM : 0 < M)
    (hbound : TransitionMassBound ν V h M) (s : FaceSmoother p) (hs : s.bandwidth = h)
    (hp : 1 ≤ p) (S : Finset (Fin (k + 1) → Face p))
    (hactive : ∀ α ∈ S, ∀ i, α i ∈ s.faces)
    (A : Matrix (Fin p) (Fin r) ℝ) (hunit : ∀ j, vectorNormSq (A j) = 1) (σ : ℝ) :
    (∫ ω, selectorFamilyMeanEnergy s S A σ (V ω) ∂ν) ≤
      (Real.exp (13 / 2 : ℝ) + 8) * (k + 1 : ℝ) * M * dimensionLog p := by
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  by_cases hS : S = ∅
  · subst S
    simp only [selectorFamilyMeanEnergy, Finset.sum_empty, integral_zero]
    have hL0 : 0 ≤ dimensionLog p := zero_le_one.trans hL
    positivity
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  have hmoment := selector_projection_max_second_moment hp A hunit
  have he := integral_selectorFamilyMeanEnergy_le_entropy ν V hV hM hbound s hs S hSne hactive
    A hunit σ (fun g => ‖linearProjectionFamily A g‖) hmoment.1
    (selector_face_projection_sq_le_max A)
  have hlog := selector_family_log_card_le hp S hSne
  have hK : 1 ≤ (k + 1 : ℝ) := by
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hKL : 1 ≤ (k + 1 : ℝ) * dimensionLog p :=
    one_le_mul_of_one_le_of_one_le hK hL
  have hDK : Real.exp (13 / 2 : ℝ) * dimensionLog p ≤
      Real.exp (13 / 2 : ℝ) * (k + 1 : ℝ) * dimensionLog p := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK (Real.exp_nonneg _)) (zero_le_one.trans hL)
  calc
    _ ≤ M * (Real.exp (13 / 2 : ℝ) * dimensionLog p + 4 + 2 * Real.log (S.card : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hmoment.2 hM.le]
    _ ≤ M * ((Real.exp (13 / 2 : ℝ) + 8) * (k + 1 : ℝ) * dimensionLog p) := by
      apply mul_le_mul_of_nonneg_left _ hM.le
      nlinarith
    _ = _ := by ring

/-- Exactly the tuples with nonzero possible selector weight. -/
def activeSelectorFamily (s : FaceSmoother p) (k : ℕ) : Finset (Fin (k + 1) → Face p) :=
  Finset.univ.filter (fun α => ∀ i, α i ∈ s.faces)

theorem selectorWeight_eq_zero_of_not_active (s : FaceSmoother p)
    (α : Fin (k + 1) → Face p) (hα : ¬ ∀ i, α i ∈ s.faces) (x : Vector p) :
    selectorWeight s α x = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hα
  have hpiz : s.pi x (α i) = 0 := by
    simp only [FaceSmoother.pi, FaceWeights.pi, FaceSmoother.weights, hi, ↓reduceIte, zero_div]
  have hpz : (∏ j, s.pi x (α j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hpiz
  simp only [selectorWeight, hpz, mul_zero]

theorem selectorFamilyMeanEnergy_univ_eq_active (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (v : Vector p) :
    selectorFamilyMeanEnergy (k := k) s Finset.univ A σ v =
      selectorFamilyMeanEnergy s (activeSelectorFamily s k) A σ v := by
  classical
  unfold selectorFamilyMeanEnergy activeSelectorFamily
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hα : ∀ i, α i ∈ s.faces
  · simp [hα]
  · have hm : weightMass (standardGaussian r)
        (fun g => selectorWeight s α ((σ • A).mulVec g + v)) = 0 := by
      unfold weightMass
      simp only [selectorWeight_eq_zero_of_not_active s α hα, integral_zero]
    simp [hα, hm]

/-- Full ordered tuple sum, including omitted faces and repeated indices.
The actual Gaussian weighted means are averaged over the concrete base law;
no averaged-energy estimate is assumed. -/
theorem integral_selectorMeanEnergy_le
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (V : Ω → Vector p) (hV : Measurable V) {h M : ℝ} (hM : 0 < M)
    (hbound : TransitionMassBound ν V h M) (s : FaceSmoother p) (hs : s.bandwidth = h)
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin r) ℝ)
    (hunit : ∀ j, vectorNormSq (A j) = 1) (σ : ℝ) :
    (∫ ω, ∑ α : Fin (k + 1) → Face p,
      weightMass (standardGaussian r) (fun g => selectorWeight s α ((σ • A).mulVec g + V ω)) *
        vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α ((σ • A).mulVec g + V ω))) ∂ν) ≤
      (Real.exp (13 / 2 : ℝ) + 8) * (k + 1 : ℝ) * M * dimensionLog p := by
  change (∫ ω, selectorFamilyMeanEnergy s Finset.univ A σ (V ω) ∂ν) ≤ _
  simp_rw [selectorFamilyMeanEnergy_univ_eq_active]
  exact integral_selectorFamilyMeanEnergy_le ν V hV hM hbound s hs hp (activeSelectorFamily s k)
    (fun α hα => (Finset.mem_filter.mp hα).2) A hunit σ

end
end RectangleCLT.Companion
