import RectangleCLTArxivV1.SupplementalHCubicFamilyEntropy
import RectangleCLTArxivV1.SupplementalHCubicSigns

/-! Actual mean-energy averaging for the two signed cubic weights.
All original tuple labels, the full base law, and zero masses are retained. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem measurable_supplementalHCubicMeanEnergy
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (V : Ω → Vector p) (hV : Measurable V) (s : FaceSmoother p)
    (M : Matrix (Fin p) (Fin r) ℝ) (α : Fin K → Face p) (u : Vector r) :
    Measurable (fun ω => supplementalHCubicMeanEnergy s M (V ω) α u) := by
  let W := fun z : Ω × Vector r => supplementalHPositiveDirection u z.2*
    selectorWeight s α (M.mulVec z.2+V z.1)
  have hM : Measurable (fun g : Vector r => M.mulVec g) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hpos : Measurable (supplementalHPositiveDirection u) := by
    unfold supplementalHPositiveDirection faceDot
    fun_prop
  have hW : Measurable W := (hpos.comp measurable_snd).mul
    ((continuous_selectorWeight s α).measurable.comp ((hM.comp measurable_snd).add (hV.comp measurable_fst)))
  have hmass : Measurable (fun ω => ∫ g, W (ω,g) ∂standardGaussian r) :=
    hW.stronglyMeasurable.integral_prod_right'.measurable
  have hnum (j : Fin r) : Measurable (fun ω => ∫ g, g j*W (ω,g) ∂standardGaussian r) :=
    (((measurable_pi_apply j).comp measurable_snd).mul hW).stronglyMeasurable.integral_prod_right'.measurable
  have hmean (j : Fin r) : Measurable (fun ω => weightMean (standardGaussian r) id
      (fun g => W (ω,g)) j) := (hnum j).div hmass
  exact hmass.mul (Finset.measurable_sum _ (fun j _ => (hmean j).pow_const 2))

/-- Actual positive-half mean energy, after integrating over the base and
summing every tuple. Integrability is a conclusion of the reference proof. -/
theorem intrinsicRectangleConcentration_positiveCubicMeanFamily
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hU : ∀ f, vectorNormSq (selectorFaceNormal A f)=1) :
    (∀ α : Fin (K+1) → Face p, Integrable
      (fun ω => supplementalHCubicMeanEnergy s (σ • A) (V ω) α (selectorFaceNormal A (α 0))) μ) ∧
    (∫ ω, ∑ α : Fin (K+1) → Face p,
      supplementalHCubicMeanEnergy s (σ • A) (V ω) α (selectorFaceNormal A (α 0)) ∂μ) ≤
      (4*C₀*s.bandwidth*κ)*((Real.sqrt (dimensionLog p))^3*Real.exp 16)+
      2*((4*Real.exp 10*C₀*s.bandwidth*κ)*((K:ℝ)+2)*dimensionLog p*Real.sqrt (dimensionLog p)) := by
  classical
  let U := selectorFaceNormal A
  let M := σ • A
  let P := supplementalHCubicTupleMoment (K := K) s M V U 0
  let Q := supplementalHCubicTupleMoment (K := K) s M V U 2
  let B := supplementalHCubicReferenceMass (K := K) s M V U
  let T := fun α ω => P α ω*Real.log (B α ω/P α ω)
  let E := fun (α : Fin (K+1) → Face p) ω => supplementalHCubicMeanEnergy s M (V ω) α (U (α 0))
  have hP := intrinsicRectangleConcentration_cubicTupleMoment (K := K) hp μ V hV s M hC₀ hκ hδh hc U hU 0
  have hQ := intrinsicRectangleConcentration_cubicTupleMoment (K := K) hp μ V hV s M hC₀ hκ hδh hc U hU 2
  have hT := intrinsicRectangleConcentration_cubicFamilyEntropy (K := K) hp μ V hV s M hC₀ hκ hδh hc U hU
  have hTi (α : Fin (K+1) → Face p) : Integrable (T α) μ := by
    have hB := supplementalHCubicReferenceMass_properties μ V hV s M U α
    exact integrable_entropy_term μ (P α) (B α) (hP.1 α).1 hB.1
      (fun ω => integral_nonneg (fun g => mul_nonneg
        (mul_nonneg (supplementalHPositiveDirection_nonneg _ _) (pow_nonneg (abs_nonneg _) _))
        (selectorWeight_nonneg s α _)))
      (fun ω => supplementalHCubicTupleMass_le_reference s M (V ω) U α) (hP.1 α).2 hB.2
  have hE0 (α) (ω : Ω) : 0 ≤ E α ω := by
    apply mul_nonneg
    · exact integral_nonneg (fun g => mul_nonneg (supplementalHPositiveDirection_nonneg _ _)
        (selectorWeight_nonneg s α _))
    · exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hbound (α : Fin (K+1) → Face p) (ω : Ω) : E α ω ≤ Q α ω+2*T α ω := by
    have h := supplementalH_cubic_mean_reference_bound_all s A (V ω) σ α (hU (α 0))
    have heQ : Q α ω = ∫ g,
        (supplementalHPositiveDirection (U (α 0)) g*selectorWeight s α (M.mulVec g+V ω))*
          (faceDot (U (α 0)) g)^2 ∂standardGaussian r := by
      apply integral_congr_ae
      exact ae_of_all _ (fun g => by dsimp [Q,supplementalHCubicTupleMoment]; rw [sq_abs]; ring_nf)
    rw [heQ]
    simpa only [E,T,P,B,supplementalHCubicTupleMoment,supplementalHCubicReferenceMass,
      pow_zero,mul_one,weightMass,add_comm,mul_assoc,U,M] using h
  have hEi (α : Fin (K+1) → Face p) : Integrable (E α) μ := by
    apply ((hQ.1 α).2.add ((hTi α).const_mul 2)).mono'
      (measurable_supplementalHCubicMeanEnergy V hV s M α (U (α 0))).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hE0 α ω)]
      exact hbound α ω)
  refine ⟨hEi,?_⟩
  have ht := integral_mono (integrable_finset_sum _ (fun α _ => hEi α))
    ((integrable_finset_sum _ (fun α _ => (hQ.1 α).2)).add (hT.1.const_mul 2))
    (fun ω => by simpa only [Finset.sum_add_distrib,←Finset.mul_sum] using
      Finset.sum_le_sum (fun α (_ : α∈Finset.univ) => hbound α ω))
  have he : (∫ ω, (∑ α : Fin (K+1) → Face p, Q α ω)+2*(∑ α, T α ω) ∂μ) =
      (∫ ω, ∑ α, Q α ω ∂μ)+2*(∫ ω, ∑ α, T α ω ∂μ) := by
    rw [integral_add (integrable_finset_sum _ (fun α _ => (hQ.1 α).2)) (hT.1.const_mul 2),integral_const_mul]
  change (∫ ω, ∑ α, E α ω ∂μ) ≤
    (∫ ω, (∑ α : Fin (K+1) → Face p, Q α ω)+2*(∑ α, T α ω) ∂μ) at ht
  rw [he] at ht
  have hQb : (∫ ω, ∑ α : Fin (K+1) → Face p, Q α ω ∂μ) ≤
      (4*C₀*s.bandwidth*κ)*((Real.sqrt (dimensionLog p))^3*Real.exp 16) := by
    convert hQ.2 using 1
    norm_num
  exact ht.trans (add_le_add hQb (mul_le_mul_of_nonneg_left hT.2 (by norm_num)))

/-- The negative branch is evaluated at precisely the same original
Gaussian smoothing point. -/
theorem intrinsicRectangleConcentration_negativeCubicMeanFamily
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hU : ∀ f, vectorNormSq (selectorFaceNormal A f)=1) :
    (∀ α : Fin (K+1) → Face p, Integrable
      (fun ω => supplementalHCubicMeanEnergy s (σ • A) (V ω) α (-(selectorFaceNormal A (α 0)))) μ) ∧
    (∫ ω, ∑ α : Fin (K+1) → Face p,
      supplementalHCubicMeanEnergy s (σ • A) (V ω) α (-(selectorFaceNormal A (α 0))) ∂μ) ≤
      (4*C₀*s.bandwidth*κ)*((Real.sqrt (dimensionLog p))^3*Real.exp 16)+
      2*((4*Real.exp 10*C₀*s.bandwidth*κ)*((K:ℝ)+2)*dimensionLog p*Real.sqrt (dimensionLog p)) := by
  have hun (f : Face p) : vectorNormSq (selectorFaceNormal (-A) f)=1 := by
    rw [supplementalH_selectorFaceNormal_neg]
    simpa only [vectorNormSq,Pi.neg_apply,neg_sq] using hU f
  have h := intrinsicRectangleConcentration_positiveCubicMeanFamily (K := K) hp μ V hV s (-A) (-σ)
    hC₀ hκ hδh hc hun
  simpa only [supplementalH_selectorFaceNormal_neg,supplementalH_negative_scale_factor] using h

private theorem cubic_mean_budget_simplify {p K : ℕ} (hp : 1≤p)
    (C₀ h κ : ℝ) (hC₀ : 0≤C₀) (hh : 0≤h) (hκ : 0≤κ) :
    (4*C₀*h*κ)*((Real.sqrt (dimensionLog p))^3*Real.exp 16)+
      2*((4*Real.exp 10*C₀*h*κ)*((K:ℝ)+2)*dimensionLog p*Real.sqrt (dimensionLog p)) ≤
      12*Real.exp 16*((K:ℝ)+2)*C₀*h*κ*dimensionLog p*Real.sqrt (dimensionLog p) := by
  let Z := C₀*h*κ*dimensionLog p*Real.sqrt (dimensionLog p)
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hZ : 0≤Z := by dsimp [Z]; positivity
  have hk : 1≤(K:ℝ)+2 := by have := Nat.cast_nonneg (α := ℝ) K; linarith
  have he : Real.exp (10:ℝ)≤Real.exp 16 := Real.exp_le_exp.mpr (by norm_num)
  have hcube : (Real.sqrt (dimensionLog p))^3=dimensionLog p*Real.sqrt (dimensionLog p) := by
    rw [pow_succ,Real.sq_sqrt hL]
  calc
    _ = 4*Real.exp 16*Z+8*Real.exp 10*((K:ℝ)+2)*Z := by rw [hcube]; dsimp [Z]; ring
    _ ≤ 4*Real.exp 16*((K:ℝ)+2)*Z+8*Real.exp 16*((K:ℝ)+2)*Z := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hk) hZ
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (by norm_num)) (by positivity)) hZ
    _ = _ := by dsimp [Z]; ring

/-- The summed two-sign cubic mean energy has the required intrinsic
order for every number of additional selector factors. -/
theorem intrinsicRectangleConcentration_cubicMeanFamilies
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (hU : ∀ f, vectorNormSq (selectorFaceNormal A f)=1) :
    Integrable (fun ω => ∑ α : Fin (K+1) → Face p,
      (supplementalHCubicMeanEnergy s (σ • A) (V ω) α (selectorFaceNormal A (α 0))+
       supplementalHCubicMeanEnergy s (σ • A) (V ω) α (-(selectorFaceNormal A (α 0))))) μ ∧
    (∫ ω, ∑ α : Fin (K+1) → Face p,
      (supplementalHCubicMeanEnergy s (σ • A) (V ω) α (selectorFaceNormal A (α 0))+
       supplementalHCubicMeanEnergy s (σ • A) (V ω) α (-(selectorFaceNormal A (α 0)))) ∂μ) ≤
      24*Real.exp 16*((K:ℝ)+2)*C₀*s.bandwidth*κ*dimensionLog p*Real.sqrt (dimensionLog p) := by
  classical
  have hplus := intrinsicRectangleConcentration_positiveCubicMeanFamily (K := K) hp μ V hV s A σ hC₀ hκ hδh hc hU
  have hminus := intrinsicRectangleConcentration_negativeCubicMeanFamily (K := K) hp μ V hV s A σ hC₀ hκ hδh hc hU
  refine ⟨integrable_finset_sum _ (fun α _ => (hplus.1 α).add (hminus.1 α)),?_⟩
  simp_rw [Finset.sum_add_distrib]
  rw [integral_add (integrable_finset_sum _ (fun α _ => hplus.1 α))
    (integrable_finset_sum _ (fun α _ => hminus.1 α))]
  have hb := cubic_mean_budget_simplify (K := K) hp C₀ s.bandwidth κ hC₀ s.bandwidth_pos.le hκ
  exact (add_le_add (hplus.2.trans hb) (hminus.2.trans hb)).trans_eq (by ring)

end
end RectangleCLTArxivV1
