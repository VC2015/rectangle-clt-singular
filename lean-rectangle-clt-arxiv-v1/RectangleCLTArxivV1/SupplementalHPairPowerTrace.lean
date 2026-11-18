import RectangleCLTArxivV1.SupplementalHGammaRidgeTrace
import RectangleCLTArxivV1.SupplementalHGammaPositiveEdgeBudget

/-! Actual signed pair-power trace under the original concentrated
physical base. The native signed ridge surface budget is proved upstream. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def supplementalHPairTraceConstant (C₀ : ℝ) : ℝ :=
  ((6144*Real.pi+12288)*Real.exp ((3:ℝ)/2))*Real.exp 128*C₀

theorem supplementalHPairTraceConstant_nonneg {C₀ : ℝ} (hC₀ : 0≤C₀) :
    0≤supplementalHPairTraceConstant C₀ := by
  unfold supplementalHPairTraceConstant
  positivity

def supplementalHSoftPairPowerTrace {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h σ : ℝ) (q : ℕ) (x : Vector r) : ℝ :=
  ∫ g, ∑ jl : Fin m × Fin m,correlationAngleWeight (faceDot (u jl.1) (u jl.2))*
    ((vectorNormSq g-(r:ℝ))*(logisticNullWeight u a h (x+σ • g)^(q+1)*
      logisticFaceWeight u a h (x+σ • g) jl.1*logisticFaceWeight u a h (x+σ • g) jl.2))
    ∂standardGaussian r

theorem supplementalH_softPairPowerTrace_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {C δ σ h : ℝ} (hC : 0≤C) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s →
      ν.real (faceLayer (fun k => U (f k)) b s)≤C*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (q : ℕ) :
    Integrable (supplementalHSoftPairPowerTrace (fun j => U (f j)) a h σ q) ν ∧
    (∫ x,|supplementalHSoftPairPowerTrace (fun j => U (f j)) a h σ q x| ∂ν)≤
      supplementalHPairTraceConstant C*h^2/σ*dimensionLog p*Real.sqrt (dimensionLog p) := by
  let u := fun j => U (f j)
  let J := fun z : (ℝ × (Face m → ℝ)) × Vector (n+1) => hardGaussianWeightedRidgeIntegral u
    (fun k => (gammaAdjustedThreshold a h z.1 k-faceDot (u k) z.2)/σ)
  let c := 2*h^2/(((q:ℝ)+1)*((q:ℝ)+2)*σ^2)
  have hc : 0≤c := by dsimp [c]; positivity
  have hb := supplementalH_gamma_weighted_ridge_budget hp ν U f a hC hδ hσ hh hu hbase q
  have hJ : Integrable J ((gammaRectangleLaw m q).prod ν) := hb.1
  have he : supplementalHSoftPairPowerTrace u a h σ q=
      fun x => c*(∫ e,J (e,x) ∂gammaRectangleLaw m q) := by
    funext x
    exact supplementalH_signedRidge_soft_sum_coarea u hu a hh hσ x q
  have hTi : Integrable (supplementalHSoftPairPowerTrace u a h σ q) ν := by
    rw [he]
    exact hJ.integral_prod_right.const_mul c
  refine ⟨hTi,?_⟩
  have hnorm : (∫ x,‖∫ e,J (e,x) ∂gammaRectangleLaw m q‖ ∂ν)≤
      ∫ x,∫ e,‖J (e,x)‖ ∂gammaRectangleLaw m q ∂ν :=
    integral_mono hJ.integral_prod_right.norm hJ.norm.integral_prod_right
      (fun x => norm_integral_le_integral_norm _)
  have hswap : (∫ x,∫ e,‖J (e,x)‖ ∂gammaRectangleLaw m q ∂ν)=
      ∫ e,∫ x,‖J (e,x)‖ ∂ν ∂gammaRectangleLaw m q := (integral_integral_swap hJ.norm).symm
  have hsharp := supplementalH_gamma_weighted_ridge_budget_small_delta hp ν U f a hC hδ hσ hh hu hbase hδσ q
  have hbound : (∫ x,‖∫ e,J (e,x) ∂gammaRectangleLaw m q‖ ∂ν)≤
      supplementalHPairTraceConstant C*σ*dimensionLog p*Real.sqrt (dimensionLog p) :=
    (hnorm.trans_eq hswap).trans (hsharp.trans_eq (by unfold supplementalHPairTraceConstant; ring))
  rw [he]
  simp_rw [abs_mul,abs_of_nonneg hc]
  rw [integral_const_mul]
  change c*(∫ x,‖∫ e,J (e,x) ∂gammaRectangleLaw m q‖ ∂ν)≤_
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hconst := supplementalHPairTraceConstant_nonneg hC
  have hq0 : 0≤(q:ℝ) := Nat.cast_nonneg q
  have hden : 0<((q:ℝ)+1)*((q:ℝ)+2) := mul_pos (by positivity) (by positivity)
  have hratio : 2/(((q:ℝ)+1)*((q:ℝ)+2))≤1 := (div_le_one hden).mpr (by nlinarith)
  calc
    _≤c*(supplementalHPairTraceConstant C*σ*dimensionLog p*Real.sqrt (dimensionLog p)) :=
      mul_le_mul_of_nonneg_left hbound hc
    _=(2/(((q:ℝ)+1)*((q:ℝ)+2)))*
        (supplementalHPairTraceConstant C*h^2/σ*dimensionLog p*Real.sqrt (dimensionLog p)) := by
      dsimp [c]
      field_simp
      ring
    _≤_ := mul_le_of_le_one_left (by positivity) hratio

end
end RectangleCLTArxivV1
