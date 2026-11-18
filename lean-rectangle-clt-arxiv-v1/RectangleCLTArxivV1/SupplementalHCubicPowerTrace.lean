import RectangleCLTArxivV1.SupplementalHCubicGammaTrace

/-! The actual soft-power trace, averaged over its original concentrated
physical base. The hard-facet supplier has been fully discharged. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def supplementalHSoftCubicPowerTrace {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h σ : ℝ) (q : ℕ) (x : Vector r) : ℝ :=
  ∫ g, ∑ j, ((vectorNormSq g-(r:ℝ))*|faceDot (u j) g|)*
    (logisticNullWeight u a h (x+σ • g)^(q+1)*logisticFaceWeight u a h (x+σ • g) j)
      ∂standardGaussian r

theorem supplementalH_softCubicPowerTrace_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {C δ σ h : ℝ} (hC : 0≤C) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0<s →
      ν.real (faceLayer (fun k => U (f k)) b s)≤C*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (q : ℕ) :
    Integrable (supplementalHSoftCubicPowerTrace (fun j => U (f j)) a h σ q) ν ∧
    (∫ x, |supplementalHSoftCubicPowerTrace (fun j => U (f j)) a h σ q x| ∂ν) ≤
      (32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C*h*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  let u := fun j => U (f j)
  let J := fun z : (ℝ × (Face m → ℝ)) × Vector (n+1) => hardGaussianWeightedFacetIntegral u
    (fun k => (gammaAdjustedThreshold a h z.1 k-faceDot (u k) z.2)/σ)
  let c := h/((q:ℝ)+1)/σ
  have hc : 0≤c := by dsimp [c]; positivity
  have hb := supplementalH_gamma_weighted_facet_budget hp ν U f a hC hδ hσ hh hu hbase q
  have hJ : Integrable J ((gammaRectangleLaw m q).prod ν) := hb.1
  have he : supplementalHSoftCubicPowerTrace u a h σ q=
      (fun x => c*(∫ e, J (e,x) ∂gammaRectangleLaw m q)) := by
    funext x
    exact supplementalH_absoluteFace_soft_sum_coarea u hu a hh hσ x q
  have hTi : Integrable (supplementalHSoftCubicPowerTrace u a h σ q) ν := by
    rw [he]
    exact hJ.integral_prod_right.const_mul c
  refine ⟨hTi,?_⟩
  have hnorm : (∫ x, ‖∫ e, J (e,x) ∂gammaRectangleLaw m q‖ ∂ν) ≤
      ∫ x, ∫ e, ‖J (e,x)‖ ∂gammaRectangleLaw m q ∂ν :=
    integral_mono hJ.integral_prod_right.norm hJ.norm.integral_prod_right
      (fun x => norm_integral_le_integral_norm _)
  have hswap : (∫ x, ∫ e, ‖J (e,x)‖ ∂gammaRectangleLaw m q ∂ν) =
      ∫ e, ∫ x, ‖J (e,x)‖ ∂ν ∂gammaRectangleLaw m q := (integral_integral_swap hJ.norm).symm
  have hsharp := supplementalH_gamma_weighted_facet_budget_small_delta hp ν U f a hC hδ hσ hh hu hbase hδσ q
  have hbound : (∫ x, ‖∫ e, J (e,x) ∂gammaRectangleLaw m q‖ ∂ν) ≤
      (32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C*σ*dimensionLog p*Real.sqrt (dimensionLog p) := by
    exact (hnorm.trans_eq hswap).trans hsharp
  rw [he]
  simp_rw [abs_mul,abs_of_nonneg hc]
  rw [integral_const_mul]
  change c*(∫ x, ‖∫ e, J (e,x) ∂gammaRectangleLaw m q‖ ∂ν) ≤ _
  have hstep := mul_le_mul_of_nonneg_left hbound hc
  have hL : 0≤dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hq : 1≤(q:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  calc
    _ ≤ c*((32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C*σ*dimensionLog p*Real.sqrt (dimensionLog p)) := hstep
    _ = (h/((q:ℝ)+1))*((32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C*dimensionLog p*Real.sqrt (dimensionLog p)) := by
      dsimp [c]
      field_simp
      ring
    _ ≤ h*((32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C*dimensionLog p*Real.sqrt (dimensionLog p)) :=
      mul_le_mul_of_nonneg_right (div_le_self hh.le hq) (by positivity)
    _ = _ := by ring

end
end RectangleCLTArxivV1
