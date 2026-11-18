import RectangleCLTArxivV1.SupplementalHCubicPhysicalTrace
import RectangleCLTArxivV1.SupplementalHCubicFamilyMeans
import RectangleCLTArxivV1.SupplementalHCubicCorrection
import RectangleCLTArxivV1.HFourthConditionalMatrix

/-! Actual intrinsic cubic matrix estimate. The signed radial trace is
supplied by the proved physical hard-facet/Gamma argument, not assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem supplementalH_cubic_selector_nuclear_reduction_all {p r K : ℕ}
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : Fin (K+1) → Face p) (u : Vector r) (hu : vectorNormSq u=1) :
    symmetricNuclearNorm (supplementalHCubicSelectorScore s M v α u) ≤
      2*supplementalHCubicMeanEnergy s M v α u+2*supplementalHCubicMeanEnergy s M v α (-u)+
      supplementalHSelectorMass s M v α*(1+vectorNormSq (weightMean (standardGaussian r) id
        (fun g => selectorWeight s α (M.mulVec g+v))))-
      ∫ g, (vectorNormSq g-(r:ℝ))*|faceDot u g| *selectorWeight s α (M.mulVec g+v) ∂standardGaussian r := by
  classical
  by_cases ha : ∀ i, α i∈s.faces
  · exact supplementalH_cubic_selector_nuclear_reduction s M v α ha u hu
  · have hz (g : Vector r) : selectorWeight s α (M.mulVec g+v)=0 :=
      selectorWeight_eq_zero_of_not_active s α ha _
    have hscore : supplementalHCubicSelectorScore s M v α u=0 := by
      ext j k
      simp only [supplementalHCubicSelectorScore,hz,mul_zero,integral_zero,Matrix.zero_apply]
    rw [hscore,symmetricNuclearNorm_zero]
    simp only [supplementalHCubicMeanEnergy,supplementalHSelectorMass,weightMass,hz,mul_zero,
      integral_zero,zero_mul,add_zero,sub_zero,le_refl]

/-- A genuine actual matrix-family bound with the three analytic costs
shown separately. Every extra face label remains unrestricted. -/
theorem intrinsicRectangleConcentration_cubicMatrix_raw {p n K : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin (n+1)) ℝ) {C₀ δ κ σ : ℝ}
    (hC₀ : 0<C₀) (hδ : 0≤δ) (hκ : 0<κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    (∫ x, ∑ α : Fin (K+1) → Face p, symmetricNuclearNorm
      (supplementalHCubicSelectorScore s (σ • A) (A.mulVec x) α (selectorFaceNormal A (α 0))) ∂ν) ≤
      48*Real.exp 16*((K:ℝ)+2)*C₀*s.bandwidth*κ*dimensionLog p*Real.sqrt (dimensionLog p)+
      (4*C₀*s.bandwidth*κ+(Real.exp (13/2:ℝ)+8)*((K:ℝ)+1)*(4*C₀*s.bandwidth*κ)*dimensionLog p)+
      (2:ℝ)^K*((32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C₀*κ*s.bandwidth*
        dimensionLog p*Real.sqrt (dimensionLog p)) := by
  classical
  let V := fun x : Vector (n+1) => A.mulVec x
  have hV : Measurable V := by unfold V Matrix.mulVec dotProduct; fun_prop
  have hU (f : Face p) : vectorNormSq (selectorFaceNormal A f)=1 := selectorFaceNormal_normSq A hunit f
  let N := fun x => ∑ α : Fin (K+1) → Face p, symmetricNuclearNorm
    (supplementalHCubicSelectorScore s (σ • A) (V x) α (selectorFaceNormal A (α 0)))
  let E := fun x => ∑ α : Fin (K+1) → Face p,
    (supplementalHCubicMeanEnergy s (σ • A) (V x) α (selectorFaceNormal A (α 0))+
      supplementalHCubicMeanEnergy s (σ • A) (V x) α (-(selectorFaceNormal A (α 0))))
  let C := fun x => ∑ α : Fin (K+1) → Face p, supplementalHSelectorMass s (σ • A) (V x) α*
    (1+vectorNormSq (weightMean (standardGaussian (n+1)) id
      (fun g => selectorWeight s α ((σ • A).mulVec g+V x))))
  let T := supplementalHCubicPhysicalTrace s A σ K
  have hmean := intrinsicRectangleConcentration_cubicMeanFamilies (K := K) hp ν V hV s A σ hC₀.le hκ.le hδh hc hU
  have hcor := intrinsicRectangleConcentration_cubicUnweightedCorrection (K := K) hp ν V hV s A σ hC₀ hκ hδh hc hunit
  have htrace := intrinsicRectangleConcentration_cubicPhysicalTrace hp ν s A hC₀.le hδ hκ.le hσ hunit hc hδσ K
  have hNi : Integrable N ν := integrable_finset_sum _ (fun α _ =>
    hFourthCubicGaussianScore_nuclear_integrable ν s (σ • A) (selectorFaceNormal A) V hV α)
  have hTsum (x : Vector (n+1)) :
      (∑ α : Fin (K+1) → Face p, ∫ g, (vectorNormSq g-((n+1:ℕ):ℝ))*
        |faceDot (selectorFaceNormal A (α 0)) g| *selectorWeight s α ((σ • A).mulVec g+V x)
        ∂standardGaussian (n+1))=T x := by
    unfold T supplementalHCubicPhysicalTrace
    apply Finset.sum_congr rfl
    intro α _
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by
      have he : (σ • A).mulVec g+V x=A.mulVec (x+σ • g) := by
        rw [Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.smul_mulVec_assoc]
        exact add_comm _ _
      dsimp only
      rw [he])
  have hpoint (x : Vector (n+1)) : N x≤2*E x+C x-T x := by
    have ht := Finset.sum_le_sum (fun (α : Fin (K+1) → Face p) (_ : α∈Finset.univ) =>
      supplementalH_cubic_selector_nuclear_reduction_all s (σ • A) (V x) α _ (hU (α 0)))
    calc
      _ ≤ _ := ht
      _ = 2*E x+C x-T x := by
        simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
        rw [hTsum]
        dsimp only [E,C]
        rw [Finset.sum_add_distrib]
        ring
  have hmono := integral_mono hNi (((hmean.1.const_mul 2).add hcor.1).sub htrace.1) hpoint
  have heI : (∫ x, 2*E x+C x-T x ∂ν)=
      2*(∫ x,E x ∂ν)+(∫ x,C x ∂ν)-(∫ x,T x ∂ν) := by
    calc
      _ = (∫ x,2*E x+C x ∂ν)-(∫ x,T x ∂ν) :=
        integral_sub ((hmean.1.const_mul 2).add hcor.1) htrace.1
      _ = _ := by rw [integral_add (hmean.1.const_mul 2) hcor.1,integral_const_mul]
  change (∫ x,N x ∂ν)≤(∫ x,2*E x+C x-T x ∂ν) at hmono
  rw [heI] at hmono
  have hneg : -(∫ x,T x ∂ν)≤∫ x,|T x| ∂ν := by
    have ht := integral_mono htrace.1.neg htrace.1.abs (fun x => neg_le_abs (T x))
    change (∫ x,-T x ∂ν)≤∫ x,|T x| ∂ν at ht
    rw [integral_neg] at ht
    exact ht
  calc
    _ ≤ 2*(∫ x,E x ∂ν)+(∫ x,C x ∂ν)+(∫ x,|T x| ∂ν) := by linarith only [hmono,hneg]
    _ ≤ 2*(24*Real.exp 16*((K:ℝ)+2)*C₀*s.bandwidth*κ*dimensionLog p*Real.sqrt (dimensionLog p))+
        (4*C₀*s.bandwidth*κ+(Real.exp (13/2:ℝ)+8)*((K:ℝ)+1)*(4*C₀*s.bandwidth*κ)*dimensionLog p)+
        (2:ℝ)^K*((32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C₀*κ*s.bandwidth*
          dimensionLog p*Real.sqrt (dimensionLog p)) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmean.2 (by norm_num)) hcor.2) htrace.2
    _ = _ := by ring

end
end RectangleCLTArxivV1
