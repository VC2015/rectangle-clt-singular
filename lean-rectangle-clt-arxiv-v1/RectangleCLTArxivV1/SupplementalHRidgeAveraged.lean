import RectangleCLTArxivV1.SupplementalHRidgeTripleTransport
import RectangleCLTArxivV1.SupplementalHRidgeMeasurable
import RectangleCLTArxivV1.SupplementalHFourthTransportAveraged

/-! Actual signed codimension-three ridge remainder averaged against
an arbitrary concentrated base law, including singular probability laws. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section

theorem hardGaussianWeightedRidgeIntegral_Green_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hreg : AllPairResidualThresholdRegularity u b) :
    hardGaussianWeightedRidgeIntegral u b=
      hardGaussianRidgeLeadingIntegral u b-hardGaussianRidgeThirdBoundaryIntegral u b := by
  unfold hardGaussianWeightedRidgeIntegral hardGaussianRidgeLeadingIntegral hardGaussianRidgeThirdBoundaryIntegral
  simp_rw [hardGaussianSignedRidgeTerm_Green_of_slack u b _ _ (hu _) (hu _) (hreg _ _),Finset.sum_sub_distrib]
  ring

/-- The actual native third-boundary quantity is integrable and paid by
the actual common outward tube; its AE measurability is derived from the
literal measurable ridge Green identity. -/
theorem hardGaussianRidgeThirdBoundaryIntegral_base_tube_bound {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {σ : ℝ} (hσ : 0<σ) (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hreg : ∀ᵐ x ∂ν,AllPairResidualThresholdRegularity (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ)) :
    Integrable (fun x => hardGaussianRidgeThirdBoundaryIntegral (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ)) ν ∧
    (∫ x,|hardGaussianRidgeThirdBoundaryIntegral (fun k => U (f k))
      (fun k => (a k-faceDot (U (f k)) x)/σ)| ∂ν)≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ z,(gaussianOutwardVariableTube (fun k => U (f k)) a σ
        (supplementalHRadius U)).indicator (fun z => supplementalHRadius U z.2^4) z
          ∂ν.prod (standardGaussian (n+1))) := by
  let C := 6144*Real.exp ((3:ℝ)/2)
  let b := fun x : Vector (n+1) => fun k => (a k-faceDot (U (f k)) x)/σ
  let J := fun x => hardGaussianRidgeThirdBoundaryIntegral (fun k => U (f k)) (b x)
  let I := (gaussianOutwardVariableTube (fun k => U (f k)) a σ (supplementalHRadius U)).indicator
    (fun z => supplementalHRadius U z.2^4)
  have hIset := fourthTransport_measurableSet_gaussianOutwardVariableTube (fun k => U (f k)) a σ
    (supplementalHRadius U) (measurable_supplementalHRadius U)
  have hi : Integrable I (ν.prod (standardGaussian (n+1))) := by
    have hr : Integrable (fun z : Vector (n+1) × Vector (n+1) => supplementalHRadius U z.2^4)
        (ν.prod (standardGaussian (n+1))) := by
      simpa only [one_mul] using (integrable_const (μ := ν) (1:ℝ)).mul_prod (supplementalHRadius_moment_le hp U 4).1
    exact hr.indicator hIset
  have hbm : Measurable b := by
    apply measurable_pi_lambda
    intro k
    exact (measurable_const.sub (measurable_thresholdDot _)).div_const σ
  have hJm : AEStronglyMeasurable J ν := by
    have hm := ((measurable_hardGaussianRidgeLeadingIntegral (fun k => U (f k))).sub
      (measurable_hardGaussianWeightedRidgeIntegral (fun k => U (f k)))).comp hbm
    apply hm.aestronglyMeasurable.congr
    filter_upwards [hreg] with x hx
    have hg := hardGaussianWeightedRidgeIntegral_Green_of_slack (fun k => U (f k)) (b x) hu hx
    dsimp only [Function.comp_def,J]
    linarith
  have hb : ∀ᵐ x ∂ν,|J x|≤C*(∫ g,I (x,g) ∂standardGaussian (n+1)) := by
    filter_upwards [hreg] with x hx
    exact abs_hardGaussianRidgeThirdBoundaryIntegral_affine_tube_bound hp U f a x hσ hu hx
  have hJi : Integrable J ν := (hi.integral_prod_left.const_mul C).mono' hJm
    (hb.mono (fun _ h => by simpa only [Real.norm_eq_abs] using h))
  refine ⟨hJi,?_⟩
  have hh := integral_mono_ae hJi.abs (hi.integral_prod_left.const_mul C) hb
  rw [integral_const_mul,← integral_prod _ hi] at hh
  exact hh

/-- The actual signed third-boundary expectation bound at volume-almost
every threshold. Only the displayed concentration hypothesis on the
arbitrary base law is used. -/
theorem ae_hardGaussianRidgeThirdBoundaryIntegral_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p)
    {K δ σ : ℝ} (hK : 0≤K) (hδ : 0≤δ) (hσ : 0<σ)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ),0<s → ν.real (faceLayer (fun k => U (f k)) b s)≤K*(s+δ)) :
    ∀ᵐ a : Vector m ∂volume,
      Integrable (fun x => hardGaussianRidgeThirdBoundaryIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)) ν ∧
      (∫ x,|hardGaussianRidgeThirdBoundaryIntegral (fun k => U (f k))
        (fun k => (a k-faceDot (U (f k)) x)/σ)| ∂ν)≤
        (6144*Real.exp ((3:ℝ)/2))*Real.exp 128*K*
          (σ*(dimensionLog p*Real.sqrt (dimensionLog p))+δ*(dimensionLog p)^2) := by
  filter_upwards [ae_threshold_ae_base_pairResidualThresholdRegularity ν (fun k => U (f k)) hσ.ne'] with a ha
  have hh := hardGaussianRidgeThirdBoundaryIntegral_base_tube_bound hp ν U f a hσ hu ha
  refine ⟨hh.1,hh.2.trans ?_⟩
  have ht := concentrated_base_threeFace_weighted_outward_tube hp ν (fun k => U (f k)) a U hK hδ hσ hbase
  exact (mul_le_mul_of_nonneg_left ht (by positivity : 0≤6144*Real.exp ((3:ℝ)/2))).trans_eq (by ring)

end
end RectangleCLTArxivV1
