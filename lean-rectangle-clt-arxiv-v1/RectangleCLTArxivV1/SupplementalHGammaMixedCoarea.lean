import RectangleCLTArxivV1.SupplementalHGammaMixedDerivative
import RectangleCLTArxivV1.SupplementalHLogisticPairCoordinateDerivative

/-! The exact second signed soft/coarea identity, obtained by
differentiating two distinct original thresholds under their actual laws. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem supplementalH_signedMixed_soft_coarea {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ k,vectorNormSq (u k)=1)
    (a : Vector m) {h σ : ℝ} (hh : 0<h) (hσ : 0<σ)
    (x : Vector (n+1)) (j l : Fin m) (hjl : j≠l)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (q : ℕ) :
    ((((q:ℝ)+1)/h)*(((q:ℝ)+2)/h))*(∫ g, (vectorNormSq g-((n+1:ℕ):ℝ))*
      (logisticNullWeight u a h (x+σ • g)^(q+1)*
        logisticFaceWeight u a h (x+σ • g) j*logisticFaceWeight u a h (x+σ • g) l)
      ∂standardGaussian (n+1)) =
      σ⁻¹*(σ⁻¹*(∫ e, supplementalHSignedMixedKernel u
        (fun k => (gammaAdjustedThreshold a h e k-faceDot (u k) x)/σ) j l
        ∂gammaRectangleLaw m q)) := by
  let P := fun g : Vector (n+1) => vectorNormSq g-((n+1:ℕ):ℝ)
  let S := fun t : ℝ => (((q:ℝ)+1)/h)*(∫ g, P g*
    (logisticNullWeight u (Function.update a l (a l+t)) h (x+σ • g)^(q+1)*
      logisticFaceWeight u (Function.update a l (a l+t)) h (x+σ • g) j)
    ∂standardGaussian (n+1))
  have hd := supplementalH_hasDerivAt_integral_logistic_power_face_offset
    (standardGaussian (n+1)) (fun g => x+σ • g) (by fun_prop)
    P ((SignedSurface.standardGaussian_integrable_vectorNormSq (n+1)).sub (integrable_const _))
    u a hh j l hjl q (a l)
  have hinner : HasDerivAt (fun t : ℝ => a l+t) 1 0 := by
    simpa using (hasDerivAt_id 0).const_add (a l)
  have hd' := (hd.comp_of_eq (0:ℝ) hinner (by simp)).const_mul (((q:ℝ)+1)/h)
  have hg := (supplementalH_hasDerivAt_gamma_signedMixed_offset u hu a hh hσ x j l hjl hp hm q).const_mul σ⁻¹
  have heS : S=(fun t => σ⁻¹*(∫ e,
      gaussianPDFReal 0 1 ((gammaAdjustedThreshold (Function.update a l (a l+t)) h e j-faceDot (u j) x)/σ)*
        Printed.thresholdSignedSection u
          (fun k => (gammaAdjustedThreshold (Function.update a l (a l+t)) h e k-faceDot (u k) x)/σ) j
          ((gammaAdjustedThreshold (Function.update a l (a l+t)) h e j-faceDot (u j) x)/σ)
      ∂gammaRectangleLaw m q)) := by
    funext t
    exact supplementalH_signedFace_soft_coarea u hu (Function.update a l (a l+t)) hh hσ x j q
  change HasDerivAt S _ 0 at hd'
  rw [heS] at hd'
  have he := hd'.unique hg
  simpa only [P,Function.update_eq_self,mul_one,mul_assoc] using he

end
end RectangleCLTArxivV1
