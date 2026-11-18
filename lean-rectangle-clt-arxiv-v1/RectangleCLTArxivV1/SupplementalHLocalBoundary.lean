import RectangleCLTArxivV1.SupplementalHLocalThreshold
import RectangleCLTArxivV1.SupplementalHLocalPartials

/-! Actual hard Gaussian differential and boundary laws at locally
regular thresholds. Parallel signed faces with positive width are
included; no whole-family independence is needed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section

/-- The actual CDF is genuinely Fréchet differentiable at locally regular
thresholds, including parallel faces with nonzero slack. -/
theorem hasFDerivAt_gaussianThresholdCDF_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j)=1) (hreg : LocalThresholdRegularity u b) :
    HasFDerivAt (gaussianThresholdCDF u)
      (∑ j, gaussianThresholdFirst u b j • (ContinuousLinearMap.proj j : Vector m →L[ℝ] ℝ)) b := by
  apply hasFDerivAt_of_local_continuous_coordinate_derivatives
    (gaussianThresholdCDF u) (fun c j => gaussianThresholdFirst u c j)
    b {c | LocalThresholdRegularity u c} (localThresholdRegularity_isOpen u) hreg
  · intro c hc j
    have hd := hasDerivAt_gaussianThresholdCDF_update_of_slack u c j (hu j) (c j)
      (fun l hl => hc j l (Finset.mem_erase.mp hl).1)
    rwa [←gaussianThresholdFirst_eq_section_of_slack u c j (hu j) (hc j)] at hd
  · intro j
    exact continuousAt_gaussianThresholdFirst_of_slack u b j (hu j) (hreg j)

/-- The actual radial score has the genuine signed facet derivative sum
without any restriction on the number of faces. -/
theorem gaussianThresholdTrace_eq_radial_first_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j)=1) (hreg : LocalThresholdRegularity u b) :
    gaussianThresholdTrace u b=-(∑ j, b j*gaussianThresholdFirst u b j) := by
  have hC := hasFDerivAt_gaussianThresholdCDF_of_slack u b hu hreg
  have hp : HasDerivAt (fun t : ℝ => fun j : Fin m => Real.exp (-t)*b j)
      (fun j => -b j) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa using (((hasDerivAt_id (0:ℝ)).neg).exp).mul_const (b j)
  have hC' : HasFDerivAt (gaussianThresholdCDF u)
      (∑ j, gaussianThresholdFirst u b j • (ContinuousLinearMap.proj j : Vector m →L[ℝ] ℝ))
      (fun j => Real.exp (-(0:ℝ))*b j) := by simpa using hC
  have hd := hC'.comp_hasDerivAt 0 hp
  have he := (hasDerivAt_gaussianThresholdCDF_logScale u b).unique hd
  rw [he]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Actual threshold translation differentiates to its signed facet
sum at locally regular thresholds. -/
theorem hasDerivAt_gaussianThresholdCDF_translate_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j)=1) (hreg : LocalThresholdRegularity u b)
    (v : Vector (n+1)) :
    HasDerivAt (fun t : ℝ => gaussianThresholdCDF u (fun j => b j-t*faceDot (u j) v))
      (-(∑ j, faceDot (u j) v*gaussianThresholdFirst u b j)) 0 := by
  have hc := hasFDerivAt_gaussianThresholdCDF_of_slack u b hu hreg
  have ht : HasDerivAt (fun t : ℝ => fun j : Fin m => b j-t*faceDot (u j) v)
      (fun j => -faceDot (u j) v) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa using (hasDerivAt_const (0:ℝ) (b j)).sub
      ((hasDerivAt_id (0:ℝ)).mul_const (faceDot (u j) v))
  have hh := hc.comp_hasDerivAt_of_eq 0 ht (by simp)
  convert hh using 1
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Translation of the actual hard polyhedron is the actual shifted
threshold CDF, for every threshold value. -/
theorem integral_hard_polyhedron_translate {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (v : Vector r) (t : ℝ) :
    (∫ g, (gaussianFiniteThresholdEvent Finset.univ u b).indicator (fun _ => (1:ℝ))
      (g+t • v) ∂standardGaussian r)=
      gaussianThresholdCDF u (fun j => b j-t*faceDot (u j) v) := by
  have hcdf : gaussianThresholdCDF u (fun j => b j-t*faceDot (u j) v)=
      gaussianFiniteThresholdCDF Finset.univ u (fun j => b j-t*faceDot (u j) v) := by
    simp [gaussianThresholdCDF,gaussianFiniteThresholdCDF,gaussianFiniteThresholdEvent]
  rw [hcdf,gaussianFiniteThresholdCDF_eq_integral]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    change (gaussianFiniteThresholdEvent Finset.univ u b).indicator (fun _ => (1:ℝ)) (g+t • v)=
      (gaussianFiniteThresholdEvent Finset.univ u (fun j => b j-t*faceDot (u j) v)).indicator (fun _ => 1) g
    have he : g+t • v∈gaussianFiniteThresholdEvent Finset.univ u b ↔
        g∈gaussianFiniteThresholdEvent Finset.univ u (fun j => b j-t*faceDot (u j) v) := by
      simp only [gaussianFiniteThresholdEvent,mem_setOf_eq,
        threshold_faceDot_add_right,threshold_faceDot_smul_right]
      apply forall_congr'
      intro j
      apply forall_congr'
      intro _
      constructor <;> intro h <;> linarith
    by_cases hg : g∈gaussianFiniteThresholdEvent Finset.univ u (fun j => b j-t*faceDot (u j) v)
    · rw [Set.indicator_of_mem (he.mpr hg),Set.indicator_of_mem hg]
    · rw [Set.indicator_of_not_mem (fun h => hg (he.mp h)),Set.indicator_of_not_mem hg])

/-- Actual Gaussian first-moment integration by parts, now including
parallel signed faces whenever their thresholds have nonzero slack. -/
theorem gaussian_hard_polyhedron_firstMoment_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j)=1) (hreg : LocalThresholdRegularity u b)
    (v : Vector (n+1)) :
    (∫ g in gaussianFiniteThresholdEvent Finset.univ u b, faceDot v g ∂standardGaussian (n+1))=
      -(∑ j, faceDot (u j) v*gaussianThresholdFirst u b j) := by
  let P := gaussianFiniteThresholdEvent Finset.univ u b
  have hP : MeasurableSet P := measurableSet_gaussianFiniteThresholdEvent _ _ _
  let w : Vector (n+1) → ℝ := P.indicator (fun _ => 1)
  have hw : Measurable w := measurable_const.indicator hP
  have hw0 (g) : 0≤w g := by by_cases hg : g∈P <;> simp [w,hg]
  have hw1 (g) : w g≤1 := by by_cases hg : g∈P <;> simp [w,hg]
  have hd := hasDerivAt_gaussian_weight_translate w hw hw0 hw1 v
  have he (t : ℝ) : (∫ g, w (g+t • v) ∂standardGaussian (n+1))=
      gaussianThresholdCDF u (fun j => b j-t*faceDot (u j) v) :=
    integral_hard_polyhedron_translate u b v t
  have hd' : HasDerivAt (fun t : ℝ => gaussianThresholdCDF u (fun j => b j-t*faceDot (u j) v))
      (∫ g, w g*faceDot v g ∂standardGaussian (n+1)) 0 := by simpa only [he] using hd
  have h := hd'.unique (hasDerivAt_gaussianThresholdCDF_translate_of_slack u b hu hreg v)
  rw [←integral_indicator hP]
  convert h using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by by_cases hg : g∈P <;> simp [w,hg])

end
end RectangleCLTArxivV1
