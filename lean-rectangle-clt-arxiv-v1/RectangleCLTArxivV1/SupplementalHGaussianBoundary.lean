import RectangleCLTArxivV1.SupplementalHThresholdRegularity
import RectangleCLTArxivV1.SupplementalHSurfaceMeasure
import RectangleCLTCompanion.TiltContractionMoments

/-! The Gaussian first-moment boundary law is obtained from the actual
Cameron--Martin formula and the genuine hard-threshold derivative. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section

/-- Translation of a bounded measurable weight differentiates to its
actual Gaussian first moment. -/
theorem hasDerivAt_gaussian_weight_translate {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0≤w x)
    (hw1 : ∀ x, w x≤1) (v : Vector r) :
    HasDerivAt (fun t : ℝ => ∫ g, w (g+t • v) ∂standardGaussian r)
      (∫ g, w g*faceDot v g ∂standardGaussian r) 0 := by
  let X := fun g => faceDot v g
  let ν := gaussianTilt w
  have hE : (0:ℝ) ∈ interior (integrableExpSet X ν) := by
    rw [gaussianTilt_integrableExpSet w hw hw0 hw1 v, interior_univ]
    trivial
  have hm : HasDerivAt (mgf X ν) (∫ g, w g*faceDot v g ∂standardGaussian r) 0 := by
    simpa only [zero_mul,Real.exp_zero,mul_one,ν,X,gaussianTilt_integral w hw hw0] using
      (hasDerivAt_mgf hE)
  have hp : HasDerivAt (fun t : ℝ => Real.exp (-(t^2*vectorNormSq v/2))) 0 0 := by
    convert (((hasDerivAt_id (0:ℝ)).pow 2).mul_const (vectorNormSq v)).div_const 2 |>.neg |>.exp using 1
    simp
  have he (t : ℝ) : (∫ g, w (g+t • v) ∂standardGaussian r)=
      Real.exp (-(t^2*vectorNormSq v/2))*mgf X ν t := by
    have hcm := gaussian_exponential_translation w (t • v)
    have hd (g : Vector r) : faceDot (t • v) g=t*faceDot v g := by
      simp only [faceDot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hn : vectorNormSq (t • v)=t^2*vectorNormSq v := by
      simp only [vectorNormSq,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
    simp_rw [hd,hn] at hcm
    have hmg : mgf X ν t=∫ g, w g*Real.exp (t*faceDot v g) ∂standardGaussian r :=
      gaussianTilt_integral w hw hw0 _
    rw [hmg,hcm,←mul_assoc,←Real.exp_add]
    simp
  simpa only [he,zero_pow (by decide : 2≠0),zero_mul,zero_div,neg_zero,
    Real.exp_zero,mul_zero,mul_one,zero_add,one_mul] using hp.mul hm

/-- Actual Gaussian first moment equals the signed sum of the genuine
hard-facet Gaussian masses. Full-family linear independence is unnecessary. -/
theorem gaussian_hard_polyhedron_firstMoment {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u)
    (v : Vector (n+1)) :
    (∫ g in gaussianFiniteThresholdEvent Finset.univ u b,
      faceDot v g ∂standardGaussian (n+1))=
      -(∑ j, faceDot (u j) v*gaussianThresholdFirst u b j) := by
  let P := gaussianFiniteThresholdEvent Finset.univ u b
  have hP : MeasurableSet P := measurableSet_gaussianFiniteThresholdEvent _ _ _
  let w : Vector (n+1) → ℝ := P.indicator (fun _ => 1)
  have hw : Measurable w := measurable_const.indicator hP
  have hw0 (g) : 0≤w g := by by_cases hg : g∈P <;> simp [w,hg]
  have hw1 (g) : w g≤1 := by by_cases hg : g∈P <;> simp [w,hg]
  have hd := hasDerivAt_gaussian_weight_translate w hw hw0 hw1 v
  have he (t : ℝ) : (∫ g, w (g+t • v) ∂standardGaussian (n+1))=
      gaussianThresholdCDF u (fun j => b j-t*faceDot (u j) v) := by
    have hcdf : gaussianThresholdCDF u (fun j => b j-t*faceDot (u j) v)=
        gaussianFiniteThresholdCDF Finset.univ u (fun j => b j-t*faceDot (u j) v) := by
      simp [gaussianThresholdCDF,gaussianFiniteThresholdCDF,gaussianFiniteThresholdEvent]
    rw [hcdf,gaussianFiniteThresholdCDF_eq_integral]
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by
      have hiff : g+t • v∈P ↔ g∈gaussianFiniteThresholdEvent Finset.univ u (fun j => b j-t*faceDot (u j) v) := by
        constructor <;> intro hg j hj
        · have hh := hg j hj
          change faceDot (u j) (g+t • v)≤b j at hh
          have heq : faceDot (u j) (g+t • v)=faceDot (u j) g+t*faceDot (u j) v := by
            simp only [faceDot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro k _
            ring
          rw [heq] at hh
          change faceDot (u j) g≤b j-t*faceDot (u j) v
          linarith
        · have hh := hg j hj
          change faceDot (u j) g≤b j-t*faceDot (u j) v at hh
          change faceDot (u j) (g+t • v)≤b j
          have heq : faceDot (u j) (g+t • v)=faceDot (u j) g+t*faceDot (u j) v := by
            simp only [faceDot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro k _
            ring
          rw [heq]
          linarith
      by_cases hg : g∈gaussianFiniteThresholdEvent Finset.univ u (fun j => b j-t*faceDot (u j) v)
      · simp only [w,Set.indicator_of_mem ((hiff).mpr hg),Set.indicator_of_mem hg]
      · simp only [w,Set.indicator_of_not_mem (fun hh => hg (hiff.mp hh)),Set.indicator_of_not_mem hg])
  have hd' : HasDerivAt (fun t : ℝ => gaussianThresholdCDF u (fun j => b j-t*faceDot (u j) v))
      (∫ g, w g*faceDot v g ∂standardGaussian (n+1)) 0 := by simpa only [he] using hd
  have h := hd'.unique (hasDerivAt_gaussianThresholdCDF_translate_nonparallel u hu hp b v)
  rw [←integral_indicator hP]
  convert h using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by by_cases hg : g∈P <;> simp [w,hg])


/-- The actual Gaussian mass of the hard supporting facet. -/
def hardGaussianFacetMass {m n : ℕ} (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) : ℝ :=
  ∫ x in gaussianFiniteThresholdEvent Finset.univ u b,
    standardGaussianDensity (n+1) x ∂affineSurfaceVolume (0 : Fin (n+1)) (u j) (b j)

/-- The first hard-threshold derivative is precisely the actual
Gaussian-weighted affine facet mass. -/
theorem hardGaussianFacetMass_eq_first {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u) :
    hardGaussianFacetMass u b j=gaussianThresholdFirst u b j := by
  let P := gaussianFiniteThresholdEvent Finset.univ u b
  let Q := gaussianFiniteThresholdEvent (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l))
    (fun l => b l-b j*faceDot (u l) (u j))
  have hP : MeasurableSet P := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have he (g : Vector (n+1)) : gaussianSectionPoint (u j) (b j) g∈P ↔ g∈Q := by
    constructor
    · intro h l hl
      have hh := h l (Finset.mem_univ _)
      rw [gaussianSectionPoint_faceDot] at hh
      change faceDot (gaussianNormalProjection (u j) (u l)) g≤b l-b j*faceDot (u l) (u j)
      linarith
    · intro h l _
      by_cases hlj : l=j
      · subst l
        rw [gaussianSectionPoint_on_hyperplane (u j) (b j) hu]
      · have hh := h l (Finset.mem_erase.mpr ⟨hlj,Finset.mem_univ _⟩)
        rw [gaussianSectionPoint_faceDot]
        dsimp only at hh
        linarith
  unfold hardGaussianFacetMass
  rw [←integral_indicator hP]
  have hs := affineSurfaceVolume_gaussian_integral (0 : Fin (n+1)) (u j) hu (b j)
    (P.indicator (fun _ => 1))
  have heq : (∫ x, P.indicator (standardGaussianDensity (n+1)) x
      ∂affineSurfaceVolume (0 : Fin (n+1)) (u j) (b j))=
      gaussianPDFReal 0 1 (b j)*(∫ x, P.indicator (fun _ => 1) x ∂gaussianSectionLaw (u j) (b j)) := by
    convert hs using 1
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by by_cases hx : x∈P <;> simp [hx])
  rw [heq,gaussianThresholdFirst_eq_section_nonparallel u b j hu hp]
  congr 1
  unfold gaussianSectionLaw
  rw [integral_map (measurable_gaussianSectionPoint (u j) (b j)).aemeasurable
    (measurable_const.indicator hP).aestronglyMeasurable]
  change (∫ g, P.indicator (fun _ => (1:ℝ)) (gaussianSectionPoint (u j) (b j) g)
    ∂standardGaussian (n+1))=gaussianFiniteThresholdCDF (Finset.univ.erase j)
      (fun l => gaussianNormalProjection (u j) (u l)) (fun l => b l-b j*faceDot (u l) (u j))
  rw [gaussianFiniteThresholdCDF_eq_integral]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    change P.indicator (fun _ => (1:ℝ)) (gaussianSectionPoint (u j) (b j) g)=Q.indicator (fun _ => 1) g
    by_cases hg : g∈Q
    · rw [Set.indicator_of_mem ((he g).mpr hg),Set.indicator_of_mem hg]
    · rw [Set.indicator_of_not_mem (fun hh => hg ((he g).mp hh)),Set.indicator_of_not_mem hg])

/-- The Gaussian boundary law with genuine affine surface integrals. -/
theorem gaussian_hard_polyhedron_firstMoment_surface {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u)
    (v : Vector (n+1)) :
    (∫ g in gaussianFiniteThresholdEvent Finset.univ u b,
      faceDot v g ∂standardGaussian (n+1))=
      -(∑ j, faceDot (u j) v*hardGaussianFacetMass u b j) := by
  simp_rw [hardGaussianFacetMass_eq_first u b _ (hu _) hp]
  exact gaussian_hard_polyhedron_firstMoment u b hu hp v

/-- Unnormalized Euclidean Gaussian first-moment boundary law. Its facet
coefficients are actual Gaussian kernel integrals in orthogonal charts. -/
theorem gaussian_hard_polyhedron_firstMoment_kernel {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u)
    (v : Vector (n+1)) :
    (∫ g in gaussianFiniteThresholdEvent Finset.univ u b,
      gaussianKernel g*faceDot v g ∂volume)=
      -(∑ j, faceDot (u j) v*(∫ g in gaussianFiniteThresholdEvent Finset.univ u b,
        gaussianKernel g ∂affineSurfaceVolume (0 : Fin (n+1)) (u j) (b j))) := by
  let P := gaussianFiniteThresholdEvent Finset.univ u b
  have hP : MeasurableSet P := measurableSet_gaussianFiniteThresholdEvent _ _ _
  let c : ℝ := ((Real.sqrt (2*Real.pi))⁻¹)^(n+1)
  have hc : c≠0 := pow_ne_zero _ (inv_ne_zero (Real.sqrt_pos.mpr (by positivity)).ne')
  have h := gaussian_hard_polyhedron_firstMoment_surface u b hu hp v
  have hl : (∫ g in P, faceDot v g ∂standardGaussian (n+1))=
      c*(∫ g in P, gaussianKernel g*faceDot v g ∂volume) := by
    rw [←integral_indicator hP,standardGaussian_integral_density_mul]
    rw [←integral_indicator hP,←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by
      by_cases hg : g∈P
      · simp only [Set.indicator_of_mem hg,standardGaussianDensity_eq_kernel]
        change c*gaussianKernel g*faceDot v g=c*(gaussianKernel g*faceDot v g)
        ring
      · simp only [Set.indicator_of_not_mem hg,mul_zero])
  have hr (j : Fin m) : hardGaussianFacetMass u b j=
      c*(∫ g in P, gaussianKernel g ∂affineSurfaceVolume (0 : Fin (n+1)) (u j) (b j)) := by
    unfold hardGaussianFacetMass
    simp_rw [standardGaussianDensity_eq_kernel]
    rw [integral_const_mul]
  rw [hl] at h
  simp_rw [hr] at h
  have he : -(∑ j, faceDot (u j) v*(c*(∫ g in P, gaussianKernel g
      ∂affineSurfaceVolume (0 : Fin (n+1)) (u j) (b j))))=
      c*(-∑ j, faceDot (u j) v*(∫ g in P, gaussianKernel g
        ∂affineSurfaceVolume (0 : Fin (n+1)) (u j) (b j))) := by
    rw [mul_neg,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  exact mul_left_cancel₀ hc h

end
end RectangleCLTArxivV1
