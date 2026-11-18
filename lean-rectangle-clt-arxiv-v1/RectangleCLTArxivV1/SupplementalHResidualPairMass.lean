import RectangleCLTArxivV1.SupplementalHResidualGreen
import RectangleCLTCompanion.SplitV4.GaussianThresholdPairCoarea

/-! Actual residual facet derivatives in a symmetric two-normal Gaussian
ridge frame. Inactive inequalities remain non-strict. No full-family
independence or assumed symmetry of a derivative is used. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section

/-- The actual symmetric two-normal Gaussian ridge density, with its
Gram Jacobian and the remaining hard inequalities in the actual pair
section. The inactive inequalities are deliberately retained as `≤`. -/
def hardGaussianRidgeDensity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (j l : Fin m) : ℝ :=
  (gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
    gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)/
      Real.sqrt (1-faceDot (u j) (u l)^2))*
    (standardGaussian r).real {g | ∀ k, k≠j → k≠l →
      faceDot (u k) (gaussianPairBase u b j l g)≤b k}

theorem hardGaussianRidgeDensity_nonneg {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (j l : Fin m) : 0≤hardGaussianRidgeDensity u b j l := by
  unfold hardGaussianRidgeDensity
  exact mul_nonneg
    (div_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _))
      (Real.sqrt_nonneg _)) measureReal_nonneg

/-- The actual conditional residual Gaussian section is exactly the
actual two-normal ridge section, with all inactive inequalities retained. -/
theorem gaussianResidualSectionProbability_eq_pairBase_le {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    gaussianThresholdSectionProbability ((Finset.univ.erase j).erase l)
      (gaussianThresholdResidualNormals u j) (gaussianThresholdResidualLevels u b j)
      (gaussianPairConditionalDirection u j l) (gaussianPairConditionalLevel u b j l)=
      (standardGaussian r).real {g | ∀ k, k≠j → k≠l →
        faceDot (u k) (gaussianPairBase u b j l g)≤b k} := by
  classical
  rw [gaussianThresholdSectionProbability_eq_section]
  congr 1
  ext g
  have hdot (k : Fin m) : faceDot (u k) (gaussianPairBase u b j l g)=
      b j*faceDot (u k) (u j)+faceDot (gaussianThresholdResidualNormals u j k)
        (gaussianSectionPoint (gaussianPairConditionalDirection u j l)
          (gaussianPairConditionalLevel u b j l) g) := by
    rw [← gaussianPairConditionalBase_eq_pairBase u b j l hu hv hp hm g]
    exact gaussianSectionPoint_faceDot (u j) (u k) _ (b j)
  constructor
  · intro h k hkj hkl
    have hk := h k (Finset.mem_erase.mpr ⟨hkl,Finset.mem_erase.mpr ⟨hkj,Finset.mem_univ _⟩⟩)
    change faceDot (gaussianThresholdResidualNormals u j k)
      (gaussianSectionPoint (gaussianPairConditionalDirection u j l)
        (gaussianPairConditionalLevel u b j l) g)≤b k-b j*faceDot (u k) (u j) at hk
    rw [hdot]
    linarith
  · intro h k hk
    have hk' := h k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1
    rw [hdot] at hk'
    change faceDot (gaussianThresholdResidualNormals u j k)
      (gaussianSectionPoint (gaussianPairConditionalDirection u j l)
        (gaussianPairConditionalLevel u b j l) g)≤b k-b j*faceDot (u k) (u j)
    linarith

/-- The residual derivative is the actual symmetric ridge density. The
only normal restrictions concern the selected nonparallel unit pair. -/
theorem hardFacetResidualDensity_eq_ridgeDensity {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hreg : ResidualThresholdRegularity u b j) :
    hardFacetResidualDensity u b j l=hardGaussianRidgeDensity u b j l := by
  classical
  let s := Finset.univ.erase j
  let v := gaussianThresholdResidualNormals u j
  let d := gaussianThresholdResidualLevels u b j
  let σ := gaussianThresholdResidualScale u j l
  have hσ : 0<σ := by
    rw [show σ=2*thresholdPairFirstCoefficient u j l*thresholdPairSecondCoefficient u j l from
      thresholdPair_residualScale_eq u j l hu hv hp hm]
    exact mul_pos (mul_pos (by norm_num)
      (div_pos (norm_pos_iff.mpr hp) (by norm_num)))
      (div_pos (norm_pos_iff.mpr hm) (by norm_num))
  have hnorm : vectorNormSq (v l)=σ^2 := (Real.sq_sqrt (vectorNormSq_nonneg _)).symm
  have hl : l∈s := Finset.mem_erase.mpr ⟨Ne.symm hjl,Finset.mem_univ _⟩
  have hlocal : ∀ k∈s.erase l, gaussianNormalProjection (σ⁻¹ • v l) (v k)≠0 ∨
      d k-(d l/σ)*faceDot (v k) (σ⁻¹ • v l)≠0 := (hreg l hl).2
  unfold hardFacetResidualDensity
  change gaussianPDFReal 0 1 (b j)*gaussianFiniteThresholdFirst s v d l=_
  rw [gaussianFiniteThresholdFirst_eq_section_of_slack s v d l hl hσ hnorm hlocal]
  have hprob := gaussianResidualSectionProbability_eq_pairBase_le u b j l hu hv hp hm
  change gaussianThresholdSectionProbability (s.erase l) v d (σ⁻¹ • v l) (d l/σ)=_ at hprob
  rw [hprob]
  have hdens := gaussianPair_conditional_density_eq u b j l hu hv hp hm
  change gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 (d l/σ)=_ at hdens
  unfold hardGaussianRidgeDensity
  calc
    _ = (gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 (d l/σ)/σ)*
        (standardGaussian (n+1)).real {g | ∀ k, k≠j → k≠l →
          faceDot (u k) (gaussianPairBase u b j l g)≤b k} := by ring
    _ = _ := by
      rw [hdens]
      dsimp only [σ]
      rw [gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv]

theorem thresholdPairBisector_swap {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m) :
    thresholdPairBisector u l j=thresholdPairBisector u j l := by
  ext k
  simp only [thresholdPairBisector,bisector,add_comm]

theorem thresholdPairDifference_swap {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m) :
    thresholdPairDifference u l j= -thresholdPairDifference u j l := by
  ext k
  change ‖projectionEuclideanVector (u l)-projectionEuclideanVector (u j)‖⁻¹*(u l k-u j k)=
    -(‖projectionEuclideanVector (u j)-projectionEuclideanVector (u l)‖⁻¹*(u j k-u l k))
  rw [norm_sub_rev]
  ring

theorem thresholdPairFirstLevel_swap {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    thresholdPairFirstLevel u b l j=thresholdPairFirstLevel u b j l := by
  simp only [thresholdPairFirstLevel,add_comm]

theorem thresholdPairSecondLevel_swap {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    thresholdPairSecondLevel u b l j= -thresholdPairSecondLevel u b j l := by
  unfold thresholdPairSecondLevel
  rw [norm_sub_rev]
  ring

theorem gaussianSectionPoint_neg_normal {r : ℕ} (u : Vector r) (b : ℝ) (g : Vector r) :
    gaussianSectionPoint (-u) (-b) g=gaussianSectionPoint u b g := by
  have hd : faceDot (-u) g= -faceDot u g := by
    simp only [faceDot,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
  unfold gaussianSectionPoint gaussianSectionResidual
  rw [hd]
  ext k
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
  ring

/-- Swapping the selected faces leaves the actual pair section point
unchanged; its difference direction and coordinate change signs together. -/
theorem gaussianPairBase_swap {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (j l : Fin m) (g : Vector r) :
    gaussianPairBase u b l j g=gaussianPairBase u b j l g := by
  unfold gaussianPairBase
  rw [thresholdPairBisector_swap u j l,thresholdPairDifference_swap u j l,
    thresholdPairFirstLevel_swap u b j l,thresholdPairSecondLevel_swap u b j l]
  unfold gaussianPairSectionPoint
  rw [gaussianSectionPoint_neg_normal]

/-- Symmetry of the actual ridge density is geometric and does not
require a mixed-partials symmetry theorem. -/
theorem hardGaussianRidgeDensity_symm {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (j l : Fin m) :
    hardGaussianRidgeDensity u b j l=hardGaussianRidgeDensity u b l j := by
  unfold hardGaussianRidgeDensity
  rw [thresholdPairFirstLevel_swap u b j l,thresholdPairSecondLevel_swap u b j l,
    faceDot_comm (u l) (u j)]
  have hpdf (t : ℝ) : gaussianPDFReal 0 1 (-t)=gaussianPDFReal 0 1 t := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,neg_sq]
  rw [hpdf]
  congr 1
  apply congrArg (fun P : Set (Vector r) => (standardGaussian r).real P)
  ext g
  simp only [mem_setOf_eq,gaussianPairBase_swap u b j l g]
  constructor <;> intro h k hkj hkl <;> exact h k hkl hkj

theorem gaussianFiniteThresholdFirst_nonneg_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (hreg : LocalFiniteThresholdRegularity s u b) (j : Fin m) :
    0≤gaussianFiniteThresholdFirst s u b j := by
  classical
  by_cases hj : j∈s
  · by_cases hu : u j=0
    · rw [gaussianFiniteThresholdFirst_zero_of_slack s u b j hj hu
        ((hreg j hj).1.resolve_left (not_not.mpr hu))]
    · have hσ : 0<localFiniteThresholdScale u j := Real.sqrt_pos.mpr (vectorNormSq_pos hu)
      rw [gaussianFiniteThresholdFirst_eq_section_of_slack s u b j hj hσ
        (Real.sq_sqrt (vectorNormSq_nonneg _)).symm (hreg j hj).2]
      exact mul_nonneg (div_nonneg (gaussianPDFReal_nonneg _ _ _) hσ.le)
        (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)
  · rw [gaussianFiniteThresholdFirst_outside s u b j hj]

theorem hardFacetResidualDensity_nonneg {m n : ℕ} (u : Fin m → Vector (n+1))
    (b : Vector m) (j l : Fin m) (hreg : ResidualThresholdRegularity u b j) :
    0≤hardFacetResidualDensity u b j l := by
  unfold hardFacetResidualDensity
  exact mul_nonneg (gaussianPDFReal_nonneg _ _ _)
    (gaussianFiniteThresholdFirst_nonneg_of_slack _ _ _ hreg l)

/-- Parallel residual normals give zero ridge derivative when their
actual affine slack is nonzero. -/
theorem hardFacetResidualDensity_zero_of_parallel_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hpar : gaussianNormalProjection (u j) (u l)=0)
    (hslack : b l-b j*faceDot (u l) (u j)≠0) :
    hardFacetResidualDensity u b j l=0 := by
  unfold hardFacetResidualDensity
  rw [gaussianFiniteThresholdFirst_zero_of_slack _ _ _ l
    (Finset.mem_erase.mpr ⟨Ne.symm hjl,Finset.mem_univ _⟩) hpar hslack,mul_zero]

theorem hardFacetResidualDensity_symm_nonparallel {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hregj : ResidualThresholdRegularity u b j) (hregl : ResidualThresholdRegularity u b l) :
    hardFacetResidualDensity u b j l=hardFacetResidualDensity u b l j := by
  have hp' : projectionEuclideanVector (u l)+projectionEuclideanVector (u j)≠0 := by
    simpa only [add_comm] using hp
  have hm' : projectionEuclideanVector (u l)-projectionEuclideanVector (u j)≠0 := by
    simpa only [sub_ne_zero,ne_comm] using hm
  rw [hardFacetResidualDensity_eq_ridgeDensity u b j l hjl hu hv hp hm hregj,
    hardFacetResidualDensity_eq_ridgeDensity u b l j (Ne.symm hjl) hv hu hp' hm' hregl]
  exact hardGaussianRidgeDensity_symm u b j l

private theorem unit_normal_projection_self {r : ℕ} (u : Vector r) (hu : vectorNormSq u=1) :
    gaussianNormalProjection u u=0 := by
  have hd : faceDot u u=1 := by simpa only [faceDot,vectorNormSq,pow_two] using hu
  simp only [gaussianNormalProjection,hd,one_smul,sub_self]

private theorem unit_normal_projection_neg {r : ℕ} (u : Vector r) (hu : vectorNormSq u=1) :
    gaussianNormalProjection u (-u)=0 := by
  have hself : faceDot u u=1 := by simpa only [faceDot,vectorNormSq,pow_two] using hu
  have hd : faceDot (-u) u= -1 := by
    simp only [faceDot,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
    change -faceDot u u= -1
    rw [hself]
  simp only [gaussianNormalProjection,hd,neg_one_smul,sub_self]

theorem gaussianNormalProjection_pair_zero_of_parallel_unit {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hpar : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)=0 ∨
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)=0) :
    gaussianNormalProjection (u j) (u l)=0 ∧ gaussianNormalProjection (u l) (u j)=0 := by
  rcases hpar with hp | hm
  · have he : u l= -u j := by
      ext k
      have hk := congrArg (fun z : EuclideanSpace ℝ (Fin r) => z k) hp
      change u j k+u l k=0 at hk
      change u l k= -(u j k)
      linarith
    have he' : u j= -u l := by rw [he,neg_neg]
    constructor
    · rw [he]
      exact unit_normal_projection_neg _ hu
    · rw [he']
      exact unit_normal_projection_neg _ hv
  · have he : u l=u j := by
      ext k
      have hk := congrArg (fun z : EuclideanSpace ℝ (Fin r) => z k) (sub_eq_zero.mp hm)
      exact hk.symm
    constructor
    · rw [he]
      exact unit_normal_projection_self _ hu
    · rw [← he]
      exact unit_normal_projection_self _ hv

/-- Symmetry holds for every pair of unit normals at locally regular
residual thresholds. Parallel pairs contribute zero on both sides. -/
theorem hardFacetResidualDensity_symm {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hregj : ResidualThresholdRegularity u b j) (hregl : ResidualThresholdRegularity u b l) :
    hardFacetResidualDensity u b j l=hardFacetResidualDensity u b l j := by
  classical
  by_cases hjl : j=l
  · subst l
    rfl
  have hzero (hpar : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)=0 ∨
      projectionEuclideanVector (u j)-projectionEuclideanVector (u l)=0) :
      hardFacetResidualDensity u b j l=hardFacetResidualDensity u b l j := by
    obtain ⟨hzj,hzl⟩ := gaussianNormalProjection_pair_zero_of_parallel_unit u j l hu hv hpar
    have hjmem : j∈Finset.univ.erase l := Finset.mem_erase.mpr ⟨hjl,Finset.mem_univ _⟩
    have hlmem : l∈Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hjl,Finset.mem_univ _⟩
    have hsj : b l-b j*faceDot (u l) (u j)≠0 :=
      (hregj l hlmem).1.resolve_left (not_not.mpr hzj)
    have hsl : b j-b l*faceDot (u j) (u l)≠0 :=
      (hregl j hjmem).1.resolve_left (not_not.mpr hzl)
    rw [hardFacetResidualDensity_zero_of_parallel_slack u b j l hjl hzj hsj,
      hardFacetResidualDensity_zero_of_parallel_slack u b l j (Ne.symm hjl) hzl hsl]
  by_cases hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0
  · by_cases hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0
    · exact hardFacetResidualDensity_symm_nonparallel u b j l hjl hu hv hp hm hregj hregl
    · exact hzero (Or.inr (not_not.mp hm))
  · exact hzero (Or.inl (not_not.mp hp))

end
end RectangleCLTArxivV1
