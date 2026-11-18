import RectangleCLTArxivV1.SupplementalHMixedCoareaDerivative
import RectangleCLTArxivV1.SupplementalHWeightedThresholdLipschitz

/-! Uniform threshold domination for the genuine signed mixed coarea
primitive. The finite constant depends on rank and the selected pair,
while all thresholds and sampled bases are unrestricted. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem abs_hardGaussianPairSignedSection_le {m n : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector (n+1)) (b : Vector m) (e f : Vector (n+1))
    (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hef : faceDot e f=0) (a c : ℝ) :
    |hardGaussianPairSignedSection s u b e f a c|≤a^2+c^2+2*((n+1:ℕ):ℝ) := by
  have hi := hardGaussianPairSignedSection_integrable s u b e f he hf hef a c
  have hp (g : Vector (n+1)) :
      |(gaussianFiniteThresholdEvent s u b).indicator (fun x => vectorNormSq x-((n+1:ℕ):ℝ))
        (gaussianPairSectionPoint e f a c g)|≤vectorNormSq g+a^2+c^2+((n+1:ℕ):ℝ) := by
    by_cases hg : gaussianPairSectionPoint e f a c g∈gaussianFiniteThresholdEvent s u b
    · rw [indicator_of_mem hg]
      apply abs_le.mpr
      have hn := vectorNormSq_nonneg (gaussianPairSectionPoint e f a c g)
      have hn' := vectorNormSq_gaussianPairSectionPoint e f he hf hef a c g
      constructor <;> nlinarith [vectorNormSq_nonneg g,sq_nonneg (faceDot e g),sq_nonneg (faceDot f g)]
    · rw [indicator_of_not_mem hg,abs_zero]
      have hn := vectorNormSq_nonneg g
      positivity
  have hB : Integrable (fun g : Vector (n+1) => vectorNormSq g+a^2+c^2+((n+1:ℕ):ℝ))
      (standardGaussian (n+1)) :=
    (((standardGaussian_integrable_vectorNormSq _).add (integrable_const _)).add (integrable_const _)).add (integrable_const _)
  have hh0 : |hardGaussianPairSignedSection s u b e f a c|≤
      ∫ g,|(gaussianFiniteThresholdEvent s u b).indicator (fun x => vectorNormSq x-((n+1:ℕ):ℝ))
        (gaussianPairSectionPoint e f a c g)| ∂standardGaussian (n+1) := abs_integral_le_integral_abs
  have hh := hh0.trans (integral_mono_ae hi.abs hB (ae_of_all _ hp))
  have heq : (∫ g : Vector (n+1),vectorNormSq g+a^2+c^2+((n+1:ℕ):ℝ) ∂standardGaussian (n+1))=
      a^2+c^2+2*((n+1:ℕ):ℝ) := by
    have hN := standardGaussian_integrable_vectorNormSq (n+1)
    have hA : Integrable (fun _ : Vector (n+1) => a^2) (standardGaussian (n+1)) := integrable_const _
    have hC : Integrable (fun _ : Vector (n+1) => c^2) (standardGaussian (n+1)) := integrable_const _
    have hR : Integrable (fun _ : Vector (n+1) => ((n+1:ℕ):ℝ)) (standardGaussian (n+1)) := integrable_const _
    have h1 := integral_add hN hA
    have h2 := integral_add (hN.add hA) hC
    have h3 := integral_add ((hN.add hA).add hC) hR
    simp only [Pi.add_apply] at h1 h2 h3
    rw [h3,h2,h1,standardGaussian_integral_vectorNormSq]
    simp only [integral_const,measureReal_univ_eq_one,smul_eq_mul,one_mul]
    ring
  exact hh.trans_eq heq

def gaussianMixedSectionDensityBudget (r : ℕ) : ℝ :=
  ((Real.sqrt (2*Real.pi))⁻¹)^2*(4+2*(r:ℝ))

theorem gaussianMixedSectionDensityBudget_nonneg (r : ℕ) : 0≤gaussianMixedSectionDensityBudget r := by
  unfold gaussianMixedSectionDensityBudget
  positivity

theorem gaussianPDFReal_pair_sq_add_dimension_le (r : ℕ) (a c : ℝ) :
    gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c*(a^2+c^2+2*(r:ℝ))≤gaussianMixedSectionDensityBudget r := by
  let N := (Real.sqrt (2*Real.pi))⁻¹
  have hN : 0≤N := by dsimp [N]; positivity
  have hpdf (t : ℝ) : gaussianPDFReal 0 1 t=N*Real.exp (-(t^2/2)) := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,neg_div,N]
  have h0 (t : ℝ) : 0≤gaussianPDFReal 0 1 t := gaussianPDFReal_nonneg _ _ _
  have h1 (t : ℝ) : gaussianPDFReal 0 1 t≤N := by
    rw [hpdf]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg t])) hN).trans_eq (mul_one N)
  have h2 (t : ℝ) : gaussianPDFReal 0 1 t*t^2≤2*N := by
    have hh := mul_le_mul_of_nonneg_left (gaussian_exp_sq_polynomial_bound t 2 (by norm_num)) hN
    rw [hpdf]
    nlinarith
  have ha := (mul_le_mul_of_nonneg_right (h2 a) (h0 c)).trans
    (mul_le_mul_of_nonneg_left (h1 c) (by positivity : 0≤2*N))
  have hc := (mul_le_mul_of_nonneg_left (h2 c) (h0 a)).trans
    (mul_le_mul_of_nonneg_right (h1 a) (by positivity : 0≤2*N))
  have hprod : gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c≤N^2 := by
    simpa only [pow_two] using mul_le_mul (h1 a) (h1 c) (h0 c) hN
  have hr := mul_le_mul_of_nonneg_right hprod (by positivity : 0≤2*(r:ℝ))
  change _≤N^2*(4+2*(r:ℝ))
  nlinarith

theorem thresholdSignedSection_update_eq_weightedThreshold {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (z : ℝ) :
    Printed.thresholdSignedSection u (Function.update b l z) j (b j)=
      gaussianFiniteWeightedThreshold (Finset.univ.erase j)
        (fun k => gaussianNormalProjection (u j) (u k))
        (Function.update (fun k => b k-b j*faceDot (u k) (u j)) l (z-b j*faceDot (u l) (u j)))
        (gaussianFacetScore (u j) (b j)) := by
  classical
  have hd : (fun k => Function.update b l z k-b j*faceDot (u k) (u j))=
      Function.update (fun k => b k-b j*faceDot (u k) (u j)) l (z-b j*faceDot (u l) (u j)) := by
    funext k
    by_cases hkl : k=l
    · subst k
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hkl]
  unfold Printed.thresholdSignedSection
  change gaussianFiniteWeightedThreshold _ _ (fun k => Function.update b l z k-b j*faceDot (u k) (u j)) _=_
  rw [hd]
  rfl

theorem gaussianFiniteWeightedSection_facetScore_eq_pairSignedSection {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (e q : Vector r) (a t : ℝ) :
    gaussianFiniteWeightedSection s (fun k => gaussianNormalProjection e (u k))
      (fun k => b k-a*faceDot (u k) e) q (gaussianFacetScore e a) t=
      hardGaussianPairSignedSection s u b e q a t := by
  unfold gaussianFiniteWeightedSection hardGaussianPairSignedSection
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have hiff : gaussianPairSectionPoint e q a t g∈gaussianFiniteThresholdEvent s u b ↔
        gaussianSectionPoint q t g∈gaussianFiniteThresholdEvent s
          (fun k => gaussianNormalProjection e (u k)) (fun k => b k-a*faceDot (u k) e) := by
      constructor <;> intro h k hk
      · have hh := h k hk
        change faceDot (u k) (gaussianSectionPoint e a (gaussianSectionPoint q t g))≤b k at hh
        rw [gaussianSectionPoint_faceDot] at hh
        change faceDot (gaussianNormalProjection e (u k)) (gaussianSectionPoint q t g)≤b k-a*faceDot (u k) e
        linarith
      · have hh := h k hk
        change faceDot (u k) (gaussianSectionPoint e a (gaussianSectionPoint q t g))≤b k
        rw [gaussianSectionPoint_faceDot]
        dsimp only at hh
        linarith
    dsimp only
    by_cases hg : gaussianSectionPoint q t g∈gaussianFiniteThresholdEvent s
        (fun k => gaussianNormalProjection e (u k)) (fun k => b k-a*faceDot (u k) e)
    · rw [indicator_of_mem hg,indicator_of_mem (hiff.mpr hg)]
      rfl
    · rw [indicator_of_not_mem hg,indicator_of_not_mem (fun h => hg (hiff.mp h))])

/-- Actual first signed density is a genuine conditional primitive even
at exceptional thresholds. This identity needs no local slack. -/
theorem gaussianSignedFacetDensity_update_eq_section_integral {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (z : ℝ) :
    gaussianPDFReal 0 1 (b j)*Printed.thresholdSignedSection u (Function.update b l z) j (b j)=
      ∫ t in Iic ((z-b j*faceDot (u l) (u j))/gaussianThresholdResidualScale u j l),
        gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 t*
          hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b (u j)
            (gaussianPairConditionalDirection u j l) (b j) t) := by
  obtain ⟨hq,heq,hν⟩ := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  have hul : gaussianNormalProjection (u j) (u l)=
      gaussianThresholdResidualScale u j l • gaussianPairConditionalDirection u j l := by
    rw [gaussianPairConditionalDirection,smul_smul,mul_inv_cancel₀ hν.ne',one_smul]
  rw [thresholdSignedSection_update_eq_weightedThreshold,
    gaussianFiniteWeightedThreshold_update_eq_section_integral _ _ _ l
      (Finset.mem_erase.mpr ⟨hjl.symm,Finset.mem_univ _⟩) _ hq hν hul _
      (measurable_gaussianFacetScore _ _) (integrable_gaussianFacetScore _ hu _),←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by dsimp only; rw [gaussianFiniteWeightedSection_facetScore_eq_pairSignedSection])

/-- A uniform finite difference-quotient budget for the actual first
signed density. It is independent of all threshold values and sampled
bases, and retains the selected pair's exact inverse residual scale. -/
theorem gaussianSignedFacetDensity_update_increment_bound {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) (c d : ℝ) :
    ‖gaussianPDFReal 0 1 (b j)*Printed.thresholdSignedSection u (Function.update b l c) j (b j)-
      gaussianPDFReal 0 1 (b j)*Printed.thresholdSignedSection u (Function.update b l d) j (b j)‖≤
      (gaussianMixedSectionDensityBudget (n+1)/gaussianThresholdResidualScale u j l)*|c-d| := by
  obtain ⟨hq,heq,hν⟩ := gaussianPairConditionalDirection_geometry_nonparallel u j l hu hv hp hm
  let H := fun t => gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 t*
    hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b (u j)
      (gaussianPairConditionalDirection u j l) (b j) t)
  have hi : Integrable H volume := by
    have hh := (standardRealGaussian_integrable_density_mul (integrable_gaussianFiniteWeightedSection
      ((Finset.univ.erase j).erase l) (fun k => gaussianNormalProjection (u j) (u k))
      (fun k => b k-b j*faceDot (u k) (u j)) (gaussianPairConditionalDirection u j l) hq
      (gaussianFacetScore (u j) (b j)) (measurable_gaussianFacetScore _ _)
      (integrable_gaussianFacetScore _ hu _))).const_mul (gaussianPDFReal 0 1 (b j))
    simpa only [gaussianFiniteWeightedSection_facetScore_eq_pairSignedSection] using hh
  have hb (t : ℝ) : ‖H t‖≤gaussianMixedSectionDensityBudget (n+1) := by
    rw [Real.norm_eq_abs]
    change |gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 t*_)|≤_
    rw [abs_mul,abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),abs_mul,
      abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    have hsec := abs_hardGaussianPairSignedSection_le ((Finset.univ.erase j).erase l) u b
      (u j) (gaussianPairConditionalDirection u j l) hu hq heq (b j) t
    have hh := mul_le_mul_of_nonneg_left hsec
      (mul_nonneg (gaussianPDFReal_nonneg 0 1 (b j)) (gaussianPDFReal_nonneg 0 1 t))
    have hh' : gaussianPDFReal 0 1 (b j)*(gaussianPDFReal 0 1 t*
        |hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b (u j)
          (gaussianPairConditionalDirection u j l) (b j) t|)≤
        gaussianPDFReal 0 1 (b j)*gaussianPDFReal 0 1 t*((b j)^2+t^2+2*((n+1:ℕ):ℝ)) := by
      convert hh using 1 <;> ring
    exact hh'.trans (gaussianPDFReal_pair_sq_add_dimension_le (n+1) (b j) t)
  rw [gaussianSignedFacetDensity_update_eq_section_integral u b j l hjl hu hv hp hm c,
    gaussianSignedFacetDensity_update_eq_section_integral u b j l hjl hu hv hp hm d,
    intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
  have hh : ‖∫ t in (d-b j*faceDot (u l) (u j))/gaussianThresholdResidualScale u j l..
      (c-b j*faceDot (u l) (u j))/gaussianThresholdResidualScale u j l,H t‖≤
      gaussianMixedSectionDensityBudget (n+1)*abs (
        (c-b j*faceDot (u l) (u j))/gaussianThresholdResidualScale u j l-
        (d-b j*faceDot (u l) (u j))/gaussianThresholdResidualScale u j l) :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => hb t)
  apply hh.trans_eq
  rw [show (c-b j*faceDot (u l) (u j))/gaussianThresholdResidualScale u j l-
      (d-b j*faceDot (u l) (u j))/gaussianThresholdResidualScale u j l=
      (c-d)/gaussianThresholdResidualScale u j l by ring,abs_div,abs_of_pos hν]
  ring

theorem lipschitzWith_gaussianSignedFacetDensity_update {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m) (hjl : j≠l)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0) :
    LipschitzWith ⟨gaussianMixedSectionDensityBudget (n+1)/gaussianThresholdResidualScale u j l,
      div_nonneg (gaussianMixedSectionDensityBudget_nonneg _) (by unfold gaussianThresholdResidualScale; positivity)⟩
      (fun z => gaussianPDFReal 0 1 (b j)*Printed.thresholdSignedSection u (Function.update b l z) j (b j)) := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  simpa only [dist_eq_norm,Real.norm_eq_abs] using
    gaussianSignedFacetDensity_update_increment_bound u b j l hjl hu hv hp hm c d

end
end RectangleCLTArxivV1
