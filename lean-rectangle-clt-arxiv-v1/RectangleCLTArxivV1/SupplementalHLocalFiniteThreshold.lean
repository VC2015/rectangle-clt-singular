import RectangleCLTArxivV1.SupplementalHLocalThreshold
import RectangleCLTArxivV1.SupplementalHLocalPartials

/-! Local differentiability for genuine finite Gaussian threshold events.
Selected nonzero normals are normalized explicitly, retaining their
Jacobian. A zero normal with nonzero threshold is locally constant. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section

theorem hasDerivAt_gaussianFiniteThresholdCDF_update_unit_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (j : Fin m) (hj : j∈s) (hu : vectorNormSq (u j)=1) (c : ℝ)
    (hreg : ∀ l∈s.erase j, gaussianNormalProjection (u j) (u l)≠0 ∨
      b l-c*faceDot (u l) (u j)≠0) :
    HasDerivAt (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t))
      (gaussianPDFReal 0 1 c*gaussianThresholdSectionProbability (s.erase j) u b (u j) c) c := by
  have hc := continuousAt_gaussianThresholdSectionProbability_of_slack (s.erase j) u b (u j) c hreg
  have hm := measurable_gaussianThresholdSectionProbability (s.erase j) u b (u j)
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have hprob : Integrable (gaussianThresholdSectionProbability (s.erase j) u b (u j)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)]
      exact gaussianThresholdSectionProbability_le_one _ _ _ _ _))
  have hd := hasDerivAt_integral_Iic_of_continuousAt_integrable _
    (hpdf.measurable.mul hm).stronglyMeasurable
    (standardRealGaussian_integrable_density_mul hprob) c (hpdf.continuousAt.mul hc)
  have he : (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t))=
      fun t => ∫ z in Iic t, gaussianPDFReal 0 1 z*
        gaussianThresholdSectionProbability (s.erase j) u b (u j) z :=
    funext (gaussianFiniteThresholdCDF_update_eq_section_integral s u b j hj hu)
  rwa [he]

/-- The exact nonunit local section formula includes its `1/σ` Jacobian. -/
theorem hasDerivAt_gaussianFiniteThresholdCDF_update_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hj : j∈s)
    {σ : ℝ} (hσ : 0<σ) (hnorm : vectorNormSq (u j)=σ^2) (c : ℝ)
    (hreg : ∀ l∈s.erase j, gaussianNormalProjection (σ⁻¹ • u j) (u l)≠0 ∨
      b l-(c/σ)*faceDot (u l) (σ⁻¹ • u j)≠0) :
    HasDerivAt (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t))
      ((gaussianPDFReal 0 1 (c/σ)/σ)*
        gaussianThresholdSectionProbability (s.erase j) u b (σ⁻¹ • u j) (c/σ)) c := by
  classical
  let v := Function.update u j (σ⁻¹ • u j)
  have hunit : vectorNormSq (v j)=1 := by
    simp only [v,Function.update_self,vectorNormSq,Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
    change σ⁻¹^2*vectorNormSq (u j)=1
    rw [hnorm]
    field_simp
  have hp (l : Fin m) (hl : l∈s.erase j) :
      gaussianNormalProjection (v j) (v l)≠0 ∨
        b l-(c/σ)*faceDot (v l) (v j)≠0 := by
    simpa only [v,Function.update_self,Function.update_of_ne (Finset.mem_erase.mp hl).1] using hreg l hl
  have hd := hasDerivAt_gaussianFiniteThresholdCDF_update_unit_of_slack s v b j hj hunit (c/σ) hp
  have hd' := hd.comp c ((hasDerivAt_id c).div_const σ)
  have he : (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t))=
      fun t => gaussianFiniteThresholdCDF s v (Function.update b j (t/σ)) :=
    funext (gaussianFiniteThresholdCDF_rescale_one_normal s u b j hσ)
  rw [he]
  convert hd' using 1
  rw [gaussianThresholdSectionProbability_update_ignored]
  simp only [v,Function.update_self]
  ring

/-- A selected identically zero inequality is either always satisfied
or makes the event empty, according to its threshold sign. -/
theorem gaussianFiniteThresholdCDF_update_zero_normal {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (j : Fin m) (hj : j∈s) (hu : u j=0) (c : ℝ) :
    gaussianFiniteThresholdCDF s u (Function.update b j c)=
      if 0≤c then gaussianFiniteThresholdCDF (s.erase j) u b else 0 := by
  classical
  by_cases hc : 0≤c
  · rw [if_pos hc]
    unfold gaussianFiniteThresholdCDF
    congr 1
    ext g
    change (∀ l∈s, faceDot (u l) g≤Function.update b j c l) ↔
      ∀ l∈s.erase j, faceDot (u l) g≤b l
    constructor
    · intro h l hl
      simpa only [Function.update_of_ne (Finset.mem_erase.mp hl).1] using h l (Finset.mem_erase.mp hl).2
    · intro h l hl
      by_cases hlj : l=j
      · subst l
        simpa [hu,faceDot] using hc
      · simpa only [Function.update_of_ne hlj] using h l (Finset.mem_erase.mpr ⟨hlj,hl⟩)
  · rw [if_neg hc]
    unfold gaussianFiniteThresholdCDF
    have he : gaussianFiniteThresholdEvent s u (Function.update b j c)=∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro g hg
      have hh := hg j hj
      exact hc (by simpa [hu,faceDot] using hh)
    rw [he,measureReal_empty]

theorem hasDerivAt_gaussianFiniteThresholdCDF_zero_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (j : Fin m) (hj : j∈s) (hu : u j=0) (c : ℝ) (hc : c≠0) :
    HasDerivAt (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t)) 0 c := by
  rcases lt_or_gt_of_ne hc with hn | hp
  · have he : ∀ᶠ t in 𝓝 c, gaussianFiniteThresholdCDF s u (Function.update b j t)=0 := by
      have hnear : ∀ᶠ t : ℝ in 𝓝 c, t<0 := Iio_mem_nhds hn
      filter_upwards [hnear] with t ht
      rw [gaussianFiniteThresholdCDF_update_zero_normal s u b j hj hu,if_neg ht.not_le]
    exact (hasDerivAt_const c (0 : ℝ)).congr_of_eventuallyEq he
  · have he : ∀ᶠ t in 𝓝 c, gaussianFiniteThresholdCDF s u (Function.update b j t)=
        gaussianFiniteThresholdCDF (s.erase j) u b := by
      have hnear : ∀ᶠ t : ℝ in 𝓝 c, 0<t := Ioi_mem_nhds hp
      filter_upwards [hnear] with t ht
      rw [gaussianFiniteThresholdCDF_update_zero_normal s u b j hj hu,if_pos ht.le]
    exact (hasDerivAt_const c _).congr_of_eventuallyEq he

theorem gaussianFiniteThresholdFirst_zero_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (j : Fin m) (hj : j∈s) (hu : u j=0) (hb : b j≠0) :
    gaussianFiniteThresholdFirst s u b j=0 :=
  (hasDerivAt_gaussianFiniteThresholdCDF_zero_of_slack s u b j hj hu (b j) hb).deriv

theorem continuousAt_gaussianFiniteThresholdFirst_zero_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (j : Fin m) (hj : j∈s) (hu : u j=0) (hb : b j≠0) :
    ContinuousAt (fun c => gaussianFiniteThresholdFirst s u c j) b := by
  have hn : ∀ᶠ c : Vector m in 𝓝 b, c j≠0 := (continuous_apply j).continuousAt.eventually_ne hb
  apply (continuousAt_const : ContinuousAt (fun _ : Vector m => (0 : ℝ)) b).congr_of_eventuallyEq
  filter_upwards [hn] with c hc
  exact gaussianFiniteThresholdFirst_zero_of_slack s u c j hj hu hc

theorem gaussianFiniteThresholdFirst_eq_section_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hj : j∈s)
    {σ : ℝ} (hσ : 0<σ) (hnorm : vectorNormSq (u j)=σ^2)
    (hreg : ∀ l∈s.erase j, gaussianNormalProjection (σ⁻¹ • u j) (u l)≠0 ∨
      b l-(b j/σ)*faceDot (u l) (σ⁻¹ • u j)≠0) :
    gaussianFiniteThresholdFirst s u b j=(gaussianPDFReal 0 1 (b j/σ)/σ)*
      gaussianThresholdSectionProbability (s.erase j) u b (σ⁻¹ • u j) (b j/σ) :=
  (hasDerivAt_gaussianFiniteThresholdCDF_update_of_slack s u b j hj hσ hnorm (b j) hreg).deriv

theorem continuousAt_gaussianFiniteThresholdFirst_of_slack_nonunit {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m) (hj : j∈s)
    {σ : ℝ} (hσ : 0<σ) (hnorm : vectorNormSq (u j)=σ^2)
    (hreg : ∀ l∈s.erase j, gaussianNormalProjection (σ⁻¹ • u j) (u l)≠0 ∨
      b l-(b j/σ)*faceDot (u l) (σ⁻¹ • u j)≠0) :
    ContinuousAt (fun c => gaussianFiniteThresholdFirst s u c j) b := by
  have hn : ∀ᶠ c : Vector m in 𝓝 b, ∀ l∈s.erase j,
      gaussianNormalProjection (σ⁻¹ • u j) (u l)≠0 ∨
        c l-(c j/σ)*faceDot (u l) (σ⁻¹ • u j)≠0 := by
    apply Filter.eventually_all.mpr
    intro l
    by_cases hl : l∈s.erase j
    · rcases hreg l hl with hp | hs
      · exact Filter.Eventually.of_forall (fun _ _ => Or.inl hp)
      · have hc : ContinuousAt (fun c : Vector m => c l-(c j/σ)*faceDot (u l) (σ⁻¹ • u j)) b := by
          fun_prop
        exact (hc.eventually_ne hs).mono (fun _ h _ => Or.inr h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hl h))
  have hsec := continuousAt_gaussianFiniteThresholdCDF_of_slack (s.erase j)
    (fun l => gaussianNormalProjection (σ⁻¹ • u j) (u l))
    (fun l => b l-(b j/σ)*faceDot (u l) (σ⁻¹ • u j)) hreg
  have hlevels : ContinuousAt
      (fun c : Vector m => fun l => c l-(c j/σ)*faceDot (u l) (σ⁻¹ • u j)) b := by fun_prop
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have harg : ContinuousAt (fun c : Vector m => c j/σ) b := by
    have ha : ContinuousAt (fun c : Vector m => c j) b := (continuous_apply j).continuousAt
    exact ha.div_const σ
  have hcoeff : ContinuousAt (fun c : Vector m => gaussianPDFReal 0 1 (c j/σ)/σ) b :=
    (hpdf.continuousAt.comp harg).div_const σ
  have hc := hcoeff.mul (hsec.comp hlevels)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hn] with c hc
  exact gaussianFiniteThresholdFirst_eq_section_of_slack s u c j hj hσ hnorm hc

/-- The standard deviation and normalized direction of a selected normal.
These are fixed geometric data as the thresholds vary. -/
def localFiniteThresholdScale {m r : ℕ} (u : Fin m → Vector r) (j : Fin m) : ℝ :=
  Real.sqrt (vectorNormSq (u j))

def localFiniteThresholdDirection {m r : ℕ} (u : Fin m → Vector r) (j : Fin m) : Vector r :=
  (localFiniteThresholdScale u j)⁻¹ • u j

/-- No retained zero inequality is at zero threshold. After conditioning
on any selected normal, every parallel remaining inequality has nonzero
affine slack. Both clauses concern the actual finite event geometry. -/
def LocalFiniteThresholdRegularity {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) : Prop :=
  ∀ j∈s, (u j≠0 ∨ b j≠0) ∧ ∀ l∈s.erase j,
    gaussianNormalProjection (localFiniteThresholdDirection u j) (u l)≠0 ∨
      b l-(b j/localFiniteThresholdScale u j)*faceDot (u l) (localFiniteThresholdDirection u j)≠0

theorem localFiniteThresholdRegularity_isOpen {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) :
    IsOpen {b | LocalFiniteThresholdRegularity s u b} := by
  simp only [LocalFiniteThresholdRegularity,setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  have hA : IsOpen {b : Vector m | u j≠0 ∨ b j≠0} := by
    by_cases hu : u j≠0
    · have he : {b : Vector m | u j≠0 ∨ b j≠0}=univ := Set.eq_univ_of_forall (fun _ => Or.inl hu)
      rw [he]
      exact isOpen_univ
    · simp only [hu,false_or]
      exact isOpen_ne.preimage (by fun_prop)
  have hB : IsOpen {b : Vector m | ∀ l∈s.erase j,
      gaussianNormalProjection (localFiniteThresholdDirection u j) (u l)≠0 ∨
        b l-(b j/localFiniteThresholdScale u j)*faceDot (u l) (localFiniteThresholdDirection u j)≠0} := by
    simp only [setOf_forall]
    apply isOpen_iInter_of_finite
    intro l
    apply isOpen_iInter_of_finite
    intro _
    by_cases hp : gaussianNormalProjection (localFiniteThresholdDirection u j) (u l)≠0
    · have he : {b : Vector m | gaussianNormalProjection (localFiniteThresholdDirection u j) (u l)≠0 ∨
          b l-(b j/localFiniteThresholdScale u j)*faceDot (u l) (localFiniteThresholdDirection u j)≠0}=univ :=
        Set.eq_univ_of_forall (fun _ => Or.inl hp)
      rw [he]
      exact isOpen_univ
    · simp only [hp,false_or]
      exact isOpen_ne.preimage (by fun_prop)
  exact hA.inter hB

theorem hasDerivAt_gaussianFiniteThresholdCDF_local_first {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (hreg : LocalFiniteThresholdRegularity s u b) (j : Fin m) :
    HasDerivAt (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t))
      (gaussianFiniteThresholdFirst s u b j) (b j) := by
  classical
  by_cases hj : j∈s
  · by_cases hu : u j=0
    · have hb : b j≠0 := (hreg j hj).1.resolve_left (not_not.mpr hu)
      rw [gaussianFiniteThresholdFirst_zero_of_slack s u b j hj hu hb]
      exact hasDerivAt_gaussianFiniteThresholdCDF_zero_of_slack s u b j hj hu (b j) hb
    · have hσ : 0<localFiniteThresholdScale u j := Real.sqrt_pos.mpr (vectorNormSq_pos hu)
      have hn : vectorNormSq (u j)=(localFiniteThresholdScale u j)^2 :=
        (Real.sq_sqrt (vectorNormSq_nonneg _)).symm
      rw [gaussianFiniteThresholdFirst_eq_section_of_slack s u b j hj hσ hn (hreg j hj).2]
      exact hasDerivAt_gaussianFiniteThresholdCDF_update_of_slack s u b j hj hσ hn (b j) (hreg j hj).2
  · rw [gaussianFiniteThresholdFirst_outside s u b j hj]
    have he : (fun t => gaussianFiniteThresholdCDF s u (Function.update b j t))=
        fun _ => gaussianFiniteThresholdCDF s u b :=
      funext (gaussianFiniteThresholdCDF_update_outside s u b j hj)
    rw [he]
    exact hasDerivAt_const _ _

theorem continuousAt_gaussianFiniteThresholdFirst_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (hreg : LocalFiniteThresholdRegularity s u b) (j : Fin m) :
    ContinuousAt (fun c => gaussianFiniteThresholdFirst s u c j) b := by
  classical
  by_cases hj : j∈s
  · by_cases hu : u j=0
    · exact continuousAt_gaussianFiniteThresholdFirst_zero_of_slack s u b j hj hu
        ((hreg j hj).1.resolve_left (not_not.mpr hu))
    · exact continuousAt_gaussianFiniteThresholdFirst_of_slack_nonunit s u b j hj
        (Real.sqrt_pos.mpr (vectorNormSq_pos hu))
        (Real.sq_sqrt (vectorNormSq_nonneg _)).symm (hreg j hj).2
  · have he : (fun c => gaussianFiniteThresholdFirst s u c j)=fun _ => (0 : ℝ) :=
      funext (fun c => gaussianFiniteThresholdFirst_outside s u c j hj)
    rw [he]
    exact continuousAt_const

/-- The actual finite CDF has the gradient of its genuine coordinate
derivatives, including nonunit and zero retained normals. -/
theorem hasFDerivAt_gaussianFiniteThresholdCDF_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (hreg : LocalFiniteThresholdRegularity s u b) :
    HasFDerivAt (gaussianFiniteThresholdCDF s u)
      (∑ j, gaussianFiniteThresholdFirst s u b j • (ContinuousLinearMap.proj j : Vector m →L[ℝ] ℝ)) b := by
  apply hasFDerivAt_of_local_continuous_coordinate_derivatives
    (gaussianFiniteThresholdCDF s u) (fun c j => gaussianFiniteThresholdFirst s u c j)
    b {c | LocalFiniteThresholdRegularity s u c} (localFiniteThresholdRegularity_isOpen s u) hreg
  · intro c hc j
    exact hasDerivAt_gaussianFiniteThresholdCDF_local_first s u c hc j
  · intro j
    exact continuousAt_gaussianFiniteThresholdFirst_of_slack s u b hreg j

/-- Logarithmic dilation differentiates the actual finite hard-event
probability to its actual radial Gaussian score, without any geometric
regularity premise. -/
theorem hasDerivAt_gaussianFiniteThresholdCDF_logScale {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) :
    HasDerivAt (fun t : ℝ => gaussianFiniteThresholdCDF s u (fun j => Real.exp (-t)*b j))
      (∫ g, (gaussianFiniteThresholdEvent s u b).indicator
        (fun g => vectorNormSq g-(r : ℝ)) g ∂standardGaussian r) 0 := by
  let P := gaussianFiniteThresholdEvent s u b
  let f := P.indicator (fun _ => (1 : ℝ))
  have hP : MeasurableSet P := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have hf : Measurable f := measurable_const.indicator hP
  have hbnd (g : Vector r) : |f g|≤1 := by by_cases hg : g∈P <;> simp [f,hg]
  have hscale (t : ℝ) : (∫ g, f (Real.exp t • g) ∂standardGaussian r)=
      gaussianFiniteThresholdCDF s u (fun j => Real.exp (-t)*b j) := by
    have he : Real.exp (-t)*Real.exp t=1 := by rw [← Real.exp_add]; simp
    have hdot (j : Fin m) (g : Vector r) :
        faceDot (u j) (Real.exp t • g)=Real.exp t*faceDot (u j) g := by
      simp only [faceDot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hev (g : Vector r) : Real.exp t • g∈P ↔
        g∈gaussianFiniteThresholdEvent s u (fun j => Real.exp (-t)*b j) := by
      simp only [P,gaussianFiniteThresholdEvent,mem_setOf_eq,hdot]
      apply forall_congr'
      intro j
      apply forall_congr'
      intro _
      constructor
      · intro hj
        have hh := mul_le_mul_of_nonneg_left hj (Real.exp_pos (-t)).le
        simpa only [← mul_assoc,he,one_mul] using hh
      · intro hj
        have hh := mul_le_mul_of_nonneg_left hj (Real.exp_pos t).le
        have he' : Real.exp t*Real.exp (-t)=1 := by rw [mul_comm]; exact he
        simpa only [← mul_assoc,he',one_mul] using hh
    have hfun : (fun g => f (Real.exp t • g))=
        (gaussianFiniteThresholdEvent s u (fun j => Real.exp (-t)*b j)).indicator (fun _ => (1 : ℝ)) := by
      funext g
      dsimp only [f]
      by_cases hg : g∈gaussianFiniteThresholdEvent s u (fun j => Real.exp (-t)*b j)
      · rw [Set.indicator_of_mem ((hev g).mpr hg),Set.indicator_of_mem hg]
      · rw [Set.indicator_of_not_mem (fun h => hg ((hev g).mp h)),Set.indicator_of_not_mem hg]
    rw [hfun,gaussianFiniteThresholdCDF_eq_integral]
  have hscore : (∫ g, (vectorNormSq g-(r : ℝ))*f g ∂standardGaussian r)=
      ∫ g, P.indicator (fun g => vectorNormSq g-(r : ℝ)) g ∂standardGaussian r := by
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by by_cases hg : g∈P <;> simp [f,hg])
  have hd := hasDerivAt_standardGaussian_logScale f hf 1 hbnd
  simpa only [hscale,hscore] using hd

/-- The finite radial trace is the negative threshold-gradient pairing.
Every term is the actual coordinate derivative of the finite event CDF. -/
theorem gaussianFiniteThreshold_radialTrace_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (hreg : LocalFiniteThresholdRegularity s u b) :
    (∫ g, (gaussianFiniteThresholdEvent s u b).indicator
      (fun g => vectorNormSq g-((n+1 : ℕ) : ℝ)) g ∂standardGaussian (n+1)) =
      -(∑ j, b j*gaussianFiniteThresholdFirst s u b j) := by
  have hC := hasFDerivAt_gaussianFiniteThresholdCDF_of_slack s u b hreg
  have hp : HasDerivAt (fun t : ℝ => fun j : Fin m => Real.exp (-t)*b j)
      (fun j => -b j) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa using (((hasDerivAt_id (0 : ℝ)).neg).exp).mul_const (b j)
  have hd := hC.comp_hasDerivAt_of_eq 0 hp (by simp)
  rw [(hasDerivAt_gaussianFiniteThresholdCDF_logScale s u b).unique hd]
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gaussianFiniteThreshold_sum_mul_first_eq_retained {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b a : Vector m) :
    (∑ j, a j*gaussianFiniteThresholdFirst s u b j)=
      ∑ j∈s, a j*gaussianFiniteThresholdFirst s u b j := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  rw [gaussianFiniteThresholdFirst_outside s u b j hj,mul_zero]

theorem gaussianFiniteThreshold_radialTrace_retained_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (hreg : LocalFiniteThresholdRegularity s u b) :
    (∫ g, (gaussianFiniteThresholdEvent s u b).indicator
      (fun g => vectorNormSq g-((n+1 : ℕ) : ℝ)) g ∂standardGaussian (n+1)) =
      -(∑ j∈s, b j*gaussianFiniteThresholdFirst s u b j) := by
  rw [gaussianFiniteThreshold_radialTrace_of_slack s u b hreg,
    gaussianFiniteThreshold_sum_mul_first_eq_retained]

/-- Threshold translation differentiates to the actual finite-event
gradient, including nonunit normals and harmless zero inequalities. -/
theorem hasDerivAt_gaussianFiniteThresholdCDF_translate_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (hreg : LocalFiniteThresholdRegularity s u b) (v : Vector (n+1)) :
    HasDerivAt (fun t : ℝ => gaussianFiniteThresholdCDF s u (fun j => b j-t*faceDot (u j) v))
      (-(∑ j, faceDot (u j) v*gaussianFiniteThresholdFirst s u b j)) 0 := by
  have hc := hasFDerivAt_gaussianFiniteThresholdCDF_of_slack s u b hreg
  have ht : HasDerivAt (fun t : ℝ => fun j : Fin m => b j-t*faceDot (u j) v)
      (fun j => -faceDot (u j) v) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa using (hasDerivAt_const (0 : ℝ) (b j)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (faceDot (u j) v))
  have hh := hc.comp_hasDerivAt_of_eq 0 ht (by simp)
  convert hh using 1
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integral_hard_finite_threshold_translate {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (v : Vector r) (t : ℝ) :
    (∫ g, (gaussianFiniteThresholdEvent s u b).indicator (fun _ => (1 : ℝ))
      (g+t • v) ∂standardGaussian r)=
      gaussianFiniteThresholdCDF s u (fun j => b j-t*faceDot (u j) v) := by
  rw [gaussianFiniteThresholdCDF_eq_integral]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have hiff : g+t • v∈gaussianFiniteThresholdEvent s u b ↔
        g∈gaussianFiniteThresholdEvent s u (fun j => b j-t*faceDot (u j) v) := by
      have hdot (j : Fin m) : faceDot (u j) (g+t • v)=faceDot (u j) g+t*faceDot (u j) v := by
        simp only [faceDot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,
          Finset.sum_add_distrib,Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        ring
      simp only [gaussianFiniteThresholdEvent,mem_setOf_eq,hdot]
      apply forall_congr'
      intro j
      apply forall_congr'
      intro _
      constructor <;> intro h <;> linarith
    dsimp only
    by_cases hg : g∈gaussianFiniteThresholdEvent s u (fun j => b j-t*faceDot (u j) v)
    · rw [Set.indicator_of_mem (hiff.mpr hg),Set.indicator_of_mem hg]
    · rw [Set.indicator_of_not_mem (fun h => hg (hiff.mp h)),Set.indicator_of_not_mem hg])

/-- Genuine first-moment boundary law for the actual finite threshold
event. The derivative coefficients already contain their nonunit normal
Jacobians; multiplying by `dot(u_j,v)` gives the correct signed pairing. -/
theorem gaussianFiniteThreshold_firstMoment_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (hreg : LocalFiniteThresholdRegularity s u b) (v : Vector (n+1)) :
    (∫ g in gaussianFiniteThresholdEvent s u b, faceDot v g ∂standardGaussian (n+1))=
      -(∑ j, faceDot (u j) v*gaussianFiniteThresholdFirst s u b j) := by
  let P := gaussianFiniteThresholdEvent s u b
  let w := P.indicator (fun _ => (1 : ℝ))
  have hP : MeasurableSet P := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have hw : Measurable w := measurable_const.indicator hP
  have hw0 (g : Vector (n+1)) : 0≤w g := by by_cases hg : g∈P <;> simp [w,hg]
  have hw1 (g : Vector (n+1)) : w g≤1 := by by_cases hg : g∈P <;> simp [w,hg]
  have hd := hasDerivAt_gaussian_weight_translate w hw hw0 hw1 v
  have he (t : ℝ) : (∫ g, w (g+t • v) ∂standardGaussian (n+1))=
      gaussianFiniteThresholdCDF s u (fun j => b j-t*faceDot (u j) v) :=
    integral_hard_finite_threshold_translate s u b v t
  have hd' : HasDerivAt
      (fun t : ℝ => gaussianFiniteThresholdCDF s u (fun j => b j-t*faceDot (u j) v))
      (∫ g, w g*faceDot v g ∂standardGaussian (n+1)) 0 := by simpa only [he] using hd
  have hh := hd'.unique (hasDerivAt_gaussianFiniteThresholdCDF_translate_of_slack s u b hreg v)
  rw [← integral_indicator hP]
  convert hh using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by by_cases hg : g∈P <;> simp [w,hg])

theorem gaussianFiniteThreshold_firstMoment_retained_of_slack {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (hreg : LocalFiniteThresholdRegularity s u b) (v : Vector (n+1)) :
    (∫ g in gaussianFiniteThresholdEvent s u b, faceDot v g ∂standardGaussian (n+1))=
      -(∑ j∈s, faceDot (u j) v*gaussianFiniteThresholdFirst s u b j) := by
  rw [gaussianFiniteThreshold_firstMoment_of_slack s u b hreg v,
    gaussianFiniteThreshold_sum_mul_first_eq_retained]

end
end RectangleCLTArxivV1
