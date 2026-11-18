import RectangleCLTArxivV1.SupplementalHGaussianBoundary

/-! Local hard-threshold regularity includes parallel faces with nonzero
slack. It does not require linear independence of a normal family. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section

/-- An identically zero normal is harmless at a nonzero threshold. -/
theorem gaussianFiniteThreshold_ae_no_boundary_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hreg : ∀ j∈s, u j≠0 ∨ b j≠0) :
    ∀ᵐ g ∂standardGaussian r, ∀ j∈s, faceDot (u j) g≠b j := by
  apply Filter.eventually_all.mpr
  intro j
  by_cases hj : j∈s
  · rcases hreg j hj with hn | hb
    · have h := standardGaussian_affine_hyperplane_zero (u j) hn (b j)
      have ha : ∀ᵐ g ∂standardGaussian r, faceDot (u j) g≠b j := by
        simpa only [ae_iff,not_not] using h
      exact ha.mono (fun _ h _ => h)
    · by_cases hn : u j=0
      · exact ae_of_all _ (fun _ _ => by simpa [hn,faceDot] using Ne.symm hb)
      · have h := standardGaussian_affine_hyperplane_zero (u j) hn (b j)
        have ha : ∀ᵐ g ∂standardGaussian r, faceDot (u j) g≠b j := by
          simpa only [ae_iff,not_not] using h
        exact ha.mono (fun _ h _ => h)
  · exact ae_of_all _ (fun _ h => False.elim (hj h))

/-- Joint threshold continuity at a model, allowing zero normals whose
thresholds have nonzero slack. -/
theorem continuousAt_gaussianFiniteThresholdCDF_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hreg : ∀ j∈s, u j≠0 ∨ b j≠0) :
    ContinuousAt (gaussianFiniteThresholdCDF s u) b := by
  change Tendsto _ (𝓝 b) (𝓝 _)
  have he : gaussianFiniteThresholdCDF s u=fun c =>
      ∫ g, (gaussianFiniteThresholdEvent s u c).indicator (fun _ => (1:ℝ)) g ∂standardGaussian r :=
    funext (gaussianFiniteThresholdCDF_eq_integral s u)
  rw [he]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
  · exact Filter.Eventually.of_forall (fun c =>
      (measurable_const.indicator (measurableSet_gaussianFiniteThresholdEvent s u c)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun c => ae_of_all _ (fun g => by
      by_cases hg : g∈gaussianFiniteThresholdEvent s u c <;> simp [hg]))
  · exact integrable_const _
  · exact (gaussianFiniteThreshold_ae_no_boundary_of_slack s u b hreg).mono
      (fun g hg => gaussianFiniteThreshold_indicator_tendsto s u b g hg)

/-- Hard finite Gaussian CDFs are measurable even when some normals vanish. -/
theorem measurable_gaussianFiniteThresholdCDF {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) :
    Measurable (gaussianFiniteThresholdCDF s u) := by
  let E : Set (Vector m × Vector r) := {p | ∀ j∈s, faceDot (u j) p.2≤p.1 j}
  have hE : MeasurableSet E := by
    unfold E
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le ((continuous_faceDot_left (u j)).measurable.comp measurable_snd)
      ((measurable_pi_apply j).comp measurable_fst)
  have hf : StronglyMeasurable (fun p : Vector m × Vector r => E.indicator (fun _ => (1:ℝ)) p) :=
    (measurable_const.indicator hE).stronglyMeasurable
  have hi := hf.integral_prod_right' (ν := standardGaussian r)
  convert hi.measurable using 1
  funext b
  rw [gaussianFiniteThresholdCDF_eq_integral]
  rfl

/-- The actual affine section probability is continuous at a threshold
where every identically zero projected inequality has nonzero slack. -/
theorem continuousAt_gaussianThresholdSectionProbability_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (v : Vector r) (c : ℝ)
    (hreg : ∀ l∈s, gaussianNormalProjection v (u l)≠0 ∨ b l-c*faceDot (u l) v≠0) :
    ContinuousAt (gaussianThresholdSectionProbability s u b v) c := by
  have hc := continuousAt_gaussianFiniteThresholdCDF_of_slack s
    (fun l => gaussianNormalProjection v (u l)) (fun l => b l-c*faceDot (u l) v) hreg
  exact hc.comp (by fun_prop)

theorem measurable_gaussianThresholdSectionProbability {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (v : Vector r) :
    Measurable (gaussianThresholdSectionProbability s u b v) :=
  (measurable_gaussianFiniteThresholdCDF s (fun l => gaussianNormalProjection v (u l))).comp
    (by fun_prop)

/-- The fundamental theorem of calculus only needs continuity at the
current upper endpoint, not global regularity of all sections. -/
theorem hasDerivAt_integral_Iic_of_continuousAt_integrable (f : ℝ → ℝ)
    (hm : StronglyMeasurable f) (hi : Integrable f volume) (c : ℝ) (hc : ContinuousAt f c) :
    HasDerivAt (fun y => ∫ t in Iic y, f t) (f c) c := by
  have he (y : ℝ) : (∫ t in Iic y, f t)=(∫ t in (0:ℝ)..y, f t)+∫ t in Iic 0, f t :=
    sub_eq_iff_eq_add.mp (intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn)
  have hd := (intervalIntegral.integral_hasDerivAt_right (a := (0:ℝ)) hi.intervalIntegrable
    hm.stronglyMeasurableAtFilter hc).add_const (∫ t in Iic 0, f t)
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall he)

/-- Genuine coordinate derivative in the presence of parallel faces.
The only excluded configuration is a parallel supporting hyperplane
coincident with the differentiated one. -/
theorem hasDerivAt_gaussianThresholdCDF_update_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (c : ℝ)
    (hreg : ∀ l∈Finset.univ.erase j, gaussianNormalProjection (u j) (u l)≠0 ∨
      b l-c*faceDot (u l) (u j)≠0) :
    HasDerivAt (fun t => gaussianThresholdCDF u (Function.update b j t))
      (gaussianPDFReal 0 1 c*gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) c) c := by
  have hc := continuousAt_gaussianThresholdSectionProbability_of_slack
    (Finset.univ.erase j) u b (u j) c hreg
  have hm := measurable_gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j)
  have hpdf : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
  have hprob : Integrable (gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j)) (gaussianReal 0 1) :=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)]
      exact gaussianThresholdSectionProbability_le_one _ _ _ _ _))
  have hi := standardRealGaussian_integrable_density_mul hprob
  have hd := hasDerivAt_integral_Iic_of_continuousAt_integrable _
    (hpdf.measurable.mul hm).stronglyMeasurable hi c (hpdf.continuousAt.mul hc)
  have he : (fun t => gaussianThresholdCDF u (Function.update b j t))=
      fun t => ∫ s in Iic t, gaussianPDFReal 0 1 s*
        gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) s :=
    funext (gaussianThresholdCDF_update_eq_section_integral u b j hu)
  rwa [he]


/-- A parallel supporting inequality does not coincide with the current
supporting hyperplane. Opposite signed faces of a positive-width strip
satisfy this condition. -/
def LocalThresholdRegularity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : Prop :=
  ∀ j l, l≠j → gaussianNormalProjection (u j) (u l)≠0 ∨
    b l-b j*faceDot (u l) (u j)≠0

theorem gaussianThresholdFirst_eq_section_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1)
    (hreg : ∀ l, l≠j → gaussianNormalProjection (u j) (u l)≠0 ∨
      b l-b j*faceDot (u l) (u j)≠0) :
    gaussianThresholdFirst u b j=gaussianPDFReal 0 1 (b j)*
      gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) (b j) :=
  (hasDerivAt_gaussianThresholdCDF_update_of_slack u b j hu (b j)
    (fun l hl => hreg l (Finset.mem_erase.mp hl).1)).deriv

theorem localThresholdRegularity_isOpen {m r : ℕ} (u : Fin m → Vector r) :
    IsOpen {b | LocalThresholdRegularity u b} := by
  simp only [LocalThresholdRegularity,setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro l
  apply isOpen_iInter_of_finite
  intro _
  by_cases hp : gaussianNormalProjection (u j) (u l)≠0
  · have he : {x : Vector m | gaussianNormalProjection (u j) (u l)≠0 ∨
        x l-x j*faceDot (u l) (u j)≠0}=Set.univ :=
      Set.eq_univ_of_forall (fun _ => Or.inl hp)
    rw [he]
    exact isOpen_univ
  · simp only [hp,false_or]
    exact isOpen_ne.preimage (by fun_prop)

/-- The genuine first derivative is continuous locally, including at
parallel signed faces with nonzero slack. -/
theorem continuousAt_gaussianThresholdFirst_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1)
    (hreg : ∀ l, l≠j → gaussianNormalProjection (u j) (u l)≠0 ∨
      b l-b j*faceDot (u l) (u j)≠0) :
    ContinuousAt (fun c => gaussianThresholdFirst u c j) b := by
  have hn : ∀ᶠ c : Vector m in 𝓝 b, ∀ l, l≠j →
      gaussianNormalProjection (u j) (u l)≠0 ∨ c l-c j*faceDot (u l) (u j)≠0 := by
    apply Filter.eventually_all.mpr
    intro l
    by_cases hlj : l=j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hlj))
    · rcases hreg l hlj with hp | hs
      · exact Filter.Eventually.of_forall (fun _ _ => Or.inl hp)
      · have hc : ContinuousAt (fun c : Vector m => c l-c j*faceDot (u l) (u j)) b := by fun_prop
        exact (hc.eventually_ne hs).mono (fun _ h _ => Or.inr h)
  have hsec := continuousAt_gaussianFiniteThresholdCDF_of_slack (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l))
    (fun l => b l-b j*faceDot (u l) (u j))
    (fun l hl => hreg l (Finset.mem_erase.mp hl).1)
  have hlevels : ContinuousAt (fun c : Vector m => fun l => c l-c j*faceDot (u l) (u j)) b := by fun_prop
  have hpdf : ContinuousAt (fun c : Vector m => gaussianPDFReal 0 1 (c j)) b :=
    by
      have hc : Continuous (gaussianPDFReal 0 1) := continuous_iff_continuousAt.mpr
        (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)
      exact (hc.comp (continuous_apply j)).continuousAt
  have hc := hpdf.mul (hsec.comp hlevels)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hn] with c hc
  exact gaussianThresholdFirst_eq_section_of_slack u c j hu hc

end
end RectangleCLTArxivV1
