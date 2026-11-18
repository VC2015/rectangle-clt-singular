import RectangleCLTArxivV1.SupplementalHMixedCoareaLipschitz

/-! The actual parallel mixed branch: a zero selected residual normal
with nonzero shifted threshold gives a locally constant hard event and
therefore a genuinely zero signed first-facet derivative. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem gaussianFiniteThresholdEvent_update_zero_of_same_sign {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (l : Fin m)
    (hu : u l=0) (c : ℝ) (hsign : 0≤c ↔ 0≤b l) :
    gaussianFiniteThresholdEvent s u (Function.update b l c)=gaussianFiniteThresholdEvent s u b := by
  classical
  ext g
  constructor <;> intro h k hk
  · by_cases hkl : k=l
    · subst k
      have hh := h l hk
      simp only [Function.update_self,hu,faceDot,Pi.zero_apply,zero_mul,Finset.sum_const_zero] at hh ⊢
      exact hsign.mp hh
    · simpa only [Function.update_of_ne hkl] using h k hk
  · by_cases hkl : k=l
    · subst k
      have hh := h l hk
      simp only [Function.update_self,hu,faceDot,Pi.zero_apply,zero_mul,Finset.sum_const_zero] at hh ⊢
      exact hsign.mpr hh
    · simpa only [Function.update_of_ne hkl] using h k hk

/-- No measurability or differentiability premise is needed: the hard
event itself is locally unchanged when a zero normal has nonzero slack. -/
theorem eventuallyEq_gaussianFiniteWeightedThreshold_update_zero_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (l : Fin m)
    (hu : u l=0) (hb : b l≠0) (F : Vector r → ℝ) :
    (fun c => gaussianFiniteWeightedThreshold s u (Function.update b l c) F)=ᶠ[𝓝 (b l)]
      (fun _ => gaussianFiniteWeightedThreshold s u b F) := by
  have hsign : ∀ᶠ c in 𝓝 (b l),(0≤c ↔ 0≤b l) := by
    by_cases hp : 0<b l
    · filter_upwards [eventually_gt_nhds hp] with c hc
      exact ⟨fun _ => hp.le,fun _ => hc.le⟩
    · have hn : b l<0 := lt_of_le_of_ne (le_of_not_gt hp) hb
      filter_upwards [eventually_lt_nhds hn] with c hc
      exact ⟨fun h => False.elim (not_le_of_gt hc h),fun h => False.elim (not_le_of_gt hn h)⟩
  filter_upwards [hsign] with c hc
  unfold gaussianFiniteWeightedThreshold
  rw [gaussianFiniteThresholdEvent_update_zero_of_same_sign s u b l hu c hc]

theorem hasDerivAt_gaussianFiniteWeightedThreshold_update_zero_of_slack {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m) (l : Fin m)
    (hu : u l=0) (hb : b l≠0) (F : Vector r → ℝ) :
    HasDerivAt (fun c => gaussianFiniteWeightedThreshold s u (Function.update b l c) F) 0 (b l) :=
  (hasDerivAt_const (b l) (gaussianFiniteWeightedThreshold s u b F)).congr_of_eventuallyEq
    (eventuallyEq_gaussianFiniteWeightedThreshold_update_zero_of_slack s u b l hu hb F)

/-- The actual signed first-facet section is locally constant in a
parallel second threshold whenever its shifted slack is nonzero. -/
theorem eventuallyEq_thresholdSignedSection_update_parallel_of_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hz : gaussianNormalProjection (u j) (u l)=0)
    (hs : b l-b j*faceDot (u l) (u j)≠0) :
    (fun c => Printed.thresholdSignedSection u (Function.update b l c) j (b j))=ᶠ[𝓝 (b l)]
      (fun _ => Printed.thresholdSignedSection u b j (b j)) := by
  let s := Finset.univ.erase j
  let v := fun k => gaussianNormalProjection (u j) (u k)
  let d := fun k => b k-b j*faceDot (u k) (u j)
  let F := gaussianFacetScore (u j) (b j)
  have he := eventuallyEq_gaussianFiniteWeightedThreshold_update_zero_of_slack s v d l hz hs F
  have ht : Tendsto (fun c : ℝ => c-b j*faceDot (u l) (u j)) (𝓝 (b l)) (𝓝 (d l)) :=
    continuousAt_id.sub_const _
  filter_upwards [ht.eventually he] with c hc
  rw [thresholdSignedSection_update_eq_weightedThreshold]
  change gaussianFiniteWeightedThreshold s v (Function.update d l (c-b j*faceDot (u l) (u j))) F=_
  rw [hc]
  rfl

theorem hasDerivAt_thresholdSignedSection_update_parallel_of_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hz : gaussianNormalProjection (u j) (u l)=0)
    (hs : b l-b j*faceDot (u l) (u j)≠0) :
    HasDerivAt (fun c => Printed.thresholdSignedSection u (Function.update b l c) j (b j)) 0 (b l) :=
  (hasDerivAt_const (b l) (Printed.thresholdSignedSection u b j (b j))).congr_of_eventuallyEq
    (eventuallyEq_thresholdSignedSection_update_parallel_of_slack u b j l hz hs)

theorem hasDerivAt_gaussianSignedFacetDensity_update_parallel_of_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hz : gaussianNormalProjection (u j) (u l)=0)
    (hs : b l-b j*faceDot (u l) (u j)≠0) :
    HasDerivAt (fun c => gaussianPDFReal 0 1 (b j)*
      Printed.thresholdSignedSection u (Function.update b l c) j (b j)) 0 (b l) := by
  simpa only [mul_zero] using
    (hasDerivAt_thresholdSignedSection_update_parallel_of_slack u b j l hz hs).const_mul
      (gaussianPDFReal 0 1 (b j))

theorem ResidualThresholdRegularity.parallel_shifted_slack {m r : ℕ}
    {u : Fin m → Vector r} {b : Vector m} {j l : Fin m}
    (h : ResidualThresholdRegularity u b j) (hlj : l≠j)
    (hz : gaussianNormalProjection (u j) (u l)=0) :
    b l-b j*faceDot (u l) (u j)≠0 := by
  have hl : l∈Finset.univ.erase j := Finset.mem_erase.mpr ⟨hlj,Finset.mem_univ _⟩
  exact (h l hl).1.resolve_left (fun hn => hn hz)

/-- All selected parallel mixed branches have derivative zero outside a
single threshold-volume null set, even for dependent normal families. -/
theorem ae_hasDerivAt_gaussianSignedFacetDensity_update_parallel {m r : ℕ}
    (u : Fin m → Vector r) :
    ∀ᵐ b : Vector m ∂volume,∀ j l,j≠l → gaussianNormalProjection (u j) (u l)=0 →
      HasDerivAt (fun c => gaussianPDFReal 0 1 (b j)*
        Printed.thresholdSignedSection u (Function.update b l c) j (b j)) 0 (b l) := by
  filter_upwards [ae_residualThresholdRegularity u] with b hb
  intro j l hjl hz
  exact hasDerivAt_gaussianSignedFacetDensity_update_parallel_of_slack u b j l hz
    ((hb j).parallel_shifted_slack hjl.symm hz)

end
end RectangleCLTArxivV1
