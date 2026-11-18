import RectangleCLTArxivV1.SupplementalHNonsimpleRidgeGreenSelection
import RectangleCLTArxivV1.SupplementalHPairSectionTrace

/-! Actual Gaussian nullity of a retained finite hard polyhedron with no
strict interior witness. Harmless zero normals have nonzero levels; hence
every point of such a polyhedron lies on a proper retained hyperplane.
This is a pointwise statement at fixed thresholds, including singular
sections and arbitrary dependent normal families. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- A non-strict hard point has an active proper supporting hyperplane
when the retained event has no strict witness. Zero normal inequalities
cannot provide the active face under the ordinary level-slack condition. -/
theorem gaussianFiniteThresholdEvent_has_nonzero_active_of_no_strictInterior {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hreg : ∀ k ∈ s, u k ≠ 0 ∨ b k ≠ 0)
    (hnot : ¬HasStrictRetainedInterior s u b)
    (x : Vector r) (hx : x ∈ gaussianFiniteThresholdEvent s u b) :
    ∃ k ∈ s, u k ≠ 0 ∧ faceDot (u k) x = b k := by
  classical
  by_contra hactive
  apply hnot
  refine ⟨x, ?_⟩
  intro k hk
  by_contra hstrict
  have heq : faceDot (u k) x = b k := le_antisymm (hx k hk) (le_of_not_gt hstrict)
  have hn : u k ≠ 0 := by
    rcases hreg k hk with hn | hb
    · exact hn
    · intro hz
      apply hb
      simpa only [hz, faceDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero] using heq.symm
  exact hactive ⟨k, hk, hn, heq⟩

theorem ae_not_mem_gaussianFiniteThresholdEvent_of_no_strictInterior {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hreg : ∀ k ∈ s, u k ≠ 0 ∨ b k ≠ 0)
    (hnot : ¬HasStrictRetainedInterior s u b) :
    ∀ᵐ g ∂standardGaussian r, g ∉ gaussianFiniteThresholdEvent s u b := by
  filter_upwards [gaussianFiniteThreshold_ae_no_boundary_of_slack s u b hreg] with g hg
  intro hgin
  obtain ⟨k, hk, _, heq⟩ :=
    gaussianFiniteThresholdEvent_has_nonzero_active_of_no_strictInterior s u b hreg hnot g hgin
  exact hg k hk heq

/-- The actual Gaussian measure is zero; this is not a totalized-integral
shortcut or an assumption about generic threshold vectors. -/
theorem gaussianFiniteThresholdEvent_measure_zero_of_no_strictInterior {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hreg : ∀ k ∈ s, u k ≠ 0 ∨ b k ≠ 0)
    (hnot : ¬HasStrictRetainedInterior s u b) :
    standardGaussian r (gaussianFiniteThresholdEvent s u b) = 0 := by
  simpa only [ae_iff, not_not] using
    ae_not_mem_gaussianFiniteThresholdEvent_of_no_strictInterior s u b hreg hnot

theorem gaussianFiniteThresholdCDF_zero_of_no_strictInterior {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hreg : ∀ k ∈ s, u k ≠ 0 ∨ b k ≠ 0)
    (hnot : ¬HasStrictRetainedInterior s u b) :
    gaussianFiniteThresholdCDF s u b = 0 := by
  change (standardGaussian r (gaussianFiniteThresholdEvent s u b)).toReal = 0
  rw [gaussianFiniteThresholdEvent_measure_zero_of_no_strictInterior s u b hreg hnot]
  rfl

/-- Every actual hard-event weighted integrand vanishes Gaussian-a.e. -/
theorem integral_gaussianFiniteThreshold_indicator_zero_of_no_strictInterior {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hreg : ∀ k ∈ s, u k ≠ 0 ∨ b k ≠ 0)
    (hnot : ¬HasStrictRetainedInterior s u b) (f : Vector r → ℝ) :
    (∫ g, (gaussianFiniteThresholdEvent s u b).indicator f g ∂standardGaussian r) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_not_mem_gaussianFiniteThresholdEvent_of_no_strictInterior s u b hreg hnot]
    with g hg
  exact Set.indicator_of_not_mem hg f

theorem gaussianFiniteThresholdRadialTrace_zero_of_no_strictInterior {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (hreg : ∀ k ∈ s, u k ≠ 0 ∨ b k ≠ 0)
    (hnot : ¬HasStrictRetainedInterior s u b) :
    gaussianFiniteThresholdRadialTrace s u b = 0 :=
  integral_gaussianFiniteThreshold_indicator_zero_of_no_strictInterior s u b hreg hnot _

theorem hardGaussianPairSectionProbability_zero_of_no_strictResidualInterior {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (a c : ℝ) (hef : faceDot e f = 0)
    (hreg : ∀ k ∈ s, hardPairResidualNormals u e f k ≠ 0 ∨
      hardPairResidualLevels u b e f a c k ≠ 0)
    (hnot : ¬HasStrictRetainedInterior s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    hardGaussianPairSectionProbability s u b e f a c = 0 := by
  rw [hardGaussianPairSectionProbability_eq_residual_CDF s u b e f a c hef]
  exact gaussianFiniteThresholdCDF_zero_of_no_strictInterior _ _ _ hreg hnot

/-- Even the full signed section integrand vanishes for a nonactual ridge.
Only orthogonality is needed for the exact residual-event equivalence. -/
theorem hardGaussianPairSignedSection_zero_of_no_strictResidualInterior {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (a c : ℝ) (hef : faceDot e f = 0)
    (hreg : ∀ k ∈ s, hardPairResidualNormals u e f k ≠ 0 ∨
      hardPairResidualLevels u b e f a c k ≠ 0)
    (hnot : ¬HasStrictRetainedInterior s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    hardGaussianPairSignedSection s u b e f a c = 0 := by
  unfold hardGaussianPairSignedSection
  apply integral_eq_zero_of_ae
  filter_upwards [ae_not_mem_gaussianFiniteThresholdEvent_of_no_strictInterior s
    (hardPairResidualNormals u e f) (hardPairResidualLevels u b e f a c) hreg hnot] with g hg
  exact Set.indicator_of_not_mem
    (fun h => hg ((gaussianPairSectionPoint_mem_event_iff s u b e f a c g hef).mp h)) _

end
end RectangleCLTArxivV1
