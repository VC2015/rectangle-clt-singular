import RectangleCLTArxivV1.FaceCoordinates
import Mathlib.MeasureTheory.Integral.Indicator

/-! Uniform concentration is inherited by every injectively selected
subsystem with exactly the same constants. The unused thresholds are
sent to positive infinity; actual layer indicators are eventually equal
at every point, and finite-measure dominated convergence applies. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
set_option autoImplicit false

def subsystemExtendedThresholds {m k : ℕ} (f : Fin k → Fin m) (b : (Fin k → ℝ)) (M : ℝ) : (Fin m → ℝ) :=
  Function.extend f b (fun _ => M)

theorem subsystemExtendedThresholds_selected {m k : ℕ} (f : Fin k → Fin m)
    (hf : Function.Injective f) (b : (Fin k → ℝ)) (M : ℝ) (i : Fin k) :
    subsystemExtendedThresholds f b M (f i)=b i := hf.extend_apply _ _ i

theorem subsystemExtendedThresholds_unused {m k : ℕ} (f : Fin k → Fin m)
    (b : (Fin k → ℝ)) (M : ℝ) (j : Fin m) (hj : ¬∃ i,f i=j) :
    subsystemExtendedThresholds f b M j=M := Function.extend_apply' _ _ _ hj

theorem eventually_mem_facePolyhedron_subsystem {m k r : ℕ} (U : Fin m → (Fin r → ℝ))
    (f : Fin k → Fin m) (hf : Function.Injective f) (b : (Fin k → ℝ)) (s : ℝ) (x : (Fin r → ℝ)) :
    ∀ᶠ M : ℝ in atTop,
      x∈facePolyhedron U (subsystemExtendedThresholds f b M) s ↔
        x∈facePolyhedron (fun i => U (f i)) b s := by
  have hlarge : ∀ᶠ M : ℝ in atTop,∀ j : Fin m,dotProduct (U j) x≤M+s := by
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [eventually_ge_atTop (dotProduct (U j) x-s)] with M hM
    linarith
  filter_upwards [hlarge] with M hM
  constructor
  · intro hx i
    have h := hx (f i)
    rwa [subsystemExtendedThresholds_selected f hf] at h
  · intro hx j
    by_cases hj : ∃ i,f i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [subsystemExtendedThresholds_selected f hf]
      exact hx i
    · rw [subsystemExtendedThresholds_unused f b M j hj]
      exact hM j

theorem eventually_mem_faceLayer_subsystem {m k r : ℕ} (U : Fin m → (Fin r → ℝ))
    (f : Fin k → Fin m) (hf : Function.Injective f) (b : (Fin k → ℝ)) (s : ℝ) (x : (Fin r → ℝ)) :
    ∀ᶠ M : ℝ in atTop,
      x∈faceLayer U (subsystemExtendedThresholds f b M) s ↔
        x∈faceLayer (fun i => U (f i)) b s := by
  filter_upwards [eventually_mem_facePolyhedron_subsystem U f hf b s x,
    eventually_mem_facePolyhedron_subsystem U f hf b (-s) x] with M houter hinner
  exact houter.and (not_congr hinner)

/-- Actual full-system layer probabilities converge to the selected
subsystem probability. No boundary regularity, moments or base density
is needed: membership is eventually exactly equal at each point. -/
theorem tendsto_real_faceLayer_subsystem {m k r : ℕ}
    (ν : Measure ((Fin r → ℝ))) [IsFiniteMeasure ν] (U : Fin m → (Fin r → ℝ))
    (f : Fin k → Fin m) (hf : Function.Injective f) (b : (Fin k → ℝ)) (s : ℝ) :
    Tendsto (fun M : ℝ => ν.real (faceLayer U (subsystemExtendedThresholds f b M) s)) atTop
      (𝓝 (ν.real (faceLayer (fun i => U (f i)) b s))) := by
  have h := tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure atTop ν
    (fun M => measurableSet_faceLayer U (subsystemExtendedThresholds f b M) s)
    (fun x => eventually_mem_faceLayer_subsystem U f hf b s x)
  exact (ENNReal.tendsto_toReal (measure_ne_top ν _)).comp h

/-- The original uniform full-threshold concentration bound supplies
every selected subsystem, with exactly the same K and delta. -/
theorem faceLayer_concentration_subsystem {m k r : ℕ}
    (ν : Measure ((Fin r → ℝ))) [IsFiniteMeasure ν] (U : Fin m → (Fin r → ℝ))
    (f : Fin k → Fin m) (hf : Function.Injective f) {K δ : ℝ}
    (hbase : ∀ (a : (Fin m → ℝ)) (s : ℝ),0<s → ν.real (faceLayer U a s)≤K*(s+δ)) :
    ∀ (b : (Fin k → ℝ)) (s : ℝ),0<s →
      ν.real (faceLayer (fun i => U (f i)) b s)≤K*(s+δ) := by
  intro b s hs
  apply le_of_tendsto (tendsto_real_faceLayer_subsystem ν U f hf b s)
  exact Eventually.of_forall (fun M => hbase (subsystemExtendedThresholds f b M) s hs)

end
end RectangleCLTArxivV1
