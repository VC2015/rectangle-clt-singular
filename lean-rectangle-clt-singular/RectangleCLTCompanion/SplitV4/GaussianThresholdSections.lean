import RectangleCLTCompanion.SplitV4.GaussianThresholdData
import RectangleCLTCompanion.SplitV4.GaussianMaximumLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual hard Gaussian polyhedra, their threshold continuity, and
orthogonal-section disintegration used for genuine threshold derivatives. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def gaussianFiniteThresholdEvent {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) : Set (Vector r) :=
  {g | ∀ j ∈ s, faceDot (u j) g ≤ b j}

def gaussianFiniteThresholdCDF {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) : ℝ :=
  (standardGaussian r).real (gaussianFiniteThresholdEvent s u b)

theorem measurableSet_gaussianFiniteThresholdEvent {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) :
    MeasurableSet (gaussianFiniteThresholdEvent s u b) := by
  unfold gaussianFiniteThresholdEvent
  simp only [setOf_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
    measurableSet_le (continuous_faceDot_left (u j)).measurable measurable_const))

theorem gaussianFiniteThresholdCDF_eq_integral {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) :
    gaussianFiniteThresholdCDF s u b =
      ∫ g, (gaussianFiniteThresholdEvent s u b).indicator (fun _ => (1 : ℝ)) g ∂standardGaussian r :=
  (integral_indicator_one (measurableSet_gaussianFiniteThresholdEvent s u b)).symm

theorem gaussianFiniteThresholdEvent_ae_no_boundary {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (hu : ∀ j ∈ s, u j ≠ 0) (b : Vector m) :
    ∀ᵐ g ∂standardGaussian r, ∀ j ∈ s, faceDot (u j) g ≠ b j := by
  apply Filter.eventually_all.mpr
  intro j
  by_cases hj : j ∈ s
  · have hn := standardGaussian_affine_hyperplane_zero (u j) (hu j hj) (b j)
    have ha : ∀ᵐ g ∂standardGaussian r, faceDot (u j) g ≠ b j := by
      simpa only [ae_iff, not_not] using hn
    exact ha.mono (fun _ h _ => h)
  · exact ae_of_all _ (fun _ h => False.elim (hj h))

theorem gaussianFiniteThreshold_indicator_tendsto {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (g : Vector r)
    (hg : ∀ j ∈ s, faceDot (u j) g ≠ b j) :
    Tendsto (fun c : Vector m => (gaussianFiniteThresholdEvent s u c).indicator
      (fun _ => (1 : ℝ)) g) (𝓝 b)
      (𝓝 ((gaussianFiniteThresholdEvent s u b).indicator (fun _ => (1 : ℝ)) g)) := by
  have hnear : ∀ᶠ c : Vector m in 𝓝 b, ∀ j ∈ s,
      (faceDot (u j) g ≤ c j ↔ faceDot (u j) g ≤ b j) := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j ∈ s
    · by_cases hle : faceDot (u j) g ≤ b j
      · have hlt : faceDot (u j) g < b j := lt_of_le_of_ne hle (hg j hj)
        have ht := (continuous_apply j).tendsto b (lt_mem_nhds hlt)
        filter_upwards [ht] with c hc
        exact fun _ => ⟨fun _ => hle, fun _ => hc.le⟩
      · have hlt : b j < faceDot (u j) g := lt_of_not_ge hle
        have ht := (continuous_apply j).tendsto b (gt_mem_nhds hlt)
        filter_upwards [ht] with c hc
        exact fun _ => ⟨fun h => False.elim (not_le.mpr hc h), fun h => False.elim (hle h)⟩
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hj h))
  apply tendsto_const_nhds.congr'
  filter_upwards [hnear] with c hc
  have he : g ∈ gaussianFiniteThresholdEvent s u c ↔ g ∈ gaussianFiniteThresholdEvent s u b := by
    exact ⟨fun h j hj => (hc j hj).mp (h j hj), fun h j hj => (hc j hj).mpr (h j hj)⟩
  by_cases hc' : g ∈ gaussianFiniteThresholdEvent s u c
  · simp [hc', he.mp hc']
  · have hb' : g ∉ gaussianFiniteThresholdEvent s u b := fun h => hc' (he.mpr h)
    simp [hc', hb']

/-- Genuine continuity of the hard finite Gaussian CDF. No nonsingularity
of the whole family is needed; each retained normal only has to be nonzero. -/
theorem continuous_gaussianFiniteThresholdCDF {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (hu : ∀ j ∈ s, u j ≠ 0) :
    Continuous (gaussianFiniteThresholdCDF s u) := by
  apply continuous_iff_continuousAt.mpr
  intro b
  change Tendsto (gaussianFiniteThresholdCDF s u) (𝓝 b) (𝓝 (gaussianFiniteThresholdCDF s u b))
  have he : gaussianFiniteThresholdCDF s u = fun c =>
      ∫ g, (gaussianFiniteThresholdEvent s u c).indicator (fun _ => (1 : ℝ)) g ∂standardGaussian r :=
    funext (gaussianFiniteThresholdCDF_eq_integral s u)
  rw [he]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Filter.Eventually.of_forall (fun c =>
      (measurable_const.indicator (measurableSet_gaussianFiniteThresholdEvent s u c)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun c => ae_of_all _ fun g => by
      by_cases hg : g ∈ gaussianFiniteThresholdEvent s u c <;> simp [hg])
  · exact integrable_const _
  · exact (gaussianFiniteThresholdEvent_ae_no_boundary s u hu b).mono
      (fun g hg => gaussianFiniteThreshold_indicator_tendsto s u b g hg)

theorem continuous_gaussianThresholdCDF {m r : ℕ}
    (u : Fin m → Vector r) (hu : ∀ j, u j ≠ 0) : Continuous (gaussianThresholdCDF u) := by
  have he : gaussianThresholdCDF u = gaussianFiniteThresholdCDF Finset.univ u := by
    funext b
    simp [gaussianThresholdCDF, gaussianFiniteThresholdCDF, gaussianFiniteThresholdEvent]
  rw [he]
  exact continuous_gaussianFiniteThresholdCDF _ u (fun j _ => hu j)

theorem threshold_faceDot_add_right {r : ℕ} (u x y : Vector r) :
    faceDot u (x + y) = faceDot u x + faceDot u y := by
  simp [faceDot, mul_add, Finset.sum_add_distrib]

theorem threshold_faceDot_sub_right {r : ℕ} (u x y : Vector r) :
    faceDot u (x - y) = faceDot u x - faceDot u y := by
  simp [faceDot, mul_sub, Finset.sum_sub_distrib]

theorem threshold_faceDot_smul_right {r : ℕ} (u x : Vector r) (t : ℝ) :
    faceDot u (t • x) = t * faceDot u x := by
  simp [faceDot, Finset.mul_sum, mul_left_comm]

theorem threshold_faceDot_sub_left {r : ℕ} (u v x : Vector r) :
    faceDot (u - v) x = faceDot u x - faceDot v x := by
  rw [faceDot_comm, threshold_faceDot_sub_right, faceDot_comm x u, faceDot_comm x v]

theorem threshold_faceDot_smul_left {r : ℕ} (u x : Vector r) (t : ℝ) :
    faceDot (t • u) x = t * faceDot u x := by
  rw [faceDot_comm, threshold_faceDot_smul_right, faceDot_comm]

def gaussianNormalProjection {r : ℕ} (u v : Vector r) : Vector r := v - faceDot v u • u

theorem gaussianSectionPoint_faceDot {r : ℕ} (u v z : Vector r) (t : ℝ) :
    faceDot v (SignedSurface.gaussianSectionPoint u t z) =
      t * faceDot v u + faceDot (gaussianNormalProjection u v) z := by
  simp only [SignedSurface.gaussianSectionPoint, SignedSurface.gaussianSectionResidual,
    gaussianNormalProjection, threshold_faceDot_add_right, threshold_faceDot_sub_right,
    threshold_faceDot_smul_right, threshold_faceDot_sub_left, threshold_faceDot_smul_left]
  ring

theorem gaussianNormalProjection_ne_zero_of_independent {m r : ℕ}
    (u : Fin m → Vector r) (hi : LinearIndependent ℝ u) (j l : Fin m) (hlj : l ≠ j) :
    gaussianNormalProjection (u j) (u l) ≠ 0 := by
  intro hz
  have he : (1 : ℝ) • u l = faceDot (u l) (u j) • u j := by
    simpa only [one_smul] using (sub_eq_zero.mp hz)
  exact hlj (hi.eq_of_smul_apply_eq_smul_apply 1 _ l j (by norm_num) he)

def gaussianThresholdSectionProbability {m r : ℕ} (s : Finset (Fin m))
    (v : Fin m → Vector r) (b : Vector m) (u : Vector r) (t : ℝ) : ℝ :=
  gaussianFiniteThresholdCDF s (fun j => gaussianNormalProjection u (v j))
    (fun j => b j - t * faceDot (v j) u)

theorem continuous_gaussianThresholdSectionProbability {m r : ℕ} (s : Finset (Fin m))
    (v : Fin m → Vector r) (b : Vector m) (u : Vector r)
    (hu : ∀ j ∈ s, gaussianNormalProjection u (v j) ≠ 0) :
    Continuous (gaussianThresholdSectionProbability s v b u) := by
  exact (continuous_gaussianFiniteThresholdCDF s _ hu).comp
    (continuous_pi (fun j => continuous_const.sub (continuous_id.mul continuous_const)))

theorem gaussianThresholdSectionProbability_eq_section {m r : ℕ} (s : Finset (Fin m))
    (v : Fin m → Vector r) (b : Vector m) (u : Vector r) (t : ℝ) :
    gaussianThresholdSectionProbability s v b u t =
      (standardGaussian r).real {z | ∀ j ∈ s,
        faceDot (v j) (SignedSurface.gaussianSectionPoint u t z) ≤ b j} := by
  unfold gaussianThresholdSectionProbability gaussianFiniteThresholdCDF gaussianFiniteThresholdEvent
  congr 1
  ext z
  simp only [mem_setOf_eq, gaussianSectionPoint_faceDot]
  constructor <;> intro h j hj <;> specialize h j hj <;> linarith

theorem gaussianSectionPoint_normalSectionChart {n : ℕ}
    (k : Fin (n + 1)) (u : Vector (n + 1)) (hu : vectorNormSq u = 1)
    (t s : ℝ) (y : Vector n) :
    SignedSurface.gaussianSectionPoint u t (SignedSurface.normalSectionChart k u s y) =
      SignedSurface.normalSectionChart k u t y := by
  rw [SignedSurface.gaussianSectionPoint_eq,
    SignedSurface.normalSectionChart_on_hyperplane k u hu,
    SignedSurface.normalSectionChart_eq_normal_add_base k u hu s,
    SignedSurface.normalSectionChart_eq_normal_add_base k u hu t]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem measurable_normalSectionChart_joint {n : ℕ}
    (k : Fin (n + 1)) (u : Vector (n + 1)) :
    Measurable (fun z : ℝ × Vector n => SignedSurface.normalSectionChart k u z.1 z.2) := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
  have hsplit : Measurable (fun z : ℝ × Vector n => (k.insertNth z.1 z.2 : Vector (n + 1))) := by
    simpa only [split, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using split.symm.measurable
  exact (SignedSurface.gaussianRotation (SignedSurface.coordinateNormalRotation k u)).measurable.comp hsplit

/-- Actual bounded-test disintegration into an independent normal scalar
and the concrete affine Gaussian section law. -/
theorem standardGaussian_integral_section_product {n : ℕ}
    (k : Fin (n + 1)) (u : Vector (n + 1)) (hu : vectorNormSq u = 1)
    (f : Vector (n + 1) → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ z, |f z| ≤ C) :
    (∫ z, f z ∂standardGaussian (n + 1)) =
      ∫ t : ℝ, ∫ z, f (SignedSurface.gaussianSectionPoint u t z)
        ∂standardGaussian (n + 1) ∂gaussianReal 0 1 := by
  have hi : Integrable f (standardGaussian (n + 1)) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hbound z)
  have hichart : Integrable (fun z : ℝ × Vector n => f (SignedSurface.normalSectionChart k u z.1 z.2))
      ((gaussianReal 0 1).prod (standardGaussian n)) :=
    (integrable_const C).mono' (hf.comp (measurable_normalSectionChart_joint k u)).aestronglyMeasurable
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hbound _)
  have he (t : ℝ) : (∫ z, f (SignedSurface.gaussianSectionPoint u t z) ∂standardGaussian (n + 1)) =
      ∫ y, f (SignedSurface.normalSectionChart k u t y) ∂standardGaussian n := by
    have his : Integrable (fun z => f (SignedSurface.gaussianSectionPoint u t z)) (standardGaussian (n + 1)) :=
      (integrable_const C).mono' (hf.comp (SignedSurface.measurable_gaussianSectionPoint u t)).aestronglyMeasurable
        (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hbound _)
    rw [SignedSurface.standardGaussian_integral_normal_sections k u his]
    simp only [gaussianSectionPoint_normalSectionChart k u hu, integral_const,
      measureReal_univ_eq_one, one_smul]
  calc
    _ = ∫ y, ∫ t : ℝ, f (SignedSurface.normalSectionChart k u t y)
        ∂gaussianReal 0 1 ∂standardGaussian n :=
      SignedSurface.standardGaussian_integral_normal_sections k u hi
    _ = ∫ t : ℝ, ∫ y, f (SignedSurface.normalSectionChart k u t y)
        ∂standardGaussian n ∂gaussianReal 0 1 := (integral_integral_swap hichart).symm
    _ = _ := by apply integral_congr_ae; exact ae_of_all _ (fun t => (he t).symm)

end
end RectangleCLT.Companion.SplitV4
