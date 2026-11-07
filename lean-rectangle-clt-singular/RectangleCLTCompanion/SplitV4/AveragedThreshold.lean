import RectangleCLT.GaussianProjectionMaximum
import RectangleCLTCompanion.SignedSurfacePolyhedron
import RectangleCLTCompanion.SignedSurfaceTubes
import RectangleCLTCompanion.SignedSurfaceGaussianSection
import RectangleCLTCompanion.SplitV4.GaussianThresholdData
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual threshold polyhedra, their threshold-independent Gaussian
projection radius, disjoint adaptive outward tubes, and concentrated-base
averaging. These geometric and averaging results do not assume a bound on a
Gaussian threshold derivative. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {m r : ℕ}

/-- Every two-normal span is included; diagonal pairs include single faces. -/
def thresholdPairSpan (u : Fin m → Vector r) (jl : Fin m × Fin m) :
    Submodule ℝ (EuclideanSpace ℝ (Fin r)) :=
  Submodule.span ℝ (Set.range (fun i : Fin 2 =>
    projectionEuclideanVector (if i = 0 then u jl.1 else u jl.2)))

theorem thresholdPairSpan_finrank_le (u : Fin m → Vector r) (jl : Fin m × Fin m) :
    Module.finrank ℝ (thresholdPairSpan u jl) ≤ 2 := by
  simpa only [thresholdPairSpan, Fintype.card_fin] using
    finrank_range_le_card (fun i : Fin 2 =>
      projectionEuclideanVector (if i = 0 then u jl.1 else u jl.2))

/-- The actual radius in the adaptive Gaussian layer. All pair projections
are genuine orthogonal projections and the radius is independent of thresholds. -/
def thresholdProjectionRadius (u : Fin m → Vector r) (g : Vector r) : ℝ :=
  1 + subspaceProjectionRadius (thresholdPairSpan u) g

theorem thresholdProjectionRadius_ge_one (u : Fin m → Vector r) (g : Vector r) :
    1 ≤ thresholdProjectionRadius u g := by
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem measurable_thresholdProjectionRadius (u : Fin m → Vector r) :
    Measurable (thresholdProjectionRadius u) :=
  measurable_const.add (measurable_subspaceProjectionRadius _)

theorem continuous_thresholdProjectionRadius (u : Fin m → Vector r) :
    Continuous (thresholdProjectionRadius u) := by
  apply continuous_const.add
  apply Continuous.norm
  apply continuous_pi
  intro jl
  exact ((thresholdPairSpan u jl).orthogonalProjection.continuous.comp
    (PiLp.continuous_equiv_symm 2 _)).norm

theorem thresholdPairSpan_projection_norm_le
    (u : Fin m → Vector r) (jl : Fin m × Fin m) (g : Vector r) :
    ‖(thresholdPairSpan u jl).orthogonalProjection (projectionEuclideanVector g)‖ ≤
      thresholdProjectionRadius u g - 1 := by
  have hh := norm_le_pi_norm (fun kl : Fin m × Fin m =>
    ‖(thresholdPairSpan u kl).orthogonalProjection (projectionEuclideanVector g)‖) jl
  simpa only [thresholdProjectionRadius, subspaceProjectionRadius,
    Real.norm_of_nonneg (norm_nonneg _), add_sub_cancel_left] using hh

theorem thresholdProjectionRadius_add_le
    (u : Fin m → Vector r) (g d : Vector r) :
    thresholdProjectionRadius u (g + d) ≤
      thresholdProjectionRadius u g + ‖projectionEuclideanVector d‖ := by
  have hh : subspaceProjectionRadius (thresholdPairSpan u) (g + d) ≤
      subspaceProjectionRadius (thresholdPairSpan u) g + ‖projectionEuclideanVector d‖ := by
    apply (pi_norm_le_iff_of_nonneg
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    intro jl
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have hadd : projectionEuclideanVector (g + d) =
        projectionEuclideanVector g + projectionEuclideanVector d := rfl
    rw [hadd, map_add]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simpa only [thresholdProjectionRadius, add_sub_cancel_left] using
        thresholdPairSpan_projection_norm_le u jl g
    · exact ((thresholdPairSpan u jl).orthogonalProjection.le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (thresholdPairSpan u jl).orthogonalProjection_norm_le
          (norm_nonneg _)).trans_eq (one_mul _))
  unfold thresholdProjectionRadius
  linarith

theorem thresholdProjectionRadius_abs_inner_le
    (u : Fin m → Vector r) (jl : Fin m × Fin m)
    {d : EuclideanSpace ℝ (Fin r)} (hd : d ∈ thresholdPairSpan u jl) (g : Vector r) :
    |⟪d, projectionEuclideanVector g⟫_ℝ| ≤
      ‖d‖ * (thresholdProjectionRadius u g - 1) := by
  let v : thresholdPairSpan u jl := ⟨d, hd⟩
  have heq : ⟪d, projectionEuclideanVector g⟫_ℝ =
      ⟪v, (thresholdPairSpan u jl).orthogonalProjection (projectionEuclideanVector g)⟫_ℝ := by
    rw [Submodule.inner_orthogonalProjection_eq_of_mem_left]
  rw [heq]
  exact (abs_real_inner_le_norm v _).trans
    (mul_le_mul_of_nonneg_left (thresholdPairSpan_projection_norm_le u jl g) (norm_nonneg _))

theorem thresholdProjectionRadius_face_le
    (u : Fin m → Vector r) (j : Fin m)
    (hu : ‖projectionEuclideanVector (u j)‖ = 1) (g : Vector r) :
    |faceDot (u j) g| ≤ thresholdProjectionRadius u g - 1 := by
  have hm : projectionEuclideanVector (u j) ∈ thresholdPairSpan u (j, j) := by
    apply Submodule.subset_span
    exact ⟨0, by simp⟩
  have hh := thresholdProjectionRadius_abs_inner_le u (j, j) hm g
  simpa only [hu, one_mul, SignedSurface.faceDot_eq_euclidean_inner] using hh

private theorem threshold_pair_basis_card_exp_le (hm : 1 ≤ m) :
    2 * (1 + (2 : ℝ) * (Fintype.card (Fin m × Fin m) : ℝ)) ≤
      Real.exp (4 * dimensionLog m) := by
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he4 : (16 : ℝ) ≤ Real.exp 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he1 4
    norm_num at hh
    simpa only [← Real.exp_nat_mul, show (4 : ℝ) * 1 = 4 by norm_num] using hh
  have hm24 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by decide)
  have hm4 : 1 ≤ (m : ℝ) ^ 4 := one_le_pow₀ hm1
  have heq : Real.exp (4 * dimensionLog m) = Real.exp 4 * (m : ℝ) ^ 4 := by
    rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _) hm0.ne', Real.log_exp]
    rw [mul_add, mul_one, Real.exp_add]
    congr 1
    rw [show (4 : ℝ) * Real.log (m : ℝ) = (4 : ℕ) * Real.log (m : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hm0]
  rw [heq]
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  calc
    2 * (1 + 2 * ((m : ℝ) * m)) ≤ 16 * (m : ℝ) ^ 4 := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right he4 (pow_nonneg hm0.le _)

/-- The actual radius has Gaussian moments depending only on the number
of faces, with no dependence on ambient dimension or a correlation gap. -/
theorem thresholdProjectionRadius_moment
    (hm : 1 ≤ m) (u : Fin m → Vector r) (k : ℕ) :
    Integrable (fun g => thresholdProjectionRadius u g ^ k) (standardGaussian r) ∧
      (∫ g, thresholdProjectionRadius u g ^ k ∂standardGaussian r) ≤
        (Real.sqrt (dimensionLog m)) ^ k * Real.exp (4 + (2 * (k + 1 : ℝ)) ^ 2 / 2) := by
  have hw := subspaceProjectionRadius_weighted_moment_le (thresholdPairSpan u) 2
    (thresholdPairSpan_finrank_le u) (log_exp_mul_nat_ge_one hm)
    (threshold_pair_basis_card_exp_le hm) (le_refl (Real.sqrt (dimensionLog m))) k
  have hp (g : Vector r) : thresholdProjectionRadius u g ^ k ≤
      Real.exp (subspaceProjectionRadius (thresholdPairSpan u) g / Real.sqrt (dimensionLog m)) *
        thresholdProjectionRadius u g ^ k := by
    have he : 1 ≤ Real.exp
        (subspaceProjectionRadius (thresholdPairSpan u) g / Real.sqrt (dimensionLog m)) :=
      Real.one_le_exp_iff.mpr (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he
      (pow_nonneg (zero_le_one.trans (thresholdProjectionRadius_ge_one u g)) k)
  have hi : Integrable (fun g => thresholdProjectionRadius u g ^ k) (standardGaussian r) := by
    apply hw.1.mono' ((measurable_thresholdProjectionRadius u).pow_const k).aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (pow_nonneg (zero_le_one.trans (thresholdProjectionRadius_ge_one u g)) k)]
      exact hp g)
  exact ⟨hi, (integral_mono hi hw.1 hp).trans hw.2⟩

theorem thresholdProjectionRadius_second_third_moments
    (hm : 1 ≤ m) (u : Fin m → Vector r) :
    Integrable (fun g => thresholdProjectionRadius u g ^ 2) (standardGaussian r) ∧
    Integrable (fun g => thresholdProjectionRadius u g ^ 3) (standardGaussian r) ∧
    (∫ g, thresholdProjectionRadius u g ^ 2 ∂standardGaussian r) ≤
      Real.exp 36 * dimensionLog m ∧
    (∫ g, thresholdProjectionRadius u g ^ 3 ∂standardGaussian r) ≤
      Real.exp 36 * dimensionLog m * Real.sqrt (dimensionLog m) := by
  have h2 := thresholdProjectionRadius_moment hm u 2
  have h3 := thresholdProjectionRadius_moment hm u 3
  have hL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
  have hsq := Real.sq_sqrt (zero_le_one.trans hL)
  refine ⟨h2.1, h3.1, ?_, ?_⟩
  · apply h2.2.trans
    norm_num at ⊢
    rw [hsq, mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by norm_num)) (zero_le_one.trans hL)
  · apply h3.2.trans_eq
    norm_num
    rw [pow_succ, hsq]
    ring

def thresholdPolyhedron (u : Fin m → Vector r) (a : Vector m) : Set (Vector r) :=
  {v | ∀ j, faceDot (u j) v ≤ a j}

theorem measurable_thresholdDot (u : Vector r) : Measurable (faceDot u) :=
  Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))

theorem measurableSet_thresholdPolyhedron (u : Fin m → Vector r) (a : Vector m) :
    MeasurableSet (thresholdPolyhedron u a) := by
  unfold thresholdPolyhedron
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun j : Fin m =>
    measurableSet_le (measurable_thresholdDot (u j)) measurable_const)

def thresholdOuterLayer (u : Fin m → Vector r) (a : Vector m) (w : ℝ) : Set (Vector r) :=
  thresholdPolyhedron u (fun j => a j + w) \ thresholdPolyhedron u a

theorem measurableSet_thresholdOuterLayer (u : Fin m → Vector r) (a : Vector m) (w : ℝ) :
    MeasurableSet (thresholdOuterLayer u a w) :=
  (measurableSet_thresholdPolyhedron _ _).diff (measurableSet_thresholdPolyhedron _ _)

/-- The paper's concentration assumption, on actual symmetric threshold
layers, with its concentration constant and logarithmic parameter retained. -/
def ConcentratedThresholdBase (μ : Measure (Vector r)) (u : Fin m → Vector r)
    (C δ L : ℝ) : Prop :=
  ∀ a : Vector m, ∀ s : ℝ, 0 < s →
    μ.real (thresholdPolyhedron u (fun j => a j + s) \
      thresholdPolyhedron u (fun j => a j - s)) ≤ C * (s + δ) * Real.sqrt L

theorem ConcentratedThresholdBase.outerLayer_le
    {μ : Measure (Vector r)} [IsProbabilityMeasure μ] {u : Fin m → Vector r}
    {C δ L : ℝ} (hc : ConcentratedThresholdBase μ u C δ L)
    (a : Vector m) {w : ℝ} (hw : 0 < w) :
    μ.real (thresholdOuterLayer u a w) ≤ C * (w + δ) * Real.sqrt L := by
  apply (measureReal_mono (show thresholdOuterLayer u a w ⊆
    thresholdPolyhedron u (fun j => a j + w) \
      thresholdPolyhedron u (fun j => a j - w) from ?_)).trans (hc a w hw)
  rintro v ⟨hv, hvnot⟩
  refine ⟨hv, ?_⟩
  intro hi
  apply hvnot
  intro j
  have hj := hi j
  dsimp only at hj
  linarith

def thresholdsFromBase (u : Fin m → Vector r) (a : Vector m) (σ : ℝ) (v : Vector r) : Vector m :=
  fun j => (a j - faceDot (u j) v) / σ

/-- The exact adaptive outer-layer event in the original base times Gaussian
space; this definition has no derivative or analytic-estimate input. -/
def adaptiveThresholdEvent (u : Fin m → Vector r) (a : Vector m) (σ : ℝ)
    (R : Vector r → ℝ) : Set (Vector r × Vector r) :=
  {vg | vg.2 ∈ thresholdOuterLayer u (thresholdsFromBase u a σ vg.1) (1 / R vg.2)}

theorem measurableSet_adaptiveThresholdEvent
    (u : Fin m → Vector r) (a : Vector m) (σ : ℝ) {R : Vector r → ℝ}
    (hR : Measurable R) : MeasurableSet (adaptiveThresholdEvent u a σ R) := by
  have hb (j : Fin m) : Measurable (fun vg : Vector r × Vector r =>
      (a j - faceDot (u j) vg.1) / σ) :=
    (measurable_const.sub ((measurable_thresholdDot _).comp measurable_fst)).div_const _
  have hr : Measurable (fun vg : Vector r × Vector r => 1 / R vg.2) :=
    measurable_const.div (hR.comp measurable_snd)
  change MeasurableSet ({vg : Vector r × Vector r | ∀ j,
      faceDot (u j) vg.2 ≤ (a j - faceDot (u j) vg.1) / σ + 1 / R vg.2} \
    {vg : Vector r × Vector r | ∀ j, faceDot (u j) vg.2 ≤ (a j - faceDot (u j) vg.1) / σ})
  simp only [Set.setOf_forall]
  exact (MeasurableSet.iInter (fun j => measurableSet_le
      ((measurable_thresholdDot (u j)).comp measurable_snd) ((hb j).add hr))).diff
        (MeasurableSet.iInter (fun j => measurableSet_le
          ((measurable_thresholdDot (u j)).comp measurable_snd) (hb j)))

theorem adaptiveThresholdEvent_section
    (u : Fin m → Vector r) (a : Vector m) {σ : ℝ} (hσ : 0 < σ)
    (R : Vector r → ℝ) (g : Vector r) :
    {v | (v, g) ∈ adaptiveThresholdEvent u a σ R} =
      thresholdOuterLayer u (fun j => a j - σ * faceDot (u j) g) (σ / R g) := by
  have he (j : Fin m) (v : Vector r) (w : ℝ) :
      faceDot (u j) g ≤ (a j - faceDot (u j) v) / σ + w ↔
        faceDot (u j) v ≤ a j - σ * faceDot (u j) g + σ * w := by
    rw [← mul_le_mul_right hσ, add_mul, div_mul_cancel₀ _ hσ.ne']
    constructor <;> intro h <;> nlinarith
  ext v
  simp only [adaptiveThresholdEvent, thresholdOuterLayer, thresholdPolyhedron,
    thresholdsFromBase, Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · rintro ⟨hout, hnot⟩
    refine ⟨fun j => ?_, fun hin => hnot (fun j => ?_)⟩
    · simpa only [mul_one_div] using (he j v (1 / R g)).mp (hout j)
    · simpa only [add_zero] using (he j v 0).mpr (by simpa using hin j)
  · rintro ⟨hout, hnot⟩
    refine ⟨fun j => ?_, fun hin => hnot (fun j => ?_)⟩
    · apply (he j v (1 / R g)).mpr
      simpa only [mul_one_div] using hout j
    · simpa only [mul_zero, add_zero] using (he j v 0).mp (by simpa using hin j)

theorem ConcentratedThresholdBase.adaptive_section_le
    {μ : Measure (Vector r)} [IsProbabilityMeasure μ] {u : Fin m → Vector r}
    {C δ L : ℝ} (hc : ConcentratedThresholdBase μ u C δ L)
    (a : Vector m) {σ : ℝ} (hσ : 0 < σ)
    (R : Vector r → ℝ) (hRpos : ∀ g, 0 < R g) (g : Vector r) :
    μ.real {v | (v, g) ∈ adaptiveThresholdEvent u a σ R} ≤
      C * (σ / R g + δ) * Real.sqrt L := by
  rw [adaptiveThresholdEvent_section u a hσ R g]
  exact hc.outerLayer_le _ (div_pos hσ (hRpos g))

/-- The exact averaging step of B.5. It integrates the actual adaptive
layer against an arbitrary concentrated base and independent probability
law. It requires only genuine second and third radius moments. -/
theorem concentratedBase_adaptiveLayer_average
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (γ : Measure (Vector r)) [IsProbabilityMeasure γ]
    (u : Fin m → Vector r) (a : Vector m) {C δ L σ : ℝ}
    (hσ : 0 < σ)
    (hc : ConcentratedThresholdBase μ u C δ L)
    (R : Vector r → ℝ) (hR : Measurable R) (hRpos : ∀ g, 0 < R g)
    (h2 : Integrable (fun g => R g ^ 2) γ) (h3 : Integrable (fun g => R g ^ 3) γ) :
    (∫ v, ∫ g, (adaptiveThresholdEvent u a σ R).indicator
      (fun vg => R vg.2 ^ 3) (v, g) ∂γ ∂μ) ≤
      C * Real.sqrt L *
        (σ * (∫ g, R g ^ 2 ∂γ) + δ * (∫ g, R g ^ 3 ∂γ)) := by
  let E := adaptiveThresholdEvent u a σ R
  let K : Vector r × Vector r → ℝ := E.indicator (fun vg => R vg.2 ^ 3)
  have hE : MeasurableSet E := measurableSet_adaptiveThresholdEvent u a σ hR
  have hweight : Integrable (fun vg : Vector r × Vector r => R vg.2 ^ 3) (μ.prod γ) := by
    simpa only [one_mul] using (integrable_const (μ := μ) (1 : ℝ)).mul_prod h3
  have hK : Integrable K (μ.prod γ) := hweight.indicator hE
  have hsection (g : Vector r) :
      (∫ v, K (v, g) ∂μ) = R g ^ 3 * μ.real {v | (v, g) ∈ E} := by
    have hm : MeasurableSet {v | (v, g) ∈ E} := hE.preimage (measurable_id.prodMk measurable_const)
    change (∫ v, ({v | (v, g) ∈ E}).indicator (fun _ => R g ^ 3) v ∂μ) = _
    rw [integral_indicator_const _ hm, smul_eq_mul, mul_comm]
  have hpoint (g : Vector r) : (∫ v, K (v, g) ∂μ) ≤
      C * Real.sqrt L * (σ * R g ^ 2 + δ * R g ^ 3) := by
    rw [hsection]
    have hp := mul_le_mul_of_nonneg_left (hc.adaptive_section_le a hσ R hRpos g)
      (pow_nonneg (hRpos g).le 3)
    apply hp.trans_eq
    field_simp [(hRpos g).ne']
    ring
  have hright : Integrable (fun g => C * Real.sqrt L * (σ * R g ^ 2 + δ * R g ^ 3)) γ :=
    ((h2.const_mul σ).add (h3.const_mul δ)).const_mul _
  calc
    _ = ∫ g, ∫ v, K (v, g) ∂μ ∂γ := integral_integral_swap hK
    _ ≤ ∫ g, C * Real.sqrt L * (σ * R g ^ 2 + δ * R g ^ 3) ∂γ :=
      integral_mono hK.integral_prod_right hright hpoint
    _ = _ := by
      rw [integral_const_mul, integral_add (h2.const_mul σ) (h3.const_mul δ),
        integral_const_mul, integral_const_mul]

/-- The Gaussian-radius version of the actual averaging step, with a fixed
constant and the paper's logarithmic and lattice powers. -/
theorem concentratedBase_gaussian_adaptiveLayer_average
    (hm : 1 ≤ m) (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) {C δ L σ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ L) (hc : ConcentratedThresholdBase μ u C δ L) :
    (∫ v, ∫ g, (adaptiveThresholdEvent u a σ (thresholdProjectionRadius u)).indicator
      (fun vg => thresholdProjectionRadius u vg.2 ^ 3) (v, g) ∂standardGaussian r ∂μ) ≤
      C * Real.exp 36 * (σ * L * Real.sqrt L + δ * L ^ 2) := by
  have hL0 : 0 ≤ L := (zero_le_one.trans (log_exp_mul_nat_ge_one hm)).trans hL
  obtain ⟨h2, h3, h2bound, h3bound⟩ := thresholdProjectionRadius_second_third_moments hm u
  have h2final : (∫ g, thresholdProjectionRadius u g ^ 2 ∂standardGaussian r) ≤
      Real.exp 36 * L := h2bound.trans (mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le)
  have h3final : (∫ g, thresholdProjectionRadius u g ^ 3 ∂standardGaussian r) ≤
      Real.exp 36 * L * Real.sqrt L := by
    apply h3bound.trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le)
      (Real.sqrt_le_sqrt hL) (Real.sqrt_nonneg _) (mul_nonneg (Real.exp_pos _).le hL0)
  have hh := concentratedBase_adaptiveLayer_average μ (standardGaussian r) u a hσ hc
    (thresholdProjectionRadius u) (measurable_thresholdProjectionRadius u)
    (fun g => zero_lt_one.trans_le (thresholdProjectionRadius_ge_one u g)) h2 h3
  apply hh.trans
  have hsq := Real.sq_sqrt hL0
  calc
    _ ≤ C * Real.sqrt L * (σ * (Real.exp 36 * L) + δ * (Real.exp 36 * L * Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left h2final hσ.le)
        (mul_le_mul_of_nonneg_left h3final hδ)) (mul_nonneg hC (Real.sqrt_nonneg _))
    _ = C * Real.exp 36 * (σ * L * Real.sqrt L + δ * L * (Real.sqrt L ^ 2)) := by ring
    _ = _ := by rw [hsq]; ring

section AdaptiveGeometry

open SignedSurface

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Outward tubes with width chosen from the radius at the actual base
point. The entire equality set at that base point is retained. -/
def adaptiveOutwardTube (normal : ι → E) (offset : ι → ℝ) (R : E → ℝ)
    (active : Finset ι) : Set E :=
  {g | ∃ x ∈ exactStratum normal offset active, ∃ c : ι → ℝ,
    (∀ j ∈ active, 0 ≤ c j) ∧ coneDisplacement normal active c ≠ 0 ∧
      ‖coneDisplacement normal active c‖ ≤ 1 / (4 * R x) ∧
      g = x + coneDisplacement normal active c}

/-- Variational uniqueness of the actual nearest point makes distinct
active-set tubes disjoint even when their widths depend on that point. -/
theorem adaptiveOutwardTube_disjoint
    (normal : ι → E) (offset : ι → ℝ) (R : E → ℝ)
    {active other : Finset ι} (hne : active ≠ other) :
    Disjoint (adaptiveOutwardTube normal offset R active)
      (adaptiveOutwardTube normal offset R other) := by
  rw [Set.disjoint_left]
  rintro g ⟨x, hx, c, hc, _, _, hg⟩ ⟨y, hy, d, hd, _, _, hg'⟩
  have hxy : x = y := SignedSurface.outward_base_unique hx.1 hy.1
    (coneDisplacement_isOutward normal offset active hx c hc)
    (coneDisplacement_isOutward normal offset other hy d hd) (hg.symm.trans hg')
  exact Set.disjoint_left.mp (exactStratum_disjoint normal offset hne) hx (hxy.symm ▸ hy)

omit [InnerProductSpace ℝ E] in
/-- A short adaptive displacement stays within the reciprocal-radius width
at its endpoint. This scalar argument is independent of the dimension. -/
theorem adaptive_displacement_le_reciprocal_radius
    (R : E → ℝ) (hR : ∀ x, 1 ≤ R x)
    (hRadd : ∀ x d, R (x + d) ≤ R x + ‖d‖)
    (x d : E) (hd : ‖d‖ ≤ 1 / (4 * R x)) : ‖d‖ ≤ 1 / R (x + d) := by
  have hRx : 0 < R x := zero_lt_one.trans_le (hR x)
  have hRg : 0 < R (x + d) := zero_lt_one.trans_le (hR _)
  have hlen : ‖d‖ ≤ (1 / 4 : ℝ) := hd.trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by linarith [hR x] : (4 : ℝ) ≤ 4 * R x))
  have hlenR := (le_div_iff₀ (by positivity : 0 < 4 * R x)).mp hd
  have hmul := mul_le_mul_of_nonneg_left (hRadd x d) (norm_nonneg d)
  apply (le_div_iff₀ hRg).mpr
  nlinarith [sq_nonneg (‖d‖ - 1 / 4)]

omit [InnerProductSpace ℝ E] in
theorem adaptive_radius_at_endpoint_lower
    (R : E → ℝ) (hR : ∀ x, 1 ≤ R x)
    (hRadd : ∀ x d, R (x + d) ≤ R x + ‖d‖)
    (x d : E) (hd : ‖d‖ ≤ 1 / (4 * R x)) : R x / 2 ≤ R (x + d) := by
  have hRx : 0 < R x := zero_lt_one.trans_le (hR x)
  have hlen : ‖d‖ ≤ (1 / 4 : ℝ) := hd.trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by linarith [hR x] : (4 : ℝ) ≤ 4 * R x))
  have hrev := hRadd (x + d) (-d)
  rw [add_neg_cancel_right, norm_neg] at hrev
  linarith [hR x]

/-- The union of the genuine disjoint outward tubes lies in the adaptive
outer layer, with the radius evaluated at the output point. -/
theorem adaptiveOutwardTube_subset_outerLayer
    (normal : ι → E) (offset : ι → ℝ) (hnormal : ∀ j, ‖normal j‖ = 1)
    (R : E → ℝ) (hR : ∀ x, 1 ≤ R x)
    (hRadd : ∀ x d, R (x + d) ≤ R x + ‖d‖) (active : Finset ι) :
    adaptiveOutwardTube normal offset R active ⊆
      {g | g ∈ polyhedron normal (fun j => offset j + 1 / R g) ∧
        g ∉ polyhedron normal offset} := by
  rintro g ⟨x, hx, c, hc, hd0, hd, rfl⟩
  have hwidth := adaptive_displacement_le_reciprocal_radius R hR hRadd x _ hd
  refine ⟨?_, outward_point_not_mem
    (coneDisplacement_isOutward normal offset active hx c hc) hd0⟩
  intro j
  rw [inner_add_right]
  apply add_le_add (hx.1 j)
  calc
    _ ≤ |⟪normal j, coneDisplacement normal active c⟫_ℝ| := le_abs_self _
    _ ≤ ‖normal j‖ * ‖coneDisplacement normal active c‖ := abs_real_inner_le_norm _ _
    _ ≤ _ := by rw [hnormal j, one_mul]; exact hwidth

/-- The actual bisector rectangle enters the adaptive tube with the same
fixed point as its base. Its exact area is the imported `ridgeRectangle_area`. -/
theorem ridgeRectangle_mem_adaptiveOutwardTube [DecidableEq ι]
    (normal : ι → E) (offset : ι → ℝ) (R : E → ℝ) (hR : ∀ x, 1 ≤ R x)
    (active : Finset ι) {j k : ι} (hj : j ∈ active) (hk : k ∈ active)
    {x : E} (hx : x ∈ exactStratum normal offset active)
    (hu : ‖normal j‖ = 1) (hv : ‖normal k‖ = 1)
    (hp : normal j + normal k ≠ 0) (hm : normal j - normal k ≠ 0)
    {st : ℝ × ℝ} (hst : st ∈ ridgeRectangle (normal j) (normal k) (1 / (4 * R x))) :
    x + ridgeDisplacement (normal j) (normal k) st ∈
      adaptiveOutwardTube normal offset R active := by
  have hε : 0 < 1 / (4 * R x) := by have := hR x; positivity
  obtain ⟨a, b, ha, hb, heq⟩ := ridgeRectangle_maps_into_cone
    (normal j) (normal k) hu hv hp hm hε.le hst
  let c : ι → ℝ := fun i => (if i = j then a else 0) + (if i = k then b else 0)
  have hdisp : coneDisplacement normal active c =
      ridgeDisplacement (normal j) (normal k) st := by
    rw [heq]
    simp only [coneDisplacement, c, add_smul, ite_smul, zero_smul]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' active j, Finset.sum_ite_eq' active k]
    simp [hj, hk]
  refine ⟨x, hx, c, ?_, ?_, ?_, ?_⟩
  · intro i hi
    dsimp only [c]
    split_ifs <;> positivity
  · rw [hdisp]

    exact ridgeRectangle_displacement_ne_zero (normal j) (normal k)
      (hu.trans hv.symm) hp hε hst
  · rw [hdisp]
    exact ridgeRectangle_displacement_norm_le (normal j) (normal k) hu hv hp hm hε.le hst
  · rw [hdisp]

/-- A real adaptive normal-fiber integral at one facet. The factor `R²`
comes from the cubic weight times a reciprocal-radius interval length. -/
theorem adaptive_facet_gaussian_integral_lower
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1 ≤ R x)
    (hRadd : ∀ x d, R (x + d) ≤ R x + ‖d‖)
    (x u z : E) (hu : ‖u‖ = 1) (hz : |⟪z, u⟫_ℝ| ≤ R x) :
    Real.exp (-(3 : ℝ) / 2) * SignedSurface.gaussianKernel z * (R x ^ 2 / 32) ≤
      ∫ t in Set.Icc (0 : ℝ) (1 / (4 * R x)),
        R (x + t • u) ^ 3 * SignedSurface.gaussianKernel (z + t • u) := by
  have hRx : 0 < R x := zero_lt_one.trans_le (hR x)
  let ε := 1 / (4 * R x)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp only [ε]
    apply (div_le_iff₀ (by positivity : 0 < 4 * R x)).mpr
    linarith [hR x]
  have hRε : R x * ε ≤ 1 := by
    dsimp only [ε]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 4 * R x)).mpr
    linarith
  have hbase := facet_gaussian_integral_lower u z hu hRx.le hε.le hε1 hRε hz
  have hk : Continuous (fun t : ℝ => SignedSurface.gaussianKernel (z + t • u)) := by fun_prop
  have hw : Continuous (fun t : ℝ => R (x + t • u) ^ 3 * SignedSurface.gaussianKernel (z + t • u)) := by
    exact ((hRm.comp (by fun_prop)).pow 3).mul hk
  have hm : (R x / 2) ^ 3 * (∫ t in Set.Icc (0 : ℝ) ε, SignedSurface.gaussianKernel (z + t • u)) ≤
      ∫ t in Set.Icc (0 : ℝ) ε, R (x + t • u) ^ 3 * SignedSurface.gaussianKernel (z + t • u) := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      ((continuous_const.mul hk).continuousOn.integrableOn_Icc (μ := volume))
      (hw.continuousOn.integrableOn_Icc (μ := volume))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hd : ‖t • u‖ ≤ ε := by
      simpa only [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_nonneg ht.1] using ht.2
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg hRx.le (by norm_num))
        (adaptive_radius_at_endpoint_lower R hR hRadd x _ hd) 3)
      (Real.exp_nonneg _)
  have hh := (mul_le_mul_of_nonneg_left hbase
    (pow_nonneg (div_nonneg hRx.le (by norm_num)) 3)).trans hm
  convert hh using 1
  dsimp only [ε]
  field_simp
  ring

/-- A real adaptive two-dimensional ridge-fiber integral. Its surviving
normal factor is `‖u−v‖`, so no inverse correlation gap is introduced. -/
theorem adaptive_ridge_gaussian_integral_lower
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1 ≤ R x)
    (hRadd : ∀ x d, R (x + d) ≤ R x + ‖d‖)
    (x u v z : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    (hb : |⟪z, bisector u v⟫_ℝ| ≤ R x)
    (hc : |⟪z, differenceDirection u v⟫_ℝ| ≤ R x) :
    Real.exp (-(3 : ℝ) / 2) * SignedSurface.gaussianKernel z * (R x * ‖u - v‖ / 2048) ≤
      ∫ st in ridgeRectangle u v (1 / (4 * R x)),
        R (x + ridgeDisplacement u v st) ^ 3 * SignedSurface.gaussianKernel (z + ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume) := by
  have hRx : 0 < R x := zero_lt_one.trans_le (hR x)
  let ε := 1 / (4 * R x)
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp only [ε]
    apply (div_le_iff₀ (by positivity : 0 < 4 * R x)).mpr
    linarith [hR x]
  have hRε : R x * ε ≤ 1 := by
    dsimp only [ε]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 4 * R x)).mpr
    linarith
  have hbase := ridgeRectangle_gaussian_integral_lower u v z hu hv hp hm hRx.le hε.le hε1 hRε hb hc
  have hk : Continuous (fun st => SignedSurface.gaussianKernel (z + ridgeDisplacement u v st)) := by fun_prop
  have hw : Continuous (fun st =>
      R (x + ridgeDisplacement u v st) ^ 3 * SignedSurface.gaussianKernel (z + ridgeDisplacement u v st)) :=
    ((hRm.comp (by fun_prop)).pow 3).mul hk
  have hcompact : IsCompact (ridgeRectangle u v ε) := isCompact_Icc.prod isCompact_Icc
  have hmono : (R x / 2) ^ 3 *
      (∫ st in ridgeRectangle u v ε, SignedSurface.gaussianKernel (z + ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume)) ≤
      ∫ st in ridgeRectangle u v ε,
        R (x + ridgeDisplacement u v st) ^ 3 * SignedSurface.gaussianKernel (z + ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume) := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      ((continuous_const.mul hk).continuousOn.integrableOn_compact hcompact)
      (hw.continuousOn.integrableOn_compact hcompact)
    filter_upwards [ae_restrict_mem hcompact.measurableSet] with st hst
    have hd := ridgeRectangle_displacement_norm_le u v hu hv hp hm hε.le hst
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (div_nonneg hRx.le (by norm_num))
        (adaptive_radius_at_endpoint_lower R hR hRadd x _ hd) 3)
      (Real.exp_nonneg _)
  have hh := (mul_le_mul_of_nonneg_left hbase
    (pow_nonneg (div_nonneg hRx.le (by norm_num)) 3)).trans hmono
  convert hh using 1
  dsimp only [ε]
  field_simp
  ring
end AdaptiveGeometry

end
end RectangleCLT.Companion.SplitV4
