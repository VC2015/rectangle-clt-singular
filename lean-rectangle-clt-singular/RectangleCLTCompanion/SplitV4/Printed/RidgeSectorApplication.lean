import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorFiber
import RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusMoments
import RectangleCLTCompanion.SplitV4.GaussianThresholdPairTubes
import RectangleCLTCompanion.SplitV4.GaussianThresholdPairCoarea

/-! Actual sector events and Gaussian section integrals for the printed
B.5 paired-ridge argument. Earlier rectangle events are retained. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace Topology

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- Measurability of a sector whose radial cutoff is a measurable function.
The rational exhaustion avoids any global continuity assumption on the
chosen branch of the polar angle. -/
theorem measurableSet_variable_planeSector {Ω : Type*} [MeasurableSpace Ω]
    (st : Ω → ℝ × ℝ) (η : Ω → ℝ) (hst : Measurable st) (hη : Measurable η) (α : ℝ) :
    MeasurableSet {ω | st ω ∈ planeSector α (η ω)} := by
  have he : {ω | st ω ∈ planeSector α (η ω)} =
      ⋃ q : ℚ, {ω | st ω ∈ planeSector α (q : ℝ)} ∩ {ω | (q : ℝ) < η ω} := by
    ext ω
    constructor
    · intro h
      obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn h.2.1.2
      exact mem_iUnion.mpr ⟨q, ⟨⟨h.1, ⟨⟨h.2.1.1, hq₁⟩, h.2.2⟩⟩, hq₂⟩⟩
    · intro h
      obtain ⟨q, hq, hqη⟩ := mem_iUnion.mp h
      exact ⟨hq.1, ⟨⟨hq.2.1.1, hq.2.1.2.trans hqη⟩, hq.2.2⟩⟩
  rw [he]
  exact MeasurableSet.iUnion (fun q =>
    (((isOpen_planeSector α (q : ℝ)).measurableSet.preimage hst).inter
      (measurableSet_lt measurable_const hη)))

/-- The actual paired event printed in B.5, with the complete angular
sector and an adaptive radial cutoff at its actual base point. -/
def gaussianPairSectorEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (j l : Fin m) : Set (Vector r) :=
  {g | (∀ k, k ≠ j → k ≠ l → faceDot (u k) (gaussianPairBase u b j l g) < b k) ∧
    (faceDot (thresholdPairBisector u j l) g - thresholdPairFirstLevel u b j l,
      faceDot (thresholdPairDifference u j l) g - thresholdPairSecondLevel u b j l) ∈
      planeSector (Real.arccos (faceDot (u j) (u l)))
        (1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l g)))}

theorem measurableSet_gaussianPairSectorEvent {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    MeasurableSet (gaussianPairSectorEvent u b j l) := by
  have hx := measurable_gaussianPairBase u b j l
  have hs : Measurable (fun g =>
      (faceDot (thresholdPairBisector u j l) g - thresholdPairFirstLevel u b j l,
        faceDot (thresholdPairDifference u j l) g - thresholdPairSecondLevel u b j l)) :=
    ((measurable_thresholdDot _).sub_const _).prodMk ((measurable_thresholdDot _).sub_const _)
  have hη : Measurable (fun g => 1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l g))) :=
    measurable_const.div (measurable_const.mul ((measurable_thresholdProjectionRadius u).comp hx))
  change MeasurableSet ({g | ∀ k, k ≠ j → k ≠ l →
    faceDot (u k) (gaussianPairBase u b j l g) < b k} ∩ _)
  simp only [Set.setOf_forall]
  refine (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
    measurableSet_lt ((measurable_thresholdDot _).comp hx) measurable_const)))).inter ?_
  exact measurableSet_variable_planeSector _ _ hs hη _

/-- Strict correlation bounds follow from two nonparallel unit normals. -/
theorem thresholdPair_correlation_bounds {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    -1 < faceDot (u j) (u l) ∧ faceDot (u j) (u l) < 1 := by
  have hU := thresholdEuclideanNormal_unit (u j) hu
  have hV := thresholdEuclideanNormal_unit (u l) hv
  have hadd := norm_add_sq_real (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
  have hsub := norm_sub_sq_real (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
  have hdot : ⟪projectionEuclideanVector (u j), projectionEuclideanVector (u l)⟫_ℝ =
      faceDot (u j) (u l) := by
    simpa only [projectionEuclideanVector] using
      (SignedSurface.faceDot_eq_euclidean_inner (u j) (u l)).symm
  rw [hU, hV, hdot] at hadd hsub
  have hp0 := norm_pos_iff.mpr hp
  have hm0 := norm_pos_iff.mpr hm
  constructor <;> nlinarith

/-- The section's actual normal-plane component has norm at most the
projection radius. This is the exact printed `norm z ≤ R(x)` transition,
without a coordinatewise square-root-of-two relaxation. -/
theorem thresholdPair_planeComponent_norm_le_radius {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (a c : ℝ) (x : Vector r)
    (hx : faceDot (thresholdPairBisector u j l) x = a)
    (hy : faceDot (thresholdPairDifference u j l) x = c) :
    ‖a • SignedSurface.bisector (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l)) +
      c • SignedSurface.differenceDirection (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))‖ ≤
      thresholdProjectionRadius u x - 1 := by
  let U := projectionEuclideanVector (u j)
  let V := projectionEuclideanVector (u l)
  let e := SignedSurface.bisector U V
  let f := SignedSurface.differenceDirection U V
  let z := a • e + c • f
  have he : ‖e‖ = 1 := SignedSurface.norm_bisector _ _ hp
  have hf : ‖f‖ = 1 := SignedSurface.norm_differenceDirection _ _ hm
  have hef : ⟪e, f⟫_ℝ = 0 := SignedSurface.inner_bisector_differenceDirection _ _
    ((thresholdEuclideanNormal_unit _ hu).trans (thresholdEuclideanNormal_unit _ hv).symm)
  have hU : U ∈ thresholdPairSpan u (j, l) := by apply Submodule.subset_span; exact ⟨0, by simp [U]⟩
  have hV : V ∈ thresholdPairSpan u (j, l) := by apply Submodule.subset_span; exact ⟨1, by simp [V]⟩
  have heV : e ∈ thresholdPairSpan u (j, l) :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ hU hV)
  have hfV : f ∈ thresholdPairSpan u (j, l) :=
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hU hV)
  have hzV : z ∈ thresholdPairSpan u (j, l) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ heV) (Submodule.smul_mem _ _ hfV)
  have hh := thresholdProjectionRadius_abs_inner_le u (j, l) hzV x
  have hx' : ⟪e, projectionEuclideanVector x⟫_ℝ = a := by
    simpa only [SignedSurface.faceDot_eq_euclidean_inner, thresholdPairBisector_euclidean] using hx
  have hy' : ⟪f, projectionEuclideanVector x⟫_ℝ = c := by
    simpa only [SignedSurface.faceDot_eq_euclidean_inner, thresholdPairDifference_euclidean] using hy
  have hin : ⟪z, projectionEuclideanVector x⟫_ℝ = a ^ 2 + c ^ 2 := by
    simp only [z, inner_add_left, inner_smul_left, conj_trivial, hx', hy']
    ring
  have hn : ‖z‖ ^ 2 = a ^ 2 + c ^ 2 := by
    dsimp only [z]
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, he, hf, mul_one, sq_abs, inner_smul_left,
      inner_smul_right, conj_trivial, hef, mul_zero, zero_mul, add_zero]
  rw [hin, abs_of_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg c)), ← hn] at hh
  have hR : 0 ≤ thresholdProjectionRadius u x - 1 := sub_nonneg.mpr (thresholdProjectionRadius_ge_one u x)
  change ‖z‖ ≤ _
  nlinarith [norm_nonneg z]

/-- The full angular sector has precisely the required section in the
independent normal-plane Gaussian coordinates. -/
theorem gaussianPairSectorEvent_section {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (z : Vector r) (s t : ℝ) :
    gaussianPairSectionPoint (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairFirstLevel u b j l + s) (thresholdPairSecondLevel u b j l + t) z ∈
        gaussianPairSectorEvent u b j l ↔
      (∀ k, k ≠ j → k ≠ l → faceDot (u k) (gaussianPairBase u b j l z) < b k) ∧
      (s, t) ∈ planeSector (Real.arccos (faceDot (u j) (u l)))
        (1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l z))) := by
  have he := thresholdPairBisector_unit u j l hp
  have hf := thresholdPairDifference_unit u j l hm
  have hef := thresholdPair_frame_orthogonal u j l hu hv
  have hl := gaussianPairSectionPoint_levels (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l + s) (thresholdPairSecondLevel u b j l + t) z he hf hef
  simp only [gaussianPairSectorEvent, Set.mem_setOf_eq, gaussianPairBase,
    gaussianPairSectionPoint_comp _ _ he hf hef, hl.1, hl.2, add_sub_cancel_left]

/-- The genuine Gaussian weighted integral over the complete sector at an
actual threshold section point. -/
theorem thresholdSector_fiber_lower {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (a c : ℝ) (x : Vector r)
    (hx : faceDot (thresholdPairBisector u j l) x = a)
    (hy : faceDot (thresholdPairDifference u j l) x = c) :
    (27 / 2048 : ℝ) * Real.exp (-(9 : ℝ) / 32) * Real.arccos (faceDot (u j) (u l)) *
        thresholdProjectionRadius u x * gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c ≤
      ∫ st in planeSector (Real.arccos (faceDot (u j) (u l)))
          (1 / (4 * thresholdProjectionRadius u x)),
        thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l +
          st.2 • thresholdPairDifference u j l) ^ 3 * gaussianPDFReal 0 1 (a + st.1) *
          gaussianPDFReal 0 1 (c + st.2) ∂((volume : Measure ℝ).prod volume) := by
  let U := projectionEuclideanVector (u j)
  let V := projectionEuclideanVector (u l)
  let e := SignedSurface.bisector U V
  let f := SignedSurface.differenceDirection U V
  let X := projectionEuclideanVector x
  let Z := a • e + c • f
  have hU : ‖U‖ = 1 := thresholdEuclideanNormal_unit _ hu
  have hV : ‖V‖ = 1 := thresholdEuclideanNormal_unit _ hv
  have he : ‖e‖ = 1 := SignedSurface.norm_bisector _ _ hp
  have hf : ‖f‖ = 1 := SignedSurface.norm_differenceDirection _ _ hm
  have hef : ⟪e, f⟫_ℝ = 0 := SignedSurface.inner_bisector_differenceDirection _ _ (hU.trans hV.symm)
  have hRbase : euclideanThresholdRadius u X = thresholdProjectionRadius u x := rfl
  have hz : ‖Z‖ ≤ euclideanThresholdRadius u X :=
    (thresholdPair_planeComponent_norm_le_radius u j l hu hv hp hm a c x hx hy).trans (by rw [hRbase]; linarith)
  have hρ := thresholdPair_correlation_bounds u j l hu hv hp hm
  have hα : 0 < Real.arccos (faceDot (u j) (u l)) := Real.arccos_pos.mpr hρ.2
  have hh := adaptive_sector_fiber_lower (euclideanThresholdRadius u)
    (continuous_euclideanThresholdRadius u) (euclideanThresholdRadius_ge_one u)
    (euclideanThresholdRadius_add_le u) U V X Z hU hV hp hm hz hα (Real.arccos_le_pi _)
  let d := (Real.sqrt (2 * Real.pi))⁻¹ ^ 2
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hnorm (s t : ℝ) : ‖s • e + t • f‖ ^ 2 = s ^ 2 + t ^ 2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, he, hf, mul_one, sq_abs,
      inner_smul_left, inner_smul_right, conj_trivial, hef, mul_zero, zero_mul, add_zero]
  have hpdf (s t : ℝ) : gaussianPDFReal 0 1 s * gaussianPDFReal 0 1 t =
      d * SignedSurface.gaussianKernel (s • e + t • f) := by
    rw [SignedSurface.gaussianKernel, hnorm]
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, d]
    rw [mul_mul_mul_comm, ← Real.exp_add]
    congr 1
    · exact (pow_two _).symm
    · congr 1
      ring
  have hint : (∫ st in planeSector (Real.arccos (faceDot (u j) (u l))) (1 / (4 * thresholdProjectionRadius u x)),
      thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l + st.2 • thresholdPairDifference u j l) ^ 3 *
        gaussianPDFReal 0 1 (a + st.1) * gaussianPDFReal 0 1 (c + st.2)
        ∂((volume : Measure ℝ).prod volume)) =
      d * ∫ st in planeSector (Real.arccos (faceDot (u j) (u l))) (1 / (4 * euclideanThresholdRadius u X)),
        euclideanThresholdRadius u (X + SignedSurface.ridgeDisplacement U V st) ^ 3 *
          SignedSurface.gaussianKernel (Z + SignedSurface.ridgeDisplacement U V st) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with st
    have hplane : Z + SignedSurface.ridgeDisplacement U V st =
        (a + st.1) • e + (c + st.2) • f := by
      dsimp only [Z, SignedSurface.ridgeDisplacement, e, f]
      module
    rw [hplane]
    have hr : euclideanThresholdRadius u (X + SignedSurface.ridgeDisplacement U V st) =
        thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l + st.2 • thresholdPairDifference u j l) := by
      change thresholdProjectionRadius u (fun k => (X + SignedSurface.ridgeDisplacement U V st) k) = _
      congr 1
      funext k
      simp only [X, SignedSurface.ridgeDisplacement, PiLp.add_apply, PiLp.smul_apply,
        U, V, e, f, thresholdPairBisector, thresholdPairDifference, projectionEuclideanVector,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      change x k + (st.1 * e k + st.2 * f k) = (x k + st.1 * e k) + st.2 * f k
      ring
    rw [hr]
    rw [show thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l + st.2 • thresholdPairDifference u j l) ^ 3 *
        gaussianPDFReal 0 1 (a + st.1) * gaussianPDFReal 0 1 (c + st.2) =
      thresholdProjectionRadius u (x + st.1 • thresholdPairBisector u j l + st.2 • thresholdPairDifference u j l) ^ 3 *
        (gaussianPDFReal 0 1 (a + st.1) * gaussianPDFReal 0 1 (c + st.2)) by ring, hpdf]
    ring
  rw [hint]
  have hm := mul_le_mul_of_nonneg_left hh hd
  calc
    _ = (27 / 2048 : ℝ) * Real.exp (-(9 : ℝ) / 32) * Real.arccos (faceDot (u j) (u l)) *
        thresholdProjectionRadius u x * (gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c) := by ring
    _ = d * ((27 / 2048 : ℝ) * Real.exp (-(9 : ℝ) / 32) * Real.arccos (faceDot (u j) (u l)) *
        euclideanThresholdRadius u X * SignedSurface.gaussianKernel Z) := by
          rw [hpdf, hRbase]
          dsimp only [Z]
          ring
    _ ≤ _ := hm

/-- The literal angular comparison, followed by the exact projected-radius
bound, for the actual fixed two-face section. -/
theorem thresholdPair_sector_coefficient_le_radius {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (x : Vector r)
    (hx : faceDot (thresholdPairBisector u j l) x = thresholdPairFirstLevel u b j l)
    (hy : faceDot (thresholdPairDifference u j l) x = thresholdPairSecondLevel u b j l) :
    (1 - faceDot (u j) (u l)) * |b j + b l| /
        Real.sqrt (1 - faceDot (u j) (u l) ^ 2) ≤
      Real.arccos (faceDot (u j) (u l)) * thresholdProjectionRadius u x := by
  let U := projectionEuclideanVector (u j)
  let V := projectionEuclideanVector (u l)
  let e := SignedSurface.bisector U V
  let f := SignedSurface.differenceDirection U V
  let a := thresholdPairFirstLevel u b j l
  let c := thresholdPairSecondLevel u b j l
  let Z := a • e + c • f
  have hU : ‖U‖ = 1 := thresholdEuclideanNormal_unit _ hu
  have hV : ‖V‖ = 1 := thresholdEuclideanNormal_unit _ hv
  have he : ‖e‖ = 1 := SignedSurface.norm_bisector _ _ hp
  have hef : ⟪e, f⟫_ℝ = 0 := SignedSurface.inner_bisector_differenceDirection _ _ (hU.trans hV.symm)
  have hsum : U + V = ‖U + V‖ • e := by
    dsimp only [e, SignedSurface.bisector]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hp), one_smul]
  have hlevels : ⟪U, Z⟫_ℝ + ⟪V, Z⟫_ℝ = b j + b l := by
    rw [← inner_add_left, hsum]
    simp only [Z, inner_smul_left, inner_add_right, inner_smul_right, conj_trivial,
      real_inner_self_eq_norm_sq, he, one_pow, hef, mul_one, mul_zero, add_zero]
    dsimp only [a, thresholdPairFirstLevel, U, V]
    field_simp
  have hρ := thresholdPair_correlation_bounds u j l hu hv hp hm
  have hdot : ⟪U, V⟫_ℝ = faceDot (u j) (u l) :=
    (SignedSurface.faceDot_eq_euclidean_inner _ _).symm
  have hang := angular_pair_coefficient U V Z hU hV hdot hρ.1 hρ.2
  rw [hlevels, Real.sin_arccos] at hang
  have hz : ‖Z‖ ≤ thresholdProjectionRadius u x :=
    (thresholdPair_planeComponent_norm_le_radius u j l hu hv hp hm a c x hx hy).trans (by linarith)
  exact hang.trans (mul_le_mul_of_nonneg_left hz (Real.arccos_nonneg _))

/-- Gaussian coarea on the full sector bounds the actual paired mixed
CDF derivative. No correlation-gap factor is retained. -/
theorem gaussianThresholdMixed_le_weighted_sector_event {m n : ℕ}
    (hmfaces : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m) (hjl : j ≠ l)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1) (hi : LinearIndependent ℝ u) :
    (27 / 2048 : ℝ) * Real.exp (-(9 : ℝ) / 32) * (1 - faceDot (u j) (u l)) * |b j + b l| *
        gaussianThresholdMixed u b j l ≤
      ∫ g, (gaussianPairSectorEvent u b j l).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  obtain ⟨hp, hm⟩ := thresholdPair_sum_sub_ne_zero_of_independent u hi j l hjl
  let F : Vector (n + 1) → ℝ :=
    (gaussianPairSectorEvent u b j l).indicator (fun g => thresholdProjectionRadius u g ^ 3)
  have hF : Measurable F := ((measurable_thresholdProjectionRadius u).pow_const 3).indicator
    (measurableSet_gaussianPairSectorEvent u b j l)
  have hFi : Integrable F (standardGaussian (n + 1)) :=
    (thresholdProjectionRadius_second_third_moments_from_radial_tail hmfaces u).2.1.indicator (measurableSet_gaussianPairSectorEvent u b j l)
  have hF0 (g) : 0 ≤ F g := Set.indicator_nonneg (fun x _ =>
    pow_nonneg (zero_le_one.trans (thresholdProjectionRadius_ge_one u x)) 3) g
  let e := thresholdPairBisector u j l
  let f := thresholdPairDifference u j l
  let a := thresholdPairFirstLevel u b j l
  let c := thresholdPairSecondLevel u b j l
  have he : vectorNormSq e = 1 := thresholdPairBisector_unit u j l hp
  have hf : vectorNormSq f = 1 := thresholdPairDifference_unit u j l hm
  have hef : faceDot e f = 0 := thresholdPair_frame_orthogonal u j l hu hv
  have hprod := (integrable_gaussianPairSectionMap_iff e f he hf F hF).mpr hFi
  let V : Set (Vector (n + 1)) := {z | ∀ k, k ≠ j → k ≠ l →
    faceDot (u k) (gaussianPairBase u b j l z) < b k}
  have hV : MeasurableSet V := by
    unfold V
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
      measurableSet_lt ((measurable_thresholdDot _).comp (measurable_gaussianPairBase u b j l)) measurable_const)))
  let C := (27 / 2048 : ℝ) * Real.exp (-(9 : ℝ) / 32)
  let d := C * ((1 - faceDot (u j) (u l)) * |b j + b l| /
      Real.sqrt (1 - faceDot (u j) (u l) ^ 2)) * gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c
  have hpoint : ∀ᵐ z ∂standardGaussian (n + 1),
      V.indicator (fun _ => d) z ≤ ∫ st, F (gaussianPairSectionPoint e f st.1 st.2 z)
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
    filter_upwards [hprod.prod_left_ae] with z hz
    by_cases hzV : z ∈ V
    · rw [Set.indicator_of_mem hzV]
      have hl := gaussianPairBase_frame_levels u b j l hu hv hp hm z
      have hbnd := thresholdSector_fiber_lower u j l hu hv hp hm a c (gaussianPairBase u b j l z) hl.1 hl.2
      have ha := thresholdPair_sector_coefficient_le_radius u b j l hu hv hp hm
        (gaussianPairBase u b j l z) hl.1 hl.2
      have hcoef : d ≤ C * Real.arccos (faceDot (u j) (u l)) *
          thresholdProjectionRadius u (gaussianPairBase u b j l z) *
          gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c := by
        have hc0 : 0 ≤ C * gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 c := by
          dsimp only [C]
          exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
            (gaussianPDFReal_nonneg _ _ _)) (gaussianPDFReal_nonneg _ _ _)
        have hh := mul_le_mul_of_nonneg_right ha hc0
        convert hh using 1 <;> dsimp only [d] <;> ring
      apply hcoef.trans (hbnd.trans ?_)
      apply normalPair_integral_dominates_translated_fiber
        (fun st => F (gaussianPairSectionPoint e f st.1 st.2 z))
        (fun st => thresholdProjectionRadius u (gaussianPairBase u b j l z + st.1 • e + st.2 • f) ^ 3)
        hz (fun st => hF0 _) (a, c)
        (planeSector (Real.arccos (faceDot (u j) (u l)))
          (1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l z))))
        (isOpen_planeSector _ _).measurableSet
      intro st hst
      have hmem : gaussianPairSectionPoint e f (a + st.1) (c + st.2) z ∈ gaussianPairSectorEvent u b j l :=
        (gaussianPairSectorEvent_section u b j l hu hv hp hm z st.1 st.2).mpr ⟨hzV, hst⟩
      dsimp only [Prod.fst_add, Prod.snd_add, F]
      rw [Set.indicator_of_mem hmem, gaussianPairSectionPoint_add_parameters e f hef]
      rfl
    · rw [Set.indicator_of_not_mem hzV]
      exact integral_nonneg (fun st => hF0 _)
  have hh := integral_mono_ae ((integrable_const d).indicator hV) hprod.integral_prod_right hpoint
  rw [integral_indicator_const _ hV, smul_eq_mul, mul_comm] at hh
  have hmass : d * (standardGaussian (n + 1)).real V ≤
      ∫ g, F g ∂standardGaussian (n + 1) := by
    apply hh.trans_eq
    rw [← integral_prod_symm _ hprod]
    exact integral_gaussianPairSectionMap e f he hf F hF
  rw [gaussianThresholdMixed_eq_pairBase u b j l hjl hu hv hi]
  convert hmass using 1 <;> dsimp only [d, C, a, c, V] <;> ring

end
end RectangleCLT.Companion.SplitV4.Printed
