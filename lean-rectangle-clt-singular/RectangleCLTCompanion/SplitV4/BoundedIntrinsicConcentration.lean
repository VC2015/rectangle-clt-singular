import RectangleCLTCompanion.SplitV4.IntrinsicVariance
import Mathlib.Topology.Order.Lattice
import RectangleCLT.BoundedMaximumScaling

/-! The intrinsic bounded-sum concentration assertion in Lemma 1. Face
coordinates may be arbitrary fixed projections of the original vectors;
their dependence is retained throughout. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def vectorFaceMaximum {p : ℕ} [NeZero p] (a y : Vector p) : ℝ :=
  finiteFamilyMaximum (fun j => y j - a j)

theorem continuous_vectorFaceMaximum {p : ℕ} [NeZero p] (a : Vector p) :
    Continuous (vectorFaceMaximum a) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun j _ => (continuous_apply j).sub continuous_const)

def vectorBoundaryIndicator {p : ℕ} [NeZero p] (a : Vector p) (s : ℝ) (y : Vector p) : ℝ :=
  if -s ≤ vectorFaceMaximum a y ∧ vectorFaceMaximum a y ≤ s then 1 else 0

theorem measurable_vectorBoundaryIndicator {p : ℕ} [NeZero p] (a : Vector p) (s : ℝ) :
    Measurable (vectorBoundaryIndicator a s) := by
  have hm := (continuous_vectorFaceMaximum a).measurable
  exact Measurable.ite ((measurableSet_le measurable_const hm).inter
    (measurableSet_le hm measurable_const)) measurable_const measurable_const

theorem vectorBoundaryIndicator_nonneg {p : ℕ} [NeZero p] (a : Vector p) (s : ℝ) (y : Vector p) :
    0 ≤ vectorBoundaryIndicator a s y := by unfold vectorBoundaryIndicator; split_ifs <;> norm_num

theorem vectorBoundaryIndicator_le_one {p : ℕ} [NeZero p] (a : Vector p) (s : ℝ) (y : Vector p) :
    vectorBoundaryIndicator a s y ≤ 1 := by unfold vectorBoundaryIndicator; split_ifs <;> norm_num

theorem integrable_vectorBoundaryIndicator {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} [NeZero p] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (a : Vector p) (s : ℝ) :
    Integrable (fun ω => vectorBoundaryIndicator a s (W ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono' ((measurable_vectorBoundaryIndicator a s).comp hW).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    change ‖vectorBoundaryIndicator a s (W ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (vectorBoundaryIndicator_nonneg a s _)]
    exact vectorBoundaryIndicator_le_one a s _)

theorem integral_vectorBoundaryIndicator_eq_real {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} [NeZero p] (μ : Measure Ω) (W : Ω → Vector p)
    (hW : Measurable W) (a : Vector p) (s : ℝ) :
    (∫ ω, vectorBoundaryIndicator a s (W ω) ∂μ) =
      μ.real {ω | -s ≤ vectorFaceMaximum a (W ω) ∧ vectorFaceMaximum a (W ω) ≤ s} := by
  have hmax := (continuous_vectorFaceMaximum a).measurable.comp hW
  have hm : MeasurableSet {ω | -s ≤ vectorFaceMaximum a (W ω) ∧ vectorFaceMaximum a (W ω) ≤ s} :=
    (measurableSet_le measurable_const hmax).inter (measurableSet_le hmax measurable_const)
  simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, vectorBoundaryIndicator] using
    integral_indicator_one (μ := μ) hm

theorem vectorFaceMaximum_signed_eq_affine {p n : ℕ} [NeZero p]
    (Y : Fin n → Vector p) (a r : Vector p) (x : Kane.Cube n) :
    vectorFaceMaximum a (r + cubeSignedVectorSum Y x) =
      affineCubeMaximum (fun j i => Y i j) (fun j => a j - r j) x := by
  unfold vectorFaceMaximum finiteFamilyMaximum affineCubeMaximum
  congr 1
  funext j
  simp only [Pi.add_apply, cubeSignedVectorSum, cubeLinear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have he : (∑ i, cubeSign x i * Y i j) = ∑ i, Y i j * cubeSign x i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he]
  ring

/-- C.1 applied to a fixed translated paired-copy array, retaining the
actual expected supremum norm of its signed sum. -/
theorem cube_translated_boundary_le_intrinsic {p n : ℕ} [NeZero p]
    (Y : Fin n → Vector p) (a r : Vector p) (s η v : ℝ)
    (hs : 0 ≤ s) (hv : 0 < v) (hY : ∀ i, ‖Y i‖ ≤ η)
    (hrow : ∀ j, v / 4 ≤ ∑ i, (Y i j) ^ 2) :
    Kane.avg (fun x => vectorBoundaryIndicator a s (r + cubeSignedVectorSum Y x)) ≤
      ((8 * s + 32 * η) / v) * Kane.avg (fun x => ‖cubeSignedVectorSum Y x‖) := by
  have hc : ∀ j i, |Y i j| ≤ η := fun j i => (norm_le_pi_norm (Y i) j).trans (hY i)
  have hbound := intrinsic_cube_boundary_avg (fun j i => Y i j) (fun j => a j - r j)
    (-s) (2 * s) η (v / 4) (by linarith) (by linarith) hc hrow
  have hI : (fun x => vectorBoundaryIndicator a s (r + cubeSignedVectorSum Y x)) =
      cubeBoundaryIndicator (fun j i => Y i j) (fun j => a j - r j) (-s) (2 * s) := by
    funext x
    simp only [vectorBoundaryIndicator, cubeBoundaryIndicator, vectorFaceMaximum_signed_eq_affine]
    rw [show -s + 2 * s = s by ring]
  rw [hI]
  have hM : intrinsicCubeMean (fun j i => Y i j) ≤ Kane.avg (fun x => ‖cubeSignedVectorSum Y x‖) := by
    apply Kane.avg_mono
    intro x
    apply (positiveLinearMaximum_le_absolute _ x).trans
    rw [absoluteLinearMaximum_eq_norm]
    apply le_of_eq
    congr 1
    funext j
    simp only [cubeSignedVectorSum, cubeLinear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hη : 0 ≤ η := by
    by_cases hn : n = 0
    · subst n
      have hz := hrow (0 : Fin p)
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hz
      linarith
    · exact (norm_nonneg (Y ⟨0, Nat.pos_of_ne_zero hn⟩)).trans (hY _)
  calc
    _ ≤ ((2 * s + 8 * η) / (v / 4)) * intrinsicCubeMean (fun j i => Y i j) := hbound
    _ ≤ ((2 * s + 8 * η) / (v / 4)) * Kane.avg (fun x => ‖cubeSignedVectorSum Y x‖) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = _ := by
      have he : (2 * s + 8 * η) / (v / 4) = (8 * s + 32 * η) / v := by
        field_simp
        ring
      rw [he]

/-- The complete bounded intrinsic estimate, for an arbitrary deterministic
translation of the actual independent centered vector sum. -/
theorem bounded_intrinsic_boundary_fixed_shift {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (a r : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | -s ≤ vectorFaceMaximum a ((∑ i, ξ i ω) + r) ∧
      vectorFaceMaximum a ((∑ i, ξ i ω) + r) ≤ s} ≤
      ((8 * s + 64 * η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ := by
  have hη : 0 ≤ η := h.delta_nonneg
  let ν := μ.prod μ
  let Y : Fin n → (Ω × Ω) → Vector p := fun i z => cubePairDifference ξ z i
  have hY (i : Fin n) : Measurable (Y i) := measurable_cubePairDifference ξ h.measurable i
  have hYi (i : Fin n) : Integrable (Y i) ν :=
    (integrable_const η).mono' (hY i).aestronglyMeasurable (cubePairDifference_bound μ ξ h i)
  have hsign := (integrable_cubeSignedVectorSum ν Y hY hYi).norm
  have hsum : Measurable (fun ω => ∑ i, ξ i ω) := Finset.measurable_sum _ (fun i _ => h.measurable i)
  have hF : Measurable (fun y : Vector p => vectorBoundaryIndicator a s (y + r)) :=
    (measurable_vectorBoundaryIndicator a s).comp (measurable_id.add_const r)
  have hFi := integrable_vectorBoundaryIndicator μ (fun ω => (∑ i, ξ i ω) + r)
    (hsum.add_const r) a s
  obtain ⟨hcopy, heq⟩ := uniformCubeSelectedSum_test_transport μ ξ h.measurable h.independent
    (fun y => vectorBoundaryIndicator a s (y + r)) hF hFi
  let bad : Set (Ω × Ω) := {z | ¬∀ j, v / 4 ≤ cubeConditionalRowSquares ξ z j}
  have hbadmeas : MeasurableSet bad := by
    apply MeasurableSet.compl
    change MeasurableSet {z | ∀ j, v / 4 ≤ cubeConditionalRowSquares ξ z j}
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le measurable_const
      ((measurable_pi_apply j).comp (measurable_cubeConditionalRowSquares ξ h.measurable)))
  have hbadint : Integrable (bad.indicator (fun _ => (1 : ℝ))) ν :=
    (integrable_const _).indicator hbadmeas
  have hbadvalue : (∫ z, bad.indicator (fun _ => (1 : ℝ)) z ∂ν) = ν.real bad :=
    integral_indicator_one hbadmeas
  let C : ℝ := (8 * s + 32 * η) / v
  have hC : 0 ≤ C := by dsimp [C]; exact div_nonneg (by linarith [h.delta_nonneg]) hv.le
  have hconditional : ∀ᵐ z ∂ν,
      (∫ x, vectorBoundaryIndicator a s ((∑ i, randomCubeSelectedArray ξ (z, x) i) + r)
        ∂cubeUniformLaw n) ≤
        C * (∫ x, ‖cubeSignedVectorSum (fun i => Y i z) x‖ ∂cubeUniformLaw n) +
          bad.indicator (fun _ => (1 : ℝ)) z := by
    have hall : ∀ᵐ z ∂ν, ∀ i, ‖Y i z‖ ≤ η :=
      ae_all_iff.mpr (cubePairDifference_bound μ ξ h)
    filter_upwards [hall] with z hz
    rw [integral_cubeUniformLaw_eq_avg]
    have hpoint (x : Kane.Cube n) :
        vectorBoundaryIndicator a s ((∑ i, randomCubeSelectedArray ξ (z, x) i) + r) =
          vectorBoundaryIndicator a s ((∑ i, cubePairMidpoint ξ z i) + r + cubeSignedVectorSum (fun i => Y i z) x) := by
      rw [show randomCubeSelectedArray ξ (z, x) = selectedArray ξ x z from rfl,
        selectedSum_eq_midpoint_add_signed_difference]
      congr 1
      dsimp only [Y, cubeSignedVectorSum]
      abel
    rw [show (fun x => vectorBoundaryIndicator a s ((∑ i, randomCubeSelectedArray ξ (z, x) i) + r)) =
      (fun x => vectorBoundaryIndicator a s ((∑ i, cubePairMidpoint ξ z i) + r + cubeSignedVectorSum (fun i => Y i z) x)) from funext hpoint]
    by_cases hgood : ∀ j, v / 4 ≤ cubeConditionalRowSquares ξ z j
    · have hn : z ∉ bad := not_not.mpr hgood
      rw [Set.indicator_of_not_mem hn, add_zero, integral_cubeUniformLaw_eq_avg]
      apply cube_translated_boundary_le_intrinsic _ a _ s η v hs hv hz
      intro j
      simpa only [cubeConditionalRowSquares, coordinateSquare, Finset.sum_apply] using hgood j
    · have hm : z ∈ bad := hgood
      rw [Set.indicator_of_mem hm]
      have h₁ : Kane.avg (fun x => vectorBoundaryIndicator a s
          ((∑ i, cubePairMidpoint ξ z i) + r + cubeSignedVectorSum (fun i => Y i z) x)) ≤ 1 := by
        calc
          _ ≤ Kane.avg (fun _ : Kane.Cube n => (1 : ℝ)) :=
            Kane.avg_mono (fun x => vectorBoundaryIndicator_le_one a s _)
          _ = 1 := Kane.avg_const _
      apply h₁.trans
      have hnn : 0 ≤ ∫ x, ‖cubeSignedVectorSum (fun i => Y i z) x‖ ∂cubeUniformLaw n :=
        integral_nonneg (fun x => norm_nonneg _)
      exact le_add_of_nonneg_left (mul_nonneg hC hnn)
  have hprob : μ.real {ω | -s ≤ vectorFaceMaximum a ((∑ i, ξ i ω) + r) ∧
      vectorFaceMaximum a ((∑ i, ξ i ω) + r) ≤ s} ≤
      C * cubePairIntrinsicBudget μ ξ + ν.real bad := by
    rw [← integral_vectorBoundaryIndicator_eq_real μ _ (hsum.add_const r) a s, ← heq,
      integral_prod _ hcopy]
    apply le_trans (integral_mono_ae hcopy.integral_prod_left
      ((hsign.integral_prod_left.const_mul C).add hbadint) hconditional)
    apply le_of_eq
    have hadd : (∫ z, C * (∫ x, ‖cubeSignedVectorSum (fun i => Y i z) x‖ ∂cubeUniformLaw n) +
        bad.indicator (fun _ => (1 : ℝ)) z ∂ν) =
        (∫ z, C * (∫ x, ‖cubeSignedVectorSum (fun i => Y i z) x‖ ∂cubeUniformLaw n) ∂ν) +
          ∫ z, bad.indicator (fun _ => (1 : ℝ)) z ∂ν :=
      integral_add (hsign.integral_prod_left.const_mul C) hbadint
    change (∫ z, C * (∫ x, ‖cubeSignedVectorSum (fun i => Y i z) x‖ ∂cubeUniformLaw n) +
      bad.indicator (fun _ => (1 : ℝ)) z ∂ν) = _
    rw [hadd, integral_const_mul,
      ← integral_prod _ hsign, hbadvalue]
    rfl
  have hb := cube_pair_bad_variance_probability_le μ ξ h hv hdiag
  have hξi (i : Fin n) : Integrable (ξ i) μ :=
    (integrable_const η).mono' (h.measurable i).aestronglyMeasurable (h.bounded i)
  have hB := cubePairIntrinsicBudget_le_norm_sum μ ξ h.measurable h.independent hξi
  calc
    _ ≤ C * cubePairIntrinsicBudget μ ξ + ν.real bad := hprob
    _ ≤ C * cubePairIntrinsicBudget μ ξ + (32 * η / v) * cubePairIntrinsicBudget μ ξ :=
      add_le_add_left hb _
    _ = ((8 * s + 64 * η) / v) * cubePairIntrinsicBudget μ ξ := by dsimp [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)

/-- Arbitrary independent noise may be integrated without any moment or
coordinate independence assumption on that noise. -/
theorem bounded_intrinsic_boundary_product_shift
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    (μ.prod ν).real {z | -s ≤ vectorFaceMaximum a ((∑ i, ξ i z.1) + R z.2) ∧
      vectorFaceMaximum a ((∑ i, ξ i z.1) + R z.2) ≤ s} ≤
      ((8 * s + 64 * η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ := by
  have hsum : Measurable (fun ω => ∑ i, ξ i ω) := Finset.measurable_sum _ (fun i _ => h.measurable i)
  have hW : Measurable (fun z : Ω × Γ => (∑ i, ξ i z.1) + R z.2) :=
    (hsum.comp measurable_fst).add (hR.comp measurable_snd)
  have hI := integrable_vectorBoundaryIndicator (μ.prod ν) _ hW a s
  rw [← integral_vectorBoundaryIndicator_eq_real (μ.prod ν) _ hW a s, integral_prod_symm _ hI]
  calc
    _ ≤ ∫ _γ : Γ, ((8 * s + 64 * η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ ∂ν := by
      apply integral_mono hI.integral_prod_right (integrable_const _)
      intro γ
      change (∫ ω, vectorBoundaryIndicator a s ((∑ i, ξ i ω) + R γ) ∂μ) ≤ _
      rw [integral_vectorBoundaryIndicator_eq_real μ _ (hsum.add_const (R γ)) a s]
      exact bounded_intrinsic_boundary_fixed_shift μ ξ h hv hdiag a (R γ) hs
    _ = _ := by rw [integral_const]; simp only [measureReal_univ_eq_one, one_smul]

def projectedFacePolyhedron {p : ℕ} (a : Vector p) (s : ℝ) : Set (Vector p) :=
  {y | ∀ j, y j ≤ a j + s}

def projectedFaceLayer {p : ℕ} (a : Vector p) (s : ℝ) : Set (Vector p) :=
  projectedFacePolyhedron a s \ projectedFacePolyhedron a (-s)

theorem vectorFaceMaximum_le_iff {p : ℕ} [NeZero p] (a y : Vector p) (s : ℝ) :
    vectorFaceMaximum a y ≤ s ↔ ∀ j, y j ≤ a j + s := by
  constructor
  · intro hs j
    have hj := le_finiteFamilyMaximum (fun j => y j - a j) j
    change y j - a j ≤ vectorFaceMaximum a y at hj
    linarith
  · intro hs
    obtain ⟨j, hj⟩ := finiteFamilyMaximum_attains (fun j => y j - a j)
    change finiteFamilyMaximum _ ≤ s
    rw [hj]
    linarith [hs j]

theorem projectedFaceLayer_subset_closed_window {p : ℕ} [NeZero p] (a : Vector p) (s : ℝ) :
    projectedFaceLayer a s ⊆ {y | -s ≤ vectorFaceMaximum a y ∧ vectorFaceMaximum a y ≤ s} := by
  intro y hy
  have hp : vectorFaceMaximum a y ≤ s := (vectorFaceMaximum_le_iff a y s).mpr hy.1
  have hm : ¬vectorFaceMaximum a y ≤ -s := by
    intro hm
    exact hy.2 ((vectorFaceMaximum_le_iff a y (-s)).mp hm)
  exact ⟨(lt_of_not_ge hm).le, hp⟩

/-- The actual polyhedron-layer event of Lemma 1, expressed in the face
projection coordinates. The intrinsic constant is explicitly `64`. -/
theorem bounded_intrinsic_layer_product_shift
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    (μ.prod ν).real {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} ≤
      64 * ((s + η) / v * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ) := by
  have hη : 0 ≤ η := h.delta_nonneg
  have hI : 0 ≤ ∫ ω, ‖∑ i, ξ i ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  calc
    _ ≤ (μ.prod ν).real {z | -s ≤ vectorFaceMaximum a ((∑ i, ξ i z.1) + R z.2) ∧
      vectorFaceMaximum a ((∑ i, ξ i z.1) + R z.2) ≤ s} :=
      measureReal_mono (fun z hz => projectedFaceLayer_subset_closed_window a s hz)
    _ ≤ _ := bounded_intrinsic_boundary_product_shift μ ξ h hv hdiag ν R hR a hs
    _ ≤ _ := by
      have hc : (8 * s + 64 * η) / v ≤ 64 * ((s + η) / v) := by
        calc
          _ ≤ (64 * (s + η)) / v := div_le_div_of_nonneg_right (by linarith) hv.le
          _ = _ := by ring
      apply (mul_le_mul_of_nonneg_right hc hI).trans_eq
      ring

theorem measurableSet_projectedFaceLayer {p : ℕ} (a : Vector p) (s : ℝ) :
    MeasurableSet (projectedFaceLayer a s) := by
  apply MeasurableSet.diff
  all_goals
    unfold projectedFacePolyhedron
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le (measurable_pi_apply j) measurable_const)

/-- The product construction is exactly the law of an actual independent
shift on the original probability space. Independence of the shift from
the sum suffices. -/
theorem independent_sum_shift_identDistrib {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (R : Ω → Vector p) (hR : Measurable R)
    (hind : IndepFun (fun ω => ∑ i, ξ i ω) R μ) :
    IdentDistrib (fun ω => (∑ i, ξ i ω) + R ω)
      (fun z : Ω × Ω => (∑ i, ξ i z.1) + R z.2) μ (μ.prod μ) := by
  have hsum : Measurable (fun ω => ∑ i, ξ i ω) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hpair : IdentDistrib (fun ω => ((∑ i, ξ i ω), R ω))
      (fun z : Ω × Ω => ((∑ i, ξ i z.1), R z.2)) μ (μ.prod μ) := by
    refine ⟨(hsum.prodMk hR).aemeasurable,
      ((hsum.comp measurable_fst).prodMk (hR.comp measurable_snd)).aemeasurable, ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map hsum.aemeasurable hR.aemeasurable).mp hind]
    exact Measure.map_prod_map μ μ hsum hR
  exact hpair.comp (measurable_fst.add measurable_snd)

/-- Actual same-space version with only the stated independent shift. -/
theorem bounded_intrinsic_layer_independent_shift {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (R : Ω → Vector p) (hR : Measurable R) (hRind : IndepFun (sumVector ξ) R μ)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s} ≤
      64 * ((s + η) / v * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ) := by
  have hid := independent_sum_shift_identDistrib μ ξ h.measurable R hR hRind
  have hset := measurableSet_projectedFaceLayer a s
  have hprob : μ {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s} =
      (μ.prod μ) {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} := by
    simpa only [Measure.map_apply_of_aemeasurable hid.aemeasurable_fst hset,
      Measure.map_apply_of_aemeasurable hid.aemeasurable_snd hset] using congrArg (fun ν => ν (projectedFaceLayer a s)) hid.map_eq
  change (μ {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s}).toReal ≤ _
  rw [hprob]
  exact bounded_intrinsic_layer_product_shift μ ξ h hv hdiag μ R hR a hs

/-- The logarithmic consequence uses the actual bounded-sum maximum
moment, splitting only according to the dimensionless envelope size. -/
theorem bounded_intrinsic_layer_product_shift_log
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    (μ.prod ν).real {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} ≤
      256 * ((s + η) * Real.sqrt (dimensionLog p / v)) := by
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hη : 0 ≤ η := h.delta_nonneg
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  let q := Real.sqrt (dimensionLog p / v)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hsη : 0 ≤ s + η := add_nonneg hs hη
  have hqq : q ^ 2 = dimensionLog p / v := Real.sq_sqrt (div_nonneg hL hv.le)
  have hLq : dimensionLog p = v * q ^ 2 := by
    apply (eq_div_iff (ne_of_gt hv)).mp at hqq
    nlinarith [hqq]
  have hsq : Real.sqrt v * Real.sqrt (dimensionLog p) = v * q := by
    have hsq₀ : Real.sqrt (dimensionLog p) = Real.sqrt v * q := by
      dsimp [q]
      rw [Real.sqrt_div hL]
      field_simp
    rw [hsq₀]
    nlinarith [Real.sq_sqrt hv.le]
  by_cases hsmall : η * q ≤ 1
  · have hnorm := h.integral_norm_sum_le_of_variance hp hv hdiag
    change (∫ ω, ‖∑ i, ξ i ω‖ ∂μ) ≤ _ at hnorm
    have hbudget : (∫ ω, ‖∑ i, ξ i ω‖ ∂μ) ≤ 4 * v * q := by
      rw [show 2 * Real.sqrt v * Real.sqrt (dimensionLog p) =
        2 * (Real.sqrt v * Real.sqrt (dimensionLog p)) by ring, hsq, hLq] at hnorm
      have hm := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hv.le hq)
      nlinarith
    have hbase := bounded_intrinsic_layer_product_shift μ ξ h hv hdiag ν R hR a hs
    apply hbase.trans
    calc
      _ ≤ 64 * ((s + η) / v * (4 * v * q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbudget (div_nonneg hsη hv.le)) (by norm_num)
      _ = _ := by dsimp [q]; field_simp [ne_of_gt hv]; ring
  · have hlarge : 1 < (s + η) * q := by nlinarith [lt_of_not_ge hsmall]
    exact (measureReal_le_one (μ := μ.prod ν)).trans (by dsimp [q] at *; nlinarith)

/-- The full bounded assertion of Lemma 1 in face coordinates. The
intrinsic expected maximum and the logarithmic alternative are both
retained, with a single explicit absolute constant. -/
theorem bounded_intrinsic_layer_product_shift_min
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    (μ.prod ν).real {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} ≤
      256 * min 1 (min (((s + η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ)
        ((s + η) * Real.sqrt (dimensionLog p / v))) := by
  let P := (μ.prod ν).real {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s}
  have hη := h.delta_nonneg
  have hI : 0 ≤ ((s + η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ :=
    mul_nonneg (div_nonneg (add_nonneg hs hη) hv.le) (integral_nonneg (fun _ => norm_nonneg _))
  have h₁ : P ≤ 1 := measureReal_le_one
  have h₂ := bounded_intrinsic_layer_product_shift μ ξ h hv hdiag ν R hR a hs
  have h₃ := bounded_intrinsic_layer_product_shift_log μ ξ h hv hdiag ν R hR a hs
  have hd : P / 256 ≤ min 1 (min (((s + η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ)
      ((s + η) * Real.sqrt (dimensionLog p / v))) := by
    apply le_min
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
      linarith
    · apply le_min
      · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
        change P ≤ _ at h₂
        linarith
      · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mpr
        simpa only [mul_comm] using h₃
  have hf := (div_le_iff₀ (by norm_num : (0 : ℝ) < 256)).mp hd
  simpa only [mul_comm] using hf

/-- The full bounded assertion on the original probability space, with
the stated independent shift and both intrinsic/logarithmic alternatives. -/
theorem bounded_intrinsic_layer_independent_shift_min {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (R : Ω → Vector p) (hR : Measurable R) (hRind : IndepFun (sumVector ξ) R μ)
    (a : Vector p) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s} ≤
      256 * min 1 (min (((s + η) / v) * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ)
        ((s + η) * Real.sqrt (dimensionLog p / v))) := by
  have hid := independent_sum_shift_identDistrib μ ξ h.measurable R hR hRind
  have hset := measurableSet_projectedFaceLayer a s
  have hprob : μ {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s} =
      (μ.prod μ) {z | ((∑ i, ξ i z.1) + R z.2) ∈ projectedFaceLayer a s} := by
    simpa only [Measure.map_apply_of_aemeasurable hid.aemeasurable_fst hset,
      Measure.map_apply_of_aemeasurable hid.aemeasurable_snd hset] using
      congrArg (fun ν => ν (projectedFaceLayer a s)) hid.map_eq
  change (μ {ω | ((∑ i, ξ i ω) + R ω) ∈ projectedFaceLayer a s}).toReal ≤ _
  rw [hprob]
  exact bounded_intrinsic_layer_product_shift_min μ ξ h hv hdiag μ R hR a hs

end

end RectangleCLT.Companion.SplitV4
