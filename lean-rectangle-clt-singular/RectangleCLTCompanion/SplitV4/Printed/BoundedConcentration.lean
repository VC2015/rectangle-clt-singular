import RectangleCLTCompanion.SplitV4.Printed.CubeBoundary
import RectangleCLTCompanion.SplitV4.BoundedIntrinsicConcentration

/-! The bounded half of the printed Lemma 1 route, with the conditional
cube estimate supplied by the new perturbation/unique-gradient proof of C.1.
All copy-selection laws, contraction, symmetrization, variance Markov and
Fubini steps are the same already checked substantive arguments. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- C.1 applied to a fixed translated paired-copy array, retaining the
actual expected supremum norm of its signed sum. -/
theorem cube_translated_boundary_printed {p n : ℕ} [NeZero p]
    (Y : Fin n → Vector p) (a r : Vector p) (s η v : ℝ)
    (hs : 0 ≤ s) (hv : 0 < v) (hY : ∀ i, ‖Y i‖ ≤ η)
    (hrow : ∀ j, v / 4 ≤ ∑ i, (Y i j) ^ 2) :
    Kane.avg (fun x => vectorBoundaryIndicator a s (r + cubeSignedVectorSum Y x)) ≤
      ((8 * s + 32 * η) / v) * Kane.avg (fun x => ‖cubeSignedVectorSum Y x‖) := by
  have hc : ∀ j i, |Y i j| ≤ η := fun j i => (norm_le_pi_norm (Y i) j).trans (hY i)
  have hbound := intrinsic_cube_boundary_printed_avg (fun j i => Y i j) (fun j => a j - r j)
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
theorem bounded_intrinsic_boundary_fixed_shift_printed {Ω : Type*} [MeasurableSpace Ω]
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
      apply cube_translated_boundary_printed _ a _ s η v hs hv hz
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

end
end RectangleCLT.Companion.SplitV4.Printed
