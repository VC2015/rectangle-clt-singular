import RectangleCLTCompanion.Statement
import RectangleCLT.IndependentCovariance
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Geometry of the standardized face map

These are deterministic inputs to Corollary 3 and Appendix D of split-V4.
They do not assert the probabilistic transfer theorem: its relative-moment,
polynomial, and Orlicz contracts require further proofs.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- The polyhedron with the specified closed face inequalities. -/
def facePolyhedron {p m : ℕ} (ν : Matrix (Fin m) (Fin p) ℝ)
    (a : Vector m) : Set (Vector p) :=
  {x | ∀ α, dotProduct (ν α) x ≤ a α}

/-- Division by the actual positive standard deviation of each face. -/
def standardizedFaceMap {p m : ℕ} (ν : Matrix (Fin m) (Fin p) ℝ)
    (σ : Vector m) : Matrix (Fin m) (Fin p) ℝ :=
  fun α j => ν α j / σ α

/-- The lower orthant is one of the full class of measurable rectangles. -/
def lowerOrthant {m : ℕ} (a : Vector m) : Rect m where
  interval := fun α => Set.Iic (a α)
  ordConnected := fun _ => Set.ordConnected_Iic
  measurable := fun _ => measurableSet_Iic

theorem mem_lowerOrthant {m : ℕ} (a x : Vector m) :
    x ∈ (lowerOrthant a).carrier ↔ ∀ α, x α ≤ a α := by
  change (∀ α, α ∈ (Set.univ : Set (Fin m)) → x α ≤ a α) ↔ _
  simp only [Set.mem_univ, true_implies]

theorem standardizedFaceMap_apply {p m : ℕ}
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (x : Vector p) (α : Fin m) :
    (standardizedFaceMap ν σ).mulVec x α = dotProduct (ν α) x / σ α := by
  simp only [standardizedFaceMap, Matrix.mulVec, dotProduct,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact event identity, without a covariance-rank hypothesis. -/
theorem mem_facePolyhedron_iff_standardized {p m : ℕ}
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ a : Vector m)
    (hσ : ∀ α, 0 < σ α) (x : Vector p) :
    x ∈ facePolyhedron ν a ↔
      (standardizedFaceMap ν σ).mulVec x ∈
        (lowerOrthant (fun α => a α / σ α)).carrier := by
  rw [mem_lowerOrthant]
  change (∀ α, dotProduct (ν α) x ≤ a α) ↔ _
  simp only [standardizedFaceMap_apply]
  exact forall_congr' fun α => (div_le_div_iff_of_pos_right (hσ α)).symm

theorem facePolyhedron_eq_preimage_standardized {p m : ℕ}
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ a : Vector m)
    (hσ : ∀ α, 0 < σ α) :
    facePolyhedron ν a = (standardizedFaceMap ν σ).mulVec ⁻¹'
      (lowerOrthant (fun α => a α / σ α)).carrier :=
  Set.ext (mem_facePolyhedron_iff_standardized ν σ a hσ)

/-- The standardized normal has the required row l1 bound. -/
theorem standardizedFaceMap_row_l1_le {p m : ℕ}
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J * σ α) (α : Fin m) :
    (∑ j, |standardizedFaceMap ν σ α j|) ≤ J := by
  simp only [standardizedFaceMap, abs_div, abs_of_pos (hσ α)]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  simpa only [div_eq_mul_inv] using (div_le_iff₀ (hσ α)).mpr (hν α)

theorem faceCovariance_diagonal {p m : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) (Sigma : Matrix (Fin p) (Fin p) ℝ) (α : Fin m) :
    (M * Sigma * M.transpose) α α = dotProduct (M α) (Sigma.mulVec (M α)) := by
  change dotProduct (Matrix.vecMul (M α) Sigma) (M α) = _
  exact (Matrix.dotProduct_mulVec (M α) Sigma (M α)).symm

/-- Standardization gives unit variances. The input is the actual face
variance identity, without requiring the full covariance to be invertible. -/
theorem standardizedFaceMap_covariance_unit_diagonal {p m : ℕ}
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m)
    (Sigma : Matrix (Fin p) (Fin p) ℝ) (hσ : ∀ α, 0 < σ α)
    (hvariance : ∀ α, dotProduct (ν α) (Sigma.mulVec (ν α)) = (σ α) ^ 2)
    (α : Fin m) :
    (standardizedFaceMap ν σ * Sigma * (standardizedFaceMap ν σ).transpose) α α = 1 := by
  rw [faceCovariance_diagonal]
  have hrow : standardizedFaceMap ν σ α = (σ α)⁻¹ • ν α := by
    ext j
    simp only [standardizedFaceMap, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hrow, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, hvariance]
  simp only [smul_eq_mul]
  field_simp [ne_of_gt (hσ α)]
  ring

/-- A row l1 bound controls each projection in the maximum norm. -/
theorem abs_mulVec_le_of_row_l1 {p m : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (x : Vector p) (α : Fin m) :
    |M.mulVec x α| ≤ J * ‖x‖ := by
  calc
    |M.mulVec x α| ≤ ∑ j, |M α j * x j| := by
      simpa only [Matrix.mulVec, dotProduct] using
        Finset.abs_sum_le_sum_abs (fun j : Fin p => M α j * x j) Finset.univ
    _ = ∑ j, |M α j| * |x j| := by simp only [abs_mul]
    _ ≤ ∑ j, |M α j| * ‖x‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
        (abs_nonneg _)
    _ = (∑ j, |M α j|) * ‖x‖ := (Finset.sum_mul ..).symm
    _ ≤ J * ‖x‖ := mul_le_mul_of_nonneg_right (hM α) (norm_nonneg _)

theorem norm_mulVec_le_of_row_l1 {p m : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (x : Vector p) :
    ‖M.mulVec x‖ ≤ J * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hJ (norm_nonneg x))).mpr
  intro α
  simpa only [Real.norm_eq_abs] using abs_mulVec_le_of_row_l1 M J hM x α

/-- The exact deterministic envelope substitution in Appendix D. -/
theorem standardizedFaceMap_envelope {p m : ℕ}
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J δ : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 0 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J * σ α)
    (x : Vector p) (hx : ‖x‖ ≤ δ) :
    ‖(standardizedFaceMap ν σ).mulVec x‖ ≤ J * δ :=
  (norm_mulVec_le_of_row_l1 _ J hJ
    (standardizedFaceMap_row_l1_le ν σ J hσ hν) x).trans
      (mul_le_mul_of_nonneg_left hx hJ)

/-- A fixed face map preserves vector independence, centering, genuine
integrability, and the amplified almost-sure envelope. -/
theorem boundedIndependent_projected
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) :
    BoundedIndependentHypotheses μ (fun i ω => M.mulVec (ξ i ω)) (J * δ) := by
  have hmeas : Measurable M.mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  refine ⟨fun i => hmeas.comp (h.measurable i),
    h.independent.comp (fun _ => M.mulVec) (fun _ => hmeas), ?_, ?_,
    mul_nonneg hJ h.delta_nonneg⟩
  · intro i α
    unfold Matrix.mulVec dotProduct
    rw [integral_finset_sum Finset.univ (fun j _ =>
      (show Integrable (fun ω => ξ i ω j) μ from by
        simpa only [pow_one] using
          integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 1).const_mul _)]
    simp only [integral_const_mul, h.centered, mul_zero, Finset.sum_const_zero]
  · intro i
    filter_upwards [h.bounded i] with ω hω
    exact (norm_mulVec_le_of_row_l1 M J hJ hM _).trans
      (mul_le_mul_of_nonneg_left hω hJ)

/-- The square projection estimate used for both relative-moment matrices.
Its proof permits repeated, zero, and arbitrarily dependent coordinates. -/
theorem mulVec_sq_le_weighted_coordinate_squares {p m : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (x : Vector p) (α : Fin m) :
    (M.mulVec x α) ^ 2 ≤ J * (∑ j, |M α j| * (x j) ^ 2) := by
  have hq : 0 ≤ ∑ j, |M α j| * (x j) ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have hd := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    (Finset.univ : Finset (Fin p))
    (r := fun j => M α j * x j)
    (f := fun j => |M α j|) (g := fun j => |M α j| * (x j) ^ 2)
    (fun j _ => abs_nonneg _) (fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun j _ => by rw [mul_pow, ← sq_abs (M α j)]; ring)
  exact hd.trans (mul_le_mul_of_nonneg_right (hM α) hq)

/-- Coordinate fourth moments amplify by at most the fourth power of the
row l1 bound, the deterministic input to the polynomial class substitution. -/
theorem mulVec_fourth_le_weighted_coordinate_fourths {p m : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (x : Vector p) (α : Fin m) :
    (M.mulVec x α) ^ 4 ≤ J ^ 3 * (∑ j, |M α j| * (x j) ^ 4) := by
  let q : ℝ := ∑ j, |M α j| * (x j) ^ 2
  let r : ℝ := ∑ j, |M α j| * (x j) ^ 4
  have hq : 0 ≤ q := Finset.sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hr : 0 ≤ r := Finset.sum_nonneg fun j _ =>
    mul_nonneg (abs_nonneg _) (by positivity)
  have h2 := mulVec_sq_le_weighted_coordinate_squares M J hM x α
  have hq2 : q ^ 2 ≤ J * r := by
    have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
      (Finset.univ : Finset (Fin p))
      (r := fun j => |M α j| * (x j) ^ 2)
      (f := fun j => |M α j|) (g := fun j => |M α j| * (x j) ^ 4)
      (fun j _ => abs_nonneg _)
      (fun j _ => mul_nonneg (abs_nonneg _) (by positivity))
      (fun j _ => by ring)
    exact hh.trans (mul_le_mul_of_nonneg_right (hM α) hr)
  calc
    (M.mulVec x α) ^ 4 = (M.mulVec x α) ^ 2 * (M.mulVec x α) ^ 2 := by ring
    _ ≤ (J * q) * (J * q) := mul_le_mul h2 h2 (sq_nonneg _) (mul_nonneg hJ hq)
    _ = J ^ 2 * q ^ 2 := by ring
    _ ≤ J ^ 2 * (J * r) := mul_le_mul_of_nonneg_left hq2 (sq_nonneg _)
    _ = J ^ 3 * r := by ring

end

end RectangleCLT.Companion.SplitV4
