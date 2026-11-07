import RectangleCLTCompanion.SplitV4.RelativeMoments
import RectangleCLTCompanion.SplitV4.PolyhedralGeometry
import RectangleCLTCompanion.SupportRows

/-!
The relative-moment substitutions in Appendix D, for an actual fixed
linear face map. Both fourth-moment matrices are transferred, with their
genuine integrability and the actual transformed covariance. This is a
matrix-moment prerequisite, not the full polyhedral CLT corollary.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

private theorem dot_projected {p m : ℕ} (M : Matrix (Fin m) (Fin p) ℝ)
    (u : Vector m) (x : Vector p) :
    dotProduct u (M.mulVec x) = dotProduct (M.transpose.mulVec u) x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

private theorem quadratic_smul' {p : ℕ} (a : ℝ)
    (A : Matrix (Fin p) (Fin p) ℝ) (u : Vector p) :
    matrixQuadratic (a • A) u = a * matrixQuadratic A u := by
  simp only [matrixQuadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem sum_interchange {n p : ℕ} (a : Fin p → ℝ)
    (f : Fin n → Fin p → ℝ) :
    (∑ i, ∑ j, a j * f i j) = ∑ j, a j * ∑ i, f i j := by
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

variable {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {δ : ℝ}

private theorem integrable_cubic_projection
    (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) (j : Fin p) (v : Vector p) :
    Integrable (fun ω => ξ i ω j * (dotProduct v (ξ i ω)) ^ 2) μ := by
  apply (integrable_observation_projection_sq h i v).bdd_mul'
    (((measurable_pi_apply j).comp (h.measurable i)).aestronglyMeasurable)
  simpa only [Real.norm_eq_abs] using h.abs_coordinate_le i j

private theorem integrable_fourth_projection
    (h : BoundedIndependentHypotheses μ ξ δ) (i : Fin n) (j : Fin p) (v : Vector p) :
    Integrable (fun ω => ξ i ω j ^ 2 * (dotProduct v (ξ i ω)) ^ 2) μ := by
  apply (integrable_observation_projection_sq h i v).bdd_mul' (c := δ ^ 2)
    ((((measurable_pi_apply j).comp (h.measurable i)).pow_const 2).aestronglyMeasurable)
  filter_upwards [ae_coordinate_sq_le h i j] with ω hω
  simpa only [Real.norm_eq_abs, Function.comp_apply, abs_sq] using hω

private theorem integral_projected_linear_weight
    (M : Matrix (Fin m) (Fin p) ℝ) (i : Fin n) (α : Fin m) (g : Ω → ℝ)
    (hint : ∀ j, Integrable (fun ω => ξ i ω j * g ω) μ) :
    (∫ ω, M.mulVec (ξ i ω) α * g ω ∂μ) =
      ∑ j, M α j * ∫ ω, ξ i ω j * g ω ∂μ := by
  have hp (ω : Ω) : M.mulVec (ξ i ω) α * g ω =
      ∑ j, M α j * (ξ i ω j * g ω) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  simp_rw [hp]
  rw [integral_finset_sum Finset.univ (fun j _ => (hint j).const_mul _)]
  simp only [integral_const_mul]

private theorem integral_projected_square_weight_le
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (i : Fin n) (α : Fin m)
    (g : Ω → ℝ) (hg : ∀ ω, 0 ≤ g ω)
    (hleft : Integrable (fun ω => (M.mulVec (ξ i ω) α) ^ 2 * g ω) μ)
    (hright : ∀ j, Integrable (fun ω => ξ i ω j ^ 2 * g ω) μ) :
    (∫ ω, (M.mulVec (ξ i ω) α) ^ 2 * g ω ∂μ) ≤
      ∑ j, (J * |M α j|) * ∫ ω, ξ i ω j ^ 2 * g ω ∂μ := by
  have hpoint (ω : Ω) : (M.mulVec (ξ i ω) α) ^ 2 * g ω ≤
      ∑ j, (J * |M α j|) * (ξ i ω j ^ 2 * g ω) := by
    have hh := mul_le_mul_of_nonneg_right
      (mulVec_sq_le_weighted_coordinate_squares M J hM (ξ i ω) α) (hg ω)
    convert hh using 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    _ ≤ ∫ ω, ∑ j, (J * |M α j|) * (ξ i ω j ^ 2 * g ω) ∂μ :=
      integral_mono hleft
        (integrable_finset_sum Finset.univ (fun j _ => (hright j).const_mul _)) hpoint
    _ = _ := by
      rw [integral_finset_sum Finset.univ (fun j _ => (hright j).const_mul _)]
      simp only [integral_const_mul]

/-- Directional covariance of the actual projected sum, proved from the
actual centered independent observations rather than assumed. -/
theorem projected_covariance_quadratic
    (h : BoundedIndependentHypotheses μ ξ δ)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (u : Vector m) :
    matrixQuadratic (covariance μ (sumVector (fun i ω => M.mulVec (ξ i ω)))) u =
      matrixQuadratic (covariance μ (sumVector ξ)) (M.transpose.mulVec u) := by
  rw [← sum_integral_observation_projection_sq (boundedIndependent_projected h M J hJ hM) u]
  simp_rw [dot_projected]
  exact sum_integral_observation_projection_sq h _

private theorem matrix_eq_of_symmetric_quadratic
    {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hq : ∀ u, matrixQuadratic A u = matrixQuadratic B u) : A = B := by
  have hd (j : Fin r) : A j j = B j j := by
    simpa only [localBasisVector_quadratic] using hq (localBasisVector j)
  ext j k
  have hp := hq (twoCoordinateVector j k 1 1)
  simp only [matrixQuadratic_twoCoordinateVector, one_pow, one_mul, mul_one] at hp
  have hAs : A k j = A j k := congrFun (congrFun hA j) k
  have hBs : B k j = B j k := congrFun (congrFun hB j) k
  linarith [hd j, hd k]

/-- Exact covariance congruence under the face map, including singular
covariance matrices and dependent coordinates within each summand. -/
theorem covariance_projected_sum
    (h : BoundedIndependentHypotheses μ ξ δ)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) :
    covariance μ (sumVector (fun i ω => M.mulVec (ξ i ω))) =
      M * covariance μ (sumVector ξ) * M.transpose := by
  refine matrix_eq_of_symmetric_quadratic _ _ (covariance_transpose _ _) ?_ ?_
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, covariance_transpose,
      Matrix.mul_assoc]
  · intro u
    rw [projected_covariance_quadratic h M J hJ hM, matrixQuadratic_congruence]

/-- Signed aggregation survives the face map: no absolute value is
inserted inside the summand sum defining the cubic matrix. -/
theorem projected_relativeThirdMatrix_quadratic
    (h : BoundedIndependentHypotheses μ ξ δ)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (α : Fin m) (u : Vector m) :
    matrixQuadratic (relativeThirdMatrix μ (fun i ω => M.mulVec (ξ i ω)) α) u =
      ∑ j, M α j * matrixQuadratic (relativeThirdMatrix μ ξ j) (M.transpose.mulVec u) := by
  rw [relativeThirdMatrix_quadratic (boundedIndependent_projected h M J hJ hM)]
  simp_rw [dot_projected]
  calc
    _ = ∑ i, ∑ j, M α j *
        ∫ ω, ξ i ω j * (dotProduct (M.transpose.mulVec u) (ξ i ω)) ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_projected_linear_weight M i α _
        (fun j => integrable_cubic_projection h i j (M.transpose.mulVec u))
    _ = _ := by
      rw [sum_interchange]
      simp_rw [relativeThirdMatrix_quadratic h]

/-- Same-copy fourth-moment contraction before applying any matrix bound. -/
theorem projected_relativeFourthMatrix_quadratic_le
    (h : BoundedIndependentHypotheses μ ξ δ)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (α : Fin m) (u : Vector m) :
    matrixQuadratic (relativeFourthMatrix μ (fun i ω => M.mulVec (ξ i ω)) α) u ≤
      ∑ j, (J * |M α j|) *
        matrixQuadratic (relativeFourthMatrix μ ξ j) (M.transpose.mulVec u) := by
  let hp := boundedIndependent_projected h M J hJ hM
  rw [relativeFourthMatrix_quadratic hp]
  simp_rw [dot_projected]
  calc
    _ ≤ ∑ i, ∑ j, (J * |M α j|) *
        ∫ ω, ξ i ω j ^ 2 * (dotProduct (M.transpose.mulVec u) (ξ i ω)) ^ 2 ∂μ := by
      apply Finset.sum_le_sum
      intro i _
      apply integral_projected_square_weight_le M J hM i α _ (fun _ => sq_nonneg _) _
        (fun j => integrable_fourth_projection h i j _)
      simpa only [dot_projected] using integrable_fourth_projection hp i α u
    _ = _ := by
      rw [sum_interchange]
      simp_rw [relativeFourthMatrix_quadratic h]

/-- Independent-copy fourth-moment contraction. Both expectations remain
actual genuine moments; the same-copy result is not substituted for this. -/
theorem projected_relativeFreshFourthMatrix_quadratic_le
    (h : BoundedIndependentHypotheses μ ξ δ)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (α : Fin m) (u : Vector m) :
    matrixQuadratic (relativeFreshFourthMatrix μ (fun i ω => M.mulVec (ξ i ω)) α) u ≤
      ∑ j, (J * |M α j|) *
        matrixQuadratic (relativeFreshFourthMatrix μ ξ j) (M.transpose.mulVec u) := by
  let hp := boundedIndependent_projected h M J hJ hM
  rw [relativeFreshFourthMatrix_quadratic hp]
  simp_rw [dot_projected]
  calc
    _ ≤ ∑ i, ∑ j, (J * |M α j|) *
        ((∫ ω, ξ i ω j ^ 2 ∂μ) *
          ∫ ω, (dotProduct (M.transpose.mulVec u) (ξ i ω)) ^ 2 ∂μ) := by
      apply Finset.sum_le_sum
      intro i _
      have hleft : Integrable (fun ω => (M.mulVec (ξ i ω) α) ^ 2) μ := by
        simpa only [pow_two] using hp.integrable_coordinate_pair i α α
      have hright (j : Fin p) : Integrable (fun ω => ξ i ω j ^ 2) μ := by
        simpa only [pow_two] using h.integrable_coordinate_pair i j j
      have hb := integral_projected_square_weight_le M J hM i α (fun _ => 1)
        (fun _ => zero_le_one) (by simpa only [mul_one] using hleft)
        (fun j => by simpa only [mul_one] using hright j)
      simp only [mul_one] at hb
      have hnonneg : 0 ≤ ∫ ω, (dotProduct (M.transpose.mulVec u) (ξ i ω)) ^ 2 ∂μ :=
        integral_nonneg (fun ω => sq_nonneg (dotProduct (M.transpose.mulVec u) (ξ i ω)))
      have hh := mul_le_mul_of_nonneg_right hb hnonneg
      convert hh using 1
      simp only [Finset.sum_mul, mul_assoc]
    _ = _ := by
      rw [sum_interchange]
      simp_rw [relativeFreshFourthMatrix_quadratic h]

/-- All actual relative-moment contracts transfer with the exact Appendix D
substitutions s3->J*s3 and s4->J^2*s4. The envelope substitution is proved
separately by `boundedIndependent_projected`. -/
theorem relativeMomentBounds_projected
    (h : BoundedIndependentHypotheses μ ξ δ) {s₃ s₄ : ℝ}
    (hr : RelativeMomentBounds μ ξ s₃ s₄)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) :
    RelativeMomentBounds μ (fun i ω => M.mulVec (ξ i ω)) (J * s₃) (J ^ 2 * s₄) := by
  let hp := boundedIndependent_projected h M J hJ hM
  have hcovnonneg (v : Vector p) : 0 ≤ matrixQuadratic (covariance μ (sumVector ξ)) v := by
    rw [← sum_integral_observation_projection_sq h]
    exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
  have hthird (α : Fin m) (u : Vector m) :
      |matrixQuadratic (relativeThirdMatrix μ (fun i ω => M.mulVec (ξ i ω)) α) u| ≤
        (J * s₃) * matrixQuadratic
          (covariance μ (sumVector (fun i ω => M.mulVec (ξ i ω)))) u := by
    rw [projected_relativeThirdMatrix_quadratic h M J hJ hM,
      projected_covariance_quadratic h M J hJ hM]
    have hb (j : Fin p) :
        |matrixQuadratic (relativeThirdMatrix μ ξ j) (M.transpose.mulVec u)| ≤
          s₃ * matrixQuadratic (covariance μ (sumVector ξ)) (M.transpose.mulVec u) := by
      apply abs_le.mpr
      have hl := hr.third_lower j (M.transpose.mulVec u)
      have hu := hr.third_upper j (M.transpose.mulVec u)
      rw [quadratic_smul'] at hl hu
      constructor <;> nlinarith only [hl, hu]
    calc
      _ ≤ ∑ j, |M α j * matrixQuadratic (relativeThirdMatrix μ ξ j) (M.transpose.mulVec u)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |M α j| *
          (s₃ * matrixQuadratic (covariance μ (sumVector ξ)) (M.transpose.mulVec u)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
      _ = (∑ j, |M α j|) *
          (s₃ * matrixQuadratic (covariance μ (sumVector ξ)) (M.transpose.mulVec u)) :=
        (Finset.sum_mul ..).symm
      _ ≤ J * (s₃ * matrixQuadratic (covariance μ (sumVector ξ)) (M.transpose.mulVec u)) :=
        mul_le_mul_of_nonneg_right (hM α) (mul_nonneg hr.s₃_nonneg (hcovnonneg _))
      _ = _ := by ring
  have hfourth (α : Fin m) (u : Vector m)
      (Q : Fin p → Matrix (Fin p) (Fin p) ℝ)
      (Q' : Matrix (Fin m) (Fin m) ℝ)
      (hcontract : ∀ j, QuadraticLE (Q j) (s₄ • covariance μ (sumVector ξ)))
      (hproject : matrixQuadratic Q' u ≤
        ∑ j, (J * |M α j|) * matrixQuadratic (Q j) (M.transpose.mulVec u)) :
      matrixQuadratic Q' u ≤ (J ^ 2 * s₄) * matrixQuadratic
        (covariance μ (sumVector (fun i ω => M.mulVec (ξ i ω)))) u := by
    rw [projected_covariance_quadratic h M J hJ hM]
    calc
      _ ≤ ∑ j, (J * |M α j|) * matrixQuadratic (Q j) (M.transpose.mulVec u) := hproject
      _ ≤ ∑ j, (J * |M α j|) *
          (s₄ * matrixQuadratic (covariance μ (sumVector ξ)) (M.transpose.mulVec u)) := by
        apply Finset.sum_le_sum
        intro j _
        have hh := hcontract j (M.transpose.mulVec u)
        rw [quadratic_smul'] at hh
        exact mul_le_mul_of_nonneg_left hh (mul_nonneg hJ (abs_nonneg _))
      _ = J * ((∑ j, |M α j|) *
          (s₄ * matrixQuadratic (covariance μ (sumVector ξ)) (M.transpose.mulVec u))) := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ ≤ J * (J * (s₄ * matrixQuadratic (covariance μ (sumVector ξ)) (M.transpose.mulVec u))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hM α) (mul_nonneg hr.s₄_nonneg (hcovnonneg _))) hJ
      _ = _ := by ring
  refine
    { measurable := hp.measurable
      second_integrable := hp.integrable_coordinate_pair
      third_integrable := integrable_relativeThird_entry hp
      fourth_integrable := integrable_relativeFourth_entry hp
      s₃_nonneg := mul_nonneg hJ hr.s₃_nonneg
      s₄_nonneg := mul_nonneg (sq_nonneg _) hr.s₄_nonneg
      third_lower := ?_
      third_upper := ?_
      fourth_upper := ?_
      fresh_fourth_upper := ?_ }
  · intro α u
    rw [quadratic_smul']
    have hh := (abs_le.mp (hthird α u)).1
    nlinarith only [hh]
  · intro α u
    rw [quadratic_smul']
    exact (abs_le.mp (hthird α u)).2
  · intro α u
    rw [quadratic_smul']
    exact hfourth α u (relativeFourthMatrix μ ξ) _ hr.fourth_upper
      (projected_relativeFourthMatrix_quadratic_le h M J hJ hM α u)
  · intro α u
    rw [quadratic_smul']
    exact hfourth α u (relativeFreshFourthMatrix μ ξ) _ hr.fresh_fourth_upper
      (projected_relativeFreshFourthMatrix_quadratic_le h M J hJ hM α u)

end

end RectangleCLT.Companion.SplitV4
