import RectangleCLTArxivV1.SupplementalGGeometry

/-! The genuine logistic Hessian, reorganized by single faces and
angular pair coefficients as in Supplemental G. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section

theorem upperFaceSmoother_pi_false {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (a : Vector m) (h : ℝ) (hh : 0 < h) (x : Vector r) (j : Fin m) :
    (upperFaceSmoother a h hh).pi (U.mulVec x) (j,false) = 0 := by
  simp [FaceSmoother.pi, FaceWeights.pi, FaceSmoother.weights, upperFaceSmoother]

theorem upperFaceSmoother_coordinateMass {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (a : Vector m) (h : ℝ) (hh : 0 < h) (x : Vector r) (j : Fin m) :
    ((upperFaceSmoother a h hh).weights (U.mulVec x)).coordinateMass j =
      logisticFaceWeight U a h x j := by
  change (upperFaceSmoother a h hh).pi (U.mulVec x) (j,true) +
    (upperFaceSmoother a h hh).pi (U.mulVec x) (j,false) = _
  rw [upperFaceSmoother_pi,upperFaceSmoother_pi_false,add_zero]

theorem upperFaceSmoother_directionalMean {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (a : Vector m) (h : ℝ) (hh : 0 < h) (x z : Vector r) :
    ((upperFaceSmoother a h hh).weights (U.mulVec x)).directionalMean (U.mulVec z) =
      ∑ j, logisticFaceWeight U a h x j * dotProduct (U j) z := by
  rw [FaceWeights.directionalMean_eq]
  apply Finset.sum_congr rfl
  intro j _
  change ((upperFaceSmoother a h hh).pi (U.mulVec x) (j,true) -
    (upperFaceSmoother a h hh).pi (U.mulVec x) (j,false)) * _ = _
  rw [upperFaceSmoother_pi,upperFaceSmoother_pi_false,sub_zero]
  rfl

/-- This is the actual contracted matrix of second coordinate derivatives
of the projected logistic smoother, rather than an assumed derivative formula. -/
def capActualHessian {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (a : Vector m) (h : ℝ) (hh : 0 < h) (x z w : Vector r) : ℝ :=
  restorationHessian (upperFaceSmoother a h hh) (U.mulVec x) (U.mulVec z) (U.mulVec w)

theorem capActualHessian_eq_ordered {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (a : Vector m) (h : ℝ) (hh : 0 < h) (x z w : Vector r) :
    capActualHessian U a h hh x z w =
      (2*(∑ j, ∑ k, logisticTupleWeight U a h ![j,k] x *
        dotProduct (U j) z * dotProduct (U k) w) -
        ∑ j, logisticTupleWeight U a h ![j] x *
          dotProduct (U j) z * dotProduct (U j) w) / h^2 := by
  rw [capActualHessian,restorationHessian_eq_moments,upperFaceSmoother_F,
    upperFaceSmoother_directionalMean,upperFaceSmoother_directionalMean]
  simp_rw [upperFaceSmoother_coordinateMass]
  change (logisticNullWeight U a h x / h^2) *
    (2*(∑ j, logisticFaceWeight U a h x j*dotProduct (U j) z)*
      (∑ k, logisticFaceWeight U a h x k*dotProduct (U k) w) -
      ∑ j, logisticFaceWeight U a h x j*dotProduct (U j) z*dotProduct (U j) w) = _
  simp only [logisticTupleWeight,Fin.prod_univ_succ,Fin.prod_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,mul_one]
  have hcross : (∑ j, ∑ k, logisticNullWeight U a h x *
      (logisticFaceWeight U a h x j*logisticFaceWeight U a h x k) *
      dotProduct (U j) z * dotProduct (U k) w) =
      logisticNullWeight U a h x *
        (∑ j, logisticFaceWeight U a h x j*dotProduct (U j) z) *
        (∑ k, logisticFaceWeight U a h x k*dotProduct (U k) w) := by
    calc
      _ = ∑ j, (logisticNullWeight U a h x*logisticFaceWeight U a h x j*dotProduct (U j) z)*
          (∑ k, logisticFaceWeight U a h x k*dotProduct (U k) w) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (∑ j, logisticNullWeight U a h x*logisticFaceWeight U a h x j*dotProduct (U j) z)*
          (∑ k, logisticFaceWeight U a h x k*dotProduct (U k) w) := (Finset.sum_mul ..).symm
      _ = _ := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hsingle : (∑ j, logisticNullWeight U a h x*logisticFaceWeight U a h x j*
      dotProduct (U j) z*dotProduct (U j) w) =
      logisticNullWeight U a h x*(∑ j, logisticFaceWeight U a h x j*dotProduct (U j) z*dotProduct (U j) w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcross,hsingle]
  ring

/-- The genuine one-face weight used in the complementary remainder. -/
def capSingleWeightDirectionalDerivative {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (h : ℝ) (x : Vector r) (j : Fin m) : ℝ :=
  deriv (fun t : ℝ => logisticTupleWeight U a h ![j] (x+t • U j)) 0

theorem capSingleWeightDirectionalDerivative_eq {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (h : ℝ) (hh : 0 < h)
    (x : Vector r) (j : Fin m) (hu : vectorNormSq (U j) = 1) :
    capSingleWeightDirectionalDerivative U a h x j =
      (logisticTupleWeight U a h ![j] x / h) *
        (1-2*∑ k, logisticFaceWeight U a h x k * dotProduct (U j) (U k)) := by
  let s := upperFaceSmoother a h hh
  have hd := (s.hasDerivAt_F_line (U.mulVec x) (U.mulVec (U j)) 0).mul
    (s.hasDerivAt_pi_line (j,true) (U.mulVec x) (U.mulVec (U j)) 0)
  have he (t : ℝ) : logisticTupleWeight U a h ![j] (x+t • U j) =
      s.F (line (U.mulVec x) (U.mulVec (U j)) t) *
        s.pi (line (U.mulVec x) (U.mulVec (U j)) t) (j,true) := by
    rw [show line (U.mulVec x) (U.mulVec (U j)) t = U.mulVec (x+t • U j) by
      ext k
      simp [FaceSmoother.line,Matrix.mulVec_add,Matrix.mulVec_smul,smul_eq_mul]]
    rw [upperFaceSmoother_F,upperFaceSmoother_pi]
    simp [logisticTupleWeight]
  unfold capSingleWeightDirectionalDerivative
  rw [show (fun t : ℝ => logisticTupleWeight U a h ![j] (x+t • U j)) = _ from funext he]
  rw [hd.deriv]
  simp only [line_zero]
  dsimp only [s]
  simp_rw [upperFaceSmoother_F,upperFaceSmoother_pi,upperFaceSmoother_directionalMean]
  have hj : dotProduct (U j) (U j) = 1 := by simpa only [vectorNormSq_eq_dot_self] using hu
  have heq : (∑ k, logisticFaceWeight U a h x k * dotProduct (U k) (U j)) =
      ∑ k, logisticFaceWeight U a h x k * dotProduct (U j) (U k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [dotProduct_comm (U k) (U j)]
  simp only [FaceSmoother.normalDot,if_true,upperFaceSmoother,Matrix.mulVec] at ⊢
  change _ = _
  rw [hj,heq]
  simp only [logisticTupleWeight,Fin.prod_univ_succ,Fin.prod_univ_zero,Matrix.cons_val_zero,mul_one]
  ring

theorem cap_hessian_pair_algebra {ι : Type*} [Fintype ι]
    (F h : ℝ) (π z w : ι → ℝ) (ρ : ι → ι → ℝ) (hρ : ∀ j k, ρ j k = ρ k j) :
    (2*(∑ j, ∑ k, F*π j*π k*z j*w k) - ∑ j, F*π j*z j*w j) / h^2 =
      -(1/h)*(∑ j, z j*w j*((F*π j/h)*(1-2*∑ k, π k*ρ j k))) +
        (1/h^2)*(∑ j, ∑ k, F*π j*π k*
          (z j*w k+z k*w j-ρ j k*(z j*w j+z k*w k))) := by
  let T := ∑ j, F*π j*z j*w j
  let Q := ∑ j, ∑ k, F*π j*π k*z j*w k
  let R := ∑ j, ∑ k, F*π j*π k*ρ j k*z j*w j
  have hc : (∑ j, ∑ k, F*π j*π k*z k*w j) = Q := by
    dsimp only [Q]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hr : (∑ j, ∑ k, F*π j*π k*ρ j k*z k*w k) = R := by
    dsimp only [R]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hρ k j]
    ring
  have hs : (∑ j, z j*w j*((F*π j/h)*(1-2*∑ k, π k*ρ j k))) = (T-2*R)/h := by
    calc
      _ = ∑ j, (F*π j*z j*w j/h - (2/h)*(∑ k, F*π j*π k*ρ j k*z j*w j)) := by
        apply Finset.sum_congr rfl
        intro j _
        have hrj : (∑ k, F*π j*π k*ρ j k*z j*w j) =
            F*π j*z j*w j*(∑ k, π k*ρ j k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        rw [hrj]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum]
        dsimp only [T,R]
        ring
  have hp : (∑ j, ∑ k, F*π j*π k*(z j*w k+z k*w j-ρ j k*(z j*w j+z k*w k))) =
      2*Q-2*R := by
    calc
      _ = ∑ j, ∑ k, (F*π j*π k*z j*w k+F*π j*π k*z k*w j-
          F*π j*π k*ρ j k*z j*w j-F*π j*π k*ρ j k*z k*w k) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by
        simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
        rw [hc,hr]
        change Q+Q-R-R = 2*Q-2*R
        ring
  rw [hs,hp]
  change (2*Q-T)/h^2 = _
  ring

/-- The actual Hessian decomposition from Supplemental G, in ordered-pair
form. Pair symmetry makes this identical to twice the unordered-pair sum;
unit diagonal coefficients vanish. The single-face term is an actual
ordinary derivative of the genuine positive logistic weight. -/
theorem capActualHessian_single_pair_decomposition {m r : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (h : ℝ) (hh : 0 < h)
    (x z w : Vector r) (hu : ∀ j, vectorNormSq (U j) = 1) :
    capActualHessian U a h hh x z w =
      -(1/h)*(∑ j, dotProduct (U j) z*dotProduct (U j) w*
        capSingleWeightDirectionalDerivative U a h x j) +
      (1/h^2)*(∑ j, ∑ k, logisticTupleWeight U a h ![j,k] x*
        capPairCoefficient (U j) (U k) z w) := by
  rw [capActualHessian_eq_ordered]
  simp_rw [capSingleWeightDirectionalDerivative_eq U a h hh x _ (hu _)]
  simp only [logisticTupleWeight,Fin.prod_univ_succ,Fin.prod_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,mul_one]
  have ht := cap_hessian_pair_algebra (logisticNullWeight U a h x) h
    (logisticFaceWeight U a h x) (fun j => dotProduct (U j) z)
    (fun j => dotProduct (U j) w) (fun j k => dotProduct (U j) (U k))
    (fun j k => dotProduct_comm (U j) (U k))
  simpa only [capPairCoefficient,mul_assoc] using ht

end
end RectangleCLTArxivV1
