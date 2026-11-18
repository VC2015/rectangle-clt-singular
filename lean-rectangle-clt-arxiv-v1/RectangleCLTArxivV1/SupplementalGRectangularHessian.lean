import RectangleCLTArxivV1.SupplementalGHessian

/-! The signed original Hessian decomposition for rectangular factors. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def capRectangularFactorNormal {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ) (f : Face p) : Vector r :=
  if f.2 then A f.1 else -A f.1

theorem capRectangularFactorNormal_unit {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (hdiag : ∀ j, (A*A.transpose) j j = 1) (f : Face p) :
    vectorNormSq (capRectangularFactorNormal A f) = 1 := by
  have hh := hdiag f.1
  simp only [Matrix.mul_apply,Matrix.transpose_apply] at hh
  unfold capRectangularFactorNormal
  split <;> simpa [vectorNormSq,pow_two] using hh

theorem cap_rectangular_normalDot_factor {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (f : Face p) (z : Vector r) :
    normalDot f (A.mulVec z) = faceDot (capRectangularFactorNormal A f) z := by
  unfold normalDot capRectangularFactorNormal
  split <;> simp [faceDot,Matrix.mulVec,dotProduct,Finset.sum_neg_distrib]

def capRectangularPairCoefficient {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (f g : Face p) (Y W : Vector p) : ℝ :=
  normalDot f Y*normalDot g W+normalDot g Y*normalDot f W -
    faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)*
      (normalDot f Y*normalDot f W+normalDot g Y*normalDot g W)

theorem capRectangularPairCoefficient_factor {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (f g : Face p) (z w : Vector r) :
    capRectangularPairCoefficient A f g (A.mulVec z) (A.mulVec w) =
      capPairCoefficient (capRectangularFactorNormal A f) (capRectangularFactorNormal A g) z w := by
  simp only [capRectangularPairCoefficient,cap_rectangular_normalDot_factor,capPairCoefficient,faceDot,dotProduct]

def capRectangularSingleDerivative {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (f : Face p) : ℝ :=
  deriv (fun t : ℝ => selectorTupleWeight s ![f]
    (line x (A.mulVec (capRectangularFactorNormal A f)) t)) 0

theorem capRectangularSingleDerivative_eq {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (x : Vector p) (f : Face p) :
    capRectangularSingleDerivative s A x f = (selectorTupleWeight s ![f] x/s.bandwidth)*
      (1-2*∑ g, s.pi x g*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)) := by
  have hd := (s.hasDerivAt_F_line x (A.mulVec (capRectangularFactorNormal A f)) 0).mul
    (s.hasDerivAt_pi_line f x (A.mulVec (capRectangularFactorNormal A f)) 0)
  unfold capRectangularSingleDerivative
  simp only [selectorTupleWeight,Fin.prod_univ_succ,Fin.prod_univ_zero,Matrix.cons_val_zero,mul_one]
  rw [hd.deriv]
  simp only [line_zero]
  have hu : faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A f) = 1 := by
    simpa only [vectorNormSq_eq_dot_self,faceDot,dotProduct] using capRectangularFactorNormal_unit A hdiag f
  rw [cap_rectangular_normalDot_factor,hu]
  have hm : (s.weights x).directionalMean (A.mulVec (capRectangularFactorNormal A f)) =
      ∑ g, s.pi x g*faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g) := by
    apply Finset.sum_congr rfl
    intro g _
    change s.pi x g*normalDot g (A.mulVec (capRectangularFactorNormal A f)) = _
    rw [cap_rectangular_normalDot_factor,faceDot_comm]
  rw [hm]
  ring

/-- The actual original-coordinate Hessian that appears inside the
repeated-direction fourth tensor is split before any absolute value. -/
theorem cap_rectangular_hessian_single_pair {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (x Y W : Vector p) :
    restorationHessian s x Y W =
      -(1/s.bandwidth)*(∑ f, normalDot f Y*normalDot f W*capRectangularSingleDerivative s A x f) +
      (1/s.bandwidth^2)*(∑ f, ∑ g, selectorTupleWeight s ![f,g] x*
        capRectangularPairCoefficient A f g Y W) := by
  rw [restorationHessian_eq_selector_partitions,restoration_sum_pi_fin_two,restoration_sum_pi_fin_one]
  simp_rw [capRectangularSingleDerivative_eq s A hdiag x]
  simp only [selectorTupleWeight,Fin.prod_univ_succ,Fin.prod_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,mul_one]
  have ht := cap_hessian_pair_algebra (s.F x) s.bandwidth (s.pi x)
    (fun f => normalDot f Y) (fun f => normalDot f W)
    (fun f g => faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g))
    (fun f g => faceDot_comm (capRectangularFactorNormal A f) (capRectangularFactorNormal A g))
  simpa only [capRectangularPairCoefficient,mul_assoc] using ht


end
end RectangleCLTArxivV1
