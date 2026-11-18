import RectangleCLTArxivV1.SupplementalGHessian

/-! The single/pair decomposition on the original rectangle smoother.
This representation plugs directly into the archived repeated-direction
Gaussian tensor identity, including singular covariance factors. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section

def capFactorNormal {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (f : Face p) : Vector p :=
  if f.2 then A f.1 else -A f.1

theorem capFactorNormal_unit {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A*A.transpose) j j = 1) (f : Face p) :
    vectorNormSq (capFactorNormal A f) = 1 := by
  have hh := hdiag f.1
  simp only [Matrix.mul_apply,Matrix.transpose_apply] at hh
  unfold capFactorNormal
  split <;> simpa [vectorNormSq,pow_two] using hh

theorem cap_normalDot_factor {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Face p) (z : Vector p) :
    normalDot f (A.mulVec z) = faceDot (capFactorNormal A f) z := by
  unfold normalDot capFactorNormal
  split <;> simp [faceDot,Matrix.mulVec,dotProduct,Finset.sum_neg_distrib]

def capOriginalPairCoefficient {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f g : Face p) (Y W : Vector p) : ℝ :=
  normalDot f Y*normalDot g W+normalDot g Y*normalDot f W -
    faceDot (capFactorNormal A f) (capFactorNormal A g)*
      (normalDot f Y*normalDot f W+normalDot g Y*normalDot g W)

theorem capOriginalPairCoefficient_factor {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f g : Face p) (z w : Vector p) :
    capOriginalPairCoefficient A f g (A.mulVec z) (A.mulVec w) =
      capPairCoefficient (capFactorNormal A f) (capFactorNormal A g) z w := by
  simp only [capOriginalPairCoefficient,cap_normalDot_factor,capPairCoefficient,faceDot,dotProduct]

def capOriginalSingleDerivative {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (f : Face p) : ℝ :=
  deriv (fun t : ℝ => selectorTupleWeight s ![f]
    (line x (A.mulVec (capFactorNormal A f)) t)) 0

theorem capOriginalSingleDerivative_eq {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (x : Vector p) (f : Face p) :
    capOriginalSingleDerivative s A x f = (selectorTupleWeight s ![f] x/s.bandwidth)*
      (1-2*∑ g, s.pi x g*faceDot (capFactorNormal A f) (capFactorNormal A g)) := by
  have hd := (s.hasDerivAt_F_line x (A.mulVec (capFactorNormal A f)) 0).mul
    (s.hasDerivAt_pi_line f x (A.mulVec (capFactorNormal A f)) 0)
  unfold capOriginalSingleDerivative
  simp only [selectorTupleWeight,Fin.prod_univ_succ,Fin.prod_univ_zero,Matrix.cons_val_zero,mul_one]
  rw [hd.deriv]
  simp only [line_zero]
  have hu : faceDot (capFactorNormal A f) (capFactorNormal A f) = 1 := by
    simpa only [vectorNormSq_eq_dot_self,faceDot,dotProduct] using capFactorNormal_unit A hdiag f
  rw [cap_normalDot_factor,hu]
  have hm : (s.weights x).directionalMean (A.mulVec (capFactorNormal A f)) =
      ∑ g, s.pi x g*faceDot (capFactorNormal A f) (capFactorNormal A g) := by
    apply Finset.sum_congr rfl
    intro g _
    change s.pi x g*normalDot g (A.mulVec (capFactorNormal A f)) = _
    rw [cap_normalDot_factor,faceDot_comm]
  rw [hm]
  ring

/-- The actual original-coordinate Hessian that appears inside the
repeated-direction fourth tensor is split before any absolute value. -/
theorem cap_original_hessian_single_pair {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (x Y W : Vector p) :
    restorationHessian s x Y W =
      -(1/s.bandwidth)*(∑ f, normalDot f Y*normalDot f W*capOriginalSingleDerivative s A x f) +
      (1/s.bandwidth^2)*(∑ f, ∑ g, selectorTupleWeight s ![f,g] x*
        capOriginalPairCoefficient A f g Y W) := by
  rw [restorationHessian_eq_selector_partitions,restoration_sum_pi_fin_two,restoration_sum_pi_fin_one]
  simp_rw [capOriginalSingleDerivative_eq s A hdiag x]
  simp only [selectorTupleWeight,Fin.prod_univ_succ,Fin.prod_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one,mul_one]
  have ht := cap_hessian_pair_algebra (s.F x) s.bandwidth (s.pi x)
    (fun f => normalDot f Y) (fun f => normalDot f W)
    (fun f g => faceDot (capFactorNormal A f) (capFactorNormal A g))
    (fun f g => faceDot_comm (capFactorNormal A f) (capFactorNormal A g))
  simpa only [capOriginalPairCoefficient,mul_assoc] using ht

end
end RectangleCLTArxivV1
