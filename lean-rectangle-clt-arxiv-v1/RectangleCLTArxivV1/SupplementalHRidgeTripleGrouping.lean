import RectangleCLTArxivV1.SupplementalHRidgeGreen

/-! Exact finite signed grouping of ordered third-boundary atoms. The
factor1/6 will cancel the six actual orders of one rank-three stratum. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

theorem sum_cube_cycle {m : ℕ} (B : Fin m → Fin m → Fin m → ℝ) :
    (∑ j, ∑ l, ∑ k, B l k j)=(∑ j, ∑ l, ∑ k, B j l k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]

theorem sum_cube_swap_last {m : ℕ} (B : Fin m → Fin m → Fin m → ℝ) :
    (∑ j, ∑ l, ∑ k, B j k l)=(∑ j, ∑ l, ∑ k, B j l k) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

theorem half_sum_cube_eq_sixth_incidence_groups {m : ℕ} (B : Fin m → Fin m → Fin m → ℝ) :
    (1/2:ℝ)*(∑ j, ∑ l, ∑ k, B j l k)=
      (1/6:ℝ)*(∑ j, ∑ l, ∑ k, (B l k j+B j k l+B j l k)) := by
  have hc := sum_cube_cycle B
  have hs := sum_cube_swap_last B
  simp_rw [Finset.sum_add_distrib]
  rw [hc,hs]
  ring

/-- Each genuine signed third-boundary atom, extended by zero outside
its two selected face exclusions. Every further hard inequality remains. -/
def hardGaussianRidgeThirdAtom {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (j l k : Fin m) : ℝ := by
  classical
  exact if hardGaussianRidgeNonparallel u j l then
    if k∈(Finset.univ.erase j).erase l then
      hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) k*
      (hardGaussianRidgeNormalWeight u b j l*
        gaussianFiniteThresholdFirst ((Finset.univ.erase j).erase l)
          (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
          (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
            (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) k)
    else 0
  else 0

theorem hardGaussianRidgeThirdAtom_sum {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    (∑ k, hardGaussianRidgeThirdAtom u b j l k)=hardGaussianRidgeThirdBoundaryTerm u b j l := by
  classical
  unfold hardGaussianRidgeThirdAtom hardGaussianRidgeThirdBoundaryTerm
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · simp only [hp,if_pos]
    rw [←Finset.sum_filter]
    congr 1
    ext k
    simp
  · simp only [hp,if_false,Finset.sum_const_zero]

/-- Exact signed three-incidence grouping of the actual ridge Green
remainder. It requires no density symmetry or geometric bound premise. -/
theorem hardGaussianRidgeThirdBoundaryIntegral_grouping {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) :
    hardGaussianRidgeThirdBoundaryIntegral u b=
      (1/6:ℝ)*(∑ j, ∑ l, ∑ k,
        (hardGaussianRidgeThirdAtom u b l k j+
          hardGaussianRidgeThirdAtom u b j k l+hardGaussianRidgeThirdAtom u b j l k)) := by
  unfold hardGaussianRidgeThirdBoundaryIntegral
  rw [Fintype.sum_prod_type]
  simp_rw [←hardGaussianRidgeThirdAtom_sum]
  exact half_sum_cube_eq_sixth_incidence_groups _


def hardGaussianRidgeThirdIncidenceGroup {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (j l k : Fin m) : ℝ :=
  hardGaussianRidgeThirdAtom u b l k j+hardGaussianRidgeThirdAtom u b j k l+
    hardGaussianRidgeThirdAtom u b j l k

theorem abs_sum_cube_le {m : ℕ} (B : Fin m → Fin m → Fin m → ℝ) :
    abs (∑ j, ∑ l, ∑ k, B j l k)≤∑ j, ∑ l, ∑ k, abs (B j l k) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  exact Finset.abs_sum_le_sum_abs _ _

/-- The absolute value is taken only after the three actual incident
ridge boundary terms have been combined. -/
theorem abs_hardGaussianRidgeThirdBoundaryIntegral_le_groups {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) :
    abs (hardGaussianRidgeThirdBoundaryIntegral u b)≤
      (1/6:ℝ)*(∑ j, ∑ l, ∑ k, abs (hardGaussianRidgeThirdIncidenceGroup u b j l k)) := by
  rw [hardGaussianRidgeThirdBoundaryIntegral_grouping,abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<1/6)]
  exact mul_le_mul_of_nonneg_left (abs_sum_cube_le _) (by norm_num)

end
end RectangleCLTArxivV1
