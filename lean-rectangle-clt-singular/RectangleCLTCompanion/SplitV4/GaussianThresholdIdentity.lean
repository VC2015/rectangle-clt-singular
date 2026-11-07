import RectangleCLTCompanion.SplitV4.GaussianRadialScaling
import RectangleCLTCompanion.SplitV4.GaussianThresholdDiagonal

/-! The common-threshold identity of Appendix B.5, for actual derivatives
of the hard Gaussian CDF and actual radial Gaussian trace. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem hasDerivAt_gaussianThresholdTrace_update {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (l : Fin m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    HasDerivAt (fun t => gaussianThresholdTrace u (Function.update b l t))
      (-(gaussianThresholdFirst u b l) - ∑ j, b j * gaussianThresholdMixed u b j l) (b l) := by
  classical
  have hcoord (j : Fin m) : HasDerivAt (fun t : ℝ => (Function.update b l t) j)
      (if j = l then 1 else 0) (b l) := by
    by_cases hj : j = l
    · subst j
      simpa only [Function.update_self, if_pos rfl] using hasDerivAt_id (b l)
    · simpa only [Function.update_of_ne hj, if_neg hj] using hasDerivAt_const (b l) (b j)
  have hfirst (j : Fin m) : HasDerivAt
      (fun t => gaussianThresholdFirst u (Function.update b l t) j)
      (gaussianThresholdMixed u b j l) (b l) := by
    simpa only [Function.update_eq_self] using
      hasDerivAt_gaussianThresholdFirst_update_mixed u b j l (hu j) hi (b l)
  have hprod (j : Fin m) := (hcoord j).mul (hfirst j)
  have hd := (HasDerivAt.sum (u := (Finset.univ : Finset (Fin m))) (fun j _ => hprod j)).neg
  have htrace : (fun t => gaussianThresholdTrace u (Function.update b l t)) =
      fun t => -(∑ j, (Function.update b l t) j *
        gaussianThresholdFirst u (Function.update b l t) j) := by
    funext t
    exact gaussianThresholdTrace_eq_radial_first u _ hu hi
  rw [htrace]
  convert hd using 1
  simp only [Function.update_eq_self, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem gaussianThresholdDerivative_eq_raw {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdDerivative u b =
      ∑ j, (-(gaussianThresholdFirst u b j) - b j * ∑ l, gaussianThresholdMixed u b j l) := by
  unfold gaussianThresholdDerivative
  simp_rw [(hasDerivAt_gaussianThresholdTrace_update u b _ hu hi).deriv]
  simp only [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem threshold_row_identity {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    -(gaussianThresholdFirst u b j) - b j * ∑ l, gaussianThresholdMixed u b j l =
      (b j ^ 2 - 1) * gaussianThresholdFirst u b j -
        ∑ l, (1 - faceDot (u j) (u l)) * b j * gaussianThresholdMixed u b j l := by
  classical
  have hself : faceDot (u j) (u j) = 1 := by simpa only [faceDot, vectorNormSq, pow_two] using hu
  have hsplit : (∑ l, gaussianThresholdMixed u b j l) = gaussianThresholdMixed u b j j +
      ∑ l ∈ Finset.univ.erase j, gaussianThresholdMixed u b j l := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm.trans (add_comm _ _)
  have hpair : (∑ l, (1 - faceDot (u j) (u l)) * b j * gaussianThresholdMixed u b j l) =
      ∑ l ∈ Finset.univ.erase j, (1 - faceDot (u j) (u l)) * b j * gaussianThresholdMixed u b j l := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp only [hself, sub_self, zero_mul, add_zero]
  rw [hsplit, gaussianThreshold_diagonal_identity u b j hu hi, hpair]
  have hf : (∑ l ∈ Finset.univ.erase j,
      (1 - faceDot (u j) (u l)) * b j * gaussianThresholdMixed u b j l) =
      b j * (∑ l ∈ Finset.univ.erase j, gaussianThresholdMixed u b j l) -
        b j * (∑ l ∈ Finset.univ.erase j, faceDot (u j) (u l) * gaussianThresholdMixed u b j l) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hf]
  ring

/-- The actual common-threshold identity. The factor `1/2` on the full
ordered pair sum is exactly the manuscript's unordered-pair convention. -/
theorem gaussianThresholdDerivative_identity {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdDerivative u b =
      (∑ j, (b j ^ 2 - 1) * gaussianThresholdFirst u b j) -
        (1 / 2 : ℝ) * ∑ j, ∑ l,
          (1 - faceDot (u j) (u l)) * (b j + b l) * gaussianThresholdMixed u b j l := by
  rw [gaussianThresholdDerivative_eq_raw u b hu hi]
  simp_rw [threshold_row_identity u b _ (hu _) hi]
  rw [Finset.sum_sub_distrib]
  congr 1
  let A : Fin m → Fin m → ℝ := fun j l =>
    (1 - faceDot (u j) (u l)) * b j * gaussianThresholdMixed u b j l
  have hdot (j l : Fin m) : faceDot (u j) (u l) = faceDot (u l) (u j) := by
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hswap : (∑ j, ∑ l, A l j) = ∑ j, ∑ l, A j l := Finset.sum_comm
  have hpoint (j l : Fin m) :
      (1 - faceDot (u j) (u l)) * (b j + b l) * gaussianThresholdMixed u b j l = A j l + A l j := by
    dsimp only [A]
    rw [← hdot j l, ← gaussianThresholdMixed_symm u b hu hi j l]
    ring
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib]
  rw [hswap]
  ring

end
end RectangleCLT.Companion.SplitV4
