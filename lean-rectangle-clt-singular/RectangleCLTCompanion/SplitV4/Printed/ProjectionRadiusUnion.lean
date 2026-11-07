import RectangleCLTCompanion.SplitV4.Printed.ProjectionRadiusLaw

/-! The finite-family union step in the printed adaptive-radius argument.
No independence between the projections is asserted or used. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem subspaceProjectionRadius_tail_union {ι : Type*} [Fintype ι] {r : ℕ}
    (V : ι → Submodule ℝ (EuclideanSpace ℝ (Fin r)))
    (hV : ∀ i, Module.finrank ℝ (V i) ≤ 2) {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian r).real {g | s < subspaceProjectionRadius V g} ≤
      (Fintype.card ι : ℝ)*Real.exp (-(s^2)/2) := by
  classical
  have hsub : {g | s < subspaceProjectionRadius V g} ⊆
      ⋃ i, {g | s < ‖(V i).orthogonalProjection (projectionEuclideanVector g)‖} := by
    intro g hg
    by_contra hnot
    have hall (i : ι) : ‖(V i).orthogonalProjection (projectionEuclideanVector g)‖ ≤ s := by
      by_contra hi
      exact hnot (mem_iUnion.mpr ⟨i,lt_of_not_ge hi⟩)
    have hnorm : subspaceProjectionRadius V g ≤ s := by
      apply (pi_norm_le_iff_of_nonneg hs).mpr
      intro i
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hall i
    exact (not_lt_of_ge hnorm) hg
  calc
    _ ≤ (standardGaussian r).real (⋃ i, {g | s < ‖(V i).orthogonalProjection (projectionEuclideanVector g)‖}) :=
      measureReal_mono hsub
    _ ≤ ∑ i, (standardGaussian r).real {g | s < ‖(V i).orthogonalProjection (projectionEuclideanVector g)‖} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, Real.exp (-(s^2)/2) := Finset.sum_le_sum (fun i _ => rank_le_two_projection_tail (V i) (hV i) hs)
    _ = _ := by simp

theorem thresholdProjectionRadius_tail_union {m r : ℕ} (u : Fin m → Vector r)
    {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian r).real {g | 1+s < thresholdProjectionRadius u g} ≤
      (m : ℝ)^2*Real.exp (-(s^2)/2) := by
  have he : {g | 1+s < thresholdProjectionRadius u g} =
      {g | s < subspaceProjectionRadius (thresholdPairSpan u) g} := by
    ext g
    simp only [mem_setOf_eq,thresholdProjectionRadius,add_lt_add_iff_left]
  rw [he]
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using
    subspaceProjectionRadius_tail_union (thresholdPairSpan u) (thresholdPairSpan_finrank_le u) hs

theorem thresholdPairCount_le_exp {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ)^2 ≤ Real.exp (2*dimensionLog m) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hlog : Real.log (m : ℝ) ≤ dimensionLog m := by
    rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _) hm0.ne', Real.log_exp]
    linarith
  have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2))
  have he : Real.exp (2*Real.log (m : ℝ)) = (m : ℝ)^2 := by
    rw [show (2 : ℝ)*Real.log (m : ℝ) = (2 : ℕ)*Real.log (m : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hm0]
  rwa [he] at hexp

/-- Past a fixed multiple of sqrt L, the polynomial number of planes is
absorbed by the Gaussian radial exponent. This is the printed tail split. -/
theorem thresholdProjectionRadius_tail_beyond_sqrt_log {m r : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector r) {x : ℝ}
    (hx : 8*Real.sqrt (dimensionLog m) ≤ x) :
    (standardGaussian r).real {g | x < thresholdProjectionRadius u g} ≤
      Real.exp (-(x^2)/16) := by
  have hL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
  have hsqrt : 1 ≤ Real.sqrt (dimensionLog m) := by
    exact (Real.one_le_sqrt).mpr hL
  have hx2 : 2 ≤ x := by linarith
  have hs : 0 ≤ x-1 := by linarith
  have htail := thresholdProjectionRadius_tail_union u hs
  have hset : 1+(x-1) = x := by ring
  rw [hset] at htail
  have hexp := mul_le_mul_of_nonneg_right (thresholdPairCount_le_exp hm) (Real.exp_nonneg (-(x-1)^2/2))
  have hsq : 64*dimensionLog m ≤ x^2 := by
    have hs := Real.sq_sqrt (show 0 ≤ dimensionLog m by linarith)
    nlinarith [sq_nonneg (x-8*Real.sqrt (dimensionLog m))]
  have hshift : x^2/4 ≤ (x-1)^2 := by nlinarith
  calc
    _ ≤ (m : ℝ)^2*Real.exp (-((x-1)^2)/2) := htail
    _ ≤ Real.exp (2*dimensionLog m)*Real.exp (-((x-1)^2)/2) := hexp
    _ = Real.exp (2*dimensionLog m-(x-1)^2/2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(x^2)/16) := Real.exp_le_exp.mpr (by nlinarith)

end
end RectangleCLT.Companion.SplitV4.Printed
