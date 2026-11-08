import RectangleCLTCompanion.SplitV4.Printed.ProjectionTail
import RectangleCLTCompanion.SplitV4.GaussianPairSections
import RectangleCLTCompanion.SplitV4.AveragedThreshold

/-! Exact two-normal projection law behind the printed adaptive radius.
The normal coordinates are obtained by the actual Gaussian section map,
and the norm is that of the genuine orthogonal projection. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def normalPairCoordinates {r : ℕ} (e f : Vector r) (g : Vector r) : ℝ × ℝ :=
  (faceDot e g, faceDot f g)

theorem measurable_normalPairCoordinates {r : ℕ} (e f : Vector r) :
    Measurable (normalPairCoordinates e f) := by
  unfold normalPairCoordinates faceDot
  fun_prop

theorem normalPairCoordinates_section {r : ℕ} (e f : Vector r)
    (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1) (hef : faceDot e f = 0)
    (z : (ℝ × ℝ) × Vector r) :
    normalPairCoordinates e f (gaussianPairSectionMap e f z) = z.1 := by
  have hee : faceDot e e = 1 := by simpa only [faceDot, vectorNormSq, pow_two] using he
  have hff : faceDot f f = 1 := by simpa only [faceDot, vectorNormSq, pow_two] using hf
  have hfe : faceDot f e = 0 := by rw [faceDot_comm]; exact hef
  unfold normalPairCoordinates gaussianPairSectionMap
  rw [gaussianPairSectionPoint_orthogonal_formula e f hef]
  ext <;> simp only [threshold_faceDot_add_right, threshold_faceDot_sub_right,
    threshold_faceDot_smul_right, hee, hff, hef, hfe] <;> ring

theorem standardGaussian_normalPairCoordinates_law {n : ℕ} (e f : Vector (n+1))
    (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1) (hef : faceDot e f = 0) :
    (standardGaussian (n+1)).map (normalPairCoordinates e f) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let ν := ((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (standardGaussian (n+1))
  have hmap := (gaussianPairSectionMap_measurePreserving e f he hf).map_eq
  calc
    _ = (ν.map (gaussianPairSectionMap e f)).map (normalPairCoordinates e f) := by rw [hmap]
    _ = ν.map ((normalPairCoordinates e f) ∘ (gaussianPairSectionMap e f)) :=
      Measure.map_map (measurable_normalPairCoordinates e f) (measurable_gaussianPairSectionMap e f)
    _ = ν.map Prod.fst := by
      congr 1
      funext z
      exact normalPairCoordinates_section e f he hf hef z
    _ = _ := by simp [ν]

def basisNormal {r k : ℕ} {V : Submodule ℝ (EuclideanSpace ℝ (Fin r))}
    (b : OrthonormalBasis (Fin k) ℝ V) (i : Fin k) : Vector r := fun j => (b i : EuclideanSpace ℝ (Fin r)) j

theorem vectorNormSq_basisNormal {r k : ℕ} {V : Submodule ℝ (EuclideanSpace ℝ (Fin r))}
    (b : OrthonormalBasis (Fin k) ℝ V) (i : Fin k) : vectorNormSq (basisNormal b i) = 1 := by
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin r => ℝ) (b i : EuclideanSpace ℝ (Fin r))
  have hn : ‖(b i : EuclideanSpace ℝ (Fin r))‖ = 1 := b.orthonormal.norm_eq_one i
  rw [hn] at hh
  simpa only [basisNormal, vectorNormSq, Real.norm_eq_abs, sq_abs, one_pow] using hh.symm

theorem faceDot_basisNormal {r k : ℕ} {V : Submodule ℝ (EuclideanSpace ℝ (Fin r))}
    (b : OrthonormalBasis (Fin k) ℝ V) {i j : Fin k} (hij : i ≠ j) :
    faceDot (basisNormal b i) (basisNormal b j) = 0 := by
  have hh := b.orthonormal.inner_eq_zero hij
  change ⟪(b i : EuclideanSpace ℝ (Fin r)), (b j : EuclideanSpace ℝ (Fin r))⟫_ℝ = 0 at hh
  simpa only [basisNormal, faceDot, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, mul_comm] using hh

theorem orthogonalProjection_norm_eq_planeRadius {r : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin r)))
    (b : OrthonormalBasis (Fin 2) ℝ V) (g : Vector r) :
    ‖V.orthogonalProjection (projectionEuclideanVector g)‖ =
      planeRadius (normalPairCoordinates (basisNormal b 0) (basisNormal b 1) g) := by
  have hs := b.sum_sq_norm_inner (V.orthogonalProjection (projectionEuclideanVector g))
  have he (i : Fin 2) : ⟪b i, V.orthogonalProjection (projectionEuclideanVector g)⟫_ℝ =
      faceDot (basisNormal b i) g := by
    rw [Submodule.inner_orthogonalProjection_eq_of_mem_left]
    simp only [basisNormal, faceDot, projectionEuclideanVector, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro j _
    change g j*(b i : EuclideanSpace ℝ (Fin r)) j = (b i : EuclideanSpace ℝ (Fin r)) j*g j
    ring
  simp_rw [he] at hs
  simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs] at hs
  unfold planeRadius normalPairCoordinates
  dsimp only
  rw [hs, Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem rankTwo_projection_tail {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (b : OrthonormalBasis (Fin 2) ℝ V) {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian (n+1)).real
      {g | s < ‖V.orthogonalProjection (projectionEuclideanVector g)‖} =
        Real.exp (-(s^2)/2) := by
  have he := standardGaussian_normalPairCoordinates_law (basisNormal b 0) (basisNormal b 1)
    (vectorNormSq_basisNormal b 0) (vectorNormSq_basisNormal b 1) (faceDot_basisNormal b (by decide))
  have hset : MeasurableSet {z : ℝ × ℝ | s < planeRadius z} :=
    measurableSet_lt measurable_const measurable_planeRadius
  have hm := Measure.map_apply (μ := standardGaussian (n+1))
    (measurable_normalPairCoordinates (basisNormal b 0) (basisNormal b 1)) hset
  rw [he] at hm
  have hr := congrArg ENNReal.toReal hm
  change ((gaussianReal 0 1).prod (gaussianReal 0 1)).real {z | s < planeRadius z} =
    (standardGaussian (n+1)).real ((normalPairCoordinates (basisNormal b 0) (basisNormal b 1)) ⁻¹'
      {z | s < planeRadius z}) at hr
  rw [normalPair_radius_tail hs] at hr
  simp_rw [orthogonalProjection_norm_eq_planeRadius V b]
  exact hr.symm

theorem standardGaussian_unitCoordinate_law {n : ℕ} (e : Vector (n+1))
    (he : vectorNormSq e = 1) :
    (standardGaussian (n+1)).map (faceDot e) = gaussianReal 0 1 := by
  let ν := (gaussianReal 0 1).prod (standardGaussian (n+1))
  have hmap := (gaussianNormalSectionMap_measurePreserving e he).map_eq
  have hee : faceDot e e = 1 := by simpa only [faceDot, vectorNormSq, pow_two] using he
  have hcoord (z : ℝ × Vector (n+1)) : faceDot e (gaussianNormalSectionMap e z) = z.1 := by
    unfold gaussianNormalSectionMap SignedSurface.gaussianSectionPoint SignedSurface.gaussianSectionResidual
    simp only [threshold_faceDot_add_right, threshold_faceDot_sub_right,
      threshold_faceDot_smul_right, hee]
    ring
  calc
    _ = (ν.map (gaussianNormalSectionMap e)).map (faceDot e) := by rw [hmap]
    _ = ν.map ((faceDot e) ∘ (gaussianNormalSectionMap e)) :=
      Measure.map_map (measurable_thresholdDot e) (measurable_gaussianNormalSectionMap e)
    _ = ν.map Prod.fst := by congr 1; funext z; exact hcoord z
    _ = _ := by simp [ν]

theorem orthogonalProjection_norm_eq_abs_coordinate {r : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin r)))
    (b : OrthonormalBasis (Fin 1) ℝ V) (g : Vector r) :
    ‖V.orthogonalProjection (projectionEuclideanVector g)‖ = |faceDot (basisNormal b 0) g| := by
  rw [b.orthogonalProjection_eq_sum]
  simp only [Fin.sum_univ_one, norm_smul, b.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs]
  congr 1
  change ⟪(b 0 : EuclideanSpace ℝ (Fin r)), projectionEuclideanVector g⟫_ℝ = _
  simp only [basisNormal, faceDot, projectionEuclideanVector, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro j _
  change g j*(b 0 : EuclideanSpace ℝ (Fin r)) j = (b 0 : EuclideanSpace ℝ (Fin r)) j*g j
  ring

theorem normal_absolute_tail_le_pair_radius {s : ℝ} (hs : 0 ≤ s) :
    (gaussianReal 0 1).real {x : ℝ | s < |x|} ≤ Real.exp (-(s^2)/2) := by
  let ν := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hm := Measure.map_apply (μ := ν) measurable_fst
    (measurableSet_lt measurable_const measurable_id.abs : MeasurableSet {x : ℝ | s < |x|})
  have he : (gaussianReal 0 1).real {x : ℝ | s < |x|} =
      ν.real {z : ℝ × ℝ | s < |z.1|} := by
    simpa only [ν, Measure.map_fst_prod, measure_univ, one_smul] using congrArg ENNReal.toReal hm
  rw [he, ← normalPair_radius_tail hs]
  apply measureReal_mono (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
  intro z hz
  have hnorm : |z.1| ≤ planeRadius z := by
    unfold planeRadius
    have hr := Real.sq_sqrt (add_nonneg (sq_nonneg z.1) (sq_nonneg z.2))
    have hp := Real.sqrt_nonneg (z.1^2+z.2^2)
    nlinarith [sq_abs z.1, sq_nonneg z.2, abs_nonneg z.1]
  exact hz.trans_le hnorm

theorem rankOne_projection_tail {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))))
    (b : OrthonormalBasis (Fin 1) ℝ V) {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian (n+1)).real
      {g | s < ‖V.orthogonalProjection (projectionEuclideanVector g)‖} ≤
        Real.exp (-(s^2)/2) := by
  have he := standardGaussian_unitCoordinate_law (basisNormal b 0) (vectorNormSq_basisNormal b 0)
  have hm := Measure.map_apply (μ := standardGaussian (n+1)) (measurable_thresholdDot (basisNormal b 0))
    (measurableSet_lt measurable_const measurable_id.abs : MeasurableSet {x : ℝ | s < |x|})
  rw [he] at hm
  have hr := congrArg ENNReal.toReal hm
  change (gaussianReal 0 1).real {x : ℝ | s < |x|} =
    (standardGaussian (n+1)).real {g | s < |faceDot (basisNormal b 0) g|} at hr
  simp_rw [orthogonalProjection_norm_eq_abs_coordinate V b]
  rw [← hr]
  exact normal_absolute_tail_le_pair_radius hs

/-- The exact radial tail controls every actual subspace of dimension at
most two, including dimensions zero and one and ambient dimension zero. -/
theorem rank_le_two_projection_tail {r : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin r))) (hV : Module.finrank ℝ V ≤ 2)
    {s : ℝ} (hs : 0 ≤ s) :
    (standardGaussian r).real {g | s < ‖V.orthogonalProjection (projectionEuclideanVector g)‖} ≤
      Real.exp (-(s^2)/2) := by
  classical
  cases r with
  | zero =>
    have hzero (g : Vector 0) : V.orthogonalProjection (projectionEuclideanVector g) = 0 :=
      Subsingleton.elim _ _
    simp only [hzero, norm_zero, not_lt_of_ge hs, setOf_false, measureReal_empty]
    positivity
  | succ n =>
    have hcases : Module.finrank ℝ V = 0 ∨ Module.finrank ℝ V = 1 ∨ Module.finrank ℝ V = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · letI : Subsingleton V := (Module.finrank_zero_iff.mp h0)
      have hzero (g : Vector (n+1)) : V.orthogonalProjection (projectionEuclideanVector g) = 0 :=
        Subsingleton.elim _ _
      simp only [hzero, norm_zero, not_lt_of_ge hs, setOf_false, measureReal_empty]
      positivity
    · exact rankOne_projection_tail V ((stdOrthonormalBasis ℝ V).reindex (finCongr h1)) hs
    · exact (rankTwo_projection_tail V ((stdOrthonormalBasis ℝ V).reindex (finCongr h2)) hs).le

end
end RectangleCLT.Companion.SplitV4.Printed
