import RectangleCLTCompanion.SignedSurfaceGeometry
import RectangleCLTArxivV1.SupplementalHRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The threshold-weighted ridge cancellation in Supplemental H.1.
The two conormal terms are paired before taking absolute values. -/
namespace RectangleCLTArxivV1
open RectangleCLT.Companion.SignedSurface
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual outward unit conormal to the `v` facet within the `u` facet. -/
def supplementalHRidgeConormal (u v : E) : E :=
  (Real.sqrt (1-⟪u,v⟫_ℝ^2))⁻¹ • (v-⟪u,v⟫_ℝ • u)

theorem supplementalHRidgeConormal_norm (u v : E) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hp : u+v≠0) (hm : u-v≠0) : ‖supplementalHRidgeConormal u v‖=1 := by
  have hprod := norm_sum_mul_norm_sub u v hu hv hp hm
  have hs : 0 < Real.sqrt (1-⟪u,v⟫_ℝ^2) := by
    nlinarith [mul_pos (norm_pos_iff.mpr hp) (norm_pos_iff.mpr hm)]
  have hn : ‖v-⟪u,v⟫_ℝ • u‖ = Real.sqrt (1-⟪u,v⟫_ℝ^2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (Real.sqrt_pos.mp hs).le]
    have hh := norm_sub_sq_real v (⟪u,v⟫_ℝ • u)
    rw [hv,norm_smul,Real.norm_eq_abs,hu,mul_one,inner_smul_right] at hh
    rw [real_inner_comm u v] at hh
    nlinarith [sq_abs ⟪u,v⟫_ℝ]
  simp only [supplementalHRidgeConormal,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs,hn]
  exact inv_mul_cancel₀ hs.ne'

theorem supplementalHRidgeConormal_pair (u v z : E) :
    ⟪supplementalHRidgeConormal u v,z⟫_ℝ+
      ⟪supplementalHRidgeConormal v u,z⟫_ℝ = pairedRidgeCoefficient u v z := by
  simp only [supplementalHRidgeConormal,inner_smul_left,inner_sub_left,
    conj_trivial,pairedRidgeCoefficient]
  rw [real_inner_comm v u]
  ring

/-- This is the weighted-pair estimate before replacing the chord length
by the angle. Its constant is uniform at both angular degeneracies. -/
theorem supplementalH_weighted_ridge_pair_le (u v z : E)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (hp : u+v≠0) (hm : u-v≠0) :
    abs (|⟪u,z⟫_ℝ| *⟪supplementalHRidgeConormal u v,z⟫_ℝ+
      |⟪v,z⟫_ℝ| *⟪supplementalHRidgeConormal v u,z⟫_ℝ) ≤
        2*‖u-v‖*‖z‖^2 := by
  have hbu : |⟪u,z⟫_ℝ| ≤ ‖z‖ := by
    simpa only [hu,one_mul] using abs_real_inner_le_norm u z
  have hdiff : abs (|⟪v,z⟫_ℝ|-|⟪u,z⟫_ℝ|) ≤ ‖u-v‖*‖z‖ := by
    calc
      _ ≤ |⟪v,z⟫_ℝ-⟪u,z⟫_ℝ| := abs_abs_sub_abs_le _ _
      _ = |⟪v-u,z⟫_ℝ| := by rw [inner_sub_left]
      _ ≤ ‖v-u‖*‖z‖ := abs_real_inner_le_norm _ _
      _ = _ := by rw [norm_sub_rev]
  have hd : |⟪supplementalHRidgeConormal v u,z⟫_ℝ| ≤ ‖z‖ := by
    have hvp : v+u≠0 := by simpa only [add_comm] using hp
    have hvm : v-u≠0 := by simpa only [sub_ne_zero,ne_comm] using hm
    simpa only [supplementalHRidgeConormal_norm v u hv hu hvp hvm,one_mul] using
      abs_real_inner_le_norm (supplementalHRidgeConormal v u) z
  have he : |⟪u,z⟫_ℝ| *⟪supplementalHRidgeConormal u v,z⟫_ℝ+
      |⟪v,z⟫_ℝ| *⟪supplementalHRidgeConormal v u,z⟫_ℝ =
      |⟪u,z⟫_ℝ| *(⟪supplementalHRidgeConormal u v,z⟫_ℝ+
        ⟪supplementalHRidgeConormal v u,z⟫_ℝ)+
      (|⟪v,z⟫_ℝ|-|⟪u,z⟫_ℝ|)*⟪supplementalHRidgeConormal v u,z⟫_ℝ := by ring
  rw [he]
  calc
    _ ≤ abs (|⟪u,z⟫_ℝ| *(⟪supplementalHRidgeConormal u v,z⟫_ℝ+
        ⟪supplementalHRidgeConormal v u,z⟫_ℝ))+
      abs ((|⟪v,z⟫_ℝ|-|⟪u,z⟫_ℝ|)*⟪supplementalHRidgeConormal v u,z⟫_ℝ) := abs_add _ _
    _ = |⟪u,z⟫_ℝ| *|pairedRidgeCoefficient u v z|+
      abs (|⟪v,z⟫_ℝ|-|⟪u,z⟫_ℝ|)*|⟪supplementalHRidgeConormal v u,z⟫_ℝ| := by
      rw [abs_mul,abs_abs,abs_mul,supplementalHRidgeConormal_pair]
    _ ≤ ‖z‖*(‖u-v‖*‖z‖)+(‖u-v‖*‖z‖)*‖z‖ :=
      add_le_add (mul_le_mul hbu (abs_pairedRidgeCoefficient_le u v z hu hv hp hm)
        (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul hdiff hd (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by ring


/-- Unit-normal chord length is at most their actual angle. -/
theorem supplementalH_chord_le_angle (u v : E) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖u-v‖ ≤ Real.arccos ⟪u,v⟫_ℝ := by
  have hn := norm_sub_sq_real u v
  rw [hu,hv] at hn
  have hinner : |⟪u,v⟫_ℝ| ≤ 1 := by
    simpa only [hu,hv,one_mul] using abs_real_inner_le_norm u v
  have hc := Real.cos_arccos (abs_le.mp hinner).1 (abs_le.mp hinner).2
  have hb := Real.one_sub_sq_div_two_le_cos (x := Real.arccos ⟪u,v⟫_ℝ)
  nlinarith [norm_nonneg (u-v),Real.arccos_nonneg ⟪u,v⟫_ℝ]

/-- The actual angle-weighted ridge coefficient estimate in H.1. -/
theorem supplementalH_weighted_ridge_pair_angle_le (u v z : E)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (hp : u+v≠0) (hm : u-v≠0) :
    abs (|⟪u,z⟫_ℝ| *⟪supplementalHRidgeConormal u v,z⟫_ℝ+
      |⟪v,z⟫_ℝ| *⟪supplementalHRidgeConormal v u,z⟫_ℝ) ≤
        2*Real.arccos ⟪u,v⟫_ℝ*‖z‖^2 := by
  exact (supplementalH_weighted_ridge_pair_le u v z hu hv hp hm).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (supplementalH_chord_le_angle u v hu hv) (by norm_num))
      (sq_nonneg _))


/-- The weighted pair of actual face coefficients is controlled by the
constructed three-face projection radius at the original Gaussian point. -/
theorem supplementalH_weighted_ridge_pair_radius_le {p r : ℕ} (hp : 1 ≤ p)
    (U : RectangleCLT.Face p → RectangleCLT.Vector r) (f : Fin 2 → RectangleCLT.Face p)
    (hu : ‖RectangleCLT.projectionEuclideanVector (U (f 0))‖=1)
    (hv : ‖RectangleCLT.projectionEuclideanVector (U (f 1))‖=1)
    (hpp : RectangleCLT.projectionEuclideanVector (U (f 0))+
      RectangleCLT.projectionEuclideanVector (U (f 1))≠0)
    (hmm : RectangleCLT.projectionEuclideanVector (U (f 0))-
      RectangleCLT.projectionEuclideanVector (U (f 1))≠0)
    (g : RectangleCLT.Vector r) :
    let u := RectangleCLT.projectionEuclideanVector (U (f 0))
    let v := RectangleCLT.projectionEuclideanVector (U (f 1))
    let x := RectangleCLT.projectionEuclideanVector g
    abs (|⟪u,x⟫_ℝ| *⟪supplementalHRidgeConormal u v,x⟫_ℝ+
      |⟪v,x⟫_ℝ| *⟪supplementalHRidgeConormal v u,x⟫_ℝ) ≤
        2*Real.arccos ⟪u,v⟫_ℝ*(supplementalHRadius U g)^2 := by
  let u := RectangleCLT.projectionEuclideanVector (U (f 0))
  let v := RectangleCLT.projectionEuclideanVector (U (f 1))
  let x := RectangleCLT.projectionEuclideanVector g
  let S := Submodule.span ℝ (Set.range (fun i => RectangleCLT.projectionEuclideanVector (U (f i))))
  let z := (S.orthogonalProjection x : EuclideanSpace ℝ (Fin r))
  have huS : u ∈ S := Submodule.subset_span ⟨0,rfl⟩
  have hvS : v ∈ S := Submodule.subset_span ⟨1,rfl⟩
  have hnuv : supplementalHRidgeConormal u v ∈ S :=
    S.smul_mem _ (S.sub_mem hvS (S.smul_mem _ huS))
  have hnvu : supplementalHRidgeConormal v u ∈ S :=
    S.smul_mem _ (S.sub_mem huS (S.smul_mem _ hvS))
  have hi (y : EuclideanSpace ℝ (Fin r)) (hy : y ∈ S) : ⟪y,z⟫_ℝ=⟪y,x⟫_ℝ :=
    S.inner_orthogonalProjection_eq_of_mem_left ⟨y,hy⟩ x
  have hh := supplementalH_weighted_ridge_pair_angle_le u v z hu hv hpp hmm
  rw [hi u huS,hi v hvS,hi _ hnuv,hi _ hnvu] at hh
  have hR := supplementalHRadius_small_span_norm_le hp U f (by norm_num) g
  have hnorm : ‖z‖^2 ≤ (supplementalHRadius U g)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hR 2
  exact hh.trans (mul_le_mul_of_nonneg_left hnorm
    (mul_nonneg (by norm_num) (Real.arccos_nonneg _)))

end
end RectangleCLTArxivV1
