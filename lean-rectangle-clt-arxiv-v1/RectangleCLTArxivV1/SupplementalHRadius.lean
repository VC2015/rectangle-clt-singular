import RectangleCLTArxivV1.SupplementalHLocalizedTube
import RectangleCLT.GaussianProjectionMaximum

/-! The actual radius formed from spans of at most three signed faces.
All triples, including repetitions, are retained. Lower-cardinality spans
are obtained by padding a tuple, and dependent tuples do not increase
the dimension bound. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT
open scoped BigOperators
noncomputable section

def threeFaceSubspace {p r : ℕ} (U : Face p → Vector r) (f : Fin 3 → Face p) :
    Submodule ℝ (EuclideanSpace ℝ (Fin r)) :=
  Submodule.span ℝ (Set.range (fun i => projectionEuclideanVector (U (f i))))

theorem threeFaceSubspace_finrank_le {p r : ℕ}
    (U : Face p → Vector r) (f : Fin 3 → Face p) :
    Module.finrank ℝ (threeFaceSubspace U f) ≤ 3 := by
  simpa [threeFaceSubspace] using
    (finrank_range_le_card (fun i : Fin 3 => projectionEuclideanVector (U (f i))))

/-- One plus the maximum Euclidean orthogonal-projection length. -/
def supplementalHRadius {p r : ℕ} (U : Face p → Vector r) (g : Vector r) : ℝ :=
  1+subspaceProjectionRadius (threeFaceSubspace U) g

theorem supplementalHRadius_ge_one {p r : ℕ} (U : Face p → Vector r) (g : Vector r) :
    1 ≤ supplementalHRadius U g := by
  have h : 0 ≤ subspaceProjectionRadius (threeFaceSubspace U) g := norm_nonneg _
  exact le_add_of_nonneg_right h

theorem supplementalHRadius_pos {p r : ℕ} (U : Face p → Vector r) (g : Vector r) :
    0 < supplementalHRadius U g := lt_of_lt_of_le zero_lt_one (supplementalHRadius_ge_one U g)

theorem measurable_supplementalHRadius {p r : ℕ} (U : Face p → Vector r) :
    Measurable (supplementalHRadius U) :=
  measurable_const.add (measurable_subspaceProjectionRadius _)

theorem supplementalHRadius_projection_norm_le {p r : ℕ}
    (U : Face p → Vector r) (f : Fin 3 → Face p) (g : Vector r) :
    ‖(threeFaceSubspace U f).orthogonalProjection (projectionEuclideanVector g)‖ ≤
      supplementalHRadius U g := by
  have h := norm_le_pi_norm
    (fun f : Fin 3 → Face p =>
      ‖(threeFaceSubspace U f).orthogonalProjection (projectionEuclideanVector g)‖) f
  have h' : ‖(threeFaceSubspace U f).orthogonalProjection (projectionEuclideanVector g)‖ ≤
      subspaceProjectionRadius (threeFaceSubspace U) g := by
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using h
  exact h'.trans (le_add_of_nonneg_left zero_le_one)

/-- Padding by repeated faces puts every span of at most three normals
under the actual radius, including dependent or empty tuples. -/
theorem supplementalHRadius_small_span_norm_le {p r q : ℕ} (hp : 1 ≤ p)
    (U : Face p → Vector r) (f : Fin q → Face p) (hq : q ≤ 3) (g : Vector r) :
    ‖(Submodule.span ℝ (Set.range (fun i => projectionEuclideanVector (U (f i))))).orthogonalProjection
      (projectionEuclideanVector g)‖ ≤ supplementalHRadius U g := by
  classical
  let fallback : Face p := (⟨0, by omega⟩, true)
  let extended : Fin 3 → Face p := fun i =>
    if hi : i.val < q then f ⟨i.val, hi⟩ else fallback
  have hle : Submodule.span ℝ (Set.range (fun i => projectionEuclideanVector (U (f i)))) ≤
      threeFaceSubspace U extended := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hq⟩, ?_⟩
    simp [extended, i.isLt]
  exact (orthogonalProjection_norm_mono hle (projectionEuclideanVector g)).trans
    (supplementalHRadius_projection_norm_le U extended g)

theorem supplementalHRadius_add_le {p r : ℕ}
    (U : Face p → Vector r) (g d : Vector r) :
    supplementalHRadius U (g+d) ≤ supplementalHRadius U g+‖projectionEuclideanVector d‖ := by
  have hg : 0 ≤ subspaceProjectionRadius (threeFaceSubspace U) g := norm_nonneg _
  have hb : subspaceProjectionRadius (threeFaceSubspace U) (g+d) ≤
      subspaceProjectionRadius (threeFaceSubspace U) g+‖projectionEuclideanVector d‖ := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg hg (norm_nonneg _))).mpr
    intro f
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have hadd : projectionEuclideanVector (g+d) =
        projectionEuclideanVector g+projectionEuclideanVector d := rfl
    rw [hadd,map_add]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · have h := norm_le_pi_norm
        (fun f : Fin 3 → Face p =>
          ‖(threeFaceSubspace U f).orthogonalProjection (projectionEuclideanVector g)‖) f
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using h
    · exact ((threeFaceSubspace U f).orthogonalProjection.le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (threeFaceSubspace U f).orthogonalProjection_norm_le
          (norm_nonneg _)).trans_eq (one_mul _))
  unfold supplementalHRadius
  linarith

private theorem threeFace_basis_card_exp_le {p : ℕ} (hp : 1 ≤ p) :
    2*(1+(3:ℝ)*(Fintype.card (Fin 3 → Face p):ℝ)) ≤ Real.exp (8*dimensionLog p) := by
  have hp1 : 1 ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : 0 < (p:ℝ) := by linarith
  have hcard : (Fintype.card (Fin 3 → Face p):ℝ) = (2*(p:ℝ))^3 := by
    simp [Face,Fintype.card_fun,Fintype.card_prod,mul_comm,Nat.cast_pow]
  have hexp1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hexp8 : (256:ℝ) ≤ Real.exp 8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hexp1 8
    norm_num at hh
    simpa only [←Real.exp_nat_mul,show (8:ℝ)*1=8 by norm_num] using hh
  have hp38 : (p:ℝ)^3 ≤ (p:ℝ)^8 := pow_le_pow_right₀ hp1 (by decide)
  have hp8 : 1 ≤ (p:ℝ)^8 := one_le_pow₀ hp1
  have heq : Real.exp (8*dimensionLog p)=Real.exp 8*(p:ℝ)^8 := by
    rw [dimensionLog,Real.log_mul (Real.exp_ne_zero _) hp0.ne',Real.log_exp]
    rw [mul_add,mul_one,Real.exp_add]
    congr 1
    rw [show (8:ℝ)*Real.log (p:ℝ)=(8:ℕ)*Real.log (p:ℝ) by norm_num,
      Real.exp_nat_mul,Real.exp_log hp0]
  rw [hcard,heq]
  calc
    _ ≤ 256*(p:ℝ)^8 := by nlinarith only [hp38,hp8]
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp8 (pow_nonneg hp0.le 8)

/-- The actual finite-subspace construction also has the exponential
polynomial moments used when translations are averaged. -/
theorem supplementalHRadius_weighted_moment_le {p r : ℕ} (hp : 1 ≤ p)
    (U : Face p → Vector r) {M : ℝ} (hM : Real.sqrt (dimensionLog p) ≤ M) (k : ℕ) :
    Integrable (fun g => Real.exp ((supplementalHRadius U g-1)/M)*
      (supplementalHRadius U g)^k) (standardGaussian r) ∧
      (∫ g, Real.exp ((supplementalHRadius U g-1)/M)*(supplementalHRadius U g)^k
        ∂standardGaussian r) ≤
      (Real.sqrt (dimensionLog p))^k*Real.exp (8+((3:ℝ)*(k+1))^2/2) := by
  simpa only [supplementalHRadius, add_sub_cancel_left] using
    subspaceProjectionRadius_weighted_moment_le (threeFaceSubspace U) 3
      (threeFaceSubspace_finrank_le U) (log_exp_mul_nat_ge_one hp)
      (threeFace_basis_card_exp_le hp) hM k

/-- Every natural moment of the exact three-face radius has its
dimension-logarithm power; the normal vectors may be dependent. -/
theorem supplementalHRadius_moment_le {p r : ℕ} (hp : 1 ≤ p)
    (U : Face p → Vector r) (k : ℕ) :
    Integrable (fun g => (supplementalHRadius U g)^k) (standardGaussian r) ∧
      (∫ g, (supplementalHRadius U g)^k ∂standardGaussian r) ≤
        (Real.sqrt (dimensionLog p))^k*Real.exp (8+((3:ℝ)*(k+1))^2/2) := by
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have h := subspaceProjectionRadius_weighted_moment_le (threeFaceSubspace U) 3
    (threeFaceSubspace_finrank_le U) hL (threeFace_basis_card_exp_le hp) (le_refl _) k
  have hdom (g : Vector r) : (supplementalHRadius U g)^k ≤
      Real.exp (subspaceProjectionRadius (threeFaceSubspace U) g/Real.sqrt (dimensionLog p))*
        (supplementalHRadius U g)^k := by
    have h0 : 0 ≤ subspaceProjectionRadius (threeFaceSubspace U) g := norm_nonneg _
    have he : 1 ≤ Real.exp (subspaceProjectionRadius (threeFaceSubspace U) g/
        Real.sqrt (dimensionLog p)) := by
      linarith [Real.add_one_le_exp (subspaceProjectionRadius (threeFaceSubspace U) g/
        Real.sqrt (dimensionLog p)),div_nonneg h0 (Real.sqrt_nonneg (dimensionLog p))]
    exact le_mul_of_one_le_left (pow_nonneg (supplementalHRadius_pos U g).le k) he
  have hi : Integrable (fun g => (supplementalHRadius U g)^k) (standardGaussian r) := by
    apply h.1.mono' ((measurable_supplementalHRadius U).pow_const k).aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (supplementalHRadius_pos U g).le k)]
      exact hdom g)
  exact ⟨hi,(integral_mono hi h.1 hdom).trans h.2⟩

/-- The exact random radius discharges the Gaussian moment premises in
the outward-tube estimate. No Hausdorff surface comparison is assumed. -/
theorem concentrated_base_threeFace_weighted_outward_tube {p r m : ℕ} (hp : 1 ≤ p)
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (B : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (U : Face p → Vector r)
    {K δ σ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0 < s → ν.real (faceLayer B b s) ≤ K*(s+δ)) :
    (∫ z, (gaussianOutwardVariableTube B a σ (supplementalHRadius U)).indicator
      (fun z => (supplementalHRadius U z.2)^4) z ∂ν.prod (standardGaussian r)) ≤
      Real.exp 128*K*(σ*(dimensionLog p*Real.sqrt (dimensionLog p))+
        δ*(dimensionLog p)^2) := by
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have h3 := supplementalHRadius_moment_le hp U 3
  have h4 := supplementalHRadius_moment_le hp U 4
  have h3pow : (Real.sqrt (dimensionLog p))^3 = dimensionLog p*Real.sqrt (dimensionLog p) := by
    calc
      _ = (Real.sqrt (dimensionLog p))^2*Real.sqrt (dimensionLog p) := by ring
      _ = _ := by rw [Real.sq_sqrt hL]
  have h4pow : (Real.sqrt (dimensionLog p))^4 = (dimensionLog p)^2 := by
    calc
      _ = ((Real.sqrt (dimensionLog p))^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hL]
  have hm3 : (∫ g, (supplementalHRadius U g)^3 ∂standardGaussian r) ≤
      Real.exp 128*(dimensionLog p*Real.sqrt (dimensionLog p)) := by
    apply h3.2.trans
    rw [h3pow]
    have hc : Real.exp (8+((3:ℝ)*(3+1))^2/2) ≤ Real.exp 128 :=
      Real.exp_le_exp.mpr (by norm_num)
    exact (mul_le_mul_of_nonneg_left hc (mul_nonneg hL (Real.sqrt_nonneg _))).trans_eq (by ring)
  have hm4 : (∫ g, (supplementalHRadius U g)^4 ∂standardGaussian r) ≤
      Real.exp 128*(dimensionLog p)^2 := by
    apply h4.2.trans
    rw [h4pow]
    have hc : Real.exp (8+((3:ℝ)*(4+1))^2/2) ≤ Real.exp 128 :=
      Real.exp_le_exp.mpr (by norm_num)
    exact (mul_le_mul_of_nonneg_left hc (sq_nonneg _)).trans_eq (by ring)
  have htube := concentrated_base_gaussian_weighted_outward_tube ν B a hσ hbase
    (supplementalHRadius U) (measurable_supplementalHRadius U) (supplementalHRadius_pos U) h3.1 h4.1
  apply htube.trans
  apply (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hm3 hσ.le) (mul_le_mul_of_nonneg_left hm4 hδ)) hK).trans_eq
  ring

theorem concentrated_base_threeFace_weighted_outward_tube_large_scale {p r m : ℕ} (hp : 1 ≤ p)
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (B : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (U : Face p → Vector r)
    {K δ σ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hσ : 0 < σ)
    (hscale : δ*Real.sqrt (dimensionLog p) ≤ σ)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0 < s → ν.real (faceLayer B b s) ≤ K*(s+δ)) :
    (∫ z, (gaussianOutwardVariableTube B a σ (supplementalHRadius U)).indicator
      (fun z => (supplementalHRadius U z.2)^4) z ∂ν.prod (standardGaussian r)) ≤
      (2*Real.exp 128)*K*σ*(dimensionLog p*Real.sqrt (dimensionLog p)) := by
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hs := mul_le_mul_of_nonneg_right hscale (mul_nonneg hL (Real.sqrt_nonneg (dimensionLog p)))
  have he : δ*Real.sqrt (dimensionLog p)*(dimensionLog p*Real.sqrt (dimensionLog p)) =
      δ*(dimensionLog p)^2 := by
    calc
      _ = δ*dimensionLog p*(Real.sqrt (dimensionLog p))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hL]; ring
  rw [he] at hs
  apply (concentrated_base_threeFace_weighted_outward_tube hp ν B a U hK hδ hσ hbase).trans
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add_left hs (σ*(dimensionLog p*Real.sqrt (dimensionLog p))))
    (mul_nonneg (Real.exp_nonneg 128) hK)
  exact hh.trans_eq (by ring)

end
end RectangleCLTArxivV1
