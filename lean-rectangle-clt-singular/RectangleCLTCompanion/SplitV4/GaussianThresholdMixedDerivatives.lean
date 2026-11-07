import RectangleCLTCompanion.SplitV4.GaussianFiniteThresholdDerivatives

/-! Actual two-normal Gaussian section densities for mixed hard-threshold
derivatives. The conditional variance is positive by linear independence;
no quantitative correlation gap is imposed. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def gaussianThresholdResidualNormals {m r : ℕ} (u : Fin m → Vector r) (j : Fin m) : Fin m → Vector r :=
  fun l => gaussianNormalProjection (u j) (u l)

def gaussianThresholdResidualLevels {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j : Fin m) : Vector m :=
  fun l => b l - b j * faceDot (u l) (u j)

def gaussianThresholdResidualScale {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m) : ℝ :=
  Real.sqrt (vectorNormSq (gaussianThresholdResidualNormals u j l))

theorem gaussianNormalProjection_twice_ne_zero_of_independent {m r : ℕ}
    (u : Fin m → Vector r) (hi : LinearIndependent ℝ u) (j l k : Fin m)
    (hkj : k ≠ j) (hkl : k ≠ l) (c : ℝ) :
    gaussianNormalProjection (c • gaussianNormalProjection (u j) (u l))
      (gaussianNormalProjection (u j) (u k)) ≠ 0 := by
  let S := Submodule.span ℝ (u '' ({j, l} : Set (Fin m)))
  have hjS : u j ∈ S := Submodule.subset_span ⟨j, by simp, rfl⟩
  have hlS : u l ∈ S := Submodule.subset_span ⟨l, by simp, rfl⟩
  have hpS : gaussianNormalProjection (u j) (u l) ∈ S :=
    S.sub_mem hlS (S.smul_mem _ hjS)
  have hqS : c • gaussianNormalProjection (u j) (u l) ∈ S := S.smul_mem c hpS
  intro hz
  have hpk : gaussianNormalProjection (u j) (u k) ∈ S := by
    rw [gaussianNormalProjection, sub_eq_zero] at hz
    rw [hz]
    exact S.smul_mem _ hqS
  have huk : u k ∈ S := by
    convert S.add_mem hpk (S.smul_mem (faceDot (u k) (u j)) hjS) using 1
    simp only [gaussianNormalProjection, sub_add_cancel]
  exact (hi.not_mem_span_image (s := ({j, l} : Set (Fin m))) (by simp [hkj, hkl])) huk

theorem gaussianThresholdResidualScale_pos {m r : ℕ}
    (u : Fin m → Vector r) (hi : LinearIndependent ℝ u) (j l : Fin m) (hlj : l ≠ j) :
    0 < gaussianThresholdResidualScale u j l :=
  Real.sqrt_pos.mpr (vectorNormSq_pos (gaussianNormalProjection_ne_zero_of_independent u hi j l hlj))

theorem gaussianThresholdResidualLevels_update {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j ≠ l) (c : ℝ) :
    gaussianThresholdResidualLevels u (Function.update b l c) j =
      Function.update (gaussianThresholdResidualLevels u b j) l (c - b j * faceDot (u l) (u j)) := by
  classical
  ext k
  by_cases hkl : k = l
  · subst k
    simp only [gaussianThresholdResidualLevels, Function.update_self, Function.update_of_ne hjl]
  · simp only [gaussianThresholdResidualLevels, Function.update_of_ne hkl, Function.update_of_ne hjl]

def gaussianThresholdMixedSection {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  let σ := gaussianThresholdResidualScale u j l
  let v := gaussianThresholdResidualNormals u j
  let d := gaussianThresholdResidualLevels u b j
  gaussianPDFReal 0 1 (b j) *
    ((gaussianPDFReal 0 1 (d l / σ) / σ) *
      gaussianThresholdSectionProbability ((Finset.univ.erase j).erase l) v d (σ⁻¹ • v l) (d l / σ))

/-- Repeating the actual one-dimensional conditioning proves the genuine
mixed derivative, including the conditional Gaussian density Jacobian. -/
theorem hasDerivAt_gaussianThresholdFirst_update {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m) (hjl : j ≠ l)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    HasDerivAt (fun c => gaussianThresholdFirst u (Function.update b l c) j)
      (gaussianThresholdMixedSection u b j l) (b l) := by
  classical
  let s := Finset.univ.erase j
  let v := gaussianThresholdResidualNormals u j
  let d := gaussianThresholdResidualLevels u b j
  let σ := gaussianThresholdResidualScale u j l
  have hσ : 0 < σ := gaussianThresholdResidualScale_pos u hi j l (Ne.symm hjl)
  have hnorm : vectorNormSq (v l) = σ ^ 2 := (Real.sq_sqrt (vectorNormSq_nonneg _)).symm
  have hl : l ∈ s := Finset.mem_erase.mpr ⟨Ne.symm hjl, Finset.mem_univ _⟩
  have hp (k : Fin m) (hk : k ∈ s.erase l) : gaussianNormalProjection (σ⁻¹ • v l) (v k) ≠ 0 := by
    have hkl := (Finset.mem_erase.mp hk).1
    have hkj := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    exact gaussianNormalProjection_twice_ne_zero_of_independent u hi j l k hkj hkl σ⁻¹
  have hd := hasDerivAt_gaussianFiniteThresholdCDF_update s v d l hl hσ hnorm hp (d l)
  have ha : HasDerivAt (fun c : ℝ => c - b j * faceDot (u l) (u j)) 1 (b l) :=
    (hasDerivAt_id _).sub_const _
  have hcomp := (hd.comp (b l) ha).const_mul (gaussianPDFReal 0 1 (b j))
  have he : (fun c => gaussianThresholdFirst u (Function.update b l c) j) =
      fun c => gaussianPDFReal 0 1 (b j) * gaussianFiniteThresholdCDF s v
        (Function.update d l (c - b j * faceDot (u l) (u j))) := by
    funext c
    rw [gaussianThresholdFirst_eq_section u _ j hu hi]
    simp only [Function.update_of_ne hjl, gaussianThresholdSectionProbability]
    have hlevels : (fun k => Function.update b l c k - b j * faceDot (u k) (u j)) =
        Function.update d l (c - b j * faceDot (u l) (u j)) := by
      ext k
      by_cases hkl : k = l
      · subst k
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hkl, d, gaussianThresholdResidualLevels]
    rw [hlevels]
    rfl
  rw [he]
  simpa only [Function.comp_apply, mul_one, gaussianThresholdMixedSection, s, v, d, σ] using hcomp

theorem gaussianThresholdMixed_eq_section {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m) (hjl : j ≠ l)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdMixed u b j l = gaussianThresholdMixedSection u b j l :=
  (hasDerivAt_gaussianThresholdFirst_update u b j l hjl hu hi).deriv

theorem gaussianThresholdResidualScale_sq_of_unit {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hj : vectorNormSq (u j) = 1) (hl : vectorNormSq (u l) = 1) :
    gaussianThresholdResidualScale u j l ^ 2 = 1 - faceDot (u j) (u l) ^ 2 := by
  rw [gaussianThresholdResidualScale, Real.sq_sqrt (vectorNormSq_nonneg _)]
  have he := SignedSurface.vectorNormSq_gaussianSectionResidual (u j) (u l) hj
  simpa only [gaussianThresholdResidualNormals, gaussianNormalProjection,
    SignedSurface.gaussianSectionResidual, faceDot_comm (u l) (u j), hl] using he

theorem gaussianThresholdResidualScale_eq_sqrt_of_unit {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hj : vectorNormSq (u j) = 1) (hl : vectorNormSq (u l) = 1) :
    gaussianThresholdResidualScale u j l = Real.sqrt (1 - faceDot (u j) (u l) ^ 2) := by
  have he := gaussianThresholdResidualScale_sq_of_unit u j l hj hl
  rw [← he]
  exact (Real.sqrt_sq (show 0 ≤ gaussianThresholdResidualScale u j l from Real.sqrt_nonneg _)).symm

theorem gaussianThreshold_pair_gram_positive {m r : ℕ}
    (u : Fin m → Vector r) (hi : LinearIndependent ℝ u) (j l : Fin m) (hjl : j ≠ l)
    (hj : vectorNormSq (u j) = 1) (hl : vectorNormSq (u l) = 1) :
    0 < 1 - faceDot (u j) (u l) ^ 2 := by
  rw [← gaussianThresholdResidualScale_sq_of_unit u j l hj hl]
  exact sq_pos_of_pos (gaussianThresholdResidualScale_pos u hi j l (Ne.symm hjl))

theorem gaussianThresholdFirst_nonneg {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    0 ≤ gaussianThresholdFirst u b j := by
  rw [gaussianThresholdFirst_eq_section u b j hu hi]
  exact mul_nonneg (gaussianPDFReal_nonneg _ _ _)
    (gaussianThresholdSectionProbability_nonneg _ _ _ _ _)

theorem gaussianThresholdMixed_nonneg_of_ne {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m) (hjl : j ≠ l)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    0 ≤ gaussianThresholdMixed u b j l := by
  rw [gaussianThresholdMixed_eq_section u b j l hjl hu hi]
  dsimp only [gaussianThresholdMixedSection]
  exact mul_nonneg (gaussianPDFReal_nonneg _ _ _) (mul_nonneg
    (div_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianThresholdResidualScale_pos u hi j l (Ne.symm hjl)).le)
    (gaussianThresholdSectionProbability_nonneg _ _ _ _ _))

end
end RectangleCLT.Companion.SplitV4
