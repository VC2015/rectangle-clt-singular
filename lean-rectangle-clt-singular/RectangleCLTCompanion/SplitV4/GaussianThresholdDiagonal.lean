import RectangleCLTCompanion.SplitV4.GaussianThresholdMixedDerivatives
import RectangleCLTCompanion.SplitV4.ContinuousPartials
import RectangleCLTCompanion.SplitV4.ContinuousSecondPartials

/-! The diagonal hard-Gaussian threshold identity, from actual residual
CDF derivatives and the finite-dimensional chain rule. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem hasFDerivAt_gaussianThresholdCDF {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (b : Vector m) :
    HasFDerivAt (gaussianThresholdCDF u)
      (∑ j, gaussianThresholdFirst u b j •
        (ContinuousLinearMap.proj j : Vector m →L[ℝ] ℝ)) b :=
  hasFDerivAt_of_continuous_coordinate_derivatives (gaussianThresholdCDF u)
    (fun d j => gaussianThresholdFirst u d j)
    (fun d j c => hasDerivAt_gaussianThresholdCDF_update_first u d j (hu j) hi c)
    (fun j => continuous_gaussianThresholdFirst u j (hu j) hi) b

theorem hasFDerivAt_gaussianResidualThresholdCDF {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (hi : LinearIndependent ℝ u) (j : Fin m) (b : Vector m) :
    HasFDerivAt (gaussianFiniteThresholdCDF (Finset.univ.erase j) (gaussianThresholdResidualNormals u j))
      (∑ k, gaussianFiniteThresholdFirst (Finset.univ.erase j) (gaussianThresholdResidualNormals u j) b k •
        (ContinuousLinearMap.proj k : Vector m →L[ℝ] ℝ)) b := by
  let s := Finset.univ.erase j
  let v := gaussianThresholdResidualNormals u j
  have hgeom (k : Fin m) (hk : k ∈ s) :
      0 < gaussianThresholdResidualScale u j k ∧
      vectorNormSq (v k) = gaussianThresholdResidualScale u j k ^ 2 ∧
      ∀ l ∈ s.erase k, gaussianNormalProjection
        ((gaussianThresholdResidualScale u j k)⁻¹ • v k) (v l) ≠ 0 := by
    refine ⟨gaussianThresholdResidualScale_pos u hi j k (Finset.mem_erase.mp hk).1,
      (Real.sq_sqrt (vectorNormSq_nonneg _)).symm, ?_⟩
    intro l hl
    exact gaussianNormalProjection_twice_ne_zero_of_independent u hi j k l
      (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1 (Finset.mem_erase.mp hl).1 _
  have hd (d : Vector m) (k : Fin m) (c : ℝ) :
      HasDerivAt (fun t => gaussianFiniteThresholdCDF s v (Function.update d k t))
        (gaussianFiniteThresholdFirst s v (Function.update d k c) k) c := by
    by_cases hk : k ∈ s
    · obtain ⟨hσ, hn, hp⟩ := hgeom k hk
      exact hasDerivAt_gaussianFiniteThresholdCDF_update_first s v d k hk hσ hn hp c
    · rw [gaussianFiniteThresholdFirst_outside s v _ k hk]
      have he : (fun t => gaussianFiniteThresholdCDF s v (Function.update d k t)) =
          fun _ => gaussianFiniteThresholdCDF s v d :=
        funext (gaussianFiniteThresholdCDF_update_outside s v d k hk)
      rw [he]
      exact hasDerivAt_const c _
  have hc (k : Fin m) : Continuous (fun d => gaussianFiniteThresholdFirst s v d k) := by
    by_cases hk : k ∈ s
    · obtain ⟨hσ, hn, hp⟩ := hgeom k hk
      exact continuous_gaussianFiniteThresholdFirst s v k hk hσ hn hp
    · have he : (fun d => gaussianFiniteThresholdFirst s v d k) = fun _ => (0 : ℝ) :=
        funext (fun d => gaussianFiniteThresholdFirst_outside s v d k hk)
      rw [he]
      exact continuous_const
  exact hasFDerivAt_of_continuous_coordinate_derivatives (gaussianFiniteThresholdCDF s v)
    (fun d k => gaussianFiniteThresholdFirst s v d k) hd hc b

theorem gaussianThresholdMixed_eq_residualFirst {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m) (hjl : j ≠ l)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdMixed u b j l = gaussianPDFReal 0 1 (b j) *
      gaussianFiniteThresholdFirst (Finset.univ.erase j) (gaussianThresholdResidualNormals u j)
        (gaussianThresholdResidualLevels u b j) l := by
  let s := Finset.univ.erase j
  let v := gaussianThresholdResidualNormals u j
  let d := gaussianThresholdResidualLevels u b j
  let σ := gaussianThresholdResidualScale u j l
  have hσ : 0 < σ := gaussianThresholdResidualScale_pos u hi j l (Ne.symm hjl)
  have hnorm : vectorNormSq (v l) = σ ^ 2 := (Real.sq_sqrt (vectorNormSq_nonneg _)).symm
  have hl : l ∈ s := Finset.mem_erase.mpr ⟨Ne.symm hjl, Finset.mem_univ _⟩
  have hp (k : Fin m) (hk : k ∈ s.erase l) : gaussianNormalProjection (σ⁻¹ • v l) (v k) ≠ 0 :=
    gaussianNormalProjection_twice_ne_zero_of_independent u hi j l k
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1 _
  have he := gaussianFiniteThresholdFirst_eq_section s v d l hl hσ hnorm hp
  rw [gaussianThresholdMixed_eq_section u b j l hjl hu hi]
  exact congrArg (fun x => gaussianPDFReal 0 1 (b j) * x) he.symm

/-- The exact diagonal identity for the actual hard Gaussian CDF.
Every mixed term is a genuine second coordinate derivative. -/
theorem gaussianThreshold_diagonal_identity {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdMixed u b j j = -b j * gaussianThresholdFirst u b j -
      ∑ l ∈ Finset.univ.erase j, faceDot (u j) (u l) * gaussianThresholdMixed u b j l := by
  classical
  let s := Finset.univ.erase j
  let v := gaussianThresholdResidualNormals u j
  let d := gaussianThresholdResidualLevels u b j
  let ρ : Vector m := fun k => faceDot (u k) (u j)
  let p : ℝ → Vector m := fun t k => b k - t * ρ k
  have hp : HasDerivAt p (fun k => -ρ k) (b j) := by
    apply hasDerivAt_pi.mpr
    intro k
    simpa only [p, id_eq, zero_sub, one_mul] using
      ((hasDerivAt_const (b j) (b k)).sub ((hasDerivAt_id (b j)).mul_const (ρ k)))
  have hf := hasFDerivAt_gaussianResidualThresholdCDF u hi j d
  have hf' : HasFDerivAt (gaussianFiniteThresholdCDF s v)
      (∑ k, gaussianFiniteThresholdFirst s v d k • (ContinuousLinearMap.proj k : Vector m →L[ℝ] ℝ)) (p (b j)) := hf
  have hc := hf'.comp_hasDerivAt (b j) hp
  have hd := (hasDerivAt_standardRealGaussian_density (b j)).mul hc
  have he : (fun t => gaussianThresholdFirst u (Function.update b j t) j) =
      fun t => gaussianPDFReal 0 1 t * gaussianFiniteThresholdCDF s v (p t) := by
    funext t
    rw [gaussianThresholdFirst_eq_section u _ j hu hi, Function.update_self,
      gaussianThresholdSectionProbability_update_levels_ignored]
    rfl
  have hdiag : gaussianThresholdMixed u b j j =
      (-b j * gaussianPDFReal 0 1 (b j)) * gaussianFiniteThresholdCDF s v d +
      gaussianPDFReal 0 1 (b j) * ∑ k, gaussianFiniteThresholdFirst s v d k * (-ρ k) := by
    have hd' : HasDerivAt (fun t => gaussianThresholdFirst u (Function.update b j t) j)
        ((-b j * gaussianPDFReal 0 1 (b j)) * gaussianFiniteThresholdCDF s v d +
          gaussianPDFReal 0 1 (b j) * ∑ k, gaussianFiniteThresholdFirst s v d k * (-ρ k)) (b j) := by
      rw [he]
      simpa only [Function.comp_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul] using hd
    exact hd'.deriv
  have hj0 : gaussianFiniteThresholdFirst s v d j = 0 :=
    gaussianFiniteThresholdFirst_outside s v d j (by simp [s])
  have hsum : (∑ k ∈ s, gaussianFiniteThresholdFirst s v d k * (-ρ k)) =
      ∑ k, gaussianFiniteThresholdFirst s v d k * (-ρ k) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    have hkj : k = j := by simpa [s] using hk
    subst k
    simp [hj0]
  rw [← hsum] at hdiag
  have hmixed : gaussianPDFReal 0 1 (b j) * (∑ k ∈ s, gaussianFiniteThresholdFirst s v d k * (-ρ k)) =
      -∑ l ∈ s, faceDot (u j) (u l) * gaussianThresholdMixed u b j l := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    rw [gaussianThresholdMixed_eq_residualFirst u b j l (Ne.symm (Finset.mem_erase.mp hl).1) hu hi]
    dsimp only [ρ]
    rw [faceDot_comm (u l) (u j)]
    ring
  rw [hmixed] at hdiag
  have hfval : gaussianThresholdFirst u b j = gaussianPDFReal 0 1 (b j) * gaussianFiniteThresholdCDF s v d :=
    gaussianThresholdFirst_eq_section u b j hu hi
  rw [hfval]
  exact hdiag.trans (by ring)

theorem hasDerivAt_gaussianThresholdFirst_update_diagonal {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    HasDerivAt (fun t => gaussianThresholdFirst u (Function.update b j t) j)
      (gaussianThresholdMixed u b j j) (b j) := by
  let s := Finset.univ.erase j
  let v := gaussianThresholdResidualNormals u j
  let d := gaussianThresholdResidualLevels u b j
  let p : ℝ → Vector m := fun t k => b k - t * faceDot (u k) (u j)
  have hp : HasDerivAt p (fun k => -faceDot (u k) (u j)) (b j) := by
    apply hasDerivAt_pi.mpr
    intro k
    simpa only [p, id_eq, zero_sub, one_mul] using
      ((hasDerivAt_const (b j) (b k)).sub ((hasDerivAt_id (b j)).mul_const (faceDot (u k) (u j))))
  have hf := hasFDerivAt_gaussianResidualThresholdCDF u hi j d
  have hf' : HasFDerivAt (gaussianFiniteThresholdCDF s v)
      (∑ k, gaussianFiniteThresholdFirst s v d k • (ContinuousLinearMap.proj k : Vector m →L[ℝ] ℝ)) (p (b j)) := hf
  have hc := hf'.comp_hasDerivAt (b j) hp
  have hd := ((hasDerivAt_standardRealGaussian_density (b j)).mul hc).differentiableAt
  have he : (fun t => gaussianThresholdFirst u (Function.update b j t) j) =
      fun t => gaussianPDFReal 0 1 t * gaussianFiniteThresholdCDF s v (p t) := by
    funext t
    rw [gaussianThresholdFirst_eq_section u _ j hu hi, Function.update_self,
      gaussianThresholdSectionProbability_update_levels_ignored]
    rfl
  change DifferentiableAt ℝ (fun t => gaussianPDFReal 0 1 t * gaussianFiniteThresholdCDF s v (p t)) (b j) at hd
  rw [← he] at hd
  exact hd.hasDerivAt

theorem hasDerivAt_gaussianThresholdFirst_update_mixed {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) (c : ℝ) :
    HasDerivAt (fun t => gaussianThresholdFirst u (Function.update b l t) j)
      (gaussianThresholdMixed u (Function.update b l c) j l) c := by
  by_cases hjl : j = l
  · subst l
    have hd := hasDerivAt_gaussianThresholdFirst_update_diagonal u (Function.update b j c) j hu hi
    simpa only [Function.update_self, Function.update_idem] using hd
  · have hd := hasDerivAt_gaussianThresholdFirst_update u (Function.update b l c) j l hjl hu hi
    rw [← gaussianThresholdMixed_eq_section u (Function.update b l c) j l hjl hu hi] at hd
    simpa only [Function.update_self, Function.update_idem] using hd

theorem continuous_gaussianThresholdMixed_of_ne {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (j l : Fin m) (hjl : j ≠ l)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Continuous (fun b => gaussianThresholdMixed u b j l) := by
  let s := Finset.univ.erase j
  let v := gaussianThresholdResidualNormals u j
  let σ := gaussianThresholdResidualScale u j l
  have hσ : 0 < σ := gaussianThresholdResidualScale_pos u hi j l (Ne.symm hjl)
  have hnorm : vectorNormSq (v l) = σ ^ 2 := (Real.sq_sqrt (vectorNormSq_nonneg _)).symm
  have hl : l ∈ s := Finset.mem_erase.mpr ⟨Ne.symm hjl, Finset.mem_univ _⟩
  have hp (k : Fin m) (hk : k ∈ s.erase l) : gaussianNormalProjection (σ⁻¹ • v l) (v k) ≠ 0 :=
    gaussianNormalProjection_twice_ne_zero_of_independent u hi j l k
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1 (Finset.mem_erase.mp hk).1 _
  have hc := continuous_gaussianFiniteThresholdFirst s v l hl hσ hnorm hp
  have hlevels : Continuous (fun b : Vector m => gaussianThresholdResidualLevels u b j) := by
    unfold gaussianThresholdResidualLevels
    fun_prop
  have hpdf : Continuous (fun b : Vector m => gaussianPDFReal 0 1 (b j)) :=
    (continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)).comp
      (continuous_apply j)
  have ht := hpdf.mul (hc.comp hlevels)
  have he : (fun b => gaussianThresholdMixed u b j l) = fun b => gaussianPDFReal 0 1 (b j) *
      gaussianFiniteThresholdFirst s v (gaussianThresholdResidualLevels u b j) l :=
    funext (fun b => gaussianThresholdMixed_eq_residualFirst u b j l hjl hu hi)
  rw [he]
  exact ht

theorem continuous_gaussianThresholdMixed_diagonal {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Continuous (fun b => gaussianThresholdMixed u b j j) := by
  have hlead := (continuous_apply j).neg.mul (continuous_gaussianThresholdFirst u j hu hi)
  have hsum : Continuous (fun b : Vector m =>
      ∑ l ∈ Finset.univ.erase j, faceDot (u j) (u l) * gaussianThresholdMixed u b j l) :=
    continuous_finset_sum _ (fun l hl => continuous_const.mul
      (continuous_gaussianThresholdMixed_of_ne u j l (Ne.symm (Finset.mem_erase.mp hl).1) hu hi))
  have he : (fun b => gaussianThresholdMixed u b j j) = fun b => -b j * gaussianThresholdFirst u b j -
      ∑ l ∈ Finset.univ.erase j, faceDot (u j) (u l) * gaussianThresholdMixed u b j l :=
    funext (fun b => gaussianThreshold_diagonal_identity u b j hu hi)
  rw [he]
  exact hlead.sub hsum

theorem continuous_gaussianThresholdMixed {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Continuous (fun b => gaussianThresholdMixed u b j l) := by
  by_cases hjl : j = l
  · subst l
    exact continuous_gaussianThresholdMixed_diagonal u j hu hi
  · exact continuous_gaussianThresholdMixed_of_ne u j l hjl hu hi

/-- Schwarz symmetry for the actual mixed threshold derivatives, obtained
from their proved genuine derivatives and joint continuity. -/
theorem gaussianThresholdMixed_symm {m n : ℕ}
    (u : Fin m → Vector (n + 1)) (b : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (j l : Fin m) :
    gaussianThresholdMixed u b j l = gaussianThresholdMixed u b l j :=
  continuous_second_coordinate_derivatives_symmetric (gaussianThresholdCDF u)
    (fun d k => gaussianThresholdFirst u d k) (fun d k i => gaussianThresholdMixed u d k i)
    (fun d k c => hasDerivAt_gaussianThresholdCDF_update_first u d k (hu k) hi c)
    (fun k => continuous_gaussianThresholdFirst u k (hu k) hi)
    (fun d k i c => hasDerivAt_gaussianThresholdFirst_update_mixed u d k i (hu k) hi c)
    (fun k i => continuous_gaussianThresholdMixed u k i (hu k) hi) b j l

end
end RectangleCLT.Companion.SplitV4
