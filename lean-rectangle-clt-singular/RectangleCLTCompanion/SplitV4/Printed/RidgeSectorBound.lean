import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorThreshold
import RectangleCLTCompanion.SplitV4.Printed.FacetRadius

/-! Appendix B.5 assembled from the full angular sectors and the radial-tail
moment proof, preserving the earlier rectangular proof. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def sectorThresholdGeometryConstant : ℝ :=
  thresholdGeometryConstant + (2048 / 27 : ℝ) * Real.exp ((9 : ℝ) / 32)

theorem sectorThresholdGeometryConstant_pos : 0 < sectorThresholdGeometryConstant := by
  unfold sectorThresholdGeometryConstant
  have := thresholdGeometryConstant_pos
  positivity

theorem abs_gaussianThreshold_facet_term_le_sector_mass {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    |(b j ^ 2 - 1) * gaussianThresholdFirst u b j| ≤ sectorThresholdGeometryConstant *
      ∫ g, (gaussianFacetEvent u b j).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  apply (abs_gaussianThreshold_facet_term_le_mass_from_radial_tail hm u b j hu hi).trans
  apply mul_le_mul_of_nonneg_right
  · unfold sectorThresholdGeometryConstant
    exact le_add_of_nonneg_right (by positivity)
  · apply integral_nonneg
    intro g
    exact Set.indicator_nonneg (fun x _ => pow_nonneg
      (zero_le_one.trans (thresholdProjectionRadius_ge_one u x)) 3) g

theorem abs_gaussianThreshold_pair_term_le_sector_mass {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m) (j l : Fin m)
    (hu : ∀ k, vectorNormSq (u k) = 1) (hi : LinearIndependent ℝ u) :
    |(1 - faceDot (u j) (u l)) * (b j + b l) * gaussianThresholdMixed u b j l| ≤
      sectorThresholdGeometryConstant * (if j = l then 0 else
        ∫ g, (gaussianPairSectorEvent u b j l).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
          ∂standardGaussian (n + 1)) := by
  classical
  by_cases hjl : j = l
  · subst l
    have hself : faceDot (u j) (u j) = 1 := by
      simpa only [faceDot, vectorNormSq, pow_two] using hu j
    simp [hself]
  rw [if_neg hjl]
  have hρ : 0 ≤ 1 - faceDot (u j) (u l) := by
    obtain ⟨hp, hm⟩ := thresholdPair_sum_sub_ne_zero_of_independent u hi j l hjl
    linarith [(thresholdPair_correlation_bounds u j l (hu j) (hu l) hp hm).2]
  have hmix := gaussianThresholdMixed_nonneg_of_ne u b j l hjl (hu j) hi
  have hmass := gaussianThresholdMixed_le_weighted_sector_event hm u b j l hjl (hu j) (hu l) hi
  let C : ℝ := (2048 / 27 : ℝ) * Real.exp ((9 : ℝ) / 32)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hh := mul_le_mul_of_nonneg_left hmass hC
  have he : C * ((27 / 2048 : ℝ) * Real.exp (-(9 : ℝ) / 32)) = 1 := by
    dsimp [C]
    rw [mul_mul_mul_comm, ← Real.exp_add]
    norm_num
  have hcancel : C * ((27 / 2048 : ℝ) * Real.exp (-(9 : ℝ) / 32) *
      (1 - faceDot (u j) (u l)) * |b j + b l| * gaussianThresholdMixed u b j l) =
      (1 - faceDot (u j) (u l)) * |b j + b l| * gaussianThresholdMixed u b j l := by
    calc
      _ = (C * ((27 / 2048 : ℝ) * Real.exp (-(9 : ℝ) / 32))) *
          ((1 - faceDot (u j) (u l)) * |b j + b l| * gaussianThresholdMixed u b j l) := by ring
      _ = _ := by rw [he, one_mul]
  rw [hcancel] at hh
  have hI : 0 ≤ ∫ g, (gaussianPairSectorEvent u b j l).indicator
      (fun g => thresholdProjectionRadius u g ^ 3) g ∂standardGaussian (n + 1) := by
    apply integral_nonneg
    intro g
    exact Set.indicator_nonneg (fun x _ => pow_nonneg
      (zero_le_one.trans (thresholdProjectionRadius_ge_one u x)) 3) g
  have hCbound : C ≤ sectorThresholdGeometryConstant := by
    dsimp [sectorThresholdGeometryConstant, C]
    linarith [thresholdGeometryConstant_pos]
  have hf := hh.trans (mul_le_mul_of_nonneg_right hCbound hI)
  simpa only [abs_mul, abs_of_nonneg hρ, abs_of_nonneg hmix] using hf

theorem gaussianThresholdDerivative_le_sectorAdaptiveLayer {m n : ℕ}
    (hm : 1 ≤ m) (u : Fin m → Vector (n + 1)) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    |gaussianThresholdDerivative u b| ≤ (2 * sectorThresholdGeometryConstant) *
      ∫ g, (gaussianAdaptiveOuterEvent u b).indicator (fun g => thresholdProjectionRadius u g ^ 3) g
        ∂standardGaussian (n + 1) := by
  classical
  let γ := standardGaussian (n + 1)
  let W : Vector (n + 1) → ℝ := fun g => thresholdProjectionRadius u g ^ 3
  let F : Fin m → Vector (n + 1) → ℝ := fun j => (gaussianFacetEvent u b j).indicator W
  let P : Fin m → Fin m → Vector (n + 1) → ℝ := fun j l =>
    if j = l then 0 else (gaussianPairSectorEvent u b j l).indicator W
  have hW : Integrable W γ := (thresholdProjectionRadius_second_third_moments_from_radial_tail hm u).2.1
  have hW0 (g) : 0 ≤ W g := pow_nonneg
    (zero_le_one.trans (thresholdProjectionRadius_ge_one u g)) 3
  have hF (j : Fin m) : Integrable (F j) γ := hW.indicator (measurableSet_gaussianFacetEvent u b j)
  have hP (j l : Fin m) : Integrable (P j l) γ := by
    by_cases h : j = l
    · simpa only [P, if_pos h] using (integrable_zero (Vector (n + 1)) ℝ γ)
    · simpa only [P, if_neg h] using hW.indicator (measurableSet_gaussianPairSectorEvent u b j l)
  have hP0 (j l : Fin m) (g) : 0 ≤ P j l g := by
    by_cases h : j = l
    · simp only [P, if_pos h, Pi.zero_apply, le_refl]
    · simp only [P, if_neg h]
      exact Set.indicator_nonneg (fun x _ => hW0 x) g
  have hpmass (j l : Fin m) : (∫ g, P j l g ∂γ) =
      if j = l then 0 else ∫ g, (gaussianPairSectorEvent u b j l).indicator W g ∂γ := by
    by_cases h : j = l
    · simp only [P, if_pos h, Pi.zero_apply, integral_zero]
    · simp only [P, if_neg h]
  let A : Fin m → ℝ := fun j => (b j ^ 2 - 1) * gaussianThresholdFirst u b j
  let B : Fin m → Fin m → ℝ := fun j l =>
    (1 - faceDot (u j) (u l)) * (b j + b l) * gaussianThresholdMixed u b j l
  have hA : (∑ j, |A j|) ≤ sectorThresholdGeometryConstant * ∑ j, ∫ g, F j g ∂γ := by
    calc
      _ ≤ ∑ j, sectorThresholdGeometryConstant * ∫ g, F j g ∂γ :=
        Finset.sum_le_sum (fun j _ => by
          simpa only [A, F, γ, W] using abs_gaussianThreshold_facet_term_le_sector_mass hm u b j (hu j) hi)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hB : (∑ j, ∑ l, |B j l|) ≤ sectorThresholdGeometryConstant * ∑ j, ∑ l, ∫ g, P j l g ∂γ := by
    calc
      _ ≤ ∑ j, ∑ l, sectorThresholdGeometryConstant * ∫ g, P j l g ∂γ := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro l _
        rw [hpmass]
        simpa only [B, γ, W] using abs_gaussianThreshold_pair_term_le_sector_mass hm u b j l hu hi
      _ = _ := by simp only [Finset.mul_sum]
  have hdouble : |∑ j, ∑ l, B j l| ≤ ∑ j, ∑ l, |B j l| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))
  have htri : |gaussianThresholdDerivative u b| ≤ (∑ j, |A j|) + ∑ j, ∑ l, |B j l| := by
    have hid : gaussianThresholdDerivative u b = (∑ j, A j) - (1 / 2 : ℝ) * (∑ j, ∑ l, B j l) :=
      gaussianThresholdDerivative_identity u b hu hi
    rw [hid]
    apply (abs_sub (∑ j, A j) ((1 / 2 : ℝ) * (∑ j, ∑ l, B j l))).trans
    apply add_le_add
    · exact Finset.abs_sum_le_sum_abs _ _
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      apply (mul_le_mul_of_nonneg_left hdouble (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
      exact mul_le_of_le_one_left (Finset.sum_nonneg (fun j _ =>
        Finset.sum_nonneg (fun l _ => abs_nonneg (B j l)))) (by norm_num)
  have hFsum : Integrable (fun g => ∑ j, F j g) γ := integrable_finset_sum _ (fun j _ => hF j)
  have hPsum : Integrable (fun g => ∑ j, ∑ l, P j l g) γ :=
    integrable_finset_sum _ (fun j _ => integrable_finset_sum _ (fun l _ => hP j l))
  have hOuter : Integrable ((gaussianAdaptiveOuterEvent u b).indicator W) γ :=
    hW.indicator (measurableSet_gaussianAdaptiveOuterEvent u b)
  have hhp (j l : Fin m) (h : j ≠ l) :
      projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0 :=
    (thresholdPair_sum_sub_ne_zero_of_independent u hi j l h).1
  have hhm (j l : Fin m) (h : j ≠ l) :
      projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0 :=
    (thresholdPair_sum_sub_ne_zero_of_independent u hi j l h).2
  have hpoint (g : Vector (n + 1)) : (∑ j, F j g) + (∑ j, ∑ l, P j l g) ≤
      2 * (gaussianAdaptiveOuterEvent u b).indicator W g := by
    have hh := gaussianThreshold_facet_sector_weighted_sum_le u b hu hhp hhm W hW0 g
    have heval : (thresholdOuterLayer u b (1 / thresholdProjectionRadius u g)).indicator W g =
        (gaussianAdaptiveOuterEvent u b).indicator W g := by
      by_cases hg : g ∈ gaussianAdaptiveOuterEvent u b
      · have hg' : g ∈ thresholdOuterLayer u b (1 / thresholdProjectionRadius u g) :=
          (mem_gaussianAdaptiveOuterEvent u b g).mp hg
        rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg']
      · have hg' : g ∉ thresholdOuterLayer u b (1 / thresholdProjectionRadius u g) :=
          fun h => hg ((mem_gaussianAdaptiveOuterEvent u b g).mpr h)
        rw [Set.indicator_of_not_mem hg, Set.indicator_of_not_mem hg']
    rw [heval] at hh
    simpa only [F, P, ite_apply, Pi.zero_apply] using hh
  have hmass : (∑ j, ∫ g, F j g ∂γ) + (∑ j, ∑ l, ∫ g, P j l g ∂γ) ≤
      2 * ∫ g, (gaussianAdaptiveOuterEvent u b).indicator W g ∂γ := by
    calc
      _ = ∫ g, (∑ j, F j g) + ∑ j, ∑ l, P j l g ∂γ := by
        rw [integral_add hFsum hPsum, integral_finset_sum _ (fun j _ => hF j),
          integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun l _ => hP j l))]
        simp_rw [integral_finset_sum _ (fun l _ => hP _ l)]
      _ ≤ ∫ g, 2 * (gaussianAdaptiveOuterEvent u b).indicator W g ∂γ :=
        integral_mono (hFsum.add hPsum) (hOuter.const_mul 2) hpoint
      _ = _ := integral_const_mul _ _
  calc
    _ ≤ sectorThresholdGeometryConstant *
        ((∑ j, ∫ g, F j g ∂γ) + ∑ j, ∑ l, ∫ g, P j l g ∂γ) :=
      htri.trans ((add_le_add hA hB).trans_eq (by ring))
    _ ≤ sectorThresholdGeometryConstant * (2 * ∫ g, (gaussianAdaptiveOuterEvent u b).indicator W g ∂γ) :=
      mul_le_mul_of_nonneg_left hmass sectorThresholdGeometryConstant_pos.le
    _ = _ := by ring


end
end RectangleCLT.Companion.SplitV4.Printed
