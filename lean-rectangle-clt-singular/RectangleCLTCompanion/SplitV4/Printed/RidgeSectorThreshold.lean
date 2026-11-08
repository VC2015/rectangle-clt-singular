import RectangleCLTCompanion.SplitV4.Printed.RidgeSectorApplication
import RectangleCLTCompanion.SplitV4.AveragedThresholdBound

/-! Disjoint outward sectors, their incidence bound, and the printed adaptive
layer estimate. Existing rectangular ridge events remain unchanged. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

open SignedSurface in
theorem planeSector_mem_adaptiveOutwardTube
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [DecidableEq ι]
    (normal : ι → E) (offset : ι → ℝ) (R : E → ℝ)
    (active : Finset ι) {j k : ι} (hj : j ∈ active) (hk : k ∈ active)
    {x : E} (hx : x ∈ exactStratum normal offset active)
    (hu : ‖normal j‖ = 1) (hv : ‖normal k‖ = 1)
    (hp : normal j + normal k ≠ 0) (hm : normal j - normal k ≠ 0)
    {ρ : ℝ} (hρ : ⟪normal j, normal k⟫_ℝ = ρ) (hlo : -1 < ρ) (hhi : ρ < 1)
    {st : ℝ × ℝ} (hst : st ∈ planeSector (Real.arccos ρ) (1 / (4 * R x))) :
    x + ridgeDisplacement (normal j) (normal k) st ∈
      adaptiveOutwardTube normal offset R active := by
  obtain ⟨a, b, ha, hb, heq⟩ := planeSector_maps_into_cone
    (normal j) (normal k) hu hv hρ hlo hhi hst
  let c : ι → ℝ := fun i => (if i = j then a else 0) + (if i = k then b else 0)
  have hdisp : coneDisplacement normal active c =
      ridgeDisplacement (normal j) (normal k) st := by
    rw [heq]
    simp only [coneDisplacement, c, add_smul, ite_smul, zero_smul]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' active j, Finset.sum_ite_eq' active k]
    simp [hj, hk]
  have hnorm := ridgeDisplacement_norm (normal j) (normal k) hu hv hp hm st
  refine ⟨x, hx, c, ?_, ?_, ?_, ?_⟩
  · intro i hi
    dsimp only [c]
    split_ifs <;> positivity
  · rw [hdisp]
    intro hz
    rw [hz, norm_zero] at hnorm
    linarith [(planeSector_radius hst).1]
  · rw [hdisp, hnorm]
    exact (planeSector_radius hst).2.le
  · rw [hdisp]

theorem gaussianPairSectorEvent_mem_adaptiveOutwardTube {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    {g : Vector r} (hg : g ∈ gaussianPairSectorEvent u b j l) :
    projectionEuclideanVector g ∈ adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b
      (euclideanThresholdRadius u) {j, l} := by
  have hx := gaussianPairBase_exactStratum u b j l hu hv hp hm g hg.1
  have hρ := thresholdPair_correlation_bounds u j l hu hv hp hm
  have hmemb := planeSector_mem_adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b
    (euclideanThresholdRadius u) {j, l} (j := j) (k := l) (by simp) (by simp) hx
    (thresholdEuclideanNormal_unit _ hu) (thresholdEuclideanNormal_unit _ hv) hp hm
    (SignedSurface.faceDot_eq_euclidean_inner (u j) (u l)).symm hρ.1 hρ.2 hg.2
  rw [← gaussianPairBase_reconstruct u b j l hu hv g] at hmemb
  exact hmemb

def gaussianThresholdSectorStratumEvent (u : Fin m → Vector r) (b : Vector m) (q : Fin m × Fin m) : Set (Vector r) :=
  if q.1 = q.2 then gaussianFacetEvent u b q.1 else gaussianPairSectorEvent u b q.1 q.2

theorem gaussianThresholdSectorStratumEvent_mem_tube (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (q : Fin m × Fin m) {g : Vector r} (hg : g ∈ gaussianThresholdSectorStratumEvent u b q) :
    projectionEuclideanVector g ∈ adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b
      (euclideanThresholdRadius u) {q.1, q.2} := by
  by_cases hq : q.1 = q.2
  · simp only [gaussianThresholdSectorStratumEvent, if_pos hq] at hg
    simpa only [hq, Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using
      gaussianFacetEvent_mem_adaptiveOutwardTube u b q.1 (hu q.1) hg
  · simp only [gaussianThresholdSectorStratumEvent, if_neg hq] at hg
    exact gaussianPairSectorEvent_mem_adaptiveOutwardTube u b q.1 q.2 (hu q.1) (hu q.2)
      (hp _ _ hq) (hm _ _ hq) hg

theorem gaussianThresholdSectorStratumEvent_shared_point (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (q q' : Fin m × Fin m) {g : Vector r}
    (hg : g ∈ gaussianThresholdSectorStratumEvent u b q) (hg' : g ∈ gaussianThresholdSectorStratumEvent u b q') :
    q = q' ∨ q = q'.swap := by
  have hq := gaussianThresholdSectorStratumEvent_mem_tube u b hu hp hm q hg
  have hq' := gaussianThresholdSectorStratumEvent_mem_tube u b hu hp hm q' hg'
  have he : ({q.1, q.2} : Finset (Fin m)) = {q'.1, q'.2} := by
    by_contra hn
    exact Set.disjoint_left.mp (adaptiveOutwardTube_disjoint (fun k => projectionEuclideanVector (u k)) b
      (euclideanThresholdRadius u) hn) hq hq'
  have hs : ({q.1, q.2} : Set (Fin m)) = {q'.1, q'.2} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      congrArg (fun s : Finset (Fin m) => (s : Set (Fin m))) he
  rcases Set.pair_eq_pair_iff.mp hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl (Prod.ext h₁ h₂)
  · exact Or.inr (Prod.ext h₁ h₂)

/-- The actual finite incidence bound: all facets plus ordered pair-ridges
contribute at most twice the adaptive outer-layer indicator at every point.
The constant two only counts the two orders of a pair, never the faces. -/
theorem gaussianThresholdSectorStratumEvent_indicator_sum_le (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (g : Vector r) :
    (∑ q : Fin m × Fin m, (gaussianThresholdSectorStratumEvent u b q).indicator (fun _ => (1 : ℝ)) g) ≤
      2 * (thresholdOuterLayer u b (1 / thresholdProjectionRadius u g)).indicator (fun _ => (1 : ℝ)) g := by
  by_cases hex : ∃ q, g ∈ gaussianThresholdSectorStratumEvent u b q
  · obtain ⟨q₀, hq₀⟩ := hex
    have houter := adaptiveThresholdTube_mem_outerLayer u b hu {q₀.1, q₀.2}
      (gaussianThresholdSectorStratumEvent_mem_tube u b hu hp hm q₀ hq₀)
    rw [Set.indicator_of_mem houter, mul_one]
    have hpoint (q : Fin m × Fin m) :
        (gaussianThresholdSectorStratumEvent u b q).indicator (fun _ => (1 : ℝ)) g ≤
          (if q = q₀ then 1 else 0) + (if q = q₀.swap then 1 else 0) := by
      by_cases hq : g ∈ gaussianThresholdSectorStratumEvent u b q
      · rw [Set.indicator_of_mem hq]
        rcases gaussianThresholdSectorStratumEvent_shared_point u b hu hp hm q q₀ hq hq₀ with h | h
        · subst q
          simp
          split_ifs <;> norm_num
        · subst q
          simp
          split_ifs <;> norm_num
      · rw [Set.indicator_of_not_mem hq]
        split_ifs <;> norm_num
    calc
      _ ≤ ∑ q : Fin m × Fin m, ((if q = q₀ then (1 : ℝ) else 0) +
          (if q = q₀.swap then 1 else 0)) := Finset.sum_le_sum (fun q _ => hpoint q)
      _ = 2 := by norm_num [Finset.sum_add_distrib]
  · have hn (q : Fin m × Fin m) : g ∉ gaussianThresholdSectorStratumEvent u b q := fun h => hex ⟨q, h⟩
    simp only [Set.indicator_of_not_mem (hn _), Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => by norm_num) g)

theorem gaussianThresholdSectorStratumEvent_indicator_sum_eq (u : Fin m → Vector r) (b : Vector m)
    (P : Vector r → ℝ) (g : Vector r) :
    (∑ q : Fin m × Fin m, (gaussianThresholdSectorStratumEvent u b q).indicator P g) =
      (∑ j, (gaussianFacetEvent u b j).indicator P g) +
        ∑ j, ∑ l, if j = l then 0 else (gaussianPairSectorEvent u b j l).indicator P g := by
  rw [Fintype.sum_prod_type]
  have hrow (j : Fin m) : (∑ l, (gaussianThresholdSectorStratumEvent u b (j, l)).indicator P g) =
      (gaussianFacetEvent u b j).indicator P g +
        ∑ l, if j = l then 0 else (gaussianPairSectorEvent u b j l).indicator P g := by
    calc
      _ = ∑ l, ((if j = l then (gaussianFacetEvent u b j).indicator P g else 0) +
          (if j = l then 0 else (gaussianPairSectorEvent u b j l).indicator P g)) := by
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : j = l <;> simp [gaussianThresholdSectorStratumEvent, h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [eq_comm]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]

theorem gaussianThreshold_facet_sector_indicator_sum_le (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (g : Vector r) :
    (∑ j, (gaussianFacetEvent u b j).indicator (fun _ => (1 : ℝ)) g) +
      (∑ j, ∑ l, if j = l then 0 else (gaussianPairSectorEvent u b j l).indicator (fun _ => (1 : ℝ)) g) ≤
      2 * (thresholdOuterLayer u b (1 / thresholdProjectionRadius u g)).indicator (fun _ => (1 : ℝ)) g := by
  rw [← gaussianThresholdSectorStratumEvent_indicator_sum_eq]
  exact gaussianThresholdSectorStratumEvent_indicator_sum_le u b hu hp hm g

theorem gaussianThreshold_facet_sector_weighted_sum_le (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (P : Vector r → ℝ) (hP : ∀ g, 0 ≤ P g) (g : Vector r) :
    (∑ j, (gaussianFacetEvent u b j).indicator P g) +
      (∑ j, ∑ l, if j = l then 0 else (gaussianPairSectorEvent u b j l).indicator P g) ≤
      2 * (thresholdOuterLayer u b (1 / thresholdProjectionRadius u g)).indicator P g := by
  have he (S : Set (Vector r)) : S.indicator P g = P g * S.indicator (fun _ => (1 : ℝ)) g := by
    by_cases hg : g ∈ S <;> simp [hg]
  rw [← gaussianThresholdSectorStratumEvent_indicator_sum_eq]
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (gaussianThresholdSectorStratumEvent_indicator_sum_le u b hu hp hm g) (hP g)
  convert hh using 1 <;> ring


end
end RectangleCLT.Companion.SplitV4.Printed
