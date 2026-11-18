import RectangleCLTArxivV1.SupplementalHFourthTransportData

/-! Genuine disjoint outward tubes for arbitrary dependent unit normals.
Only nonparallel pairs index a ridge; parallel coefficient terms vanish
separately in the Green decomposition. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem fourthFacetEvent_mem_tube {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (j : Fin m) (hu : vectorNormSq (u j)=1)
    {g : Vector r} (hg : g∈fourthFacetEvent u b R j) :
    projectionEuclideanVector g∈adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b R {j} := by
  let t := faceDot (u j) g-b j
  let c : Fin m → ℝ := fun k => if k=j then t else 0
  have hx := gaussianFacetBase_exactStratum u b j hu g hg.1
  have he : coneDisplacement (fun k => projectionEuclideanVector (u k)) {j} c=
      t • projectionEuclideanVector (u j) := by simp [coneDisplacement,c]
  have ht : 0<t := hg.2.1
  have hnrm := thresholdEuclideanNormal_unit _ hu
  have hn : projectionEuclideanVector (u j)≠0 := by
    intro hz
    rw [hz,norm_zero] at hnrm
    norm_num at hnrm
  refine ⟨projectionEuclideanVector (gaussianFacetBase u b j g),hx,c,?_,?_,?_,?_⟩
  · intro k hk
    have hkj := Finset.mem_singleton.mp hk
    simpa only [c,hkj,if_pos rfl] using ht.le
  · rw [he]
    exact smul_ne_zero ht.ne' hn
  · rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos ht,hnrm,mul_one]
    exact hg.2.2
  · rw [he]
    exact gaussianFacetBase_reconstruct u b j g

theorem fourthPairEvent_mem_tube {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    {g : Vector r} (hg : g∈fourthPairEvent u b R j l) :
    projectionEuclideanVector g∈adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b R {j,l} := by
  have hx := gaussianPairBase_exactStratum u b j l hu hv hp hm g hg.1
  have ht := ridgeRectangle_mem_adaptiveOutwardTube (fun k => projectionEuclideanVector (u k))
    b R hR {j,l} (j := j) (k := l) (by simp) (by simp) hx
    (thresholdEuclideanNormal_unit _ hu) (thresholdEuclideanNormal_unit _ hv) hp hm hg.2
  rw [← gaussianPairBase_reconstruct u b j l hu hv g] at ht
  exact ht

def fourthStratumEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (q : Fin m × Fin m) : Set (Vector r) := by
  classical
  exact if q.1=q.2 then fourthFacetEvent u b R q.1 else
    if projectionEuclideanVector (u q.1)+projectionEuclideanVector (u q.2)≠0 ∧
        projectionEuclideanVector (u q.1)-projectionEuclideanVector (u q.2)≠0 then
      fourthPairEvent u b R q.1 q.2 else ∅

theorem measurableSet_fourthStratumEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : Continuous R) (q : Fin m × Fin m) :
    MeasurableSet (fourthStratumEvent u b R q) := by
  classical
  unfold fourthStratumEvent
  split_ifs
  · exact measurableSet_fourthFacetEvent u b R hR q.1
  · exact measurableSet_fourthPairEvent u b R hR q.1 q.2
  · exact MeasurableSet.empty

theorem fourthStratumEvent_mem_tube {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x)
    (hu : ∀ j,vectorNormSq (u j)=1) (q : Fin m × Fin m)
    {g : Vector r} (hg : g∈fourthStratumEvent u b R q) :
    projectionEuclideanVector g∈adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b R {q.1,q.2} := by
  classical
  unfold fourthStratumEvent at hg
  split_ifs at hg with hq hpair
  · simpa only [hq,Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using
      fourthFacetEvent_mem_tube u b R q.1 (hu q.1) hg
  · exact fourthPairEvent_mem_tube u b R hR q.1 q.2 (hu q.1) (hu q.2) hpair.1 hpair.2 hg
  · exact False.elim hg

theorem fourthStratumEvent_shared_point {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x) (hu : ∀ j,vectorNormSq (u j)=1)
    (q q' : Fin m × Fin m) {g : Vector r}
    (hg : g∈fourthStratumEvent u b R q) (hg' : g∈fourthStratumEvent u b R q') : q=q' ∨ q=q'.swap := by
  have hq := fourthStratumEvent_mem_tube u b R hR hu q hg
  have hq' := fourthStratumEvent_mem_tube u b R hR hu q' hg'
  have he : ({q.1,q.2} : Finset (Fin m))={q'.1,q'.2} := by
    by_contra hn
    exact disjoint_left.mp (adaptiveOutwardTube_disjoint (fun k => projectionEuclideanVector (u k)) b R hn) hq hq'
  have hs : ({q.1,q.2} : Set (Fin m))={q'.1,q'.2} := by
    simpa only [Finset.coe_insert,Finset.coe_singleton] using congrArg (fun s : Finset (Fin m) => (s : Set (Fin m))) he
  rcases pair_eq_pair_iff.mp hs with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl (Prod.ext h₁ h₂)
  · exact Or.inr (Prod.ext h₁ h₂)

def fourthOuterLayer {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) : Set (Vector r) :=
  {g | g∈thresholdOuterLayer u b (1/fourthTransportRadius R g)}

theorem measurableSet_fourthOuterLayer {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : Continuous R) :
    MeasurableSet (fourthOuterLayer u b R) := by
  have hrec : Measurable (fun g => 1/fourthTransportRadius R g) :=
    measurable_const.div (continuous_fourthTransportRadius R hR).measurable
  change MeasurableSet ({g | ∀ j,faceDot (u j) g≤b j+1/fourthTransportRadius R g} \ thresholdPolyhedron u b)
  simp only [setOf_forall]
  exact (MeasurableSet.iInter (fun j => measurableSet_le (measurable_thresholdDot _) (measurable_const.add hrec))).diff
    (measurableSet_thresholdPolyhedron _ _)

theorem fourthStratumEvent_mem_outerLayer {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ j,vectorNormSq (u j)=1)
    (q : Fin m × Fin m) {g : Vector r} (hg : g∈fourthStratumEvent u b R q) :
    g∈fourthOuterLayer u b R := by
  have ht := adaptiveOutwardTube_subset_outerLayer (fun k => projectionEuclideanVector (u k)) b
    (fun j => thresholdEuclideanNormal_unit _ (hu j)) R hR hRadd {q.1,q.2}
    (fourthStratumEvent_mem_tube u b R hR hu q hg)
  have hd (k : Fin m) : ⟪projectionEuclideanVector (u k),projectionEuclideanVector g⟫_ℝ=faceDot (u k) g :=
    (faceDot_eq_euclidean_inner _ _).symm
  change (∀ k,⟪_,_⟫_ℝ≤b k+_) ∧ ¬(∀ k,⟪_,_⟫_ℝ≤b k) at ht
  simpa only [hd] using ht

/-- At most two ordered representations belong to one true outward tube,
even for dependent signed normals and vanishing pair gaps. -/
theorem fourthStratumEvent_indicator_sum_le {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ j,vectorNormSq (u j)=1)
    (P : Vector r → ℝ) (hP : ∀ g,0≤P g) (g : Vector r) :
    (∑ q : Fin m × Fin m,(fourthStratumEvent u b R q).indicator P g)≤
      2*(fourthOuterLayer u b R).indicator P g := by
  classical
  have hpoint : (∑ q : Fin m × Fin m,(fourthStratumEvent u b R q).indicator (fun _ => (1:ℝ)) g)≤
      2*(fourthOuterLayer u b R).indicator (fun _ => (1:ℝ)) g := by
    by_cases hex : ∃ q,g∈fourthStratumEvent u b R q
    · obtain ⟨q₀,hq₀⟩ := hex
      rw [indicator_of_mem (fourthStratumEvent_mem_outerLayer u b R hR hRadd hu q₀ hq₀),mul_one]
      have hc (q : Fin m × Fin m) : (fourthStratumEvent u b R q).indicator (fun _ => (1:ℝ)) g≤
          (if q=q₀ then 1 else 0)+(if q=q₀.swap then 1 else 0) := by
        by_cases hq : g∈fourthStratumEvent u b R q
        · rw [indicator_of_mem hq]
          rcases fourthStratumEvent_shared_point u b R hR hu q q₀ hq hq₀ with h | h
          · subst q; simp; split_ifs <;> norm_num
          · subst q; simp; split_ifs <;> norm_num
        · rw [indicator_of_not_mem hq]
          split_ifs <;> norm_num
      exact (Finset.sum_le_sum (fun q _ => hc q)).trans_eq (by norm_num [Finset.sum_add_distrib])
    · have hn q : g∉fourthStratumEvent u b R q := fun h => hex ⟨q,h⟩
      simp only [indicator_of_not_mem (hn _),Finset.sum_const_zero]
      exact mul_nonneg (by norm_num) (indicator_nonneg (fun _ _ => by norm_num) g)
  have he (S : Set (Vector r)) : S.indicator P g=P g*S.indicator (fun _ => (1:ℝ)) g := by
    by_cases hg : g∈S <;> simp [hg]
  simp_rw [he]
  rw [← Finset.mul_sum]
  convert mul_le_mul_of_nonneg_left hpoint (hP g) using 1 <;> ring

/-- Genuine finite Gaussian Fubini/sum transport for the common fourth
radius. All event tests are integrable consequences of the actual moment. -/
theorem fourthStratumEvent_integral_sum_le {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ j,vectorNormSq (u j)=1)
    (hR4 : Integrable (fun g => fourthTransportRadius R g^4) (standardGaussian r)) :
    (∑ q : Fin m × Fin m, ∫ g,(fourthStratumEvent u b R q).indicator
      (fun g => fourthTransportRadius R g^4) g ∂standardGaussian r)≤
      2*(∫ g,(fourthOuterLayer u b R).indicator (fun g => fourthTransportRadius R g^4) g ∂standardGaussian r) := by
  classical
  have hi q := hR4.indicator (measurableSet_fourthStratumEvent u b R hRm q)
  rw [← integral_finset_sum Finset.univ (fun q _ => hi q),← integral_const_mul]
  exact integral_mono (integrable_finset_sum _ (fun q _ => hi q))
    ((hR4.indicator (measurableSet_fourthOuterLayer u b R hRm)).const_mul 2)
    (fun g => fourthStratumEvent_indicator_sum_le u b R hR hRadd hu _ (fun _ => pow_nonneg (zero_le_one.trans (hR _)) 4) g)

end
end RectangleCLTArxivV1
