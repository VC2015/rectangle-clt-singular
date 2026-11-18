import RectangleCLTArxivV1.SupplementalHTripleTransportGeometry

/-! Ordered triples representing one actual rank-three outward stratum
have at most six orders. The incidence bound is proved, not supplied. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev TripleFaceTuple (m : ℕ) := {τ : Fin 3 → Fin m // Function.Injective τ}
noncomputable instance tripleFaceTupleFintype (m : ℕ) : Fintype (TripleFaceTuple m) := Fintype.ofFinite _

def tripleFaceActive {m : ℕ} (τ : TripleFaceTuple m) : Finset (Fin m) := Finset.univ.image τ.1

theorem tripleFaceTuple_eq_perm_of_active_eq {m : ℕ} (τ τ₀ : TripleFaceTuple m)
    (he : tripleFaceActive τ=tripleFaceActive τ₀) :
    ∃ σ : Equiv.Perm (Fin 3),τ.1=τ₀.1 ∘ σ := by
  classical
  have hex (i : Fin 3) : ∃ j,τ₀.1 j=τ.1 i := by
    have hm : τ.1 i∈tripleFaceActive τ := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    rw [he] at hm
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hm
    exact ⟨j,hj⟩
  choose σ hσ using hex
  have hinj : Function.Injective σ := by
    intro i j hij
    apply τ.2
    rw [← hσ i,← hσ j,hij]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective σ ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨e,funext (fun i => (hσ i).symm)⟩


def tripleOrderedEvent {ι : Type*} {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (τ : ι → TripleFaceTuple m)
    (L : ι → EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : ι → EuclideanSpace ℝ (Fin 3)) (i : ι) : Set (Vector r) :=
  tripleConeEvent (L i) (Z i) R u b (Finset.univ\tripleFaceActive (τ i))
    (tripleOutwardNormalCone u (tripleFaceActive (τ i)) (L i))

theorem tripleOrderedEvent_shared_active {ι : Type*} {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (τ : ι → TripleFaceTuple m)
    (L : ι → EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : ι → EuclideanSpace ℝ (Fin 3))
    (hspan : ∀ i k,k∈tripleFaceActive (τ i) → projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame (L i))))
    (hlevel : ∀ i k,k∈tripleFaceActive (τ i) → ⟪projectionEuclideanVector (u k),L i (Z i)⟫_ℝ=b k)
    (i i₀ : ι) {g : Vector r}
    (hg : g∈tripleOrderedEvent u b R τ L Z i) (hg₀ : g∈tripleOrderedEvent u b R τ L Z i₀) :
    tripleFaceActive (τ i)=tripleFaceActive (τ i₀) := by
  have hi := tripleConeEvent_mem_adaptiveOutwardTube u b (tripleFaceActive (τ i)) (L i) (Z i) R (hspan i) (hlevel i) hg
  have hi₀ := tripleConeEvent_mem_adaptiveOutwardTube u b (tripleFaceActive (τ i₀)) (L i₀) (Z i₀) R (hspan i₀) (hlevel i₀) hg₀
  by_contra hn
  exact disjoint_left.mp (adaptiveOutwardTube_disjoint (fun k => projectionEuclideanVector (u k)) b R hn) hi hi₀

/-- Six is the actual permutation count of one rank-three active set.
Only the supplied finite subfamily needs frames, so actual LI3 families
and low-rank empty families are both covered. -/
theorem tripleOrderedEvent_indicator_sum_le {ι : Type*} [Fintype ι] {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ k,vectorNormSq (u k)=1)
    (τ : ι → TripleFaceTuple m) (hτ : Function.Injective τ)
    (L : ι → EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : ι → EuclideanSpace ℝ (Fin 3))
    (hspan : ∀ i k,k∈tripleFaceActive (τ i) → projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame (L i))))
    (hlevel : ∀ i k,k∈tripleFaceActive (τ i) → ⟪projectionEuclideanVector (u k),L i (Z i)⟫_ℝ=b k)
    (P : Vector r → ℝ) (hP : ∀ g,0≤P g) (g : Vector r) :
    (∑ i : ι,(tripleOrderedEvent u b R τ L Z i).indicator P g)≤6*(fourthOuterLayer u b R).indicator P g := by
  classical
  have hcount : (∑ i : ι,(tripleOrderedEvent u b R τ L Z i).indicator (fun _ => (1:ℝ)) g)≤
      6*(fourthOuterLayer u b R).indicator (fun _ => (1:ℝ)) g := by
    by_cases hex : ∃ i,g∈tripleOrderedEvent u b R τ L Z i
    · obtain ⟨i₀,hg₀⟩ := hex
      have houter := tripleConeEvent_mem_outerLayer u b (tripleFaceActive (τ i₀)) (L i₀) (Z i₀)
        R hR hRadd hu (hspan i₀) (hlevel i₀) hg₀
      rw [indicator_of_mem houter,mul_one]
      have hp (i : ι) : (tripleOrderedEvent u b R τ L Z i).indicator (fun _ => (1:ℝ)) g≤
          ∑ σ : Equiv.Perm (Fin 3),if (τ i).1=(τ i₀).1 ∘ σ then (1:ℝ) else 0 := by
        by_cases hg : g∈tripleOrderedEvent u b R τ L Z i
        · rw [indicator_of_mem hg]
          obtain ⟨σ,hσ⟩ := tripleFaceTuple_eq_perm_of_active_eq (τ i) (τ i₀)
            (tripleOrderedEvent_shared_active u b R τ L Z hspan hlevel i i₀ hg hg₀)
          have ht := Finset.single_le_sum (s := Finset.univ)
            (f := fun σ : Equiv.Perm (Fin 3) => if (τ i).1=(τ i₀).1 ∘ σ then (1:ℝ) else 0)
            (fun _ _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ σ)
          simpa only [if_pos hσ] using ht
        · rw [indicator_of_not_mem hg]
          exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
      apply (Finset.sum_le_sum (fun i _ => hp i)).trans
      rw [Finset.sum_comm]
      have hs (σ : Equiv.Perm (Fin 3)) : (∑ i : ι,if (τ i).1=(τ i₀).1 ∘ σ then (1:ℝ) else 0)≤1 := by
        by_cases hex : ∃ i,(τ i).1=(τ i₀).1 ∘ σ
        · obtain ⟨i₁,hi₁⟩ := hex
          have he (i : ι) : (τ i).1=(τ i₀).1 ∘ σ ↔ i=i₁ := by
            constructor
            · intro hi
              apply hτ
              exact Subtype.ext (hi.trans hi₁.symm)
            · rintro rfl
              exact hi₁
          simp_rw [he]
          simp
        · have hn (i : ι) : (τ i).1≠(τ i₀).1 ∘ σ := fun h => hex ⟨i,h⟩
          simp only [if_neg (hn _),Finset.sum_const_zero]
          norm_num
      apply (Finset.sum_le_sum (fun σ _ => hs σ)).trans_eq
      norm_num [Fintype.card_perm,Nat.factorial]
    · have hn i : g∉tripleOrderedEvent u b R τ L Z i := fun h => hex ⟨i,h⟩
      simp only [indicator_of_not_mem (hn _),Finset.sum_const_zero]
      exact mul_nonneg (by norm_num) (indicator_nonneg (fun _ _ => by norm_num) g)
  have he (S : Set (Vector r)) : S.indicator P g=P g*S.indicator (fun _ => (1:ℝ)) g := by
    by_cases hg : g∈S <;> simp [hg]
  simp_rw [he]
  rw [← Finset.mul_sum]
  convert mul_le_mul_of_nonneg_left hcount (hP g) using 1 <;> ring

/-- Genuine finite Gaussian integration of an arbitrary selected family
of actual rank-three normal events. Its factor six is proved above. -/
theorem tripleOrderedEvent_integral_sum_le {ι : Type*} [Fintype ι] {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (hu : ∀ k,vectorNormSq (u k)=1)
    (τ : ι → TripleFaceTuple m) (hτ : Function.Injective τ)
    (L : ι → EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : ι → EuclideanSpace ℝ (Fin 3))
    (hspan : ∀ i k,k∈tripleFaceActive (τ i) → projectionEuclideanVector (u k)∈Submodule.span ℝ (range (tripleTransportFrame (L i))))
    (hlevel : ∀ i k,k∈tripleFaceActive (τ i) → ⟪projectionEuclideanVector (u k),L i (Z i)⟫_ℝ=b k)
    (hC : ∀ i,MeasurableSet (tripleOutwardNormalCone u (tripleFaceActive (τ i)) (L i)))
    (hR4 : Integrable (fun g => R (projectionEuclideanVector g)^4) (standardGaussian r)) :
    (∑ i : ι,∫ g,(tripleOrderedEvent u b R τ L Z i).indicator
      (fun g => R (projectionEuclideanVector g)^4) g ∂standardGaussian r)≤
    6*(∫ g,(fourthOuterLayer u b R).indicator (fun g => R (projectionEuclideanVector g)^4) g ∂standardGaussian r) := by
  classical
  have hi (i : ι) : Integrable ((tripleOrderedEvent u b R τ L Z i).indicator
      (fun g => R (projectionEuclideanVector g)^4)) (standardGaussian r) :=
    hR4.indicator (measurableSet_tripleConeEvent (L i) (Z i) R hRm u b _ _ (hC i))
  rw [← integral_finset_sum Finset.univ (fun i _ => hi i),← integral_const_mul]
  exact integral_mono (integrable_finset_sum _ (fun i _ => hi i))
    ((hR4.indicator (measurableSet_fourthOuterLayer u b R hRm)).const_mul 6)
    (fun g => tripleOrderedEvent_indicator_sum_le u b R hR hRadd hu τ hτ L Z hspan hlevel _
      (fun _ => pow_nonneg (zero_le_one.trans (hR _)) 4) g)

end
end RectangleCLTArxivV1
