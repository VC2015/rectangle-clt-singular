import RectangleCLTCompanion.SignedSurfaceConditioning
import RectangleCLTCompanion.SignedSurfaceShells

/-! Finite disjoint tube families are estimated in one actual common
experiment. Summation introduces no factor counting the number of faces. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def liftedImageEventOf {Ω : Type*} {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ)) : Set (CommonSamples p × Ω) :=
  {z | z.1 ∈ imageEventOf S s A (V z.2) B D}

theorem measurableSet_liftedImageEventOf {Ω : Type*} [MeasurableSpace Ω] {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    MeasurableSet (liftedImageEventOf S s A V B D) :=
  (measurableSet_imageEventOf_joint S s A hB hD hd).preimage
    ((hV.comp measurable_snd).prodMk measurable_fst)

/-- Actual base averaging equals the common-space image probability. -/
theorem integral_image_probability_eq_lifted {Ω : Type*} [MeasurableSpace Ω] {p q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (γ : Measure (CommonSamples p)) [IsProbabilityMeasure γ]
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫ ω, γ.real (imageEventOf S s A (V ω) B D) ∂μ) =
      (γ.prod μ).real (liftedImageEventOf S s A V B D) := by
  let E := liftedImageEventOf S s A V B D
  have hE := measurableSet_liftedImageEventOf S s A V hV B D hB hD hd
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) (γ.prod μ) :=
    (integrable_const (1 : ℝ)).indicator hE
  have hh := integral_prod_symm (E.indicator (fun _ => (1 : ℝ))) hi
  have hprob : (∫ z, E.indicator (fun _ => (1 : ℝ)) z ∂γ.prod μ) = (γ.prod μ).real E :=
    integral_indicator_one hE
  rw [hprob] at hh
  rw [hh]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    have hs : MeasurableSet (imageEventOf S s A (V ω) B D) :=
      hE.preimage (measurable_id.prodMk measurable_const)
    exact (integral_indicator_one hs).symm

/-- Disjoint complete active sets remain disjoint after lifting a measurable
random base. No coefficient-size bound is needed. -/
theorem liftedImageEventOf_disjoint {Ω : Type*} {p q k : ℕ}
    (S : CompatibleFaceTuple p q) (T : CompatibleFaceTuple p k)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p)
    (hS : ∀ i, S.face i ∈ s.faces) (hT : ∀ i, T.face i ∈ s.faces)
    (B C : Set (Vector p)) (D : Set (Fin q → ℝ)) (E : Set (Fin k → ℝ))
    (hD : ∀ c ∈ D, ∀ i, 0 < c i) (hE : ∀ c ∈ E, ∀ i, 0 < c i)
    (hne : activeFaces S ≠ activeFaces T) :
    Disjoint (liftedImageEventOf S s A V B D) (liftedImageEventOf T s A V C E) := by
  rw [Set.disjoint_left]
  intro z hz ht
  exact Set.disjoint_left.mp
    (imageEventOf_disjoint S T s A (V z.2) hS hT B D C E hD hE hne) hz ht

/-- The actual finite image-probability sum is bounded by one conditioned
boundary/tail event. The only probability premise is the displayed uniform
boundary-section bound, supplied by the proved bounded or Gaussian chain. -/
theorem sum_dyadic_image_probability_le
    {Ω ι : Type*} [MeasurableSpace Ω] {p q : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Measure (ℝ × (Face p → ℝ))) [IsProbabilityMeasure τ]
    (V : Ω → Vector p) (hV : Measurable V)
    (I : Finset ι) (S : ι → CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (D : ι → Set (Fin q → ℝ))
    (hD : ∀ i ∈ I, MeasurableSet (D i))
    (hactive : ∀ i ∈ I, ∀ j, (S i).face j ∈ s.faces)
    (hpositive : ∀ i ∈ I, ∀ c ∈ D i, ∀ j, 0 < c j)
    (hgram : ∀ i ∈ I, IsUnit ((normalMatrix (S i) A).transpose * normalMatrix (S i) A).det)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, activeFaces (S i) = activeFaces (S j) → i = j)
    {σ ε : ℝ} (hσ : 0 ≤ σ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hrow : ∀ f, ‖projectionEuclideanVector (signedRowNormal A f)‖ ≤ σ)
    (hphysical : ∀ i ∈ I, ∀ c ∈ D i,
      ‖projectionEuclideanVector ((normalMatrix (S i) A).mulVec c)‖ ≤ ε)
    (hq : 0 < q) (n : ℕ) (M : ℝ)
    (hsections : ∀ e : CommonSamples p,
      μ.real {ω | V ω + A.mulVec e.1 ∈
        (s.randomRectangle e.2).boundaryLayer (σ * ε)} ≤ M) :
    (∑ i ∈ I, ∫ ω, ((standardGaussian p).prod τ).real
      (imageEventOf (S i) s A (V ω) (dyadicShell (fourFaceProjectionRadius A) n) (D i)) ∂μ) ≤
      M * (standardGaussian p).real
        {g | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A g} := by
  classical
  let B := dyadicShell (fourFaceProjectionRadius A) n
  let γ := (standardGaussian p).prod τ
  let E := fun i => liftedImageEventOf (S i) s A V B (D i)
  let U := ⋃ i ∈ I, E i
  have hB : MeasurableSet B := measurableSet_dyadicShell _ (measurable_fourFaceProjectionRadius A) n
  have hE (i : ι) (hi : i ∈ I) : MeasurableSet (E i) :=
    measurableSet_liftedImageEventOf (S i) s A V hV B (D i) hB (hD i hi) (hgram i hi)
  have hU : MeasurableSet U := MeasurableSet.biUnion I.countable_toSet hE
  have hdis : Set.PairwiseDisjoint (I : Set ι) E := by
    intro i hi j hj hne
    exact liftedImageEventOf_disjoint (S i) (S j) s A V (hactive i hi) (hactive j hj)
      B B (D i) (D j) (hpositive i hi) (hpositive j hj)
      (fun he => hne (hinj i hi j hj he))
  have hsub : U ⊆ annulusEvent s A V (σ * ε) ∩
      {z | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A z.1.1} := by
    intro z hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hi, hz⟩ := Set.mem_iUnion.mp hzi
    refine ⟨?_, ?_⟩
    · exact imageEventOf_mem_boundaryLayer (S i) s A (V z.2) (hactive i hi)
        hσ hε hrow (hgram i hi) hq B (D i) (hpositive i hi) (hphysical i hi) hz
    · exact imageEventOf_dyadicShell_tail (S i) s A (V z.2) n (D i)
        (fun c hc => (hphysical i hi c hc).trans hε1) hz
  have hh := measure_subset_annulus_tail_le μ s A V hV (σ * ε) γ
    (fourFaceProjectionRadius A) (measurable_fourFaceProjectionRadius A)
    (dyadicRadius n / 2 - 1) M hsections U hU hsub
  rw [common_gaussian_tail_probability_of_law τ _ (measurable_fourFaceProjectionRadius A) _] at hh
  rw [measureReal_biUnion_finset hdis hE] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_image_probability_eq_lifted μ γ (S i) s A V hV B (D i)
    hB (hD i hi) (hgram i hi)

end
end RectangleCLT.Companion.SignedSurface
