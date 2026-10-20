import RectangleCLT.GaussianTubeUnion

/-! Measurable arbitrary tube domains for the existing, genuine augmented
Gaussian/exponential change of variables. The domains keep the base shell
and the coefficient region separate for Fubini. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def sourceDomainOf {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (B : Set (Vector p)) (D : Set (Fin q → ℝ)) :
    Set (Coordinates p q) :=
  {w | base w ∈ B ∧ tube w ∈ D ∧
    ∀ f ∈ s.faces, f ∉ activeFaces S →
      E₀ * (s.weights (A.mulVec (base w) + r)).weight f < e f}

def imageEventOf {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ)) :
    Set (Vector p × (ℝ × (Face p → ℝ))) :=
  {ze | 0 < ze.2.1 ∧ (∀ f, 0 < ze.2.2 f) ∧
    Sum.elim ze.1 (fun i => ze.2.2 (S.face i)) ∈
      GaussianTube.map (normalMatrix S A) s.bandwidth ze.2.1 (activeOffsets S s r) ''
        sourceDomainOf S s A r ze.2.1 ze.2.2 B D}

theorem measurableSet_sourceDomainOf {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) {B : Set (Vector p)} {D : Set (Fin q → ℝ)}
    (hB : MeasurableSet B) (hD : MeasurableSet D) :
    MeasurableSet (sourceDomainOf S s A r E₀ e B D) := by
  have hb : Measurable (base : Coordinates p q → Vector p) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q))
  have ht : Measurable (tube : Coordinates p q → Fin q → ℝ) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (Sum.inr i : Fin p ⊕ Fin q))
  have hW := ((measurable_mulVec A).comp hb).add_const r
  simp only [sourceDomainOf, Set.setOf_and, Set.setOf_forall]
  refine (hB.preimage hb).inter ((hD.preimage ht).inter ?_)
  exact MeasurableSet.iInter (fun f => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun _ => measurableSet_lt
      (((s.continuous_weight f).measurable.comp hW).const_mul E₀) measurable_const)))

theorem imageEventOf_iff_preimage {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (ze : Vector p × (ℝ × (Face p → ℝ))) :
    ze ∈ imageEventOf S s A r B D ↔ 0 < ze.2.1 ∧ (∀ f, 0 < ze.2.2 f) ∧
      imagePreimage S s A (r, ze) ∈ sourceDomainOf S s A r ze.2.1 ze.2.2 B D := by
  constructor
  · rintro ⟨h0, he, w, hw, hm⟩
    refine ⟨h0, he, ?_⟩
    change inverse (normalMatrix S A) s.bandwidth ze.2.1 (activeOffsets S s r)
      (Sum.elim ze.1 (fun i => ze.2.2 (S.face i))) ∈ _
    rw [← hm, inverse_map _ s.bandwidth_pos.ne' h0.ne' hd]
    exact hw
  · rintro ⟨h0, he, hw⟩
    refine ⟨h0, he, imagePreimage S s A (r, ze), hw, ?_⟩
    exact map_inverse _ s.bandwidth_pos.ne' h0 hd _ _ (fun i => he (S.face i))

theorem measurableSet_imageEventOf_joint {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    {B : Set (Vector p)} {D : Set (Fin q → ℝ)}
    (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    MeasurableSet {rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) |
      rze.2 ∈ imageEventOf S s A rze.1 B D} := by
  simp_rw [imageEventOf_iff_preimage S s A _ B D hd]
  have hpre := measurable_imagePreimage S s A
  have hb : Measurable (fun rze => base (imagePreimage S s A rze)) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp hpre)
  have ht : Measurable (fun rze => tube (imagePreimage S s A rze)) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply (Sum.inr i : Fin p ⊕ Fin q)).comp hpre)
  have hW := ((measurable_mulVec A).comp hb).add measurable_fst
  change MeasurableSet {rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) |
    0 < rze.2.2.1 ∧ (∀ f, 0 < rze.2.2.2 f) ∧
    base (imagePreimage S s A rze) ∈ B ∧ tube (imagePreimage S s A rze) ∈ D ∧
    ∀ f ∈ s.faces, f ∉ activeFaces S →
      rze.2.2.1 * (s.weights (A.mulVec (base (imagePreimage S s A rze)) + rze.1)).weight f < rze.2.2.2 f}
  simp only [Set.setOf_and, Set.setOf_forall]
  refine (measurableSet_lt measurable_const (by fun_prop)).inter
    ((MeasurableSet.iInter (fun f => measurableSet_lt measurable_const (by fun_prop))).inter
      ((hB.preimage hb).inter ((hD.preimage ht).inter ?_)))
  exact MeasurableSet.iInter (fun f => MeasurableSet.iInter (fun _ =>
    MeasurableSet.iInter (fun _ => measurableSet_lt
      ((by fun_prop : Measurable (fun rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) => rze.2.2.1)).mul
        ((s.continuous_weight f).measurable.comp hW)) (by fun_prop))))

/-- Arbitrary positive-coefficient domains retain the old pointwise
complete-active-set disjointness, with no uniform coefficient-size bound. -/
theorem imageEventOf_disjoint {p q k : ℕ}
    (S : CompatibleFaceTuple p q) (T : CompatibleFaceTuple p k)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hS : ∀ i, S.face i ∈ s.faces) (hT : ∀ i, T.face i ∈ s.faces)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (C : Set (Vector p)) (E : Set (Fin k → ℝ))
    (hD : ∀ u ∈ D, ∀ i, 0 < u i) (hE : ∀ u ∈ E, ∀ i, 0 < u i)
    (hne : activeFaces S ≠ activeFaces T) :
    Disjoint (imageEventOf S s A r B D) (imageEventOf T s A r C E) := by
  rw [Set.disjoint_left]
  rintro ze ⟨h0, he, w, hw, hm⟩ ⟨_, _, v, hv, hn⟩
  let width : ℝ := 1 + ‖tube w‖ + ‖tube v‖
  have hwsize (i : Fin q) : 0 < tube w i ∧ tube w i < width := by
    refine ⟨hD _ hw.2.1 i, ?_⟩
    have hh := (le_abs_self (tube w i)).trans
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (tube w) i)
    dsimp [width]
    linarith [norm_nonneg (tube v)]
  have hvsize (i : Fin k) : 0 < tube v i ∧ tube v i < width := by
    refine ⟨hE _ hv.2.1 i, ?_⟩
    have hh := (le_abs_self (tube v i)).trans
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (tube v) i)
    dsimp [width]
    linarith [norm_nonneg (tube w)]
  exact Set.disjoint_left.mp (imageEvent_disjoint S T s A r hS hT width hne)
    ⟨h0, he, w, ⟨hwsize, hw.2.2⟩, hm⟩ ⟨h0, he, v, ⟨hvsize, hv.2.2⟩, hn⟩

end
end RectangleCLT.Companion.SignedSurface
