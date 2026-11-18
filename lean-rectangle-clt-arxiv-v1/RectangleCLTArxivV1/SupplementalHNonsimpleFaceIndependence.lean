import RectangleCLTArxivV1.SupplementalHNonsimpleFaceGeometry
import RectangleCLTArxivV1.SupplementalHTripleIncidenceGeometry
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! Simultaneously active original facets have no dependent pair or
triple in an irredundant full-dimensional presentation.  This does not
exclude four or more facets at an actual codimension-three face. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4 RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem nonsimple_active_pair_linearIndependent {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1) (j k : Fin m) (hjk : j≠k)
    (x : Vector r) (hxj : faceDot (u j) x=b j) (hxk : faceDot (u k) x=b k) :
    LinearIndependent ℝ ![u j,u k] := by
  have hz : u j≠0 := by
    intro he
    have h := hu j
    simp [he,vectorNormSq] at h
  apply (LinearIndependent.pair_iff' hz).mpr
  intro a ha
  apply actualFacet_pair_affine_inconsistent u b hi hw j k hjk.symm a ha.symm
  rw [←hxk,ha.symm,threshold_faceDot_smul_left,hxj]

theorem nonsimple_active_triple_linearIndependent {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1) (F : Fin 3 → Fin m) (hF : Function.Injective F)
    (x : Vector r) (hx : ∀ i,faceDot (u (F i)) x=b (F i)) :
    LinearIndependent ℝ (fun i => u (F i)) := by
  have htail : LinearIndependent ℝ ![u (F 1),u (F 2)] :=
    nonsimple_active_pair_linearIndependent u b hi hw hu _ _
      (hF.ne (by decide : (1 : Fin 3)≠2)) x (hx 1) (hx 2)
  have hnot : u (F 0)∉Submodule.span ℝ (range ![u (F 1),u (F 2)]) := by
    intro hm
    have hp : range ![u (F 1),u (F 2)]={u (F 1),u (F 2)} := by
      ext y
      simp only [mem_range,mem_insert_iff,mem_singleton_iff]
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp
      · rintro (rfl|rfl)
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
    rw [hp] at hm
    obtain ⟨a,c,hn⟩ := Submodule.mem_span_pair.mp hm
    apply actualFacet_triple_affine_inconsistent u b hi hw (F 1) (F 2) (F 0)
      (hF.ne (by decide : (1 : Fin 3)≠2))
      (hF.ne (by decide : (0 : Fin 3)≠1))
      (hF.ne (by decide : (0 : Fin 3)≠2)) a c hn.symm
    rw [←hx 0,hn.symm,gaussianPair_faceDot_add_left,threshold_faceDot_smul_left,
      threshold_faceDot_smul_left,hx 1,hx 2]
  have h := linearIndependent_fin_cons.mpr ⟨htail,hnot⟩
  convert h using 1
  ext i
  fin_cases i <;> rfl

theorem nonsimple_active_triple_euclidean_linearIndependent {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1) (F : Fin 3 → Fin m) (hF : Function.Injective F)
    (x : Vector r) (hx : ∀ i,faceDot (u (F i)) x=b (F i)) :
    LinearIndependent ℝ (fun i => projectionEuclideanVector (u (F i))) := by
  let L := (WithLp.linearEquiv 2 ℝ (Vector r)).symm
  exact (nonsimple_active_triple_linearIndependent u b hi hw hu F hF x hx).map'
    L.toLinearMap (LinearMap.ker_eq_bot.mpr L.injective)

theorem nonsimple_active_rank_le_two_card_le_two {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1) (S : Finset (Fin m))
    (hS : (exactStratum (fun j => projectionEuclideanVector (u j)) b S).Nonempty)
    (hr : Module.finrank ℝ (nonsimpleFaceNormalSpace
      (fun j => projectionEuclideanVector (u j)) S)≤2) : S.card≤2 := by
  classical
  by_contra hn
  obtain ⟨a,c,d,ha,hc,hd,hac,had,hcd⟩ := Finset.two_lt_card_iff.mp (lt_of_not_ge hn)
  let F : Fin 3 → Fin m := ![a,c,d]
  have hF : Function.Injective F := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [F]
  have hFS (i : Fin 3) : F i∈S := by fin_cases i <;> simp [F,ha,hc,hd]
  obtain ⟨x,hx⟩ := hS
  let v : Vector r := WithLp.equiv 2 (Vector r) x
  have hlev (i : Fin 3) : faceDot (u (F i)) v=b (F i) := by
    rw [faceDot_eq_euclidean_inner]
    simpa only [v,projectionEuclideanVector,Equiv.symm_apply_apply] using (hx.2 (F i)).mpr (hFS i)
  have hli := nonsimple_active_triple_euclidean_linearIndependent u b hi hw hu F hF v hlev
  have hspan : Submodule.span ℝ (range (fun i => projectionEuclideanVector (u (F i))))≤
      nonsimpleFaceNormalSpace (fun j => projectionEuclideanVector (u j)) S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact nonsimple_normal_mem _ _ _ (hFS i)
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli,Fintype.card_fin] at hdim
  omega

theorem nonsimpleFaceNormalSpace_finrank_le_card {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (u : Fin m → E) (S : Finset (Fin m)) :
    Module.finrank ℝ (nonsimpleFaceNormalSpace u S)≤S.card := by
  have he : range (fun j : S => u j.1)=u '' (S : Set (Fin m)) := by
    ext y
    simp
  have h := finrank_range_le_card (R := ℝ) (fun j : S => u j.1)
  simpa only [he,Fintype.card_coe,nonsimpleFaceNormalSpace] using h

/-- Every actual ridge has exactly two active original facets. There
can nevertheless be arbitrarily many active facets at codimension3. -/
theorem nonsimple_ridge_card_eq_two {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (F : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 2) : F.1.card=2 := by
  have hupper := nonsimple_active_rank_le_two_card_le_two u b hi hw hu F.1 F.2.1 F.2.2.le
  have hlower := nonsimpleFaceNormalSpace_finrank_le_card (fun j => projectionEuclideanVector (u j)) F.1
  rw [F.2.2] at hlower
  exact Nat.le_antisymm hupper hlower

theorem nonsimple_ridge_exists_actual_pair_witness {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (F : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 2) :
    ∃ j k : Fin m,j≠k ∧ F.1={j,k} ∧ ∃ x : Vector r,
      faceDot (u j) x=b j ∧ faceDot (u k) x=b k ∧
      ∀ l,l≠j → l≠k → faceDot (u l) x<b l := by
  classical
  obtain ⟨j,k,hjk,hF⟩ := Finset.card_eq_two.mp (nonsimple_ridge_card_eq_two u b hi hw hu F)
  let z := nonsimpleFaceRepresentative (fun l => projectionEuclideanVector (u l)) b F
  let x : Vector r := WithLp.equiv 2 (Vector r) z
  have he (l : Fin m) : faceDot (u l) x=⟪projectionEuclideanVector (u l),z⟫_ℝ := by
    rw [faceDot_eq_euclidean_inner]
    rfl
  refine ⟨j,k,hjk,hF,x,?_,?_,?_⟩
  · rw [he]
    exact nonsimpleFaceRepresentative_levels _ b F j (by simp [hF])
  · rw [he]
    exact nonsimpleFaceRepresentative_levels _ b F k (by simp [hF])
  · intro l hlj hlk
    rw [he]
    exact nonsimpleFaceRepresentative_strict _ b F l (by simp [hF,hlj,hlk])

theorem nonsimple_codimThree_triple_spans {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3)
    (F : Fin 3 → Fin m) (hF : Function.Injective F) (hFS : ∀ i,F i∈H.1) :
    Submodule.span ℝ (range (fun i => projectionEuclideanVector (u (F i))))=
      nonsimpleFaceNormalSpace (fun j => projectionEuclideanVector (u j)) H.1 := by
  let z := nonsimpleFaceRepresentative (fun j => projectionEuclideanVector (u j)) b H
  let x : Vector r := WithLp.equiv 2 (Vector r) z
  have hlev (i : Fin 3) : faceDot (u (F i)) x=b (F i) := by
    rw [faceDot_eq_euclidean_inner]
    exact nonsimpleFaceRepresentative_levels _ b H (F i) (hFS i)
  have hli := nonsimple_active_triple_euclidean_linearIndependent u b hi hw hu F hF x hlev
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact nonsimple_normal_mem _ _ _ (hFS i)
  · rw [finrank_span_eq_card hli,Fintype.card_fin,H.2.2]

theorem nonsimple_codimThree_exists_spanning_triple {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3) :
    ∃ F : Fin 3 → Fin m,Function.Injective F ∧ (∀ i,F i∈H.1) ∧
      Submodule.span ℝ (range (fun i => projectionEuclideanVector (u (F i))))=
        nonsimpleFaceNormalSpace (fun j => projectionEuclideanVector (u j)) H.1 := by
  classical
  have hcard := nonsimpleFaceNormalSpace_finrank_le_card (fun j => projectionEuclideanVector (u j)) H.1
  rw [H.2.2] at hcard
  obtain ⟨a,c,d,ha,hc,hd,hac,had,hcd⟩ := Finset.two_lt_card_iff.mp (by omega : 2<H.1.card)
  let F : Fin 3 → Fin m := ![a,c,d]
  have hF : Function.Injective F := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [F]
  have hFS (i : Fin 3) : F i∈H.1 := by fin_cases i <;> simp [F,ha,hc,hd]
  exact ⟨F,hF,hFS,nonsimple_codimThree_triple_spans u b hi hw hu H F hF hFS⟩

/-- A supporting plane of the actual three-dimensional normal cone has
exactly its two original endpoint generators as zeros. Irredundancy
rules out a hidden third zero generator without a genericity premise. -/
theorem nonsimple_codimThree_supporting_pair_strict {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hi : HasStrictFacetInterior u b) (hw : HasIrredundantFacetWitnesses u b)
    (hu : ∀ j,vectorNormSq (u j)=1)
    (H : NonsimpleFaceIndex (fun j => projectionEuclideanVector (u j)) b 3)
    (n : EuclideanSpace ℝ (Fin r)) (hn : n≠0)
    (hnS : n∈nonsimpleFaceNormalSpace (fun j => projectionEuclideanVector (u j)) H.1)
    (hpos : ∀ j∈H.1,0≤⟪n,projectionEuclideanVector (u j)⟫_ℝ)
    (a d : Fin m) (ha : a∈H.1) (hd : d∈H.1) (had : a≠d)
    (hna : ⟪n,projectionEuclideanVector (u a)⟫_ℝ=0)
    (hnd : ⟪n,projectionEuclideanVector (u d)⟫_ℝ=0) :
    ∀ k∈H.1,k≠a → k≠d → 0<⟪n,projectionEuclideanVector (u k)⟫_ℝ := by
  intro k hk hka hkd
  by_contra hp
  have hnk : ⟪n,projectionEuclideanVector (u k)⟫_ℝ=0 := le_antisymm (le_of_not_gt hp) (hpos k hk)
  let F : Fin 3 → Fin m := ![a,d,k]
  have hF : Function.Injective F := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [F]
  have hFS (i : Fin 3) : F i∈H.1 := by fin_cases i <;> simp [F,ha,hd,hk]
  have hspan := nonsimple_codimThree_triple_spans u b hi hw hu H F hF hFS
  have hz : ∀ z∈Submodule.span ℝ (range (fun i => projectionEuclideanVector (u (F i)))),⟪n,z⟫_ℝ=0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i,rfl⟩ := hz
      fin_cases i <;> simp [F,hna,hnd,hnk]
    | zero => simp
    | add z w hz hw ihz ihw => simp [inner_add_right,ihz,ihw]
    | smul c z hz ih => simp [inner_smul_right,ih]
  apply hn
  exact inner_self_eq_zero.mp (hz n (hspan.symm ▸ hnS))

end
end RectangleCLTArxivV1
