import RectangleCLTArxivV1.SupplementalHTripleMass
import RectangleCLTArxivV1.SupplementalHGenericPairGreen

/-! Concrete conditioning frames of one actually selected independent
three-tuple of normals from a global finite family. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section

def tripleIncidenceLeft {m : ℕ} (F : Fin 3 → Fin m) (i : Fin 3) : Fin m := F (i.succAbove 0)
def tripleIncidenceRight {m : ℕ} (F : Fin 3 → Fin m) (i : Fin 3) : Fin m := F (i.succAbove 1)

def tripleIncidenceFirst {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m) (i : Fin 3) : Vector r :=
  thresholdPairBisector u (tripleIncidenceLeft F i) (tripleIncidenceRight F i)
def tripleIncidenceSecond {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m) (i : Fin 3) : Vector r :=
  thresholdPairDifference u (tripleIncidenceLeft F i) (tripleIncidenceRight F i)

def tripleIncidenceAlpha {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (i : Fin 3) : ℝ :=
  thresholdPairFirstLevel u b (tripleIncidenceLeft F i) (tripleIncidenceRight F i)
def tripleIncidenceBeta {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (i : Fin 3) : ℝ :=
  thresholdPairSecondLevel u b (tripleIncidenceLeft F i) (tripleIncidenceRight F i)

def tripleIncidenceThird {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m) (i : Fin 3) : Vector r :=
  hardPairThirdDirection u (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i) (F i)
def tripleIncidenceScale {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m) (i : Fin 3) : ℝ :=
  hardPairThirdScale u (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i) (F i)

def tripleIncidenceShift {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (i : Fin 3) : ℝ :=
  hardPairResidualLevels u b (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i)
    (tripleIncidenceAlpha u b F i) (tripleIncidenceBeta u b F i) (F i)

def tripleIncidenceFrame {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (i : Fin 3) : Fin 3 → EuclideanSpace ℝ (Fin r) :=
  nativeTripleFrame (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i) (tripleIncidenceThird u F i)

def tripleIncidenceLevels {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (i : Fin 3) : Fin 3 → ℝ :=
  nativeTripleLevels (tripleIncidenceAlpha u b F i) (tripleIncidenceBeta u b F i)
    (tripleIncidenceShift u b F i/tripleIncidenceScale u F i)

def tripleIncidenceOriginalNormals {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) : Fin 3 → EuclideanSpace ℝ (Fin r) :=
  fun i => (WithLp.equiv 2 (Vector r)).symm (u (F i))

def tripleIncidenceNormalPoint {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (i : Fin 3) : EuclideanSpace ℝ (Fin r) :=
  ∑ j, tripleIncidenceLevels u b F i j • tripleIncidenceFrame u F i j

theorem tripleIncidence_pair_nondegenerate {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun i => u (F i))) (i : Fin 3) :
    projectionEuclideanVector (u (tripleIncidenceLeft F i))+
      projectionEuclideanVector (u (tripleIncidenceRight F i))≠0 ∧
    projectionEuclideanVector (u (tripleIncidenceLeft F i))-
      projectionEuclideanVector (u (tripleIncidenceRight F i))≠0 :=
  thresholdPair_sum_sub_ne_zero_of_independent (fun j => u (F j)) hi _ _
    ((Fin.succAboveEmb i).injective.ne (by decide))

theorem tripleIncidence_pair_geometry {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    vectorNormSq (tripleIncidenceFirst u F i)=1 ∧
      vectorNormSq (tripleIncidenceSecond u F i)=1 ∧
      faceDot (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i)=0 := by
  obtain ⟨hp,hm⟩ := tripleIncidence_pair_nondegenerate u F hi i
  exact ⟨thresholdPairBisector_unit _ _ _ hp,thresholdPairDifference_unit _ _ _ hm,
    thresholdPair_frame_orthogonal _ _ _ (hu _) (hu _)⟩

theorem tripleIncidence_third_residual_ne_zero {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    hardPairResidualNormal (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i) (u (F i))≠0 := by
  let S := Submodule.span ℝ ((fun j => u (F j)) '' ({i.succAbove 0,i.succAbove 1} : Set (Fin 3)))
  have hL : u (tripleIncidenceLeft F i)∈S := Submodule.subset_span ⟨i.succAbove 0,by simp,rfl⟩
  have hR : u (tripleIncidenceRight F i)∈S := Submodule.subset_span ⟨i.succAbove 1,by simp,rfl⟩
  have he : tripleIncidenceFirst u F i∈S := by
    change ‖projectionEuclideanVector (u (tripleIncidenceLeft F i))+
      projectionEuclideanVector (u (tripleIncidenceRight F i))‖⁻¹ •
      (u (tripleIncidenceLeft F i)+u (tripleIncidenceRight F i))∈S
    exact S.smul_mem _ (S.add_mem hL hR)
  have hf : tripleIncidenceSecond u F i∈S := by
    change ‖projectionEuclideanVector (u (tripleIncidenceLeft F i))-
      projectionEuclideanVector (u (tripleIncidenceRight F i))‖⁻¹ •
      (u (tripleIncidenceLeft F i)-u (tripleIncidenceRight F i))∈S
    exact S.smul_mem _ (S.sub_mem hL hR)
  intro hz
  have heq := hardPairResidualNormal_eq_sub (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i)
    (u (F i)) (tripleIncidence_pair_geometry u F hi hu i).2.2
  rw [hz,sub_sub] at heq
  have hm : u (F i)∈S := by
    rw [sub_eq_zero.mp heq.symm]
    exact S.add_mem (S.smul_mem _ he) (S.smul_mem _ hf)
  exact (hi.not_mem_span_image (s := ({i.succAbove 0,i.succAbove 1} : Set (Fin 3)))
    (by simp [Ne.symm (Fin.succAbove_ne i 0),Ne.symm (Fin.succAbove_ne i 1)])) hm

theorem tripleIncidenceFrame_orthonormal {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    Orthonormal ℝ (tripleIncidenceFrame u F i) := by
  obtain ⟨he,hf,hef⟩ := tripleIncidence_pair_geometry u F hi hu i
  exact hardPairThirdFrame_orthonormal u _ _ he hf hef (F i)
    (tripleIncidence_third_residual_ne_zero u F hi hu i)

/-- Each actual conditioning frame spans the original selected normal
space. Both inclusions are proved from the actual bisector/difference
formulas and the checked two-normal expansions. -/
theorem tripleIncidenceFrame_span {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    Submodule.span ℝ (Set.range (tripleIncidenceFrame u F i))=
      Submodule.span ℝ (Set.range (tripleIncidenceOriginalNormals u F)) := by
  let E := tripleIncidenceFirst u F i
  let G := tripleIncidenceSecond u F i
  let j := tripleIncidenceLeft F i
  let l := tripleIncidenceRight F i
  let S := Submodule.span ℝ (Set.range (tripleIncidenceOriginalNormals u F))
  let T := Submodule.span ℝ (Set.range (nativeTripleFrame E G (u (F i))))
  obtain ⟨hp,hm⟩ := tripleIncidence_pair_nondegenerate u F hi i
  have hgeom := tripleIncidence_pair_geometry u F hi hu i
  change Submodule.span ℝ (Set.range (nativeTripleFrame E G (hardPairThirdDirection u E G (F i))))=_
  rw [hardPairThirdFrame_span u E G hgeom.2.2 (F i)
    (tripleIncidence_third_residual_ne_zero u F hi hu i)]
  have hjS : (WithLp.equiv 2 (Vector r)).symm (u j)∈S := Submodule.subset_span ⟨i.succAbove 0,rfl⟩
  have hlS : (WithLp.equiv 2 (Vector r)).symm (u l)∈S := Submodule.subset_span ⟨i.succAbove 1,rfl⟩
  have hkS : (WithLp.equiv 2 (Vector r)).symm (u (F i))∈S := Submodule.subset_span ⟨i,rfl⟩
  have hES : (WithLp.equiv 2 (Vector r)).symm E∈S := by
    change (WithLp.equiv 2 (Vector r)).symm
      (‖projectionEuclideanVector (u j)+projectionEuclideanVector (u l)‖⁻¹ • (u j+u l))∈S
    rw [WithLp.equiv_symm_smul,WithLp.equiv_symm_add]
    exact S.smul_mem _ (S.add_mem hjS hlS)
  have hGS : (WithLp.equiv 2 (Vector r)).symm G∈S := by
    change (WithLp.equiv 2 (Vector r)).symm
      (‖projectionEuclideanVector (u j)-projectionEuclideanVector (u l)‖⁻¹ • (u j-u l))∈S
    rw [WithLp.equiv_symm_smul,WithLp.equiv_symm_sub]
    exact S.smul_mem _ (S.sub_mem hjS hlS)
  have hET : (WithLp.equiv 2 (Vector r)).symm E∈T := Submodule.subset_span ⟨0,by simp [nativeTripleFrame]⟩
  have hGT : (WithLp.equiv 2 (Vector r)).symm G∈T := Submodule.subset_span ⟨1,by simp [nativeTripleFrame]⟩
  have hkT : (WithLp.equiv 2 (Vector r)).symm (u (F i))∈T := Submodule.subset_span ⟨2,by simp [nativeTripleFrame]⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    fin_cases a
    · exact hES
    · exact hGS
    · exact hkS
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    by_cases hai : a=i
    · subst a
      exact hkT
    · obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq hai
      fin_cases t
      · change (WithLp.equiv 2 (Vector r)).symm (u j)∈T
        rw [thresholdPair_left_expansion u j l hp hm,WithLp.equiv_symm_add,
          WithLp.equiv_symm_smul,WithLp.equiv_symm_smul]
        exact T.add_mem (T.smul_mem _ hET) (T.smul_mem _ hGT)
      · change (WithLp.equiv 2 (Vector r)).symm (u l)∈T
        rw [thresholdPair_right_expansion u j l hp hm,WithLp.equiv_symm_sub,
          WithLp.equiv_symm_smul,WithLp.equiv_symm_smul]
        exact T.sub_mem (T.smul_mem _ hET) (T.smul_mem _ hGT)

private theorem tripleIncidence_framePoint_zero {r q : ℕ}
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (a : Fin q → ℝ) :
    gaussianFrameSectionPoint v a 0=∑ j, a j • v j := by
  simp [gaussianFrameSectionPoint,gaussianFrameProjection]

/-- The actual affine normal point is the concrete successive triple
section at zero residual Gaussian. -/
theorem tripleIncidenceNormalPoint_native {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    WithLp.equiv 2 (Vector r) (tripleIncidenceNormalPoint u b F i)=
      gaussianPairBase u b (tripleIncidenceLeft F i) (tripleIncidenceRight F i)
        (gaussianSectionPoint (tripleIncidenceThird u F i)
          (tripleIncidenceShift u b F i/tripleIncidenceScale u F i) 0) := by
  obtain ⟨he,hf,hef⟩ := tripleIncidence_pair_geometry u F hi hu i
  have hg := hardPairThirdDirection_geometry u _ _ he hf hef (F i)
    (tripleIncidence_third_residual_ne_zero u F hi hu i)
  have hp := gaussianFrameSectionPoint_native_triple (tripleIncidenceFirst u F i)
    (tripleIncidenceSecond u F i) (tripleIncidenceThird u F i) hef hg.2.1 hg.2.2
    (tripleIncidenceAlpha u b F i) (tripleIncidenceBeta u b F i)
    (tripleIncidenceShift u b F i/tripleIncidenceScale u F i) (0 : Vector r)
  rw [WithLp.equiv_symm_zero,tripleIncidence_framePoint_zero] at hp
  exact hp

private theorem tripleIncidence_native_inner {r : ℕ} (v : Vector r) (x : EuclideanSpace ℝ (Fin r)) :
    ⟪(WithLp.equiv 2 (Vector r)).symm v,x⟫_ℝ=faceDot v (WithLp.equiv 2 (Vector r) x) := by
  rw [faceDot_eq_euclidean_inner]
  rfl

/-- Every conditioning choice has all three actual original supporting
levels, not only the two orthonormal coordinate levels. -/
theorem tripleIncidenceNormalPoint_supporting_levels {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i a : Fin 3) :
    ⟪tripleIncidenceOriginalNormals u F a,tripleIncidenceNormalPoint u b F i⟫_ℝ=b (F a) := by
  obtain ⟨hp,hm⟩ := tripleIncidence_pair_nondegenerate u F hi i
  obtain ⟨he,hf,hef⟩ := tripleIncidence_pair_geometry u F hi hu i
  have hpoint := tripleIncidenceNormalPoint_native u b F hi hu i
  have hleft := gaussianPairBase_left_level u b (tripleIncidenceLeft F i) (tripleIncidenceRight F i)
    (hu _) (hu _) hp hm (gaussianSectionPoint (tripleIncidenceThird u F i)
      (tripleIncidenceShift u b F i/tripleIncidenceScale u F i) 0)
  have hright := gaussianPairBase_right_level u b (tripleIncidenceLeft F i) (tripleIncidenceRight F i)
    (hu _) (hu _) hp hm (gaussianSectionPoint (tripleIncidenceThird u F i)
      (tripleIncidenceShift u b F i/tripleIncidenceScale u F i) 0)
  have hthird := (hardPairThirdSection_selected_levels u b (tripleIncidenceFirst u F i)
    (tripleIncidenceSecond u F i) he hf hef (tripleIncidenceAlpha u b F i)
    (tripleIncidenceBeta u b F i) (F i) (tripleIncidence_third_residual_ne_zero u F hi hu i) 0).2.2
  rw [←hpoint] at hleft hright
  change faceDot (u (F i)) (gaussianPairBase u b (tripleIncidenceLeft F i) (tripleIncidenceRight F i)
    (gaussianSectionPoint (tripleIncidenceThird u F i)
      (tripleIncidenceShift u b F i/tripleIncidenceScale u F i) 0))=b (F i) at hthird
  rw [←hpoint] at hthird
  change ⟪(WithLp.equiv 2 (Vector r)).symm (u (F a)),tripleIncidenceNormalPoint u b F i⟫_ℝ=_
  rw [tripleIncidence_native_inner]
  by_cases hai : a=i
  · subst a
    exact hthird
  · obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq hai
    fin_cases t
    · exact hleft
    · exact hright

theorem tripleIncidenceNormalPoint_mem_span {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    tripleIncidenceNormalPoint u b F i∈Submodule.span ℝ (Set.range (tripleIncidenceOriginalNormals u F)) := by
  rw [←tripleIncidenceFrame_span u F hi hu i]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

/-- The three actual Gram--Schmidt descriptions have one actual normal
point, derived from their original spanning normals and true levels. -/
theorem tripleIncidenceNormalPoint_eq {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i j : Fin 3) :
    tripleIncidenceNormalPoint u b F i=tripleIncidenceNormalPoint u b F j := by
  exact normalPoint_eq_of_spanning_levels (tripleIncidenceOriginalNormals u F) _ _
    (tripleIncidenceNormalPoint_mem_span u b F hi hu i)
    (tripleIncidenceNormalPoint_mem_span u b F hi hu j)
    (fun a => (tripleIncidenceNormalPoint_supporting_levels u b F hi hu i a).trans
      (tripleIncidenceNormalPoint_supporting_levels u b F hi hu j a).symm)

/-- Conversely, a nonparallel selected pair and a nonzero actual third
residual force the original selected three normals to be independent. -/
theorem tripleIncidence_independent_of_third_residual_ne_zero {m r : ℕ}
    (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (hu : ∀ a, vectorNormSq (u (F a))=1) (i : Fin 3)
    (hp : projectionEuclideanVector (u (tripleIncidenceLeft F i))+
      projectionEuclideanVector (u (tripleIncidenceRight F i))≠0)
    (hm : projectionEuclideanVector (u (tripleIncidenceLeft F i))-
      projectionEuclideanVector (u (tripleIncidenceRight F i))≠0)
    (hk : hardPairResidualNormal (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i) (u (F i))≠0) :
    LinearIndependent ℝ (fun a => u (F a)) := by
  let E := tripleIncidenceFirst u F i
  let G := tripleIncidenceSecond u F i
  let H := tripleIncidenceThird u F i
  let S := Submodule.span ℝ (Set.range (fun a => u (F a)))
  have hL : u (tripleIncidenceLeft F i)∈S := Submodule.subset_span ⟨i.succAbove 0,rfl⟩
  have hR : u (tripleIncidenceRight F i)∈S := Submodule.subset_span ⟨i.succAbove 1,rfl⟩
  have hK : u (F i)∈S := Submodule.subset_span ⟨i,rfl⟩
  have hE : E∈S := by
    change ‖projectionEuclideanVector (u (tripleIncidenceLeft F i))+
      projectionEuclideanVector (u (tripleIncidenceRight F i))‖⁻¹ •
      (u (tripleIncidenceLeft F i)+u (tripleIncidenceRight F i))∈S
    exact S.smul_mem _ (S.add_mem hL hR)
  have hG : G∈S := by
    change ‖projectionEuclideanVector (u (tripleIncidenceLeft F i))-
      projectionEuclideanVector (u (tripleIncidenceRight F i))‖⁻¹ •
      (u (tripleIncidenceLeft F i)-u (tripleIncidenceRight F i))∈S
    exact S.smul_mem _ (S.sub_mem hL hR)
  have he : vectorNormSq E=1 := thresholdPairBisector_unit _ _ _ hp
  have hf : vectorNormSq G=1 := thresholdPairDifference_unit _ _ _ hm
  have hef : faceDot E G=0 := thresholdPair_frame_orthogonal _ _ _ (hu _) (hu _)
  have hH : H∈S := by
    change (hardPairThirdScale u E G (F i))⁻¹ • hardPairResidualNormal E G (u (F i))∈S
    apply S.smul_mem
    rw [hardPairResidualNormal_eq_sub E G (u (F i)) hef]
    exact S.sub_mem (S.sub_mem hK (S.smul_mem _ hE)) (S.smul_mem _ hG)
  let V := nativeTripleFrame E G H
  let B : Fin 3 → Vector r := fun a => WithLp.equiv 2 (Vector r) (V a)
  let L := WithLp.linearEquiv 2 ℝ (Vector r)
  have hV : Orthonormal ℝ V := hardPairThirdFrame_orthonormal u E G he hf hef (F i) hk
  have hB : LinearIndependent ℝ B := by
    exact hV.linearIndependent.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr L.injective)
  have hspan : Submodule.span ℝ (Set.range B)≤S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    fin_cases a
    · exact hE
    · exact hG
    · exact hH
  apply linearIndependent_iff_card_le_finrank_span.mpr
  change Fintype.card (Fin 3)≤Module.finrank ℝ S
  rw [←finrank_span_eq_card hB]
  exact Submodule.finrank_mono hspan

end
end RectangleCLTArxivV1
