import RectangleCLTArxivV1.ActiveFaceCoordinates
import RectangleCLTArxivV1.SupplementalHSelectorTuples

/-! Exact active-face enumeration for the original physical smoother.
No inactive or empty-list contribution is discarded by assumption. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def activeFaceIndex {p : ℕ} (s : FaceSmoother p) (j : Fin s.faces.card) : Face p :=
  (activeFaceEquiv s j).1

theorem activeFaceIndex_mem {p : ℕ} (s : FaceSmoother p) (j : Fin s.faces.card) :
    activeFaceIndex s j∈s.faces := (activeFaceEquiv s j).2

theorem activeFaceIndex_injective {p : ℕ} (s : FaceSmoother p) :
    Function.Injective (activeFaceIndex s) := by
  intro j l h
  exact (activeFaceEquiv s).injective (Subtype.ext h)

theorem mem_faces_iff_activeFaceIndex {p : ℕ} (s : FaceSmoother p) (f : Face p) :
    f∈s.faces ↔ ∃ j,activeFaceIndex s j=f := by
  constructor
  · intro hf
    exact ⟨(activeFaceEquiv s).symm ⟨f,hf⟩,by simp [activeFaceIndex]⟩
  · rintro ⟨j,rfl⟩
    exact activeFaceIndex_mem s j

theorem activeFace_card_le {p : ℕ} (s : FaceSmoother p) : s.faces.card≤2*p := by
  have hh := Finset.card_le_univ s.faces
  simpa only [Face,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm] using hh

theorem activeFaceNormals_eq_selectorFaceNormal {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (j : Fin s.faces.card) :
    activeFaceNormals s A j=selectorFaceNormal A (activeFaceIndex s j) := by
  unfold activeFaceNormals selectorFaceNormal activeFaceIndex
  cases hf : (activeFaceEquiv s j).1.2 <;> simp [hf] <;> rfl

theorem activeFaceProjection_mulVec {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (y : Vector r) :
    activeFaceProjection s (A.mulVec y)=Matrix.mulVec (activeFaceNormals s A) y := by
  have hz : activeFaceProjection s (0 : Vector p)=0 := by
    ext j
    unfold activeFaceProjection FaceSmoother.normalDot
    split_ifs <;> simp
  simpa only [one_smul,add_zero,hz] using activeFaceProjection_affine s A y 0 1

theorem activeFace_nullWeight {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (y : Vector r) :
    s.F (A.mulVec y)=logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y := by
  rw [←activeFace_upper_F s (A.mulVec y),activeFaceProjection_mulVec,upperFaceSmoother_F]

theorem activeFace_piWeight {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (y : Vector r) (j : Fin s.faces.card) :
    s.pi (A.mulVec y) (activeFaceIndex s j)=
      logisticFaceWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y j := by
  unfold activeFaceIndex
  rw [←activeFace_upper_pi s (A.mulVec y) j,activeFaceProjection_mulVec,upperFaceSmoother_pi]

theorem activeFace_thetaWeight {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (y : Vector r) :
    s.theta (A.mulVec y)=1-logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y := by
  change 1-s.F (A.mulVec y)=_
  rw [activeFace_nullWeight]

theorem activeFace_selectorWeight_physical {p r k : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (β : Fin k → Fin s.faces.card) (y : Vector r) :
    selectorWeight s (fun i => activeFaceIndex s (β i)) (A.mulVec y)=
      logisticTupleWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth β y := by
  unfold activeFaceIndex
  rw [←activeFace_selectorWeight s β (A.mulVec y),activeFaceProjection_mulVec,
    upperFaceSmoother_selectorWeight]

theorem sum_activeFace_values {p : ℕ} (s : FaceSmoother p) (c : Face p → ℝ)
    (hz : ∀ f,f∉s.faces → c f=0) :
    (∑ f : Face p,c f)=∑ j : Fin s.faces.card,c (activeFaceIndex s j) := by
  classical
  have he := (activeFaceEquiv s).sum_comp (fun f : s.faces => c f.1)
  change _=∑ j : Fin s.faces.card,c (activeFaceEquiv s j).1
  rw [he]
  rw [←Finset.sum_subtype s.faces (fun _ => Iff.rfl) c]
  exact (Finset.sum_subset (Finset.subset_univ s.faces) (fun f _ hf => hz f hf)).symm

/-- The signed or absolute first-face coefficient can be any real
function. The exact theta power and original physical point are retained. -/
theorem sum_activeFace_first_weight_physical {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (y : Vector r) (c : Face p → ℝ) (K : ℕ) :
    (∑ f : Face p,c f*s.F (A.mulVec y)*s.pi (A.mulVec y) f*s.theta (A.mulVec y)^K)=
      ∑ j : Fin s.faces.card,c (activeFaceIndex s j)*
        logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y*
        logisticFaceWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y j*
        (1-logisticNullWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth y)^K := by
  rw [sum_activeFace_values s _ (fun f hf => by
    simp [FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hf])]
  simp_rw [activeFace_nullWeight,activeFace_piWeight,activeFace_thetaWeight]

/-- Every extra tuple label is reindexed exactly. Inactive tuples are
proved to vanish before the original finite family is replaced. -/
theorem sum_active_selectorWeight_physical {p r k : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (y : Vector r) (c : (Fin k → Face p) → ℝ) :
    (∑ α : Fin k → Face p,c α*selectorWeight s α (A.mulVec y))=
      ∑ β : Fin k → Fin s.faces.card,c (fun i => activeFaceIndex s (β i))*
        logisticTupleWeight (activeFaceNormals s A) (activeFaceOffsets s) s.bandwidth β y := by
  rw [sum_activeFace_tuples s _ (fun α hα => by
    cases k with
    | zero => exact False.elim (hα (fun i => Fin.elim0 i))
    | succ k => rw [selectorWeight_eq_zero_of_not_active s α hα,mul_zero])]
  change (∑ β : Fin k → Fin s.faces.card,c (fun i => activeFaceIndex s (β i))*
    selectorWeight s (fun i => activeFaceIndex s (β i)) (A.mulVec y))=_
  simp_rw [activeFace_selectorWeight_physical]

theorem selectorWeight_zero_of_faces_empty {p K : ℕ} (s : FaceSmoother p)
    (hs : s.faces=∅) (α : Fin (K+1) → Face p) (x : Vector p) :
    selectorWeight s α x=0 := by
  apply selectorWeight_eq_zero_of_not_active
  intro h
  have hh := h 0
  simpa only [hs,Finset.not_mem_empty] using hh

end
end RectangleCLTArxivV1
