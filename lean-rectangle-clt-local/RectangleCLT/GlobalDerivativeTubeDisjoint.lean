import RectangleCLT.GlobalDerivativeTube
import RectangleCLT.GaussianTubeUnion

/-! Full coordinate dual tubes have disjoint images. In physical
coordinates their displacement changes only active coordinates, pushing
each active face outward and every inactive face inward or tangentially.
Consequently the violated face set identifies the active face family.
These are geometric facts, not an asserted Gaussian derivative cap. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

def dualImageEvent {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) : Set (Vector p × (ℝ × (Face p → ℝ))) :=
  {ze | 0 < ze.2.1 ∧ (∀ f, 0 < ze.2.2 f) ∧
    Sum.elim ze.1 (fun i => ze.2.2 (S.face i)) ∈
      dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth ze.2.1 (activeOffsets S s r) ''
          sourceDomain S s A r ze.2.1 ze.2.2 width}

def dualImagePreimage {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (w : Vector p × (Vector p × (ℝ × (Face p → ℝ)))) : Coordinates p q :=
  dualInverse (normalMatrix S A) (fullDualMatrix S A)
    s.bandwidth w.2.2.1 (activeOffsets S s w.1)
      (Sum.elim w.2.1 (fun i => w.2.2.2 (S.face i)))

theorem faceDot_signedRow_eq_normalDot {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (f : Face p) (x : Vector p) :
    faceDot (signedRowNormal A f) x = FaceSmoother.normalDot f (A.mulVec x) := by
  simp only [faceDot, signedRowNormal, normalDot_eq_faceSign_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem inactive_face_fullDual_column_nonpos {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (A * A.transpose).det) (f : Face p)
    (hf : f ∉ activeFaces S) (i : Fin q) :
    faceDot (signedRowNormal A f) (fun j => fullDualMatrix S A j i) ≤ 0 := by
  classical
  rw [faceDot_signedRow_eq_normalDot]
  by_cases hcoord : f.1 = (S.face i).1
  · have hneq : f ≠ S.face i := by
      intro heq
      apply hf
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq.symm⟩
    have hbool : f.2 ≠ (S.face i).2 := fun h => hneq (Prod.ext hcoord h)
    have hsign : faceSign f * faceSign (S.face i) ≤ 0 := by
      cases hfb : f.2 <;> cases hsb : (S.face i).2 <;>
        simp_all [faceSign]
    rw [fullDualMatrix_factor_column S A hd]
    simpa only [normalDot_eq_faceSign_mul, Pi.smul_apply, smul_eq_mul,
      FaceSmoother.coordinateDirection, if_pos hcoord, mul_one] using hsign
  · rw [normalDot_fullDualMatrix_factor_column_eq_zero S A hd i f hcoord]

theorem faceDot_fullDual_displacement {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Face p) (u : Fin q → ℝ) :
    faceDot (signedRowNormal A f) ((fullDualMatrix S A).mulVec u) =
      ∑ i, faceDot (signedRowNormal A f) (fun j => fullDualMatrix S A j i) * u i := by
  simp only [faceDot, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem active_face_fullDual_displacement {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (A * A.transpose).det) (u : Fin q → ℝ) (i : Fin q) :
    faceDot (signedRowNormal A (S.face i)) ((fullDualMatrix S A).mulVec u) = u i := by
  have hrow (v : Vector p) :
      (normalMatrix S A).transpose.mulVec v i =
        faceDot (signedRowNormal A (S.face i)) v := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      normalMatrix, signedRowNormal, faceDot]
  rw [← hrow, Matrix.mulVec_mulVec,
    normalMatrix_transpose_mul_fullDualMatrix S A hd, Matrix.one_mulVec]

theorem fullDual_displacement_violates_iff {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (offset : Face p → ℝ) (z : Vector p) (u : Fin q → ℝ)
    (hz : z ∈ exactActiveFace s.faces (activeFaces S) (signedRowNormal A) offset)
    (hu : ∀ i, 0 < u i) (f : Face p) (hf : f ∈ s.faces) :
    offset f < faceDot (signedRowNormal A f) (z + (fullDualMatrix S A).mulVec u) ↔
      f ∈ activeFaces S := by
  classical
  have hadd : faceDot (signedRowNormal A f) (z + (fullDualMatrix S A).mulVec u) =
      faceDot (signedRowNormal A f) z +
        faceDot (signedRowNormal A f) ((fullDualMatrix S A).mulVec u) := by
    simp only [faceDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hadd]
  by_cases hfa : f ∈ activeFaces S
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hfa
    have heq := (hz.2 (S.face i) hf).mpr hfa
    rw [active_face_fullDual_displacement S A hd, heq]
    constructor
    · intro _
      exact hfa
    · intro _
      linarith [hu i]
  · have hmove : faceDot (signedRowNormal A f) ((fullDualMatrix S A).mulVec u) ≤ 0 := by
      rw [faceDot_fullDual_displacement]
      exact Finset.sum_nonpos (fun i _ =>
        mul_nonpos_of_nonpos_of_nonneg
          (inactive_face_fullDual_column_nonpos S A hd f hfa i) (hu i).le)
    have hbase := hz.1 f hf
    exact iff_of_false (by linarith) hfa

theorem dualImageEvent_violates_iff {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (r : Vector p) (hactive : ∀ i, S.face i ∈ s.faces)
    (width : ℝ) {ze : Vector p × (ℝ × (Face p → ℝ))}
    (hze : ze ∈ dualImageEvent S s A r width) (f : Face p) (hf : f ∈ s.faces) :
    commonOffsets s r ze.2 f < faceDot (signedRowNormal A f) ze.1 ↔
      f ∈ activeFaces S := by
  obtain ⟨h0, he, w, hw, hmap⟩ := hze
  have hb : base w + (fullDualMatrix S A).mulVec (tube w) = ze.1 :=
    congrArg base hmap
  have ht (i : Fin q) :
      tube (map (normalMatrix S A) s.bandwidth ze.2.1 (activeOffsets S s r) w) i =
        ze.2.2 (S.face i) := by
    exact congrFun (congrArg tube hmap) i
  have hsource := source_base_exactActiveFace S s A r hactive ze.2 h0 he width w hw ht
  rw [← hb]
  exact fullDual_displacement_violates_iff S s A hd _ _ _ hsource
    (fun i => (hw.1 i).1) f hf

theorem dualImageEvent_disjoint {p q k : ℕ}
    (S : CompatibleFaceTuple p q) (T : CompatibleFaceTuple p k)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (A * A.transpose).det) (r : Vector p)
    (hS : ∀ i, S.face i ∈ s.faces) (hT : ∀ i, T.face i ∈ s.faces)
    (width : ℝ) (hne : activeFaces S ≠ activeFaces T) :
    Disjoint (dualImageEvent S s A r width) (dualImageEvent T s A r width) := by
  classical
  rw [Set.disjoint_left]
  intro ze hzS hzT
  apply hne
  ext f
  constructor
  · intro hf
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hf
    have hface : f ∈ s.faces := hi ▸ hS i
    exact (dualImageEvent_violates_iff T s A hd r hT width hzT f hface).mp
      ((dualImageEvent_violates_iff S s A hd r hS width hzS f hface).mpr hf)
  · intro hf
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hf
    have hface : f ∈ s.faces := hi ▸ hT i
    exact (dualImageEvent_violates_iff S s A hd r hS width hzS f hface).mp
      ((dualImageEvent_violates_iff T s A hd r hT width hzT f hface).mpr hf)

theorem dualImageEvent_mem_boundaryLayer {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (r : Vector p) (hactive : ∀ i, S.face i ∈ s.faces) (hq : 0 < q)
    {width : ℝ} (hw0 : 0 ≤ width) {ze : CommonSamples p}
    (hze : ze ∈ dualImageEvent S s A r width) :
    A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).boundaryLayer ((q : ℝ) * width) := by
  obtain ⟨h0, he, w, hw, hmap⟩ := hze
  have hb : base w + (fullDualMatrix S A).mulVec (tube w) = ze.1 :=
    congrArg base hmap
  have ht (i : Fin q) :
      tube (map (normalMatrix S A) s.bandwidth ze.2.1 (activeOffsets S s r) w) i =
        ze.2.2 (S.face i) := congrFun (congrArg tube hmap) i
  have hsource := source_base_exactActiveFace S s A r hactive ze.2 h0 he width w hw ht
  have hphysical (f : Face p) :
      FaceSmoother.normalDot f (A.mulVec ze.1 + r) =
        faceDot (signedRowNormal A f) ze.1 + FaceSmoother.normalDot f r := by
    rw [faceDot_signedRow_eq_normalDot]
    cases hf : f.2 <;> simp [FaceSmoother.normalDot, hf, add_comm]
  have hstep (f : Face p) :
      faceDot (signedRowNormal A f) ((fullDualMatrix S A).mulVec (tube w)) ≤
        (q : ℝ) * width := by
    rw [faceDot_fullDual_displacement]
    calc
      _ ≤ ∑ i, |faceDot (signedRowNormal A f) (fun j => fullDualMatrix S A j i)| *
          |tube w i| := Finset.sum_le_sum (fun i _ => by
        simpa only [abs_mul] using le_abs_self
          (faceDot (signedRowNormal A f) (fun j => fullDualMatrix S A j i) * tube w i))
      _ ≤ ∑ _i : Fin q, (1 : ℝ) * width := by
        apply Finset.sum_le_sum
        intro i _
        have hcol : |faceDot (signedRowNormal A f)
            (fun j => fullDualMatrix S A j i)| ≤ 1 := by
          rw [faceDot_signedRow_eq_normalDot]
          exact abs_normalDot_fullDualMatrix_factor_column_le_one S A hd i f
        exact mul_le_mul hcol (by simpa only [abs_of_pos (hw.1 i).1] using (hw.1 i).2.le)
          (abs_nonneg _) zero_le_one
      _ = _ := by simp
  have hqwidth : 0 ≤ (q : ℝ) * width := mul_nonneg (Nat.cast_nonneg q) hw0
  change (∀ f ∈ s.faces, FaceSmoother.normalDot f (A.mulVec ze.1 + r) ≤
      s.offsets f + s.bandwidth * Real.log (ze.2.2 f / ze.2.1) + (q : ℝ) * width) ∧
    ¬ (∀ f ∈ s.faces, FaceSmoother.normalDot f (A.mulVec ze.1 + r) ≤
      s.offsets f + s.bandwidth * Real.log (ze.2.2 f / ze.2.1) + -((q : ℝ) * width))
  constructor
  · intro f hf
    have hbase := hsource.1 f hf
    have hout : faceDot (signedRowNormal A f) ze.1 ≤
        commonOffsets s r ze.2 f + (q : ℝ) * width := by
      rw [← hb]
      have hadd : faceDot (signedRowNormal A f)
          (base w + (fullDualMatrix S A).mulVec (tube w)) =
          faceDot (signedRowNormal A f) (base w) +
            faceDot (signedRowNormal A f) ((fullDualMatrix S A).mulVec (tube w)) := by
        simp only [faceDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [hadd]
      exact add_le_add hbase (hstep f)
    rw [hphysical]
    dsimp only [commonOffsets] at hout
    linarith
  · intro hinner
    let i : Fin q := ⟨0, hq⟩
    have hmem : S.face i ∈ activeFaces S :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hviol := (fullDual_displacement_violates_iff S s A hd
      (commonOffsets s r ze.2) (base w) (tube w) hsource
      (fun j => (hw.1 j).1) (S.face i) (hactive i)).mpr hmem
    rw [hb] at hviol
    have hi := hinner (S.face i) (hactive i)
    rw [hphysical] at hi
    dsimp only [commonOffsets] at hviol
    linarith

end

end RectangleCLT.GaussianTube
