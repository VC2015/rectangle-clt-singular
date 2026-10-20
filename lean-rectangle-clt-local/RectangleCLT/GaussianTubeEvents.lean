import RectangleCLT.GaussianTubeMap
import RectangleCLT.ExponentialMixture

/-! Concrete common-space events for the augmented Gaussian face tubes.
Inactive face inequalities are strict, so distinct active sets have disjoint
images pointwise. They retain the same exponential tail probabilities. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

def activeFaces {p q : ℕ} (S : CompatibleFaceTuple p q) : Finset (Face p) :=
  Finset.univ.image S.face

def normalMatrix {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin q) ℝ :=
  fun j i => faceSign (S.face i) * A (S.face i).1 j

def activeOffsets {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (r : Vector p) : Fin q → ℝ :=
  fun i => s.offsets (S.face i) - FaceSmoother.normalDot (S.face i) r

def sourceDomain {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (width : ℝ) : Set (Coordinates p q) :=
  {w | (∀ i, 0 < tube w i ∧ tube w i < width) ∧
    ∀ f ∈ s.faces, f ∉ activeFaces S →
      E₀ * (s.weights (A.mulVec (base w) + r)).weight f < e f}

/-- The image lives in one common Gaussian/null-exponential/face-exponential
experiment, independently of the number or choice of its active coordinates. -/
def imageEvent {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) : Set (Vector p × (ℝ × (Face p → ℝ))) :=
  {ze | 0 < ze.2.1 ∧ (∀ f, 0 < ze.2.2 f) ∧
    Sum.elim ze.1 (fun i => ze.2.2 (S.face i)) ∈
      map (normalMatrix S A) s.bandwidth ze.2.1 (activeOffsets S s r) ''
        sourceDomain S s A r ze.2.1 ze.2.2 width}

theorem normalDot_eq_faceSign_mul {p : ℕ} (f : Face p) (x : Vector p) :
    FaceSmoother.normalDot f x = faceSign f * x f.1 := by
  cases hf : f.2 <;> simp [FaceSmoother.normalDot, faceSign, hf]

theorem activeScore_eq {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r z : Vector p) (i : Fin q) :
    (normalMatrix S A).transpose.mulVec z i - activeOffsets S s r i =
      s.faceScore (S.face i) (A.mulVec z + r) := by
  simp only [normalMatrix, activeOffsets, FaceSmoother.faceScore,
    normalDot_eq_faceSign_mul, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Pi.add_apply, Finset.mul_sum]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem activeExponential_eq {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces) (E₀ : ℝ) (w : Coordinates p q) (i : Fin q) :
    tube (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) w) i =
      E₀ * (s.weights (A.mulVec (base w) + r)).weight (S.face i) := by
  rw [tube_map, activeScore_eq]
  simp only [FaceSmoother.weights, hactive i, ↓reduceIte]

theorem measurableSet_sourceDomain {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (width : ℝ) :
    MeasurableSet (sourceDomain S s A r E₀ e width) := by
  have hb : Measurable (base : Coordinates p q → Vector p) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q))
  have hW := ((measurable_mulVec A).comp hb).add_const r
  simp only [sourceDomain, Set.setOf_and, Set.setOf_forall]
  refine MeasurableSet.inter (MeasurableSet.iInter (fun i => ?_))
    (MeasurableSet.iInter (fun f => MeasurableSet.iInter (fun _ =>
      MeasurableSet.iInter (fun _ => ?_))))
  · exact (measurableSet_lt measurable_const (measurable_pi_apply (Sum.inr i : Fin p ⊕ Fin q))).inter
      (measurableSet_lt (measurable_pi_apply (Sum.inr i : Fin p ⊕ Fin q)) measurable_const)
  · exact measurableSet_lt (((s.continuous_weight f).measurable.comp hW).const_mul E₀)
      measurable_const

theorem map_inverse {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : 0 < E₀)
    (hd : IsUnit (N.transpose * N).det) (a : Fin q → ℝ) (y : Coordinates p q)
    (hE : ∀ i, 0 < tube y i) :
    map N h E₀ a (inverse N h E₀ a y) = y := by
  have hscores : N.transpose.mulVec (base (inverse N h E₀ a y)) =
      activeThreshold h E₀ a (tube y) := by
    change N.transpose.mulVec (base y - N.mulVec (recoveredTube N h E₀ a y)) = _
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    unfold recoveredTube
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec,
      sub_sub_cancel]
  ext j
  cases j with
  | inl j =>
    change (base y - N.mulVec (recoveredTube N h E₀ a y) +
      N.mulVec (recoveredTube N h E₀ a y)) j = y (.inl j)
    rw [sub_add_cancel]
    rfl
  | inr i =>
    change E₀ * Real.exp ((N.transpose.mulVec (base (inverse N h E₀ a y)) i - a i) / h) = _
    rw [hscores]
    have he : (activeThreshold h E₀ a (tube y) i - a i) / h = Real.log (tube y i / E₀) := by
      dsimp [activeThreshold]
      field_simp
    rw [he, Real.exp_log (div_pos (hE i) hE₀), mul_div_cancel₀ _ hE₀.ne']
    rfl

/-- Explicit inverse coordinates, jointly measurable in the deterministic
shift and the common Gaussian/exponential output experiment. -/
def imagePreimage {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (rze : Vector p × (Vector p × (ℝ × (Face p → ℝ)))) : Coordinates p q :=
  inverse (normalMatrix S A) s.bandwidth rze.2.2.1 (activeOffsets S s rze.1)
    (Sum.elim rze.2.1 (fun i => rze.2.2.2 (S.face i)))

theorem imageEvent_iff_preimage {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (ze : Vector p × (ℝ × (Face p → ℝ))) :
    ze ∈ imageEvent S s A r width ↔ 0 < ze.2.1 ∧ (∀ f, 0 < ze.2.2 f) ∧
      imagePreimage S s A (r, ze) ∈ sourceDomain S s A r ze.2.1 ze.2.2 width := by
  constructor
  · rintro ⟨h0, he, w, hw, hmap⟩
    refine ⟨h0, he, ?_⟩
    change inverse (normalMatrix S A) s.bandwidth ze.2.1 (activeOffsets S s r)
      (Sum.elim ze.1 (fun i => ze.2.2 (S.face i))) ∈ _
    rw [← hmap, inverse_map _ s.bandwidth_pos.ne' h0.ne' hd]
    exact hw
  · rintro ⟨h0, he, hw⟩
    refine ⟨h0, he, imagePreimage S s A (r, ze), hw, ?_⟩
    exact map_inverse _ s.bandwidth_pos.ne' h0 hd _ _ (fun i => he (S.face i))

theorem measurable_imagePreimage {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (imagePreimage S s A) := by
  apply measurable_pi_lambda
  intro j
  cases j <;> simp only [imagePreimage, inverse, recoveredTube, activeThreshold,
    activeOffsets, base, tube, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec,
    dotProduct, Pi.sub_apply, normalDot_eq_faceSign_mul]
  all_goals fun_prop

/-- Joint measurability allows a bounded random base to enter as the shift
without conditioning on a nonmeasurable family of tube images. -/
theorem measurableSet_imageEvent_joint {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (width : ℝ)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    MeasurableSet {rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) |
      rze.2 ∈ imageEvent S s A rze.1 width} := by
  simp_rw [imageEvent_iff_preimage S s A _ width hd]
  have hpre := measurable_imagePreimage S s A
  have hb : Measurable (fun rze => base (imagePreimage S s A rze)) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp hpre)
  have hW : Measurable (fun rze => A.mulVec (base (imagePreimage S s A rze)) + rze.1) :=
    ((measurable_mulVec A).comp hb).add measurable_fst
  change MeasurableSet {rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) |
    0 < rze.2.2.1 ∧ (∀ f, 0 < rze.2.2.2 f) ∧
      (∀ i, 0 < tube (imagePreimage S s A rze) i ∧ tube (imagePreimage S s A rze) i < width) ∧
      ∀ f ∈ s.faces, f ∉ activeFaces S →
        rze.2.2.1 * (s.weights (A.mulVec (base (imagePreimage S s A rze)) + rze.1)).weight f < rze.2.2.2 f}
  simp only [Set.setOf_and, Set.setOf_forall]
  refine MeasurableSet.inter (measurableSet_lt measurable_const ?_)
    (MeasurableSet.inter (MeasurableSet.iInter (fun f => ?_))
      (MeasurableSet.inter (MeasurableSet.iInter (fun i => ?_))
        (MeasurableSet.iInter (fun f => MeasurableSet.iInter (fun _ =>
          MeasurableSet.iInter (fun _ => ?_))))))
  · fun_prop
  · exact measurableSet_lt measurable_const (by fun_prop)
  · have ht := (measurable_pi_apply (Sum.inr i : Fin p ⊕ Fin q)).comp hpre
    exact (measurableSet_lt measurable_const ht).inter (measurableSet_lt ht measurable_const)
  · have h0 : Measurable (fun rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) => rze.2.2.1) := by
      fun_prop
    exact measurableSet_lt (h0.mul ((s.continuous_weight f).measurable.comp hW)) (by fun_prop)

end
end RectangleCLT.GaussianTube
