import RectangleCLT.GaussianFourthDetAssembly
import RectangleCLT.GaussianFourthStability

/-! Nonnegative quantitative fourth-derivative caps, stable throughout the
actual local Taylor cube. Only their Gaussian soft-face moments depend on
the evaluation point. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

open GaussianTube

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

private theorem familyGram_det_nonneg {q : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Fin q → Face p) : 0 ≤ (faceFamilyGram f (A * A.transpose)).det := by
  let N : Matrix (Fin p) (Fin q) ℝ := fun j i => signedRowNormal A (f i) j
  have heq : faceFamilyGram f (A * A.transpose) = N.transpose * N := by
    ext i j
    symm
    exact signedRowNormal_gram A (f i) (f j)
  rw [heq]
  have hh := gram_det_ordered N.transpose
  simp only [Matrix.transpose_transpose] at hh
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin q)) := Nat.cast_pos.mpr Fintype.card_pos
  have hs : 0 ≤ ∑ g : Fin q → Fin p, ((N.transpose.submatrix id g).det) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith

private theorem tupleGram_det_nonneg {q : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (T : CompatibleFaceTuple p q) : 0 ≤ (T.gram (A * A.transpose)).det :=
  familyGram_det_nonneg A T.face

private theorem appendGram_det_nonneg {q : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (T : CompatibleFaceTuple p q) (f : Face p) :
    0 ≤ (T.appendGram f (A * A.transpose)).det :=
  familyGram_det_nonneg A (Fin.snoc T.face f)

private theorem appendTwoGram_det_nonneg {q : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (T : CompatibleFaceTuple p q) (f g : Face p) :
    0 ≤ (T.appendTwoGram f g (A * A.transpose)).det :=
  familyGram_det_nonneg A (Fin.snoc (Fin.snoc T.face f) g)

private theorem appendThreeGram_det_nonneg {q : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (T : CompatibleFaceTuple p q) (f g h : Face p) :
    0 ≤ (T.appendThreeGram f g h (A * A.transpose)).det :=
  familyGram_det_nonneg A (Fin.snoc (Fin.snoc (Fin.snoc T.face f) g) h)

private def StableCap (F : Vector p → ℝ) : Prop :=
  (∀ x, 0 ≤ F x) ∧ ∀ x {u : Vector p} {r : ℝ}, ‖u‖ ≤ r → r ≤ s.bandwidth →
    F (x + u) ≤ Real.exp 9 * F x

private theorem stableCap_add {F G : Vector p → ℝ} (hF : s.StableCap F)
    (hG : s.StableCap G) : s.StableCap (fun x => F x + G x) := by
  refine ⟨fun x => add_nonneg (hF.1 x) (hG.1 x), ?_⟩
  intro x u r hu hr
  exact (add_le_add (hF.2 x hu hr) (hG.2 x hu hr)).trans_eq (by ring)

private theorem stableCap_const_mul {F : Vector p → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hF : s.StableCap F) : s.StableCap (fun x => c * F x) := by
  refine ⟨fun x => mul_nonneg hc (hF.1 x), ?_⟩
  intro x u r hu hr
  exact (mul_le_mul_of_nonneg_left (hF.2 x hu hr) hc).trans_eq (by ring)

private theorem stableCap_sum {ι : Type*} (I : Finset ι) (F : ι → Vector p → ℝ)
    (hF : ∀ i ∈ I, s.StableCap (F i)) : s.StableCap (fun x => ∑ i ∈ I, F i x) := by
  refine ⟨fun x => Finset.sum_nonneg (fun i hi => (hF i hi).1 x), ?_⟩
  intro x u r hu hr
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => (hF i hi).2 x hu hr)

private theorem stableCap_moment (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (hS : S.card ≤ 4) (k : ℕ) :
    s.StableCap (fun x => s.gaussianSoftFaceMoment A x S k) :=
  ⟨fun x => s.gaussianSoftFaceMoment_nonneg A x S k,
    fun x _ _ hu hr => s.gaussianSoftFaceMoment_shift_le_exp_nine hp A x S hS k hu hr⟩

private theorem singletonCap_stable (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (T : CompatibleFaceTuple p 1) :
    s.StableCap (fun x => s.fourthSingletonMomentCap A a₃ a₄ x T) := by
  classical
  have hden : 0 < pairGap (A * A.transpose) * a₃ * a₄ := mul_pos (mul_pos hc ha3) ha4
  have hb := s.bandwidth_pos
  unfold fourthSingletonMomentCap
  apply s.stableCap_add
  · exact s.stableCap_const_mul (by positivity)
      (s.stableCap_moment hp A _ (by simp) 3)
  · apply s.stableCap_const_mul (by positivity)
    apply s.stableCap_sum
    intro f _
    apply s.stableCap_add
    · apply s.stableCap_const_mul
        (mul_nonneg (div_nonneg (by norm_num) hden.le) (appendGram_det_nonneg A T f))
      exact s.stableCap_moment hp A _ (by
        have hh := Finset.card_insert_le f T.activeFaceSet
        simp only [CompatibleFaceTuple.activeFaceSet_card] at hh
        omega) 2
    · apply s.stableCap_const_mul (by positivity)
      apply s.stableCap_sum
      intro g _
      apply s.stableCap_add
      · apply s.stableCap_const_mul
          (mul_nonneg (div_nonneg (by norm_num) hden.le) (appendTwoGram_det_nonneg A T f g))
        exact s.stableCap_moment hp A _ (by
          have hh := Finset.card_insert_le f T.activeFaceSet
          have hg := Finset.card_insert_le g (insert f T.activeFaceSet)
          simp only [CompatibleFaceTuple.activeFaceSet_card] at hh
          omega) 1
      · apply s.stableCap_const_mul (by positivity)
        apply s.stableCap_sum
        intro h _
        apply s.stableCap_const_mul
          (mul_nonneg (div_nonneg (by norm_num) hden.le) (appendThreeGram_det_nonneg A T f g h))
        exact s.stableCap_moment hp A _ (by
          have hh := Finset.card_insert_le f T.activeFaceSet
          have hg := Finset.card_insert_le g (insert f T.activeFaceSet)
          have hk := Finset.card_insert_le h (insert g (insert f T.activeFaceSet))
          simp only [CompatibleFaceTuple.activeFaceSet_card] at hh
          omega) 0

private theorem pairCap_stable (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (T : CompatibleFaceTuple p 2) :
    s.StableCap (fun x => s.fourthPairMomentCap A a₃ a₄ x T) := by
  classical
  have hden : 0 < pairGap (A * A.transpose) * a₃ * a₄ := mul_pos (mul_pos hc ha3) ha4
  have hb := s.bandwidth_pos
  unfold fourthPairMomentCap
  apply s.stableCap_add
  · exact s.stableCap_const_mul
      (mul_nonneg (div_nonneg (by norm_num) hden.le) (tupleGram_det_nonneg A T))
      (s.stableCap_moment hp A _ (by simp) 2)
  · apply s.stableCap_const_mul (by positivity)
    apply s.stableCap_sum
    intro f _
    apply s.stableCap_add
    · apply s.stableCap_const_mul
        (mul_nonneg (div_nonneg (by norm_num) hden.le) (appendGram_det_nonneg A T f))
      exact s.stableCap_moment hp A _ (by
        have hh := Finset.card_insert_le f T.activeFaceSet
        simp only [CompatibleFaceTuple.activeFaceSet_card] at hh
        omega) 1
    · apply s.stableCap_const_mul (by positivity)
      apply s.stableCap_sum
      intro g _
      apply s.stableCap_const_mul
        (mul_nonneg (div_nonneg (by norm_num) hden.le) (appendTwoGram_det_nonneg A T f g))
      exact s.stableCap_moment hp A _ (by
        have hh := Finset.card_insert_le f T.activeFaceSet
        have hg := Finset.card_insert_le g (insert f T.activeFaceSet)
        simp only [CompatibleFaceTuple.activeFaceSet_card] at hh
        omega) 0

private theorem tripleCap_stable (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (T : CompatibleFaceTuple p 3) :
    s.StableCap (fun x => s.fourthTripleMomentCap A a₃ a₄ x T) := by
  classical
  have hden : 0 < pairGap (A * A.transpose) * a₃ * a₄ := mul_pos (mul_pos hc ha3) ha4
  have hb := s.bandwidth_pos
  unfold fourthTripleMomentCap
  apply s.stableCap_add
  · exact s.stableCap_const_mul
      (mul_nonneg (div_nonneg zero_le_one hden.le) (tupleGram_det_nonneg A T))
      (s.stableCap_moment hp A _ (by simp) 1)
  · apply s.stableCap_const_mul (by positivity)
    apply s.stableCap_sum
    intro f _
    apply s.stableCap_const_mul
      (mul_nonneg (div_nonneg (by norm_num) hden.le) (appendGram_det_nonneg A T f))
    exact s.stableCap_moment hp A _ (by
      have hh := Finset.card_insert_le f T.activeFaceSet
      simp only [CompatibleFaceTuple.activeFaceSet_card] at hh
      omega) 0

private theorem quadrupleCap_stable (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (T : CompatibleFaceTuple p 4) :
    s.StableCap (fun x => s.fourthQuadrupleMomentCap A a₃ a₄ x T) := by
  have hden : 0 < pairGap (A * A.transpose) * a₃ * a₄ := mul_pos (mul_pos hc ha3) ha4
  exact s.stableCap_const_mul
    (mul_nonneg (div_nonneg zero_le_one hden.le) (tupleGram_det_nonneg A T))
    (s.stableCap_moment hp A _ (by simp) 0)

theorem fourthSingletonMomentCap_nonneg (A : Matrix (Fin p) (Fin p) ℝ)
    {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (T : CompatibleFaceTuple p 1) :
    0 ≤ s.fourthSingletonMomentCap A a₃ a₄ x T := by
  have hp : 1 ≤ p := by have hh := (T.face 0).1.isLt; omega
  exact (s.singletonCap_stable hp A ha3 ha4 hc T).1 x

theorem fourthPairMomentCap_nonneg (A : Matrix (Fin p) (Fin p) ℝ)
    {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (T : CompatibleFaceTuple p 2) :
    0 ≤ s.fourthPairMomentCap A a₃ a₄ x T := by
  have hp : 1 ≤ p := by have hh := (T.face 0).1.isLt; omega
  exact (s.pairCap_stable hp A ha3 ha4 hc T).1 x

theorem fourthTripleMomentCap_nonneg (A : Matrix (Fin p) (Fin p) ℝ)
    {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (T : CompatibleFaceTuple p 3) :
    0 ≤ s.fourthTripleMomentCap A a₃ a₄ x T := by
  have hp : 1 ≤ p := by have hh := (T.face 0).1.isLt; omega
  exact (s.tripleCap_stable hp A ha3 ha4 hc T).1 x

theorem fourthQuadrupleMomentCap_nonneg (A : Matrix (Fin p) (Fin p) ℝ)
    {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (T : CompatibleFaceTuple p 4) :
    0 ≤ s.fourthQuadrupleMomentCap A a₃ a₄ x T := by
  have hp : 1 ≤ p := by have hh := (T.face 0).1.isLt; omega
  exact (s.quadrupleCap_stable hp A ha3 ha4 hc T).1 x

theorem fourthSingletonMomentCap_shift_le_exp_nine (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (T : CompatibleFaceTuple p 1)
    {u : Vector p} {r : ℝ} (hu : ‖u‖ ≤ r) (hr : r ≤ s.bandwidth) :
    s.fourthSingletonMomentCap A a₃ a₄ (x + u) T ≤ Real.exp 9 * s.fourthSingletonMomentCap A a₃ a₄ x T :=
  (s.singletonCap_stable hp A ha3 ha4 hc T).2 x hu hr

theorem fourthPairMomentCap_shift_le_exp_nine (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (T : CompatibleFaceTuple p 2)
    {u : Vector p} {r : ℝ} (hu : ‖u‖ ≤ r) (hr : r ≤ s.bandwidth) :
    s.fourthPairMomentCap A a₃ a₄ (x + u) T ≤ Real.exp 9 * s.fourthPairMomentCap A a₃ a₄ x T :=
  (s.pairCap_stable hp A ha3 ha4 hc T).2 x hu hr

theorem fourthTripleMomentCap_shift_le_exp_nine (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (T : CompatibleFaceTuple p 3)
    {u : Vector p} {r : ℝ} (hu : ‖u‖ ≤ r) (hr : r ≤ s.bandwidth) :
    s.fourthTripleMomentCap A a₃ a₄ (x + u) T ≤ Real.exp 9 * s.fourthTripleMomentCap A a₃ a₄ x T :=
  (s.tripleCap_stable hp A ha3 ha4 hc T).2 x hu hr

theorem fourthQuadrupleMomentCap_shift_le_exp_nine (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {a₃ a₄ : ℝ} (ha3 : 0 < a₃) (ha4 : 0 < a₄)
    (hc : 0 < pairGap (A * A.transpose)) (x : Vector p) (T : CompatibleFaceTuple p 4)
    {u : Vector p} {r : ℝ} (hu : ‖u‖ ≤ r) (hr : r ≤ s.bandwidth) :
    s.fourthQuadrupleMomentCap A a₃ a₄ (x + u) T ≤ Real.exp 9 * s.fourthQuadrupleMomentCap A a₃ a₄ x T :=
  (s.quadrupleCap_stable hp A ha3 ha4 hc T).2 x hu hr

end
end RectangleCLT.FaceSmoother
