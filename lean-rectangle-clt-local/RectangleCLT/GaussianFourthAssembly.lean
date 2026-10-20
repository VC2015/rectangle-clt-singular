import RectangleCLT.GaussianFourthBound
import RectangleCLT.GaussianThirdAssembly
import RectangleCLT.GaussianFaceIndexFour

/-! Finite bookkeeping for the five equality patterns of an ordered fourth
derivative tensor. The constants count positions, independently of dimension. -/

open scoped BigOperators

namespace RectangleCLT

noncomputable section

private def fourthPatternTerms {ι : Type*} [DecidableEq ι]
    (M4 : ι → ℝ) (M31 M22 : ι → ι → ℝ)
    (M211 : ι → ι → ι → ℝ) (M1111 : ι → ι → ι → ι → ℝ)
    (a b c d : ι) : Fin 15 → ℝ :=
  ![if a = b ∧ a = c ∧ a = d then M4 a else 0,
    if a = b ∧ a = c then M31 a d else 0,
    if a = b ∧ a = d then M31 a c else 0,
    if a = c ∧ a = d then M31 a b else 0,
    if b = c ∧ b = d then M31 b a else 0,
    if a = b ∧ c = d then M22 a c else 0,
    if a = c ∧ b = d then M22 a b else 0,
    if a = d ∧ b = c then M22 a b else 0,
    if a = b then M211 a c d else 0,
    if a = c then M211 a b d else 0,
    if a = d then M211 a b c else 0,
    if b = c then M211 b a d else 0,
    if b = d then M211 b a c else 0,
    if c = d then M211 c a b else 0,
    M1111 a b c d]

private theorem fourthPatternTerms_nonneg {ι : Type*} [DecidableEq ι]
    (M4 : ι → ℝ) (M31 M22 : ι → ι → ℝ)
    (M211 : ι → ι → ι → ℝ) (M1111 : ι → ι → ι → ι → ℝ)
    (h4 : ∀ a, 0 ≤ M4 a) (h31 : ∀ a b, 0 ≤ M31 a b)
    (h22 : ∀ a b, 0 ≤ M22 a b) (h211 : ∀ a b c, 0 ≤ M211 a b c)
    (h1111 : ∀ a b c d, 0 ≤ M1111 a b c d)
    (a b c d : ι) (i : Fin 15) : 0 ≤ fourthPatternTerms M4 M31 M22 M211 M1111 a b c d i := by
  fin_cases i <;> dsimp [fourthPatternTerms]
  all_goals first
    | exact h1111 _ _ _ _
    | split_ifs <;> first
      | exact h4 _
      | exact h31 _ _
      | exact h22 _ _
      | exact h211 _ _ _
      | exact le_rfl

private theorem fourth_le_pattern_terms {ι : Type*} [DecidableEq ι]
    (f : ι → ι → ι → ι → ℝ)
    (hs01 : ∀ a b c d, f a b c d = f b a c d)
    (hs12 : ∀ a b c d, f a b c d = f a c b d)
    (hs23 : ∀ a b c d, f a b c d = f a b d c)
    (M4 : ι → ℝ) (M31 M22 : ι → ι → ℝ)
    (M211 : ι → ι → ι → ℝ) (M1111 : ι → ι → ι → ι → ℝ)
    (h4 : ∀ a, 0 ≤ M4 a) (h31 : ∀ a b, 0 ≤ M31 a b)
    (h22 : ∀ a b, 0 ≤ M22 a b) (h211 : ∀ a b c, 0 ≤ M211 a b c)
    (h1111 : ∀ a b c d, 0 ≤ M1111 a b c d)
    (hf4 : ∀ a, f a a a a ≤ M4 a)
    (hf31 : ∀ a b, a ≠ b → f a a a b ≤ M31 a b)
    (hf22 : ∀ a b, a ≠ b → f a a b b ≤ M22 a b)
    (hf211 : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → f a a b c ≤ M211 a b c)
    (hf1111 : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d →
      b ≠ c → b ≠ d → c ≠ d → f a b c d ≤ M1111 a b c d)
    (a b c d : ι) :
    f a b c d ≤ ∑ i, fourthPatternTerms M4 M31 M22 M211 M1111 a b c d i := by
  have choose (i : Fin 15)
      (hi : f a b c d ≤ fourthPatternTerms M4 M31 M22 M211 M1111 a b c d i) :
      f a b c d ≤ ∑ i, fourthPatternTerms M4 M31 M22 M211 M1111 a b c d i :=
    hi.trans (Finset.single_le_sum
      (fun j _ => fourthPatternTerms_nonneg M4 M31 M22 M211 M1111
        h4 h31 h22 h211 h1111 a b c d j) (Finset.mem_univ i))
  by_cases hab : a = b
  · subst b
    by_cases hac : a = c
    · subst c
      by_cases had : a = d
      · subst d
        apply choose 0
        simpa [fourthPatternTerms] using hf4 a
      · apply choose 1
        simpa [fourthPatternTerms] using hf31 a d had
    · by_cases had : a = d
      · subst d
        apply choose 2
        simpa [fourthPatternTerms, hs23 a a c a] using hf31 a c hac
      · by_cases hcd : c = d
        · subst d
          apply choose 5
          simpa [fourthPatternTerms] using hf22 a c hac
        · apply choose 8
          simpa [fourthPatternTerms] using hf211 a c d hac had hcd
  · by_cases hac : a = c
    · subst c
      by_cases had : a = d
      · subst d
        apply choose 3
        have heq : f a b a a = f a a a b :=
          (hs12 a b a a).trans (hs23 a a b a)
        simpa [fourthPatternTerms, heq] using hf31 a b hab
      · by_cases hbd : b = d
        · subst d
          apply choose 6
          simpa [fourthPatternTerms, hs12 a b a b] using hf22 a b hab
        · apply choose 9
          simpa [fourthPatternTerms, hs12 a b a d] using hf211 a b d hab had hbd
    · by_cases had : a = d
      · subst d
        by_cases hbc : b = c
        · subst c
          apply choose 7
          have heq : f a b b a = f a a b b :=
            (hs23 a b b a).trans (hs12 a b a b)
          simpa [fourthPatternTerms, heq] using hf22 a b hab
        · apply choose 10
          have heq : f a b c a = f a a b c :=
            (hs23 a b c a).trans (hs12 a b a c)
          simpa [fourthPatternTerms, heq] using hf211 a b c hab hac hbc
      · by_cases hbc : b = c
        · subst c
          by_cases hbd : b = d
          · subst d
            apply choose 4
            have heq : f a b b b = f b b b a :=
              (hs01 a b b b).trans ((hs12 b a b b).trans (hs23 b b a b))
            simpa [fourthPatternTerms, heq] using hf31 b a (Ne.symm hab)
          · apply choose 11
            have heq : f a b b d = f b b a d :=
              (hs01 a b b d).trans (hs12 b a b d)
            simpa [fourthPatternTerms, heq] using hf211 b a d (Ne.symm hab) hbd had
        · by_cases hbd : b = d
          · subst d
            apply choose 12
            have heq : f a b c b = f b b a c :=
              (hs23 a b c b).trans ((hs01 a b b c).trans (hs12 b a b c))
            simpa [fourthPatternTerms, heq] using hf211 b a c (Ne.symm hab) hbc hac
          · by_cases hcd : c = d
            · subst d
              apply choose 13
              have heq : f a b c c = f c c a b :=
                (hs12 a b c c).trans ((hs01 a c b c).trans
                  ((hs23 c a b c).trans (hs12 c a c b)))
              simpa [fourthPatternTerms, heq] using hf211 c a b (Ne.symm hac) (Ne.symm hbc) hab
            · apply choose 14
              simpa [fourthPatternTerms] using hf1111 a b c d hab hac had hbc hbd hcd

private theorem sum_fourthPatternTerms_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M4 : ι → ℝ) (M31 M22 : ι → ι → ℝ)
    (M211 : ι → ι → ι → ℝ) (M1111 : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ i,
      fourthPatternTerms M4 M31 M22 M211 M1111 a b c d i) =
      (∑ a, M4 a) + 4 * (∑ a, ∑ b, M31 a b) + 3 * (∑ a, ∑ b, M22 a b) +
        6 * (∑ a, ∑ b, ∑ c, M211 a b c) + ∑ a, ∑ b, ∑ c, ∑ d, M1111 a b c d := by
  have hif (P : Prop) [Decidable P] (g : ι → ℝ) :
      (∑ i, if P then g i else 0) = if P then ∑ i, g i else 0 := by
    by_cases hP : P <;> simp [hP]
  have h31swap : (∑ a, ∑ b, M31 b a) = ∑ a, ∑ b, M31 a b := Finset.sum_comm
  have h211swap : (∑ a, ∑ b, ∑ c, M211 b a c) = ∑ a, ∑ b, ∑ c, M211 a b c :=
    Finset.sum_comm
  have h211rotate : (∑ a, ∑ b, ∑ c, M211 c a b) = ∑ a, ∑ b, ∑ c, M211 a b c := by
    calc
      _ = ∑ a, ∑ c, ∑ b, M211 c a b := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp only [fourthPatternTerms, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Finset.sum_add_distrib, Finset.sum_const_zero, add_zero,
    ite_and, hif, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h31swap, h211swap, h211rotate]
  ring

/-- Summing a symmetric ordered fourth tensor costs only the five canonical
equality patterns, with universal position counts `1,4,3,6,1`. The caps are
summed over all indices; nonnegativity permits repeated indices in these
upper sums. No nonnegativity assumption is made on the tensor itself. -/
theorem sum_symmetric_fourth_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ι → ι → ι → ℝ)
    (hs01 : ∀ a b c d, f a b c d = f b a c d)
    (hs12 : ∀ a b c d, f a b c d = f a c b d)
    (hs23 : ∀ a b c d, f a b c d = f a b d c)
    (M4 : ι → ℝ) (M31 M22 : ι → ι → ℝ)
    (M211 : ι → ι → ι → ℝ) (M1111 : ι → ι → ι → ι → ℝ)
    (h4 : ∀ a, 0 ≤ M4 a) (h31 : ∀ a b, 0 ≤ M31 a b)
    (h22 : ∀ a b, 0 ≤ M22 a b) (h211 : ∀ a b c, 0 ≤ M211 a b c)
    (h1111 : ∀ a b c d, 0 ≤ M1111 a b c d)
    (hf4 : ∀ a, f a a a a ≤ M4 a)
    (hf31 : ∀ a b, a ≠ b → f a a a b ≤ M31 a b)
    (hf22 : ∀ a b, a ≠ b → f a a b b ≤ M22 a b)
    (hf211 : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → f a a b c ≤ M211 a b c)
    (hf1111 : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d →
      b ≠ c → b ≠ d → c ≠ d → f a b c d ≤ M1111 a b c d) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) ≤
      (∑ a, M4 a) + 4 * (∑ a, ∑ b, M31 a b) + 3 * (∑ a, ∑ b, M22 a b) +
        6 * (∑ a, ∑ b, ∑ c, M211 a b c) + ∑ a, ∑ b, ∑ c, ∑ d, M1111 a b c d := by
  rw [← sum_fourthPatternTerms_eq]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro c _
  apply Finset.sum_le_sum
  intro d _
  exact fourth_le_pattern_terms f hs01 hs12 hs23 M4 M31 M22 M211 M1111
    h4 h31 h22 h211 h1111 hf4 hf31 hf22 hf211 hf1111 a b c d

end
end RectangleCLT

namespace RectangleCLT.FaceSmoother

open MeasureTheory
open GaussianTube

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem convolutionFourthDerivative_eq_standardGaussian
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw A) x j k l m =
      ∫ z, s.mixedFourthDerivativeF (A.mulVec z + x) j k l m ∂standardGaussian p := by
  have hm : AEStronglyMeasurable
      (fun y : Vector p => s.mixedFourthDerivativeF (x + y) j k l m)
      ((standardGaussian p).map A.mulVec) :=
    (((s.continuous_fourthDerivative j k l m).comp
      (continuous_const.add continuous_id)).measurable.aestronglyMeasurable)
  calc
    _ = ∫ y, s.mixedFourthDerivativeF (x + y) j k l m ∂gaussianLaw A :=
      s.convolutionFourthDerivative_eq_integral (gaussianLaw A) x j k l m
    _ = ∫ z, s.mixedFourthDerivativeF (x + A.mulVec z) j k l m ∂standardGaussian p :=
      integral_map (measurable_mulVec A).aemeasurable hm
    _ = _ := integral_congr_ae (ae_of_all _ (fun z =>
      congrArg (fun y : Vector p => s.mixedFourthDerivativeF y j k l m)
        (add_comm x (A.mulVec z))))

private theorem fourth_diag_symm (w : FaceWeights p) (j k : Fin p) :
    w.diagonalMass j k = w.diagonalMass k j := by
  by_cases h : j = k
  · subst k; rfl
  · simp only [FaceWeights.diagonalMass, h, Ne.symm h, ↓reduceIte]

private theorem fourth_third01 (w : FaceWeights p) (j k l : Fin p) :
    w.thirdDiagonalMass j k l = w.thirdDiagonalMass k j l := by
  by_cases h : j = k
  · subst k; rfl
  · simp only [FaceWeights.thirdDiagonalMass, h, Ne.symm h, false_and, ↓reduceIte]

private theorem fourth_third12 (w : FaceWeights p) (j k l : Fin p) :
    w.thirdDiagonalMass j k l = w.thirdDiagonalMass j l k := by
  simp only [FaceWeights.thirdDiagonalMass, and_comm]

private theorem fourth_fourth01 (w : FaceWeights p) (j k l m : Fin p) :
    w.fourthDiagonalMass j k l m = w.fourthDiagonalMass k j l m := by
  by_cases h : j = k
  · subst k; rfl
  · simp only [FaceWeights.fourthDiagonalMass, h, Ne.symm h, false_and, ↓reduceIte]

private theorem fourth_fourth12 (w : FaceWeights p) (j k l m : Fin p) :
    w.fourthDiagonalMass j k l m = w.fourthDiagonalMass j l k m := by
  simp only [FaceWeights.fourthDiagonalMass, and_left_comm]

private theorem fourth_fourth23 (w : FaceWeights p) (j k l m : Fin p) :
    w.fourthDiagonalMass j k l m = w.fourthDiagonalMass j k m l := by
  simp only [FaceWeights.fourthDiagonalMass, and_comm]

theorem mixedFourthDerivativeF_swap_first_two (x : Vector p) (j k l m : Fin p) :
    s.mixedFourthDerivativeF x j k l m = s.mixedFourthDerivativeF x k j l m := by
  simp only [s.mixedFourthDerivativeF_eq, FaceWeights.fourthFactor]
  rw [fourth_diag_symm (s.weights x) j k,
    fourth_third01 (s.weights x) j k l, fourth_third01 (s.weights x) j k m,
    fourth_fourth01 (s.weights x) j k l m]
  ring

theorem mixedFourthDerivativeF_swap_middle_two (x : Vector p) (j k l m : Fin p) :
    s.mixedFourthDerivativeF x j k l m = s.mixedFourthDerivativeF x j l k m := by
  simp only [s.mixedFourthDerivativeF_eq, FaceWeights.fourthFactor]
  rw [fourth_diag_symm (s.weights x) k l,
    fourth_third12 (s.weights x) j k l, fourth_third01 (s.weights x) k l m,
    fourth_fourth12 (s.weights x) j k l m]
  ring

theorem mixedFourthDerivativeF_swap_last_two (x : Vector p) (j k l m : Fin p) :
    s.mixedFourthDerivativeF x j k l m = s.mixedFourthDerivativeF x j k m l := by
  simp only [s.mixedFourthDerivativeF_eq, FaceWeights.fourthFactor]
  rw [fourth_diag_symm (s.weights x) l m,
    fourth_third12 (s.weights x) j l m, fourth_third12 (s.weights x) k l m,
    fourth_fourth23 (s.weights x) j k l m]
  ring

theorem convolutionFourthDerivative_swap_first_two
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw A) x j k l m =
      s.convolutionFourthDerivative (gaussianLaw A) x k j l m := by
  rw [s.convolutionFourthDerivative_eq_standardGaussian,
    s.convolutionFourthDerivative_eq_standardGaussian]
  exact integral_congr_ae (ae_of_all _ (fun z => s.mixedFourthDerivativeF_swap_first_two _ j k l m))

theorem convolutionFourthDerivative_swap_middle_two
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw A) x j k l m =
      s.convolutionFourthDerivative (gaussianLaw A) x j l k m := by
  rw [s.convolutionFourthDerivative_eq_standardGaussian,
    s.convolutionFourthDerivative_eq_standardGaussian]
  exact integral_congr_ae (ae_of_all _ (fun z => s.mixedFourthDerivativeF_swap_middle_two _ j k l m))

theorem convolutionFourthDerivative_swap_last_two
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw A) x j k l m =
      s.convolutionFourthDerivative (gaussianLaw A) x j k m l := by
  rw [s.convolutionFourthDerivative_eq_standardGaussian,
    s.convolutionFourthDerivative_eq_standardGaussian]
  exact integral_congr_ae (ae_of_all _ (fun z => s.mixedFourthDerivativeF_swap_last_two _ j k l m))

theorem integrable_softFaceCoordinateThird_gaussian
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (x : Vector p) (j : Fin p) :
    Integrable (fun z => s.softFaceCoordinateThird S j (A.mulVec z + x))
      (standardGaussian p) := by
  obtain ⟨C, hC⟩ := s.softFaceCoordinateThird_bounded S j
  apply (integrable_const C).mono'
    (((s.continuous_softFaceCoordinateThird S j).comp
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun z => hC _)

theorem integrable_softFaceMixedSecond_gaussian
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (x : Vector p) (j k : Fin p) :
    Integrable (fun z => s.softFaceMixedSecond S j k (A.mulVec z + x))
      (standardGaussian p) := by
  obtain ⟨C, hC⟩ := s.softFaceMixedSecond_bounded S j k
  apply (integrable_const C).mono'
    (((s.continuous_softFaceMixedSecond S j k).comp
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun z => hC _)

theorem convolutionFourthDerivative_diagonal_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j : Fin p)
     :
    s.convolutionFourthDerivative (gaussianLaw A) x j j j j =
      -(1 / s.bandwidth) * ∑ b : Bool,
        (faceSign (j, b)) * (∫ z, s.softFaceCoordinateThird {(j, b)} j (A.mulVec z + x) ∂standardGaussian p) := by
  let F : (Bool) → Vector p → ℝ := fun b z =>
    (faceSign (j, b)) * s.softFaceCoordinateThird {(j, b)} j (A.mulVec z + x)
  have hF (b : Bool) : Integrable (F b) (standardGaussian p) :=
    (s.integrable_softFaceCoordinateThird_gaussian A _ x j).const_mul _
  have hpoint (z : Vector p) : s.mixedFourthDerivativeF (A.mulVec z + x) j j j j =
      -(1 / s.bandwidth) * ∑ b, F b z := by
    simpa only [Fintype.sum_prod_type, F] using
      s.mixedFourthDerivativeF_diagonal_soft_faces (A.mulVec z + x) j
  rw [s.convolutionFourthDerivative_eq_standardGaussian]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ => hF b)]
  simp only [F, integral_const_mul]

theorem convolutionFourthDerivative_triple_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k : Fin p}
    (hjk : j ≠ k) :
    s.convolutionFourthDerivative (gaussianLaw A) x j j j k =
      (2 / s.bandwidth ^ 2) * ∑ b : Bool × Bool,
        (faceSign (j, b.1) * faceSign (k, b.2)) * (∫ z, s.softFaceCoordinateSecond {(j, b.1), (k, b.2)} j (A.mulVec z + x) ∂standardGaussian p) := by
  let F : (Bool × Bool) → Vector p → ℝ := fun b z =>
    (faceSign (j, b.1) * faceSign (k, b.2)) * s.softFaceCoordinateSecond {(j, b.1), (k, b.2)} j (A.mulVec z + x)
  have hF (b : Bool × Bool) : Integrable (F b) (standardGaussian p) :=
    (s.integrable_softFaceCoordinateSecond_gaussian A _ x j).const_mul _
  have hpoint (z : Vector p) : s.mixedFourthDerivativeF (A.mulVec z + x) j j j k =
      (2 / s.bandwidth ^ 2) * ∑ b, F b z := by
    simpa only [Fintype.sum_prod_type, F] using
      s.mixedFourthDerivativeF_triple_soft_faces (A.mulVec z + x) hjk
  rw [s.convolutionFourthDerivative_eq_standardGaussian]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ => hF b)]
  simp only [F, integral_const_mul]

theorem convolutionFourthDerivative_two_pairs_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k : Fin p}
    (hjk : j ≠ k) :
    s.convolutionFourthDerivative (gaussianLaw A) x j j k k =
      (2 / s.bandwidth ^ 2) * ∑ b : Bool × Bool,
        (faceSign (j, b.1) * faceSign (k, b.2)) * (∫ z, s.softFaceMixedSecond {(j, b.1), (k, b.2)} j k (A.mulVec z + x) ∂standardGaussian p) := by
  let F : (Bool × Bool) → Vector p → ℝ := fun b z =>
    (faceSign (j, b.1) * faceSign (k, b.2)) * s.softFaceMixedSecond {(j, b.1), (k, b.2)} j k (A.mulVec z + x)
  have hF (b : Bool × Bool) : Integrable (F b) (standardGaussian p) :=
    (s.integrable_softFaceMixedSecond_gaussian A _ x j k).const_mul _
  have hpoint (z : Vector p) : s.mixedFourthDerivativeF (A.mulVec z + x) j j k k =
      (2 / s.bandwidth ^ 2) * ∑ b, F b z := by
    simpa only [Fintype.sum_prod_type, F] using
      s.mixedFourthDerivativeF_two_pairs_soft_faces (A.mulVec z + x) hjk
  rw [s.convolutionFourthDerivative_eq_standardGaussian]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ => hF b)]
  simp only [F, integral_const_mul]

theorem convolutionFourthDerivative_one_pair_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k l : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    s.convolutionFourthDerivative (gaussianLaw A) x j j k l =
      -(6 / s.bandwidth ^ 3) * ∑ b : Bool × Bool × Bool,
        (faceSign (j, b.1) * faceSign (k, b.2.1) * faceSign (l, b.2.2)) * (∫ z, s.softFaceDirectional {(j, b.1), (k, b.2.1), (l, b.2.2)} (coordinateDirection j) (A.mulVec z + x) ∂standardGaussian p) := by
  let F : (Bool × Bool × Bool) → Vector p → ℝ := fun b z =>
    (faceSign (j, b.1) * faceSign (k, b.2.1) * faceSign (l, b.2.2)) * s.softFaceDirectional {(j, b.1), (k, b.2.1), (l, b.2.2)} (coordinateDirection j) (A.mulVec z + x)
  have hF (b : Bool × Bool × Bool) : Integrable (F b) (standardGaussian p) :=
    (s.integrable_softFaceDirectional_gaussian A _ x _).const_mul _
  have hpoint (z : Vector p) : s.mixedFourthDerivativeF (A.mulVec z + x) j j k l =
      -(6 / s.bandwidth ^ 3) * ∑ b, F b z := by
    simpa only [Fintype.sum_prod_type, F] using
      s.mixedFourthDerivativeF_one_pair_soft_faces (A.mulVec z + x) hjk hjl hkl
  rw [s.convolutionFourthDerivative_eq_standardGaussian]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ => hF b)]
  simp only [F, integral_const_mul]

theorem convolutionFourthDerivative_distinct_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k l m : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    s.convolutionFourthDerivative (gaussianLaw A) x j k l m =
      (24 / s.bandwidth ^ 4) * ∑ b : Bool × Bool × Bool × Bool,
        (faceSign (j, b.1) * faceSign (k, b.2.1) * faceSign (l, b.2.2.1) * faceSign (m, b.2.2.2)) * (∫ z, s.softFaceWeight {(j, b.1), (k, b.2.1), (l, b.2.2.1), (m, b.2.2.2)} (A.mulVec z + x) ∂standardGaussian p) := by
  let F : (Bool × Bool × Bool × Bool) → Vector p → ℝ := fun b z =>
    (faceSign (j, b.1) * faceSign (k, b.2.1) * faceSign (l, b.2.2.1) * faceSign (m, b.2.2.2)) * s.softFaceWeight {(j, b.1), (k, b.2.1), (l, b.2.2.1), (m, b.2.2.2)} (A.mulVec z + x)
  have hF (b : Bool × Bool × Bool × Bool) : Integrable (F b) (standardGaussian p) :=
    (s.integrable_softFaceWeight_gaussian A _ x).const_mul _
  have hpoint (z : Vector p) : s.mixedFourthDerivativeF (A.mulVec z + x) j k l m =
      (24 / s.bandwidth ^ 4) * ∑ b, F b z := by
    simpa only [Fintype.sum_prod_type, F] using
      s.mixedFourthDerivativeF_distinct_soft_faces (A.mulVec z + x) hjk hjl hjm hkl hkm hlm
  rw [s.convolutionFourthDerivative_eq_standardGaussian]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ => hF b)]
  simp only [F, integral_const_mul]

private theorem fourth_abs_signed_sum_le {ι : Type*} [Fintype ι] (c t : ι → ℝ)
    (hc : ∀ i, |c i| = 1) : |∑ i, c i * t i| ≤ ∑ i, |t i| := by
  calc
    _ ≤ ∑ i, |c i * t i| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_congr rfl (fun i _ => by rw [abs_mul, hc, one_mul])

theorem abs_convolutionFourthDerivative_diagonal_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j : Fin p)
     :
    |s.convolutionFourthDerivative (gaussianLaw A) x j j j j| ≤
      (1 / s.bandwidth) * ∑ b : Bool,
        |∫ z, s.softFaceCoordinateThird {(j, b)} j (A.mulVec z + x) ∂standardGaussian p| := by
  have hband := s.bandwidth_pos
  rw [s.convolutionFourthDerivative_diagonal_soft_faces A x j, abs_mul]
  simp only [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (1 / s.bandwidth))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact fourth_abs_signed_sum_le (fun b : Bool => faceSign (j, b))
    (fun b => ∫ z, s.softFaceCoordinateThird {(j, b)} j (A.mulVec z + x) ∂standardGaussian p)
    (fun b => by simp only [abs_mul, abs_faceSign, one_mul])

theorem abs_convolutionFourthDerivative_triple_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k : Fin p}
    (hjk : j ≠ k) :
    |s.convolutionFourthDerivative (gaussianLaw A) x j j j k| ≤
      (2 / s.bandwidth ^ 2) * ∑ b : Bool × Bool,
        |∫ z, s.softFaceCoordinateSecond {(j, b.1), (k, b.2)} j (A.mulVec z + x) ∂standardGaussian p| := by
  have hband := s.bandwidth_pos
  rw [s.convolutionFourthDerivative_triple_soft_faces A x hjk, abs_mul]
  simp only [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (2 / s.bandwidth ^ 2))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact fourth_abs_signed_sum_le (fun b : Bool × Bool => faceSign (j, b.1) * faceSign (k, b.2))
    (fun b => ∫ z, s.softFaceCoordinateSecond {(j, b.1), (k, b.2)} j (A.mulVec z + x) ∂standardGaussian p)
    (fun b => by simp only [abs_mul, abs_faceSign, one_mul])

theorem abs_convolutionFourthDerivative_two_pairs_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k : Fin p}
    (hjk : j ≠ k) :
    |s.convolutionFourthDerivative (gaussianLaw A) x j j k k| ≤
      (2 / s.bandwidth ^ 2) * ∑ b : Bool × Bool,
        |∫ z, s.softFaceMixedSecond {(j, b.1), (k, b.2)} j k (A.mulVec z + x) ∂standardGaussian p| := by
  have hband := s.bandwidth_pos
  rw [s.convolutionFourthDerivative_two_pairs_soft_faces A x hjk, abs_mul]
  simp only [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (2 / s.bandwidth ^ 2))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact fourth_abs_signed_sum_le (fun b : Bool × Bool => faceSign (j, b.1) * faceSign (k, b.2))
    (fun b => ∫ z, s.softFaceMixedSecond {(j, b.1), (k, b.2)} j k (A.mulVec z + x) ∂standardGaussian p)
    (fun b => by simp only [abs_mul, abs_faceSign, one_mul])

theorem abs_convolutionFourthDerivative_one_pair_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k l : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    |s.convolutionFourthDerivative (gaussianLaw A) x j j k l| ≤
      (6 / s.bandwidth ^ 3) * ∑ b : Bool × Bool × Bool,
        |∫ z, s.softFaceDirectional {(j, b.1), (k, b.2.1), (l, b.2.2)} (coordinateDirection j) (A.mulVec z + x) ∂standardGaussian p| := by
  have hband := s.bandwidth_pos
  rw [s.convolutionFourthDerivative_one_pair_soft_faces A x hjk hjl hkl, abs_mul]
  simp only [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (6 / s.bandwidth ^ 3))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact fourth_abs_signed_sum_le (fun b : Bool × Bool × Bool => faceSign (j, b.1) * faceSign (k, b.2.1) * faceSign (l, b.2.2))
    (fun b => ∫ z, s.softFaceDirectional {(j, b.1), (k, b.2.1), (l, b.2.2)} (coordinateDirection j) (A.mulVec z + x) ∂standardGaussian p)
    (fun b => by simp only [abs_mul, abs_faceSign, one_mul])

theorem abs_convolutionFourthDerivative_distinct_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k l m : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    |s.convolutionFourthDerivative (gaussianLaw A) x j k l m| ≤
      (24 / s.bandwidth ^ 4) * ∑ b : Bool × Bool × Bool × Bool,
        |∫ z, s.softFaceWeight {(j, b.1), (k, b.2.1), (l, b.2.2.1), (m, b.2.2.2)} (A.mulVec z + x) ∂standardGaussian p| := by
  have hband := s.bandwidth_pos
  rw [s.convolutionFourthDerivative_distinct_soft_faces A x hjk hjl hjm hkl hkm hlm, abs_mul]
  simp only [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (24 / s.bandwidth ^ 4))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact fourth_abs_signed_sum_le (fun b : Bool × Bool × Bool × Bool => faceSign (j, b.1) * faceSign (k, b.2.1) * faceSign (l, b.2.2.1) * faceSign (m, b.2.2.2))
    (fun b => ∫ z, s.softFaceWeight {(j, b.1), (k, b.2.1), (l, b.2.2.1), (m, b.2.2.2)} (A.mulVec z + x) ∂standardGaussian p)
    (fun b => by simp only [abs_mul, abs_faceSign, one_mul])

def fourthSingleContribution (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j : Fin p) : ℝ :=
  (1 / s.bandwidth) * ∑ b : Bool,
    |∫ z, s.softFaceCoordinateThird {(j, b)} j (A.mulVec z + x) ∂standardGaussian p|

def fourthTripleContribution (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k : Fin p) : ℝ :=
  if j = k then 0 else (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
    |∫ z, s.softFaceCoordinateSecond {(j, b), (k, c)} j (A.mulVec z + x) ∂standardGaussian p|

def fourthTwoPairsContribution (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k : Fin p) : ℝ :=
  if j = k then 0 else (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
    |∫ z, s.softFaceMixedSecond {(j, b), (k, c)} j k (A.mulVec z + x) ∂standardGaussian p|

def fourthOnePairContribution (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k l : Fin p) : ℝ :=
  if j ≠ k ∧ j ≠ l ∧ k ≠ l then (6 / s.bandwidth ^ 3) *
    ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
      |∫ z, s.softFaceDirectional {(j, b), (k, c), (l, d)} (coordinateDirection j)
        (A.mulVec z + x) ∂standardGaussian p|
  else 0

def fourthDistinctContribution (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k l m : Fin p) : ℝ :=
  if j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m then
    (24 / s.bandwidth ^ 4) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, ∑ e : Bool,
      (∫ z, s.softFaceWeight {(j, b), (k, c), (l, d), (m, e)}
        (A.mulVec z + x) ∂standardGaussian p)
  else 0

/-- The entire actual fourth-derivative tensor is reduced to five positive
active-face contributions. The position multiplicities are universal. -/
theorem sum_abs_convolutionFourthDerivative_le_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, |s.convolutionFourthDerivative (gaussianLaw A) x j k l m|) ≤
      (∑ j, s.fourthSingleContribution A x j) +
      4 * (∑ j, ∑ k, s.fourthTripleContribution A x j k) +
      3 * (∑ j, ∑ k, s.fourthTwoPairsContribution A x j k) +
      6 * (∑ j, ∑ k, ∑ l, s.fourthOnePairContribution A x j k l) +
      ∑ j, ∑ k, ∑ l, ∑ m, s.fourthDistinctContribution A x j k l m := by
  have hband := s.bandwidth_pos
  apply sum_symmetric_fourth_le
    (fun j k l m => |s.convolutionFourthDerivative (gaussianLaw A) x j k l m|)
    (fun j k l m => congrArg abs (s.convolutionFourthDerivative_swap_first_two A x j k l m))
    (fun j k l m => congrArg abs (s.convolutionFourthDerivative_swap_middle_two A x j k l m))
    (fun j k l m => congrArg abs (s.convolutionFourthDerivative_swap_last_two A x j k l m))
    (s.fourthSingleContribution A x) (s.fourthTripleContribution A x)
    (s.fourthTwoPairsContribution A x) (s.fourthOnePairContribution A x)
    (s.fourthDistinctContribution A x)
  · intro j
    unfold fourthSingleContribution
    positivity
  · intro j k
    unfold fourthTripleContribution
    split_ifs <;> positivity
  · intro j k
    unfold fourthTwoPairsContribution
    split_ifs <;> positivity
  · intro j k l
    unfold fourthOnePairContribution
    split_ifs <;> positivity
  · intro j k l m
    unfold fourthDistinctContribution
    split_ifs
    · exact mul_nonneg (by positivity)
        (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
          Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
            integral_nonneg (fun z => s.softFaceWeight_nonneg _ _))))))
    · exact le_rfl
  · intro j
    exact s.abs_convolutionFourthDerivative_diagonal_soft_faces A x j
  · intro j k hjk
    simpa only [fourthTripleContribution, if_neg hjk, Fintype.sum_prod_type] using
      s.abs_convolutionFourthDerivative_triple_soft_faces A x hjk
  · intro j k hjk
    simpa only [fourthTwoPairsContribution, if_neg hjk, Fintype.sum_prod_type] using
      s.abs_convolutionFourthDerivative_two_pairs_soft_faces A x hjk
  · intro j k l hjk hjl hkl
    simpa only [fourthOnePairContribution, if_pos (show j ≠ k ∧ j ≠ l ∧ k ≠ l from
      ⟨hjk, hjl, hkl⟩), Fintype.sum_prod_type] using
      s.abs_convolutionFourthDerivative_one_pair_soft_faces A x hjk hjl hkl
  · intro j k l m hjk hjl hjm hkl hkm hlm
    have hh := s.abs_convolutionFourthDerivative_distinct_soft_faces A x hjk hjl hjm hkl hkm hlm
    have hi (S : Finset (Face p)) :
        0 ≤ ∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p :=
      integral_nonneg (fun z => s.softFaceWeight_nonneg S _)
    simpa only [fourthDistinctContribution, if_pos (show
      j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m from
        ⟨hjk, hjl, hjm, hkl, hkm, hlm⟩), Fintype.sum_prod_type,
      abs_of_nonneg (hi _)] using hh

@[simp] theorem faceFamilySet_quadruple (f g h i : Face p) :
    faceFamilySet ![f, g, h, i] = {f, g, h, i} := by
  classical
  ext a
  simp [faceFamilySet, Fin.exists_fin_succ, eq_comm]

theorem sum_fourthSingleContribution_eq_ordered (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) :
    (∑ j, s.fourthSingleContribution A x j) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * |∫ z, s.softFaceCoordinateThird T.val.activeFaceSet
          (T.val.face 0).1 (A.mulVec z + x) ∂standardGaussian p| := by
  classical
  let g : (Fin 1 → Face p) → ℝ := fun f => (1 / s.bandwidth) *
    |∫ z, s.softFaceCoordinateThird (faceFamilySet f) (f 0).1 (A.mulVec z + x)
      ∂standardGaussian p|
  have hi := sum_singleton_coordinate_signs g
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [g, faceFamilySet_singleton, Matrix.cons_val_zero,
    fourthSingleContribution, ← Finset.mul_sum]

theorem sum_fourthTripleContribution_eq_ordered (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) :
    (∑ j, ∑ k, s.fourthTripleContribution A x j k) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) * |∫ z, s.softFaceCoordinateSecond T.val.activeFaceSet
          (T.val.face 0).1 (A.mulVec z + x) ∂standardGaussian p| := by
  classical
  let g : (Fin 2 → Face p) → ℝ := fun f => (2 / s.bandwidth ^ 2) *
    |∫ z, s.softFaceCoordinateSecond (faceFamilySet f) (f 0).1
      (A.mulVec z + x) ∂standardGaussian p|
  have hi := sum_pair_coordinate_signs g
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j = k
  · simp only [fourthTripleContribution, if_pos hjk, if_neg (not_not_intro hjk)]
  · simp only [fourthTripleContribution, if_neg hjk, if_pos hjk,
      g, faceFamilySet_pair, Matrix.cons_val_zero, ← Finset.mul_sum]

theorem sum_fourthTwoPairsContribution_eq_ordered (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) :
    (∑ j, ∑ k, s.fourthTwoPairsContribution A x j k) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) * |∫ z, s.softFaceMixedSecond T.val.activeFaceSet
          (T.val.face 0).1 (T.val.face 1).1 (A.mulVec z + x) ∂standardGaussian p| := by
  classical
  let g : (Fin 2 → Face p) → ℝ := fun f => (2 / s.bandwidth ^ 2) *
    |∫ z, s.softFaceMixedSecond (faceFamilySet f) (f 0).1 (f 1).1
      (A.mulVec z + x) ∂standardGaussian p|
  have hi := sum_pair_coordinate_signs g
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j = k
  · simp only [fourthTwoPairsContribution, if_pos hjk, if_neg (not_not_intro hjk)]
  · simp only [fourthTwoPairsContribution, if_neg hjk, if_pos hjk,
      g, faceFamilySet_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
      ← Finset.mul_sum]

theorem sum_fourthOnePairContribution_eq_ordered (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) :
    (∑ j, ∑ k, ∑ l, s.fourthOnePairContribution A x j k l) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
        (6 / s.bandwidth ^ 3) *
          |∫ z, s.softFaceDirectional T.val.activeFaceSet
            (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p| := by
  classical
  let g : (Fin 3 → Face p) → ℝ := fun f => (6 / s.bandwidth ^ 3) *
    |∫ z, s.softFaceDirectional (faceFamilySet f) (coordinateDirection (f 0).1)
      (A.mulVec z + x) ∂standardGaussian p|
  have hi := sum_triple_coordinate_signs g
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hd : j ≠ k ∧ j ≠ l ∧ k ≠ l
  · simp only [fourthOnePairContribution, if_pos hd, g, faceFamilySet_triple,
      Matrix.cons_val_zero, ← Finset.mul_sum]
  · simp only [fourthOnePairContribution, if_neg hd]

theorem sum_fourthDistinctContribution_eq_ordered (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.fourthDistinctContribution A x j k l m) =
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4,
        (24 / s.bandwidth ^ 4) *
          (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) := by
  classical
  let g : (Fin 4 → Face p) → ℝ := fun f => (24 / s.bandwidth ^ 4) *
    (∫ z, s.softFaceWeight (faceFamilySet f) (A.mulVec z + x) ∂standardGaussian p)
  have hi := sum_quadruple_coordinate_signs g
  convert hi using 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  by_cases hd : j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m
  · simp only [fourthDistinctContribution, if_pos hd, g, faceFamilySet_quadruple,
      ← Finset.mul_sum]
  · simp only [fourthDistinctContribution, if_neg hd]

/-- Actual Gaussian-smoothed fourth derivatives, grouped into compatible
ordered face families of sizes one through four. -/
theorem sum_abs_convolutionFourthDerivative_le_ordered_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, |s.convolutionFourthDerivative (gaussianLaw A) x j k l m|) ≤
      (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 1,
        (1 / s.bandwidth) * |∫ z, s.softFaceCoordinateThird T.val.activeFaceSet
          (T.val.face 0).1 (A.mulVec z + x) ∂standardGaussian p|) +
      4 * (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) * |∫ z, s.softFaceCoordinateSecond T.val.activeFaceSet
          (T.val.face 0).1 (A.mulVec z + x) ∂standardGaussian p|) +
      3 * (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 2,
        (2 / s.bandwidth ^ 2) * |∫ z, s.softFaceMixedSecond T.val.activeFaceSet
          (T.val.face 0).1 (T.val.face 1).1 (A.mulVec z + x) ∂standardGaussian p|) +
      6 * (∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 3,
        (6 / s.bandwidth ^ 3) * |∫ z, s.softFaceDirectional T.val.activeFaceSet
          (coordinateDirection (T.val.face 0).1) (A.mulVec z + x) ∂standardGaussian p|) +
      ∑ T : OrderedFaceTuples (Finset.univ : Finset (Face p)) 4,
        (24 / s.bandwidth ^ 4) *
          (∫ z, s.softFaceWeight T.val.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) := by
  simpa only [s.sum_fourthSingleContribution_eq_ordered,
    s.sum_fourthTripleContribution_eq_ordered, s.sum_fourthTwoPairsContribution_eq_ordered,
    s.sum_fourthOnePairContribution_eq_ordered, s.sum_fourthDistinctContribution_eq_ordered]
      using s.sum_abs_convolutionFourthDerivative_le_soft_faces A x

end
end RectangleCLT.FaceSmoother
