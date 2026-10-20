import RectangleCLT.GaussianTripleBound
import RectangleCLT.GaussianDualBounds

/-! Actual fourth derivative multiplicity expansions into smooth positive
active-face kernels and their checked coordinate derivatives. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

def softFaceMixedSecond (S : Finset (Face p)) (j k : Fin p) (x : Vector p) : ℝ :=
  s.softFaceWeight S x / s.bandwidth ^ 2 *
    (((∑ f ∈ S, normalDot f (coordinateDirection j)) -
        ((S.card : ℝ) + 1) * (s.weights x).v j) *
      ((∑ f ∈ S, normalDot f (coordinateDirection k)) -
        ((S.card : ℝ) + 1) * (s.weights x).v k) -
      ((S.card : ℝ) + 1) * ((s.weights x).diagonalMass j k -
        (s.weights x).v j * (s.weights x).v k))

theorem hasDerivAt_softFaceMixedSecond (S : Finset (Face p))
    (j k : Fin p) (x : Vector p) (t : ℝ) :
    HasDerivAt (fun r => s.softFaceDirectional S (coordinateDirection j)
      (line x (coordinateDirection k) r))
      (s.softFaceMixedSecond S j k (line x (coordinateDirection k) t)) t := by
  have hP := s.hasDerivAt_softFaceWeight_line S x (coordinateDirection k) t
  have hV := s.hasDerivAt_v_coordinate x j k t
  simp only [directionalMean_coordinate] at hP
  have hd := (hP.div_const s.bandwidth).mul
    ((hasDerivAt_const t (∑ f ∈ S, normalDot f (coordinateDirection j))).sub
      (hV.const_mul ((S.card : ℝ) + 1)))
  convert hd using 1
  · ext r
    simp only [softFaceDirectional, directionalMean_coordinate]
  · simp only [softFaceMixedSecond]
    field_simp [s.bandwidth_pos.ne']
    ring

def softFaceCoordinateThird (S : Finset (Face p)) (j : Fin p) (x : Vector p) : ℝ :=
  let c : ℝ := S.card + 1
  let a := (∑ f ∈ S, normalDot f (coordinateDirection j)) - c * (s.weights x).v j
  let b := (s.weights x).coordinateMass j - (s.weights x).v j ^ 2
  s.softFaceWeight S x / s.bandwidth ^ 3 *
    (a ^ 3 - 3 * c * a * b -
      c * ((s.weights x).v j - 3 * (s.weights x).coordinateMass j * (s.weights x).v j +
        2 * (s.weights x).v j ^ 3))

theorem hasDerivAt_softFaceCoordinateThird (S : Finset (Face p))
    (j : Fin p) (x : Vector p) (t : ℝ) :
    HasDerivAt (fun r => s.softFaceCoordinateSecond S j (line x (coordinateDirection j) r))
      (s.softFaceCoordinateThird S j (line x (coordinateDirection j) t)) t := by
  have hP := s.hasDerivAt_softFaceWeight_line S x (coordinateDirection j) t
  have hV := s.hasDerivAt_v_coordinate x j j t
  have hM := s.hasDerivAt_diagonalMass_coordinate x j j j t
  simp only [directionalMean_coordinate, FaceWeights.diagonalMass,
    FaceWeights.thirdDiagonalMass, ↓reduceIte] at hP hV hM
  have hA := (hasDerivAt_const t (∑ f ∈ S, normalDot f (coordinateDirection j))).sub
    (hV.const_mul ((S.card : ℝ) + 1))
  have hB := hM.sub (hV.pow 2)
  have hd := (hP.div_const (s.bandwidth ^ 2)).mul
    ((hA.pow 2).sub (hB.const_mul ((S.card : ℝ) + 1)))
  convert hd using 1
  simp only [softFaceCoordinateThird]
  field_simp [s.bandwidth_pos.ne']
  ring

theorem softFaceWeight_quadruple (x : Vector p) {j k l m : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) (b c d e : Bool) :
    s.softFaceWeight {(j, b), (k, c), (l, d), (m, e)} x =
      s.F x * (s.weights x).pi (j, b) * (s.weights x).pi (k, c) *
        (s.weights x).pi (l, d) * (s.weights x).pi (m, e) := by
  classical
  have hn : (j, b) ∉ ({(k, c), (l, d), (m, e)} : Finset (Face p)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
    exact ⟨fun h => hjk h.1, fun h => hjl h.1, fun h => hjm h.1⟩
  rw [s.softFaceWeight_insert _ _ _ hn, s.softFaceWeight_triple x hkl hkm hlm]
  ring

theorem mixedFourthDerivativeF_distinct_soft_faces (x : Vector p) {j k l m : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    s.mixedFourthDerivativeF x j k l m =
      (24 / s.bandwidth ^ 4) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, ∑ e : Bool,
        faceSign (j, b) * faceSign (k, c) * faceSign (l, d) * faceSign (m, e) *
          s.softFaceWeight {(j, b), (k, c), (l, d), (m, e)} x := by
  simp only [s.mixedFourthDerivativeF_eq, FaceWeights.fourthFactor,
    FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass, FaceWeights.fourthDiagonalMass,
    hjk, hjl, hjm, hkl, hkm, hlm, false_and, ↓reduceIte,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  simp_rw [s.softFaceWeight_quadruple x hjk hjl hjm hkl hkm hlm]
  simp only [Fintype.sum_bool, faceSign, Bool.false_eq_true, ↓reduceIte, FaceWeights.v]
  ring

theorem mixedFourthDerivativeF_one_pair_soft_faces (x : Vector p) {j k l : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    s.mixedFourthDerivativeF x j j k l =
      -(6 / s.bandwidth ^ 3) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
        faceSign (j, b) * faceSign (k, c) * faceSign (l, d) *
          s.softFaceDirectional {(j, b), (k, c), (l, d)} (coordinateDirection j) x := by
  classical
  have hne₁ (b c : Bool) : (j, b) ≠ (k, c) := fun h => hjk (congrArg Prod.fst h)
  have hne₂ (b d : Bool) : (j, b) ≠ (l, d) := fun h => hjl (congrArg Prod.fst h)
  have hne₃ (c d : Bool) : (k, c) ≠ (l, d) := fun h => hkl (congrArg Prod.fst h)
  have hn (b c d : Bool) : (j, b) ∉ ({(k, c), (l, d)} : Finset (Face p)) := by
    simp [hne₁ b c, hne₂ b d]
  simp only [s.mixedFourthDerivativeF_eq, FaceWeights.fourthFactor,
    FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass, FaceWeights.fourthDiagonalMass,
    hjk, hjl, hkl, false_and, and_false, ↓reduceIte,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  simp only [softFaceDirectional, Finset.sum_insert (hn _ _ _),
    Finset.sum_pair (hne₃ _ _), Finset.card_insert_of_not_mem (hn _ _ _),
    Finset.card_pair (hne₃ _ _), normalDot_coordinate_eq, hjk, hjl,
    Ne.symm hjk, Ne.symm hjl, ↓reduceIte, directionalMean_coordinate]
  simp_rw [s.softFaceWeight_triple x hjk hjl hkl]
  simp only [Fintype.sum_bool, faceSign, ↓reduceIte, FaceWeights.v, FaceWeights.coordinateMass]
  field_simp [s.bandwidth_pos.ne']
  ring_nf
  field_simp [s.bandwidth_pos.ne']

theorem mixedFourthDerivativeF_triple_soft_faces (x : Vector p) {j k : Fin p}
    (hjk : j ≠ k) :
    s.mixedFourthDerivativeF x j j j k =
      (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
        faceSign (j, b) * faceSign (k, c) *
          s.softFaceCoordinateSecond {(j, b), (k, c)} j x := by
  classical
  have hne (b c : Bool) : (j, b) ≠ (k, c) := fun h => hjk (congrArg Prod.fst h)
  simp only [s.mixedFourthDerivativeF_eq, FaceWeights.fourthFactor,
    FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass, FaceWeights.fourthDiagonalMass,
    hjk, false_and, and_false, ↓reduceIte,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  simp only [softFaceCoordinateSecond, Finset.sum_pair (hne _ _), Finset.card_pair (hne _ _),
    normalDot_coordinate_eq, hjk, Ne.symm hjk, ↓reduceIte]
  simp_rw [s.softFaceWeight_pair x hjk]
  simp only [Fintype.sum_bool, faceSign, ↓reduceIte, FaceWeights.v, FaceWeights.coordinateMass]
  field_simp [s.bandwidth_pos.ne']
  ring

theorem mixedFourthDerivativeF_two_pairs_soft_faces (x : Vector p) {j k : Fin p}
    (hjk : j ≠ k) :
    s.mixedFourthDerivativeF x j j k k =
      (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
        faceSign (j, b) * faceSign (k, c) *
          s.softFaceMixedSecond {(j, b), (k, c)} j k x := by
  classical
  have hne (b c : Bool) : (j, b) ≠ (k, c) := fun h => hjk (congrArg Prod.fst h)
  simp only [s.mixedFourthDerivativeF_eq, FaceWeights.fourthFactor,
    FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass, FaceWeights.fourthDiagonalMass,
    hjk, false_and, and_false, ↓reduceIte,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  simp only [softFaceMixedSecond, Finset.sum_pair (hne _ _), Finset.card_pair (hne _ _),
    normalDot_coordinate_eq, hjk, Ne.symm hjk, ↓reduceIte,
    FaceWeights.diagonalMass]
  simp_rw [s.softFaceWeight_pair x hjk]
  simp only [Fintype.sum_bool, faceSign, ↓reduceIte, FaceWeights.v, FaceWeights.coordinateMass]
  field_simp [s.bandwidth_pos.ne']
  ring

theorem mixedFourthDerivativeF_diagonal_soft_faces (x : Vector p) (j : Fin p) :
    s.mixedFourthDerivativeF x j j j j =
      -(1 / s.bandwidth) * ∑ b : Bool, faceSign (j, b) *
        s.softFaceCoordinateThird {(j, b)} j x := by
  classical
  simp only [s.mixedFourthDerivativeF_eq, FaceWeights.fourthFactor,
    FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass, FaceWeights.fourthDiagonalMass,
    ↓reduceIte]
  simp only [softFaceCoordinateThird, Finset.sum_singleton, Finset.card_singleton,
    normalDot_coordinate_eq, ↓reduceIte, softFaceWeight, Finset.prod_singleton]
  simp only [Fintype.sum_bool, faceSign, ↓reduceIte, FaceWeights.v, FaceWeights.coordinateMass]
  field_simp [s.bandwidth_pos.ne']
  ring

@[fun_prop] theorem continuous_softFaceMixedSecond (S : Finset (Face p)) (j k : Fin p) :
    Continuous (s.softFaceMixedSecond S j k) := by
  unfold softFaceMixedSecond
  fun_prop

@[fun_prop] theorem continuous_softFaceCoordinateThird (S : Finset (Face p)) (j : Fin p) :
    Continuous (s.softFaceCoordinateThird S j) := by
  unfold softFaceCoordinateThird
  dsimp only
  fun_prop

/-- Uniform boundedness needed only to justify dominated differentiation.
The quantitative face bounds below use the exact kernel coefficients. -/
theorem softFaceCoordinateThird_bounded (S : Finset (Face p)) (j : Fin p) :
    ∃ C : ℝ, ∀ x, ‖s.softFaceCoordinateThird S j x‖ ≤ C := by
  let c : ℝ := S.card + 1
  let a : ℝ := ∑ f ∈ S, normalDot f (coordinateDirection j)
  let G : (Fin 3 → ℝ) → ℝ := fun u => u 0 / s.bandwidth ^ 3 *
    ((a - c * u 1) ^ 3 - 3 * c * (a - c * u 1) * (u 2 - u 1 ^ 2) -
      c * (u 1 - 3 * u 2 * u 1 + 2 * u 1 ^ 3))
  have hGc : Continuous G := by unfold G; fun_prop
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hGc.continuousOn
  refine ⟨C, fun x => ?_⟩
  let u : Fin 3 → ℝ := ![s.softFaceWeight S x, (s.weights x).v j, (s.weights x).coordinateMass j]
  have hu : u ∈ Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 : ℝ) 1) := by
    intro i _
    fin_cases i
    · exact ⟨by simpa [u] using (show -1 ≤ s.softFaceWeight S x by
        linarith [s.softFaceWeight_nonneg S x]), by simpa [u] using s.softFaceWeight_le_one S x⟩
    · simpa [u] using abs_le.mp ((s.weights x).abs_v_le_one j)
    · exact ⟨by simpa [u] using (show -1 ≤ (s.weights x).coordinateMass j by
        linarith [(s.weights x).coordinateMass_nonneg j]),
        by simpa [u] using (s.weights x).coordinateMass_le_one j⟩
  simpa [G, u, c, a, softFaceCoordinateThird] using hC u hu

theorem softFaceMixedSecond_bounded (S : Finset (Face p)) (j k : Fin p) :
    ∃ C : ℝ, ∀ x, ‖s.softFaceMixedSecond S j k x‖ ≤ C := by
  let c : ℝ := S.card + 1
  let a : ℝ := ∑ f ∈ S, normalDot f (coordinateDirection j)
  let b : ℝ := ∑ f ∈ S, normalDot f (coordinateDirection k)
  let G : (Fin 4 → ℝ) → ℝ := fun u => u 0 / s.bandwidth ^ 2 *
    ((a - c * u 1) * (b - c * u 2) - c * (u 3 - u 1 * u 2))
  have hGc : Continuous G := by unfold G; fun_prop
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hGc.continuousOn
  refine ⟨C, fun x => ?_⟩
  let u : Fin 4 → ℝ := ![s.softFaceWeight S x, (s.weights x).v j,
    (s.weights x).v k, (s.weights x).diagonalMass j k]
  have hdiag1 : (s.weights x).diagonalMass j k ≤ 1 := by
    by_cases h : j = k
    · simpa [FaceWeights.diagonalMass, h] using (s.weights x).coordinateMass_le_one j
    · simp [FaceWeights.diagonalMass, h]
  have hu : u ∈ Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-1 : ℝ) 1) := by
    intro i _
    fin_cases i
    · exact ⟨by simpa [u] using (show -1 ≤ s.softFaceWeight S x by
        linarith [s.softFaceWeight_nonneg S x]), by simpa [u] using s.softFaceWeight_le_one S x⟩
    · simpa [u] using abs_le.mp ((s.weights x).abs_v_le_one j)
    · simpa [u] using abs_le.mp ((s.weights x).abs_v_le_one k)
    · exact ⟨by simpa [u] using (show -1 ≤ (s.weights x).diagonalMass j k by
        linarith [(s.weights x).diagonalMass_nonneg j k]), by simpa [u] using hdiag1⟩
  simpa [G, u, c, a, b, softFaceMixedSecond] using hC u hu

end
end RectangleCLT.FaceSmoother
