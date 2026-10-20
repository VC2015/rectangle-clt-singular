import RectangleCLT.GaussianTriple
import RectangleCLT.GaussianCurvature
import RectangleCLT.GaussianShiftIntegral
import RectangleCLT.GaussianSoftRecursion

/-! Exact multiplicity expansions of the actual third derivatives into
positive soft active-face kernels and their checked coordinate derivatives. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

def softFaceCoordinateSecond (S : Finset (Face p)) (j : Fin p) (x : Vector p) : ℝ :=
  s.softFaceWeight S x / s.bandwidth ^ 2 *
    (((∑ f ∈ S, normalDot f (coordinateDirection j)) -
        ((S.card : ℝ) + 1) * (s.weights x).v j) ^ 2 -
      ((S.card : ℝ) + 1) * ((s.weights x).coordinateMass j - (s.weights x).v j ^ 2))

/-- Actual second coordinate derivatives of every soft active-face kernel. -/
theorem hasDerivAt_softFaceCoordinateSecond (S : Finset (Face p))
    (j : Fin p) (x : Vector p) (t : ℝ) :
    HasDerivAt (fun r => s.softFaceDirectional S (coordinateDirection j)
      (line x (coordinateDirection j) r))
      (s.softFaceCoordinateSecond S j (line x (coordinateDirection j) t)) t := by
  have hP := s.hasDerivAt_softFaceWeight_line S x (coordinateDirection j) t
  have hV := s.hasDerivAt_v_coordinate_line x (coordinateDirection j) j t
  simp only [directionalMean_coordinate, coordinateDirection, ↓reduceIte, mul_one,
    v] at hV hP
  have hd := (hP.div_const s.bandwidth).mul
    ((hasDerivAt_const t (∑ f ∈ S, normalDot f (coordinateDirection j))).sub
      (hV.const_mul ((S.card : ℝ) + 1)))
  convert hd using 1
  · ext r
    simp only [softFaceDirectional, directionalMean_coordinate, v]
  · simp only [softFaceCoordinateSecond]
    field_simp [s.bandwidth_pos.ne']
    ring

@[fun_prop] theorem continuous_softFaceCoordinateSecond (S : Finset (Face p)) (j : Fin p) :
    Continuous (s.softFaceCoordinateSecond S j) := by
  apply ((s.continuous_softFaceWeight S).div_const _).mul
  apply Continuous.sub
  · exact (continuous_const.sub (continuous_const.mul (s.continuous_v j))).pow 2
  · exact continuous_const.mul ((s.continuous_coordinateMass j).sub ((s.continuous_v j).pow 2))

theorem abs_softFaceCoordinateSecond_le (S : Finset (Face p)) (j : Fin p) (x : Vector p) :
    |s.softFaceCoordinateSecond S j x| ≤
      ((|(∑ f ∈ S, normalDot f (coordinateDirection j))| + ((S.card : ℝ) + 1)) ^ 2 +
        2 * ((S.card : ℝ) + 1)) / s.bandwidth ^ 2 := by
  let a := ∑ f ∈ S, normalDot f (coordinateDirection j)
  let c : ℝ := (S.card : ℝ) + 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hv := (s.weights x).abs_v_le_one j
  have hv2 : (s.weights x).v j ^ 2 ≤ 1 := by
    have hh := (sq_le_sq₀ (abs_nonneg ((s.weights x).v j)) zero_le_one).mpr hv
    simpa only [sq_abs, one_pow] using hh
  have hm0 := (s.weights x).coordinateMass_nonneg j
  have hm1 := (s.weights x).coordinateMass_le_one j
  have hvar : |(s.weights x).coordinateMass j - (s.weights x).v j ^ 2| ≤ 2 := by
    calc
      _ ≤ |(s.weights x).coordinateMass j| + |(s.weights x).v j ^ 2| := abs_sub _ _
      _ ≤ 2 := by rw [abs_of_nonneg hm0, abs_of_nonneg (sq_nonneg _)]; linarith
  have hlin : |a - c * (s.weights x).v j| ≤ |a| + c := by
    calc
      _ ≤ |a| + |c * (s.weights x).v j| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_of_nonneg hc]
        exact add_le_add_left (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv hc) _
  have hsq : (a - c * (s.weights x).v j) ^ 2 ≤ (|a| + c) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (a - c * (s.weights x).v j))
      (add_nonneg (abs_nonneg _) hc)).mpr hlin
    simpa only [sq_abs] using hh
  have hfactor : |(a - c * (s.weights x).v j) ^ 2 -
      c * ((s.weights x).coordinateMass j - (s.weights x).v j ^ 2)| ≤
      (|a| + c) ^ 2 + 2 * c := by
    calc
      _ ≤ |(a - c * (s.weights x).v j) ^ 2| +
          |c * ((s.weights x).coordinateMass j - (s.weights x).v j ^ 2)| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_of_nonneg hc]
        exact add_le_add hsq ((mul_le_mul_of_nonneg_left hvar hc).trans_eq (mul_comm _ _))
  unfold softFaceCoordinateSecond
  rw [abs_mul, abs_div, abs_of_nonneg (s.softFaceWeight_nonneg S x),
    abs_of_nonneg (sq_nonneg s.bandwidth)]
  calc
    _ ≤ (1 / s.bandwidth ^ 2) * ((|a| + c) ^ 2 + 2 * c) :=
      mul_le_mul (div_le_div_of_nonneg_right (s.softFaceWeight_le_one S x)
        (sq_nonneg s.bandwidth)) hfactor (abs_nonneg _)
        (div_nonneg zero_le_one (sq_nonneg s.bandwidth))
    _ = _ := by dsimp [a, c]; ring

theorem hasDerivAt_integral_softFaceWeight_line (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x y : Vector p) (W : Vector p → ℝ)
    (hW : Integrable W (standardGaussian p)) :
    HasDerivAt
      (fun t => ∫ z, W z * s.softFaceWeight S (A.mulVec z + line x y t)
        ∂standardGaussian p)
      (∫ z, W z * s.softFaceDirectional S y (A.mulVec z + x) ∂standardGaussian p) 0 := by
  apply hasDerivAt_weighted_gaussian_shift_integral A x y W (s.softFaceWeight S)
    (s.softFaceDirectional S y) hW (s.continuous_softFaceWeight S).measurable
    (s.continuous_softFaceDirectional S y).measurable 1
    (((∑ f ∈ S, |normalDot f y|) + ((S.card : ℝ) + 1) * ‖y‖) / s.bandwidth)
  · intro u
    simpa only [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg S u)] using
      s.softFaceWeight_le_one S u
  · intro u
    exact s.abs_softFaceDirectional_le S y u
  · exact s.hasDerivAt_softFaceDirectional S y

theorem hasDerivAt_integral_softFaceDirectional_coordinate (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x : Vector p) (j : Fin p) (W : Vector p → ℝ)
    (hW : Integrable W (standardGaussian p)) :
    HasDerivAt
      (fun t => ∫ z, W z * s.softFaceDirectional S (coordinateDirection j)
        (A.mulVec z + line x (coordinateDirection j) t) ∂standardGaussian p)
      (∫ z, W z * s.softFaceCoordinateSecond S j (A.mulVec z + x)
        ∂standardGaussian p) 0 := by
  apply hasDerivAt_weighted_gaussian_shift_integral A x (coordinateDirection j) W
    (s.softFaceDirectional S (coordinateDirection j)) (s.softFaceCoordinateSecond S j)
    hW (s.continuous_softFaceDirectional S (coordinateDirection j)).measurable
    (s.continuous_softFaceCoordinateSecond S j).measurable
    (((∑ f ∈ S, |normalDot f (coordinateDirection j)|) +
      ((S.card : ℝ) + 1) * ‖coordinateDirection j‖) / s.bandwidth)
    (((|(∑ f ∈ S, normalDot f (coordinateDirection j))| + ((S.card : ℝ) + 1)) ^ 2 +
      2 * ((S.card : ℝ) + 1)) / s.bandwidth ^ 2)
  · intro u
    exact s.abs_softFaceDirectional_le S (coordinateDirection j) u
  · intro u
    exact s.abs_softFaceCoordinateSecond_le S j u
  · exact s.hasDerivAt_softFaceCoordinateSecond S j

/-- Differentiating the checked active-face Stein recursion is justified by
uniform kernel bounds and integrable Gaussian weights. This supplies the
repeated-coordinate recursion at the level of actual integrals. -/
theorem softFaceCoordinateSecond_gaussian_active_coordinate
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    (∫ z, s.softFaceCoordinateSecond S j (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot u z * s.softFaceDirectional S (coordinateDirection j)
        (A.mulVec z + x) ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
          (∫ z, s.softFaceDirectional (insert f S) (coordinateDirection j)
            (A.mulVec z + x) ∂standardGaussian p) := by
  have hleft := s.hasDerivAt_integral_softFaceDirectional_coordinate A S x j
    (fun _ => 1) (integrable_const 1)
  simp only [one_mul] at hleft
  have hright₁ := s.hasDerivAt_integral_softFaceWeight_line A S x (coordinateDirection j)
    (faceDot u) (standardGaussian_integrable_faceDot u)
  have hright₂ := HasDerivAt.sum (u := inactiveCoordinateFaces S) (fun f _ =>
    (s.hasDerivAt_integral_softFaceWeight_line A (insert f S) x (coordinateDirection j)
      (fun _ => 1) (integrable_const 1)).const_mul (normalDot f (A.mulVec u)))
  simp only [one_mul] at hright₂
  have hright := hright₁.add (hright₂.const_mul (((S.card : ℝ) + 1) / s.bandwidth))
  have hright' : HasDerivAt
      (fun t => ∫ z, s.softFaceDirectional S (coordinateDirection j)
        (A.mulVec z + line x (coordinateDirection j) t) ∂standardGaussian p)
      ((∫ z, faceDot u z * s.softFaceDirectional S (coordinateDirection j)
        (A.mulVec z + x) ∂standardGaussian p) +
        ((S.card : ℝ) + 1) / s.bandwidth *
          ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
            (∫ z, s.softFaceDirectional (insert f S) (coordinateDirection j)
              (A.mulVec z + x) ∂standardGaussian p)) 0 := by
    convert hright using 1
    ext t
    exact s.softFaceDirectional_gaussian_active_coordinate A S j hj
      (line x (coordinateDirection j) t) u hu
  exact hleft.unique hright'

theorem softFaceCoordinateSecond_gaussian_weighted_recursion
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    (∫ z, s.softFaceCoordinateSecond S j (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot u z * (faceDot u z * s.softFaceWeight S (A.mulVec z + x))
        ∂standardGaussian p) -
      faceDot u u * (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
          (∫ z, faceDot u z * s.softFaceWeight (insert f S) (A.mulVec z + x)
            ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
          (∫ z, s.softFaceDirectional (insert f S) (coordinateDirection j)
            (A.mulVec z + x) ∂standardGaussian p) := by
  rw [s.softFaceCoordinateSecond_gaussian_active_coordinate A S j hj x u hu,
    s.softFaceDirectional_gaussian_weighted_active_coordinate A S j hj x u u hu]

theorem softFaceWeight_pair (x : Vector p) {j k : Fin p} (hjk : j ≠ k) (b c : Bool) :
    s.softFaceWeight {(j, b), (k, c)} x =
      s.F x * (s.weights x).pi (j, b) * (s.weights x).pi (k, c) := by
  classical
  have hne : (j, b) ≠ (k, c) := fun h => hjk (congrArg Prod.fst h)
  simp only [softFaceWeight, Finset.prod_pair hne]
  ring

theorem softFaceWeight_triple (x : Vector p) {j k l : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (b c d : Bool) :
    s.softFaceWeight {(j, b), (k, c), (l, d)} x =
      s.F x * (s.weights x).pi (j, b) * (s.weights x).pi (k, c) * (s.weights x).pi (l, d) := by
  classical
  have hne₁ : (j, b) ≠ (k, c) := fun h => hjk (congrArg Prod.fst h)
  have hne₂ : (j, b) ≠ (l, d) := fun h => hjl (congrArg Prod.fst h)
  have hne₃ : (k, c) ≠ (l, d) := fun h => hkl (congrArg Prod.fst h)
  have hn : (j, b) ∉ ({(k, c), (l, d)} : Finset (Face p)) := by simp [hne₁, hne₂]
  simp only [softFaceWeight, Finset.prod_insert hn,
    Finset.prod_pair hne₃]
  ring

theorem mixedThirdDerivativeF_distinct_soft_faces (x : Vector p) {j k l : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    s.mixedThirdDerivativeF x j k l =
      -(6 / s.bandwidth ^ 3) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
        faceSign (j, b) * faceSign (k, c) * faceSign (l, d) *
          s.softFaceWeight {(j, b), (k, c), (l, d)} x := by
  simp only [s.mixedThirdDerivativeF_eq, FaceWeights.thirdFactor,
    FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass, hjk, hjl, hkl,
    false_and, ↓reduceIte, zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  simp_rw [s.softFaceWeight_triple x hjk hjl hkl]
  simp only [Fintype.sum_bool, faceSign, Bool.false_eq_true, ↓reduceIte, FaceWeights.v]
  ring

theorem mixedThirdDerivativeF_repeated_soft_faces (x : Vector p) {j k : Fin p}
    (hjk : j ≠ k) :
    s.mixedThirdDerivativeF x j j k =
      (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
        faceSign (j, b) * faceSign (k, c) *
          s.softFaceDirectional {(j, b), (k, c)} (coordinateDirection j) x := by
  classical
  have hne (b c : Bool) : (j, b) ≠ (k, c) := fun h => hjk (congrArg Prod.fst h)
  simp only [s.mixedThirdDerivativeF_eq, FaceWeights.thirdFactor,
    FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass, hjk,
    false_and, and_false, ↓reduceIte, zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  simp only [softFaceDirectional, Finset.sum_pair (hne _ _), Finset.card_pair (hne _ _),
    normalDot_coordinate_eq, hjk, Ne.symm hjk, ↓reduceIte, directionalMean_coordinate]
  simp_rw [s.softFaceWeight_pair x hjk]
  simp only [Fintype.sum_bool, faceSign, ↓reduceIte, FaceWeights.v, FaceWeights.coordinateMass]
  field_simp [s.bandwidth_pos.ne']
  ring

theorem mixedThirdDerivativeF_diagonal_soft_faces (x : Vector p) (j : Fin p) :
    s.mixedThirdDerivativeF x j j j =
      -(1 / s.bandwidth) * ∑ b : Bool, faceSign (j, b) *
        s.softFaceCoordinateSecond {(j, b)} j x := by
  classical
  simp only [s.mixedThirdDerivativeF_eq, FaceWeights.thirdFactor,
    FaceWeights.diagonalMass, FaceWeights.thirdDiagonalMass, ↓reduceIte]
  simp only [softFaceCoordinateSecond, Finset.sum_singleton, Finset.card_singleton,
    normalDot_coordinate_eq, ↓reduceIte, softFaceWeight, Finset.prod_singleton]
  simp only [Fintype.sum_bool, faceSign, ↓reduceIte, FaceWeights.v, FaceWeights.coordinateMass]
  field_simp [s.bandwidth_pos.ne']
  ring

theorem integrable_softFaceCoordinateSecond_gaussian (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x : Vector p) (j : Fin p) :
    Integrable (fun z => s.softFaceCoordinateSecond S j (A.mulVec z + x))
      (standardGaussian p) := by
  apply (integrable_const
    (((|(∑ f ∈ S, normalDot f (coordinateDirection j))| + ((S.card : ℝ) + 1)) ^ 2 +
      2 * ((S.card : ℝ) + 1)) / s.bandwidth ^ 2)).mono'
    (((s.continuous_softFaceCoordinateSecond S j).comp
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs] using
      s.abs_softFaceCoordinateSecond_le S j (A.mulVec z + x))

theorem convolutionThirdDerivative_eq_standardGaussian
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw A) x j k l =
      ∫ z, s.mixedThirdDerivativeF (A.mulVec z + x) j k l ∂standardGaussian p := by
  have hm : AEStronglyMeasurable (fun y : Vector p => s.mixedThirdDerivativeF (x + y) j k l)
      ((standardGaussian p).map A.mulVec) := by
    exact (((s.continuous_thirdDerivative j k l).comp
      (continuous_const.add continuous_id)).measurable.aestronglyMeasurable)
  calc
    _ = ∫ y, s.mixedThirdDerivativeF (x + y) j k l ∂gaussianLaw A :=
      s.convolutionThirdDerivative_eq_integral (gaussianLaw A) x j k l
    _ = ∫ z, s.mixedThirdDerivativeF (x + A.mulVec z) j k l ∂standardGaussian p :=
      integral_map (measurable_mulVec A).aemeasurable hm
    _ = _ := integral_congr_ae (ae_of_all _ (fun z =>
      congrArg (fun y : Vector p => s.mixedThirdDerivativeF y j k l) (add_comm x (A.mulVec z))))

private theorem diagonalMass_symmetric (w : FaceWeights p) (j k : Fin p) :
    w.diagonalMass j k = w.diagonalMass k j := by
  by_cases hjk : j = k
  · subst k; rfl
  · simp only [FaceWeights.diagonalMass, hjk, Ne.symm hjk, ↓reduceIte]

theorem mixedThirdDerivativeF_swap_first_two (x : Vector p) (j k l : Fin p) :
    s.mixedThirdDerivativeF x j k l = s.mixedThirdDerivativeF x k j l := by
  have hdiag : (s.weights x).thirdDiagonalMass j k l =
      (s.weights x).thirdDiagonalMass k j l := by
    by_cases hjk : j = k
    · subst k; rfl
    · simp only [FaceWeights.thirdDiagonalMass, hjk, Ne.symm hjk, false_and, ↓reduceIte]
  simp only [s.mixedThirdDerivativeF_eq, FaceWeights.thirdFactor]
  rw [diagonalMass_symmetric (s.weights x) j k, hdiag]
  ring

theorem mixedThirdDerivativeF_swap_last_two (x : Vector p) (j k l : Fin p) :
    s.mixedThirdDerivativeF x j k l = s.mixedThirdDerivativeF x j l k := by
  have hdiag : (s.weights x).thirdDiagonalMass j k l =
      (s.weights x).thirdDiagonalMass j l k := by
    simp only [FaceWeights.thirdDiagonalMass, and_comm]
  simp only [s.mixedThirdDerivativeF_eq, FaceWeights.thirdFactor]
  rw [diagonalMass_symmetric (s.weights x) k l, hdiag]
  ring

theorem convolutionThirdDerivative_swap_first_two
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw A) x j k l =
      s.convolutionThirdDerivative (gaussianLaw A) x k j l := by
  rw [s.convolutionThirdDerivative_eq_standardGaussian, s.convolutionThirdDerivative_eq_standardGaussian]
  exact integral_congr_ae (ae_of_all _ (fun z => s.mixedThirdDerivativeF_swap_first_two _ j k l))

theorem convolutionThirdDerivative_swap_last_two
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw A) x j k l =
      s.convolutionThirdDerivative (gaussianLaw A) x j l k := by
  rw [s.convolutionThirdDerivative_eq_standardGaussian, s.convolutionThirdDerivative_eq_standardGaussian]
  exact integral_congr_ae (ae_of_all _ (fun z => s.mixedThirdDerivativeF_swap_last_two _ j k l))

theorem convolutionThirdDerivative_distinct_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k l : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    s.convolutionThirdDerivative (gaussianLaw A) x j k l =
      -(6 / s.bandwidth ^ 3) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
        faceSign (j, b) * faceSign (k, c) * faceSign (l, d) *
          (∫ z, s.softFaceWeight {(j, b), (k, c), (l, d)} (A.mulVec z + x)
            ∂standardGaussian p) := by
  let F : (Bool × Bool × Bool) → Vector p → ℝ := fun b z =>
    (faceSign (j, b.1) * faceSign (k, b.2.1) * faceSign (l, b.2.2)) *
      s.softFaceWeight {(j, b.1), (k, b.2.1), (l, b.2.2)} (A.mulVec z + x)
  have hF (b : Bool × Bool × Bool) : Integrable (F b) (standardGaussian p) :=
    (s.integrable_softFaceWeight_gaussian A _ x).const_mul _
  have hpoint (z : Vector p) : s.mixedThirdDerivativeF (A.mulVec z + x) j k l =
      -(6 / s.bandwidth ^ 3) * ∑ b, F b z := by
    simpa only [Fintype.sum_prod_type, F] using
      s.mixedThirdDerivativeF_distinct_soft_faces (A.mulVec z + x) hjk hjl hkl
  rw [s.convolutionThirdDerivative_eq_standardGaussian]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ => hF b)]
  simp only [F, integral_const_mul, Fintype.sum_prod_type]

theorem convolutionThirdDerivative_repeated_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k : Fin p} (hjk : j ≠ k) :
    s.convolutionThirdDerivative (gaussianLaw A) x j j k =
      (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
        faceSign (j, b) * faceSign (k, c) *
          (∫ z, s.softFaceDirectional {(j, b), (k, c)} (coordinateDirection j)
            (A.mulVec z + x) ∂standardGaussian p) := by
  let F : (Bool × Bool) → Vector p → ℝ := fun b z =>
    (faceSign (j, b.1) * faceSign (k, b.2)) *
      s.softFaceDirectional {(j, b.1), (k, b.2)} (coordinateDirection j) (A.mulVec z + x)
  have hF (b : Bool × Bool) : Integrable (F b) (standardGaussian p) :=
    (s.integrable_softFaceDirectional_gaussian A _ x _).const_mul _
  have hpoint (z : Vector p) : s.mixedThirdDerivativeF (A.mulVec z + x) j j k =
      (2 / s.bandwidth ^ 2) * ∑ b, F b z := by
    simpa only [Fintype.sum_prod_type, F] using
      s.mixedThirdDerivativeF_repeated_soft_faces (A.mulVec z + x) hjk
  rw [s.convolutionThirdDerivative_eq_standardGaussian]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ => hF b)]
  simp only [F, integral_const_mul, Fintype.sum_prod_type]

theorem convolutionThirdDerivative_diagonal_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw A) x j j j =
      -(1 / s.bandwidth) * ∑ b : Bool, faceSign (j, b) *
        (∫ z, s.softFaceCoordinateSecond {(j, b)} j (A.mulVec z + x) ∂standardGaussian p) := by
  rw [s.convolutionThirdDerivative_eq_standardGaussian]
  simp_rw [s.mixedThirdDerivativeF_diagonal_soft_faces]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun b _ =>
    (s.integrable_softFaceCoordinateSecond_gaussian A _ x j).const_mul (faceSign (j, b)))]
  simp only [integral_const_mul]

private theorem abs_signed_sum_le {ι : Type*} [Fintype ι] (c t : ι → ℝ)
    (hc : ∀ i, |c i| = 1) : |∑ i, c i * t i| ≤ ∑ i, |t i| := by
  calc
    _ ≤ ∑ i, |c i * t i| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_congr rfl (fun i _ => by rw [abs_mul, hc, one_mul])

theorem abs_convolutionThirdDerivative_distinct_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k l : Fin p}
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    |s.convolutionThirdDerivative (gaussianLaw A) x j k l| ≤
      (6 / s.bandwidth ^ 3) * ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
        (∫ z, s.softFaceWeight {(j, b), (k, c), (l, d)} (A.mulVec z + x)
          ∂standardGaussian p) := by
  have hband := s.bandwidth_pos
  rw [s.convolutionThirdDerivative_distinct_soft_faces A x hjk hjl hkl,
    abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 6 / s.bandwidth ^ 3)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  let c : (Bool × Bool × Bool) → ℝ := fun b =>
    faceSign (j, b.1) * faceSign (k, b.2.1) * faceSign (l, b.2.2)
  let t : (Bool × Bool × Bool) → ℝ := fun b =>
    ∫ z, s.softFaceWeight {(j, b.1), (k, b.2.1), (l, b.2.2)} (A.mulVec z + x)
      ∂standardGaussian p
  have hc : ∀ b, |c b| = 1 := fun b => by simp only [c, abs_mul, abs_faceSign, one_mul]
  have ht : ∀ b, 0 ≤ t b := fun b => integral_nonneg (fun z => s.softFaceWeight_nonneg _ _)
  have hh : |∑ b, c b * t b| ≤ ∑ b, t b :=
    (abs_signed_sum_le c t hc).trans_eq
      (Finset.sum_congr rfl (fun b _ => abs_of_nonneg (ht b)))
  simpa only [c, t, Fintype.sum_prod_type] using hh

theorem abs_convolutionThirdDerivative_repeated_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {j k : Fin p} (hjk : j ≠ k) :
    |s.convolutionThirdDerivative (gaussianLaw A) x j j k| ≤
      (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
        |∫ z, s.softFaceDirectional {(j, b), (k, c)} (coordinateDirection j)
          (A.mulVec z + x) ∂standardGaussian p| := by
  have hband := s.bandwidth_pos
  rw [s.convolutionThirdDerivative_repeated_soft_faces A x hjk, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 / s.bandwidth ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh := abs_signed_sum_le
    (fun b : Bool × Bool => faceSign (j, b.1) * faceSign (k, b.2))
    (fun b : Bool × Bool => ∫ z, s.softFaceDirectional {(j, b.1), (k, b.2)}
      (coordinateDirection j) (A.mulVec z + x) ∂standardGaussian p)
    (fun b => by simp only [abs_mul, abs_faceSign, one_mul])
  simpa only [Fintype.sum_prod_type] using hh

theorem abs_convolutionThirdDerivative_diagonal_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j : Fin p) :
    |s.convolutionThirdDerivative (gaussianLaw A) x j j j| ≤
      (1 / s.bandwidth) * ∑ b : Bool,
        |∫ z, s.softFaceCoordinateSecond {(j, b)} j (A.mulVec z + x) ∂standardGaussian p| := by
  have hband := s.bandwidth_pos
  rw [s.convolutionThirdDerivative_diagonal_soft_faces A x j, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1 / s.bandwidth)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact abs_signed_sum_le (fun b : Bool => faceSign (j, b))
    (fun b : Bool => ∫ z, s.softFaceCoordinateSecond {(j, b)} j (A.mulVec z + x)
      ∂standardGaussian p) (fun _ => abs_faceSign _)

theorem abs_integral_linear_softFaceWeight_le (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x u : Vector p) :
    |∫ z, faceDot u z * s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p| ≤
      ∫ z, |faceDot u z| * s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p := by
  simpa only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
    norm_integral_le_integral_norm
      (fun z => faceDot u z * s.softFaceWeight S (A.mulVec z + x)) (μ := standardGaussian p)

theorem abs_integral_bilinear_softFaceWeight_le (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x u v : Vector p) :
    |∫ z, faceDot u z * (faceDot v z * s.softFaceWeight S (A.mulVec z + x))
      ∂standardGaussian p| ≤
      ∫ z, |faceDot u z| * |faceDot v z| * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p := by
  simpa only [Real.norm_eq_abs, abs_mul, mul_assoc,
    abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
    norm_integral_le_integral_norm
      (fun z => faceDot u z * (faceDot v z * s.softFaceWeight S (A.mulVec z + x)))
      (μ := standardGaussian p)

theorem abs_softFaceDirectional_gaussian_active_coordinate_le
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    |∫ z, s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x)
      ∂standardGaussian p| ≤
      (∫ z, |faceDot u z| * s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec u)| *
          (∫ z, s.softFaceWeight (insert f S) (A.mulVec z + x) ∂standardGaussian p) := by
  rw [s.softFaceDirectional_gaussian_active_coordinate A S j hj x u hu]
  have hC : 0 ≤ ((S.card : ℝ) + 1) / s.bandwidth :=
    div_nonneg (by positivity) s.bandwidth_pos.le
  have hsum : |∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
      (∫ z, s.softFaceWeight (insert f S) (A.mulVec z + x) ∂standardGaussian p)| ≤
      ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec u)| *
        (∫ z, s.softFaceWeight (insert f S) (A.mulVec z + x) ∂standardGaussian p) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    apply Finset.sum_congr rfl
    intro f _
    rw [abs_mul, abs_of_nonneg (integral_nonneg (fun z => s.softFaceWeight_nonneg _ _))]
  calc
    _ ≤ |∫ z, faceDot u z * s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p| +
        |((S.card : ℝ) + 1) / s.bandwidth *
          ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
            (∫ z, s.softFaceWeight (insert f S) (A.mulVec z + x) ∂standardGaussian p)| :=
      abs_add _ _
    _ ≤ _ := add_le_add (s.abs_integral_linear_softFaceWeight_le A S x u) (by
      rw [abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_left hsum hC)

theorem abs_softFaceDirectional_gaussian_weighted_active_coordinate_le
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u v : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    |∫ z, faceDot v z * s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x)
      ∂standardGaussian p| ≤
      (∫ z, |faceDot u z| * |faceDot v z| * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) +
      |faceDot u v| * (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec u)| *
          (∫ z, |faceDot v z| * s.softFaceWeight (insert f S) (A.mulVec z + x)
            ∂standardGaussian p) := by
  rw [s.softFaceDirectional_gaussian_weighted_active_coordinate A S j hj x u v hu]
  have hC : 0 ≤ ((S.card : ℝ) + 1) / s.bandwidth :=
    div_nonneg (by positivity) s.bandwidth_pos.le
  have hsum : |∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
      (∫ z, faceDot v z * s.softFaceWeight (insert f S) (A.mulVec z + x)
        ∂standardGaussian p)| ≤
      ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec u)| *
        (∫ z, |faceDot v z| * s.softFaceWeight (insert f S) (A.mulVec z + x)
          ∂standardGaussian p) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro f _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (s.abs_integral_linear_softFaceWeight_le A _ x v)
      (abs_nonneg _)
  calc
    _ ≤ |(∫ z, faceDot u z * (faceDot v z * s.softFaceWeight S (A.mulVec z + x))
        ∂standardGaussian p) -
        faceDot u v * (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p)| +
        |((S.card : ℝ) + 1) / s.bandwidth *
          ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
            (∫ z, faceDot v z * s.softFaceWeight (insert f S) (A.mulVec z + x)
              ∂standardGaussian p)| := abs_add _ _
    _ ≤ (|∫ z, faceDot u z * (faceDot v z * s.softFaceWeight S (A.mulVec z + x))
        ∂standardGaussian p| +
        |faceDot u v * (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p)|) +
        ((S.card : ℝ) + 1) / s.bandwidth *
          ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec u)| *
            (∫ z, |faceDot v z| * s.softFaceWeight (insert f S) (A.mulVec z + x)
              ∂standardGaussian p) := by
      apply add_le_add (abs_sub _ _)
      rw [abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_left hsum hC
    _ ≤ _ := by
      have hM : 0 ≤ ∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p :=
        integral_nonneg (fun z => s.softFaceWeight_nonneg S _)
      rw [abs_mul, abs_of_nonneg hM]
      exact add_le_add_right (add_le_add_right (s.abs_integral_bilinear_softFaceWeight_le A S x u v) _) _

end

end RectangleCLT.FaceSmoother

namespace RectangleCLT

/-- Numerical multiplicity bookkeeping for a symmetric third-order tensor.
The repeated-index terms have factor three, with no dimension-dependent loss. -/
theorem sum_symmetric_third_le {p : ℕ} (f : Fin p → Fin p → Fin p → ℝ)
    (hs₁ : ∀ j k l, f j k l = f k j l) (hs₂ : ∀ j k l, f j k l = f j l k)
    (M₁ : Fin p → ℝ) (M₂ : Fin p → Fin p → ℝ) (M₃ : Fin p → Fin p → Fin p → ℝ)
    (hM₂ : ∀ j k, 0 ≤ M₂ j k) (hM₃ : ∀ j k l, 0 ≤ M₃ j k l)
    (hdiag : ∀ j, f j j j ≤ M₁ j)
    (hrepeated : ∀ j k, j ≠ k → f j j k ≤ M₂ j k)
    (hdistinct : ∀ j k l, j ≠ k → j ≠ l → k ≠ l → f j k l ≤ M₃ j k l) :
    (∑ j, ∑ k, ∑ l, f j k l) ≤
      (∑ j, M₁ j) + 3 * (∑ j, ∑ k, M₂ j k) + ∑ j, ∑ k, ∑ l, M₃ j k l := by
  classical
  have hpoint (j k l : Fin p) : f j k l ≤
      (if j = k ∧ j = l then M₁ j else 0) +
      (if j = k then M₂ j l else 0) +
      (if j = l then M₂ j k else 0) +
      (if k = l then M₂ k j else 0) + M₃ j k l := by
    by_cases hjk : j = k
    · subst k
      by_cases hjl : j = l
      · subst l
        simp only [eq_self_iff_true, true_and, ↓reduceIte]
        linarith [hdiag j, hM₂ j j, hM₃ j j j]
      · simp only [eq_self_iff_true, true_and, hjl, ↓reduceIte, zero_add, add_zero]
        linarith [hrepeated j l hjl, hM₃ j j l]
    · by_cases hjl : j = l
      · subst l
        simp only [hjk, Ne.symm hjk, eq_self_iff_true, false_and, ↓reduceIte, zero_add, add_zero]
        have hh : f j k j ≤ M₂ j k := by
          rw [hs₂ j k j]
          exact hrepeated j k hjk
        linarith [hh, hM₃ j k j]
      · by_cases hkl : k = l
        · subst l
          simp only [hjk, eq_self_iff_true, false_and, ↓reduceIte, zero_add, add_zero]
          have hh : f j k k ≤ M₂ k j := by
            rw [hs₁ j k k, hs₂ k j k]
            exact hrepeated k j (Ne.symm hjk)
          linarith [hh, hM₃ j k k]
        · simp only [hjk, hjl, hkl, false_and, ↓reduceIte, zero_add]
          exact hdistinct j k l hjk hjl hkl
  have hsum₁ : (∑ j, ∑ k, ∑ l, if j = k ∧ j = l then M₁ j else 0) = ∑ j, M₁ j := by
    simp [ite_and]
  have hsum₂ : (∑ j, ∑ k, ∑ l, if j = k then M₂ j l else 0) = ∑ j, ∑ k, M₂ j k := by
    simp
  have hsum₃ : (∑ j, ∑ k, ∑ l, if j = l then M₂ j k else 0) = ∑ j, ∑ k, M₂ j k := by
    simp
  have hsum₄ : (∑ j, ∑ k, ∑ l, if k = l then M₂ k j else 0) = ∑ j, ∑ k, M₂ j k := by
    simpa using (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j k : Fin p => M₂ k j))
  calc
    _ ≤ ∑ j, ∑ k, ∑ l,
        ((if j = k ∧ j = l then M₁ j else 0) +
          (if j = k then M₂ j l else 0) + (if j = l then M₂ j k else 0) +
          (if k = l then M₂ k j else 0) + M₃ j k l) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ =>
        Finset.sum_le_sum (fun l _ => hpoint j k l)))
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [hsum₁, hsum₂, hsum₃, hsum₄]
      ring

end RectangleCLT

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

def thirdSingleContribution (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j : Fin p) : ℝ :=
  (1 / s.bandwidth) * ∑ b : Bool,
    |∫ z, s.softFaceCoordinateSecond {(j, b)} j (A.mulVec z + x) ∂standardGaussian p|

def thirdPairContribution (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (j k : Fin p) : ℝ :=
  if j = k then 0 else (2 / s.bandwidth ^ 2) * ∑ b : Bool, ∑ c : Bool,
    |∫ z, s.softFaceDirectional {(j, b), (k, c)} (coordinateDirection j)
      (A.mulVec z + x) ∂standardGaussian p|

def thirdDistinctContribution (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k l : Fin p) : ℝ :=
  if j ≠ k ∧ j ≠ l ∧ k ≠ l then (6 / s.bandwidth ^ 3) *
    ∑ b : Bool, ∑ c : Bool, ∑ d : Bool,
      (∫ z, s.softFaceWeight {(j, b), (k, c), (l, d)} (A.mulVec z + x)
        ∂standardGaussian p)
  else 0

/-- The entire actual third-derivative tensor is reduced to the three
positive active-face contributions, with fixed numerical multiplicities. -/
theorem sum_abs_convolutionThirdDerivative_le_soft_faces
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative (gaussianLaw A) x j k l|) ≤
      (∑ j, s.thirdSingleContribution A x j) +
        3 * (∑ j, ∑ k, s.thirdPairContribution A x j k) +
        ∑ j, ∑ k, ∑ l, s.thirdDistinctContribution A x j k l := by
  apply sum_symmetric_third_le
    (fun j k l => |s.convolutionThirdDerivative (gaussianLaw A) x j k l|)
    (fun j k l => congrArg abs (s.convolutionThirdDerivative_swap_first_two A x j k l))
    (fun j k l => congrArg abs (s.convolutionThirdDerivative_swap_last_two A x j k l))
    (s.thirdSingleContribution A x) (s.thirdPairContribution A x) (s.thirdDistinctContribution A x)
  · intro j k
    unfold thirdPairContribution
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
        (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  · intro j k l
    unfold thirdDistinctContribution
    split_ifs
    · exact mul_nonneg (div_nonneg (by norm_num) (pow_nonneg s.bandwidth_pos.le _))
        (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
          Finset.sum_nonneg (fun _ _ => integral_nonneg (fun z => s.softFaceWeight_nonneg _ _)))))
    · exact le_rfl
  · exact s.abs_convolutionThirdDerivative_diagonal_soft_faces A x
  · intro j k hjk
    simpa only [thirdPairContribution, if_neg hjk] using
      s.abs_convolutionThirdDerivative_repeated_soft_faces A x hjk
  · intro j k l hjk hjl hkl
    have hdistinct : j ≠ k ∧ j ≠ l ∧ k ≠ l := ⟨hjk, hjl, hkl⟩
    unfold thirdDistinctContribution
    rw [if_pos hdistinct]
    exact s.abs_convolutionThirdDerivative_distinct_soft_faces A x hjk hjl hkl

end

end RectangleCLT.FaceSmoother
