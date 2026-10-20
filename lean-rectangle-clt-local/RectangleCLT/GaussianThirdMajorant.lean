import RectangleCLT.GaussianTripleBound
import RectangleCLT.GaussianDualBounds

/-! Positive Gaussian face moments for the actual third-derivative reduction.
The radius is the threshold-independent maximum of projections onto spans of
at most four signed covariance normals. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

namespace CompatibleFaceTuple

/-- Gram matrix of an appended signed face family, before compatibility is
checked. This keeps finite-sum summands independent of membership proofs. -/
def appendGram {p q : ℕ} (S : CompatibleFaceTuple p q) (f : Face p)
    (Q : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  let faces : Fin (q + 1) → Face p := Fin.snoc S.face f
  fun i j => faceSign (faces i) * faceSign (faces j) * Q (faces i).1 (faces j).1

def appendTwoGram {p q : ℕ} (S : CompatibleFaceTuple p q) (f g : Face p)
    (Q : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin (q + 2)) (Fin (q + 2)) ℝ :=
  let faces : Fin (q + 2) → Face p := Fin.snoc (Fin.snoc S.face f) g
  fun i j => faceSign (faces i) * faceSign (faces j) * Q (faces i).1 (faces j).1

/-- Append a new coordinate face to an ordered active family. -/
def appendFace {p q : ℕ} (S : CompatibleFaceTuple p q) (f : Face p)
    (hf : ∀ i, (S.face i).1 ≠ f.1) : CompatibleFaceTuple p (q + 1) where
  face := Fin.snoc S.face f
  coordinate_injective := by
    intro i j hij
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc] at hij
        exact congrArg Fin.castSucc (S.coordinate_injective hij)
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij
        exact False.elim (hf i hij)
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc, Fin.snoc_last] at hij
        exact False.elim (hf j hij.symm)
      · rfl

@[simp] theorem appendFace_initial {p q : ℕ} (S : CompatibleFaceTuple p q) (f : Face p)
    (hf : ∀ i, (S.face i).1 ≠ f.1) : (S.appendFace f hf).initial = S := by
  cases S
  simp only [appendFace, initial, Fin.snoc_castSucc]

@[simp] theorem appendFace_last {p q : ℕ} (S : CompatibleFaceTuple p q) (f : Face p)
    (hf : ∀ i, (S.face i).1 ≠ f.1) : (S.appendFace f hf).face (Fin.last q) = f := by
  simp only [appendFace, Fin.snoc_last]

@[simp] theorem appendFace_castSucc {p q : ℕ} (S : CompatibleFaceTuple p q) (f : Face p)
    (hf : ∀ i, (S.face i).1 ≠ f.1) (i : Fin q) :
    (S.appendFace f hf).face i.castSucc = S.face i := by
  simp only [appendFace, Fin.snoc_castSucc]

@[simp] theorem activeFaceSet_appendFace {p q : ℕ} (S : CompatibleFaceTuple p q) (f : Face p)
    (hf : ∀ i, (S.face i).1 ≠ f.1) :
    (S.appendFace f hf).activeFaceSet = insert f S.activeFaceSet := by
  classical
  ext g
  simp only [activeFaceSet, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · exact Or.inr ⟨i, by simp⟩
    · exact Or.inl (by simp)
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨Fin.last q, by simp⟩
    · exact ⟨i.castSucc, by simp⟩

theorem distinct_coordinate_of_inactive {p q : ℕ} (S : CompatibleFaceTuple p q)
    {f : Face p} (hf : f ∈ inactiveCoordinateFaces S.activeFaceSet) :
    ∀ i, (S.face i).1 ≠ f.1 := by
  intro i hi
  exact (Finset.mem_filter.mp hf).2 (Finset.mem_image.mpr
    ⟨S.face i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩)

@[simp] theorem activeFaceSet_card {p q : ℕ} (S : CompatibleFaceTuple p q) :
    S.activeFaceSet.card = q := by
  classical
  have hinj : Function.Injective S.face := fun _ _ h =>
    S.coordinate_injective (congrArg Prod.fst h)
  simp only [activeFaceSet, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin]

end CompatibleFaceTuple

theorem integrable_fourFaceProjectionRadius_polynomial {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    Integrable (fun z => (1 + fourFaceProjectionRadius A z) ^ k)
      (standardGaussian p) := by
  have hh := (fourFaceProjectionRadius_weighted_moment_le hp A le_rfl k).1
  apply hh.mono'
    ((measurable_const.add (measurable_fourFaceProjectionRadius A)).pow_const k).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by
    linarith [fourFaceProjectionRadius_nonneg A z] : 0 ≤ 1 + fourFaceProjectionRadius A z) k)]
  exact le_mul_of_one_le_left (pow_nonneg (by
    linarith [fourFaceProjectionRadius_nonneg A z]) k)
    (Real.one_le_exp_iff.mpr (div_nonneg (fourFaceProjectionRadius_nonneg A z)
      (Real.sqrt_nonneg _)))

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem softFaceWeight_eq_zero_of_missing {S : Finset (Face p)} {f : Face p}
    (hf : f ∈ S) (hmissing : f ∉ s.faces) (x : Vector p) :
    s.softFaceWeight S x = 0 := by
  classical
  have hpi : (s.weights x).pi f = 0 := by
    simp only [FaceWeights.pi, weights, if_neg hmissing, zero_div]
  unfold softFaceWeight
  rw [Finset.prod_eq_zero hf hpi, mul_zero]

theorem softFaceDirectional_eq_zero_of_missing {S : Finset (Face p)} {f : Face p}
    (hf : f ∈ S) (hmissing : f ∉ s.faces) (y x : Vector p) :
    s.softFaceDirectional S y x = 0 := by
  simp only [softFaceDirectional, s.softFaceWeight_eq_zero_of_missing hf hmissing x,
    zero_div, zero_mul]

theorem softFaceCoordinateSecond_eq_zero_of_missing {S : Finset (Face p)} {f : Face p}
    (hf : f ∈ S) (hmissing : f ∉ s.faces) (j : Fin p) (x : Vector p) :
    s.softFaceCoordinateSecond S j x = 0 := by
  simp only [softFaceCoordinateSecond, s.softFaceWeight_eq_zero_of_missing hf hmissing x,
    zero_div, zero_mul]

def gaussianSoftFaceMoment (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (S : Finset (Face p)) (k : ℕ) : ℝ :=
  ∫ z, (1 + fourFaceProjectionRadius A z) ^ k * s.softFaceWeight S (A.mulVec z + x)
    ∂standardGaussian p

theorem gaussianSoftFaceMoment_nonneg (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (S : Finset (Face p)) (k : ℕ) :
    0 ≤ s.gaussianSoftFaceMoment A x S k := by
  apply integral_nonneg
  intro z
  exact mul_nonneg (pow_nonneg (by linarith [fourFaceProjectionRadius_nonneg A z]) k)
    (s.softFaceWeight_nonneg S _)

theorem gaussianSoftFaceMoment_eq_zero_of_missing
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (k : ℕ)
    {S : Finset (Face p)} {f : Face p} (hf : f ∈ S) (hmissing : f ∉ s.faces) :
    s.gaussianSoftFaceMoment A x S k = 0 := by
  simp only [gaussianSoftFaceMoment, s.softFaceWeight_eq_zero_of_missing hf hmissing,
    mul_zero, integral_zero]

theorem integrable_gaussianSoftFaceMoment (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (S : Finset (Face p)) (k : ℕ) :
    Integrable (fun z => (1 + fourFaceProjectionRadius A z) ^ k *
      s.softFaceWeight S (A.mulVec z + x)) (standardGaussian p) := by
  simpa only [mul_comm] using
    (integrable_fourFaceProjectionRadius_polynomial hp A k).bdd_mul
      (s.integrable_softFaceWeight_gaussian A S x).aestronglyMeasurable
      ⟨1, fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
          s.softFaceWeight_le_one S (A.mulVec z + x)⟩

@[simp] theorem gaussianSoftFaceMoment_zero (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (S : Finset (Face p)) :
    s.gaussianSoftFaceMoment A x S 0 =
      ∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p := by
  simp only [gaussianSoftFaceMoment, pow_zero, one_mul]

theorem integral_abs_linear_softFaceWeight_le_moment (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (x u : Vector p)
    {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ z, |faceDot u z| ≤ C * fourFaceProjectionRadius A z) :
    (∫ z, |faceDot u z| * s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) ≤
      C * s.gaussianSoftFaceMoment A x S 1 := by
  rw [gaussianSoftFaceMoment, ← integral_const_mul]
  apply integral_mono
  · simpa only [abs_mul, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
      (s.integrable_linear_softFaceWeight_gaussian A S x u).abs
  · exact (s.integrable_gaussianSoftFaceMoment hp A x S 1).const_mul C
  · intro z
    dsimp only
    rw [pow_one]
    calc
      _ ≤ (C * fourFaceProjectionRadius A z) * s.softFaceWeight S (A.mulVec z + x) :=
        mul_le_mul_of_nonneg_right (hu z) (s.softFaceWeight_nonneg S _)
      _ ≤ C * (1 + fourFaceProjectionRadius A z) * s.softFaceWeight S (A.mulVec z + x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC)
          (s.softFaceWeight_nonneg S _)
      _ = _ := mul_assoc _ _ _

/-- An absolute second-coordinate recursion, after the genuine Gaussian
integration by parts and differentiation under the integral. Every term on
the right is nonnegative and retains its concrete active-face kernel. -/
theorem abs_softFaceCoordinateSecond_gaussian_active_coordinate_le
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    |∫ z, s.softFaceCoordinateSecond S j (A.mulVec z + x) ∂standardGaussian p| ≤
      (∫ z, |faceDot u z| * |faceDot u z| * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) +
      |faceDot u u| * (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec u)| *
          (∫ z, |faceDot u z| * s.softFaceWeight (insert f S) (A.mulVec z + x)
            ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, |normalDot f (A.mulVec u)| *
          |∫ z, s.softFaceDirectional (insert f S) (coordinateDirection j)
            (A.mulVec z + x) ∂standardGaussian p| := by
  have hC : 0 ≤ ((S.card : ℝ) + 1) / s.bandwidth := by
    exact div_nonneg (by positivity) s.bandwidth_pos.le
  rw [s.softFaceCoordinateSecond_gaussian_active_coordinate A S j hj x u hu]
  refine (abs_add _ _).trans (add_le_add
    (s.abs_softFaceDirectional_gaussian_weighted_active_coordinate_le A S j hj x u u hu) ?_)
  rw [abs_mul, abs_of_nonneg hC]
  apply mul_le_mul_of_nonneg_left _ hC
  exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
    apply Finset.sum_congr rfl
    intro f _
    exact abs_mul _ _)

theorem abs_softFaceDirectional_pair_le_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 2)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (i : Fin 2) (x : Vector p) :
    |∫ z, s.softFaceDirectional T.activeFaceSet (coordinateDirection (T.face i).1)
      (A.mulVec z + x) ∂standardGaussian p| ≤
      (1 / Real.sqrt (pairGap (A * A.transpose))) *
        s.gaussianSoftFaceMoment A x T.activeFaceSet 1 +
      (3 / s.bandwidth) *
        ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
          |normalDot f (A.mulVec (T.coordinateDual A (T.face i).1))| *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0 := by
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hd : IsUnit (T.gram (A * A.transpose)).det := isUnit_iff_ne_zero.mpr
    (ne_of_gt (hc.trans_le (T.gram_two_det_ge_pairGap hsym hdiag hc.le)))
  have hbase := s.abs_softFaceDirectional_gaussian_active_coordinate_le A
    T.activeFaceSet (T.face i).1 (T.coordinate_mem_activeFaceSet i) x
    (T.coordinateDual A (T.face i).1)
    (T.coordinateDual_agrees_on_activeFaceSet A hd (T.face i).1)
  simp only [CompatibleFaceTuple.activeFaceSet_card, Nat.cast_ofNat,
    show (2 : ℝ) + 1 = 3 by norm_num] at hbase
  apply hbase.trans
  simp only [gaussianSoftFaceMoment_zero]
  apply add_le_add_right
  exact s.integral_abs_linear_softFaceWeight_le_moment hp A T.activeFaceSet x _
    (div_nonneg zero_le_one (Real.sqrt_nonneg _))
    (T.pair_abs_faceDot_coordinateDual_le A hdiag hc i)

theorem abs_softFaceCoordinateSecond_singleton_le_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 1)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (i : Fin 1) (x : Vector p) :
    |∫ z, s.softFaceCoordinateSecond T.activeFaceSet (T.face i).1 (A.mulVec z + x)
      ∂standardGaussian p| ≤
      2 * s.gaussianSoftFaceMoment A x T.activeFaceSet 2 +
      (2 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 +
      (2 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        |∫ z, s.softFaceDirectional (insert f T.activeFaceSet)
          (coordinateDirection (T.face i).1) (A.mulVec z + x) ∂standardGaussian p| := by
  let u := T.coordinateDual A (T.face i).1
  have hG : T.gram (A * A.transpose) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext j k
    have hjk : j = k := Subsingleton.elim _ _
    subst k
    simpa using T.gram_diagonal hdiag j
  have hd : IsUnit (T.gram (A * A.transpose)).det := by
    rw [hG, Matrix.det_one]
    exact isUnit_one
  have hu (z : Vector p) : |faceDot u z| ≤ fourFaceProjectionRadius A z :=
    T.singleton_abs_faceDot_coordinateDual_le A hdiag i z
  have huu : |faceDot u u| ≤ 1 := by
    have hn := T.singleton_coordinateDual_norm_le_one A hdiag i
    change ‖projectionEuclideanVector u‖ ≤ 1 at hn
    have hn2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin p => ℝ) (projectionEuclideanVector u)
    change ‖projectionEuclideanVector u‖ ^ 2 = ∑ j, ‖u j‖ ^ 2 at hn2
    simp only [Real.norm_eq_abs, sq_abs] at hn2
    have hd0 : 0 ≤ faceDot u u := by
      exact Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
    rw [abs_of_nonneg hd0]
    change (∑ j, u j * u j) ≤ 1
    have heq : (∑ j, u j * u j) = ∑ j, u j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    nlinarith [norm_nonneg (projectionEuclideanVector u)]
  have hbase := s.abs_softFaceCoordinateSecond_gaussian_active_coordinate_le A
    T.activeFaceSet (T.face i).1 (T.coordinate_mem_activeFaceSet i) x u
    (T.coordinateDual_agrees_on_activeFaceSet A hd (T.face i).1)
  simp only [CompatibleFaceTuple.activeFaceSet_card, Nat.cast_one,
    show (1 : ℝ) + 1 = 2 by norm_num] at hbase
  have hbil : (∫ z, |faceDot u z| * |faceDot u z| *
      s.softFaceWeight T.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) ≤
      s.gaussianSoftFaceMoment A x T.activeFaceSet 2 := by
    apply integral_mono
    · simpa only [abs_mul, abs_of_nonneg (s.softFaceWeight_nonneg T.activeFaceSet _)] using
        (s.integrable_bilinear_softFaceWeight_gaussian A T.activeFaceSet x u u).abs
    · exact s.integrable_gaussianSoftFaceMoment hp A x T.activeFaceSet 2
    · intro z
      dsimp only
      apply mul_le_mul_of_nonneg_right _ (s.softFaceWeight_nonneg T.activeFaceSet _)
      have hh := hu z
      have hR := fourFaceProjectionRadius_nonneg A z
      calc
        _ = |faceDot u z| ^ 2 := by ring
        _ ≤ (fourFaceProjectionRadius A z) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
        _ ≤ _ := by nlinarith
  have hconst : |faceDot u u| *
      (∫ z, s.softFaceWeight T.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) ≤
      s.gaussianSoftFaceMoment A x T.activeFaceSet 2 := by
    apply (mul_le_mul_of_nonneg_right huu
      (integral_nonneg (fun z => s.softFaceWeight_nonneg _ _))).trans
    rw [one_mul]
    apply integral_mono (s.integrable_softFaceWeight_gaussian A T.activeFaceSet x)
      (s.integrable_gaussianSoftFaceMoment hp A x T.activeFaceSet 2)
    intro z
    dsimp only
    apply le_mul_of_one_le_left (s.softFaceWeight_nonneg T.activeFaceSet _)
    nlinarith [fourFaceProjectionRadius_nonneg A z,
      sq_nonneg (fourFaceProjectionRadius A z)]
  have hsumlin :
      (∑ f ∈ inactiveCoordinateFaces T.activeFaceSet, |normalDot f (A.mulVec u)| *
        (∫ z, |faceDot u z| * s.softFaceWeight (insert f T.activeFaceSet) (A.mulVec z + x)
          ∂standardGaussian p)) ≤
      ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 := by
    apply Finset.sum_le_sum
    intro f _
    calc
      _ ≤ 1 * (∫ z, |faceDot u z| * s.softFaceWeight (insert f T.activeFaceSet)
          (A.mulVec z + x) ∂standardGaussian p) :=
        mul_le_mul_of_nonneg_right (T.singleton_abs_newFace_coefficient_le_one A hdiag i f)
          (integral_nonneg (fun z => mul_nonneg (abs_nonneg _) (s.softFaceWeight_nonneg _ _)))
      _ ≤ _ := by
        rw [one_mul]
        simpa only [one_mul] using s.integral_abs_linear_softFaceWeight_le_moment hp A
          (insert f T.activeFaceSet) x u zero_le_one (fun z => by simpa using hu z)
  have hsumdir :
      (∑ f ∈ inactiveCoordinateFaces T.activeFaceSet, |normalDot f (A.mulVec u)| *
        |∫ z, s.softFaceDirectional (insert f T.activeFaceSet) (coordinateDirection (T.face i).1)
          (A.mulVec z + x) ∂standardGaussian p|) ≤
      ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        |∫ z, s.softFaceDirectional (insert f T.activeFaceSet) (coordinateDirection (T.face i).1)
          (A.mulVec z + x) ∂standardGaussian p| := by
    apply Finset.sum_le_sum
    intro f _
    exact (mul_le_mul_of_nonneg_right
      (T.singleton_abs_newFace_coefficient_le_one A hdiag i f) (abs_nonneg _)).trans_eq
        (one_mul _)
  have hC : 0 ≤ 2 / s.bandwidth := div_nonneg (by norm_num) s.bandwidth_pos.le
  apply hbase.trans
  exact add_le_add
    (add_le_add (by linarith) (mul_le_mul_of_nonneg_left hsumlin hC))
    (mul_le_mul_of_nonneg_left hsumdir hC)

/-- The pair derivative costs exactly one pair gap and one three-coordinate
Rayleigh lower bound. The prospective third-face regression coefficient is
absorbed with its own final Gram determinant before summation. -/
theorem abs_softFaceDirectional_pair_le_det_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 2)
    {a : ℝ} (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose))
    (i : Fin 2) (x : Vector p) :
    |∫ z, s.softFaceDirectional T.activeFaceSet (coordinateDirection (T.face i).1)
      (A.mulVec z + x) ∂standardGaussian p| ≤
      (1 / (pairGap (A * A.transpose) * a)) * (T.gram (A * A.transpose)).det *
        s.gaussianSoftFaceMoment A x T.activeFaceSet 1 +
      (3 / s.bandwidth) *
        ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
          (2 / (a * pairGap (A * A.transpose))) *
            (T.appendGram f (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 0 := by
  classical
  have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hdet : 0 < (T.gram (A * A.transpose)).det :=
    hc.trans_le (T.gram_two_det_ge_pairGap hsym hdiag hc.le)
  have hpcoef := (div_le_iff₀ hdet).mp
    (T.pair_inverse_sqrt_weight_div_det_le A hdiag hc ha hac)
  apply (s.abs_softFaceDirectional_pair_le_moments hp A T hdiag hc i x).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right hpcoef
      (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 1)
  · apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) s.bandwidth_pos.le)
    apply Finset.sum_le_sum
    intro f hf
    let U := T.appendFace f (T.distinct_coordinate_of_inactive hf)
    have hUdet : 0 < (U.gram (A * A.transpose)).det := U.gram_det_pos hQ ha hsym
    have hcoef := U.triple_initial_dualCoefficient_weight_div_det_le A hQ ha hdiag hc i
    have hsame : U.initial = T := T.appendFace_initial f _
    have hlast : U.face 2 = f := T.appendFace_last f _
    rw [hsame, hlast] at hcoef
    have habs := (div_le_iff₀ hUdet).mp hcoef
    apply mul_le_mul_of_nonneg_right _
      (s.gaussianSoftFaceMoment_nonneg A x (insert f T.activeFaceSet) 0)
    change |normalDot f (A.mulVec (T.coordinateDual A (T.face i).1))| ≤
      (2 / (a * pairGap (A * A.transpose))) * (U.gram (A * A.transpose)).det
    exact (le_add_of_nonneg_left zero_le_one).trans habs

theorem abs_softFaceCoordinateSecond_singleton_le_det_moments (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (T : CompatibleFaceTuple p 1)
    {a : ℝ} (hQ : LocalCovarianceLower (A * A.transpose) 3 a) (ha : 0 < a)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hac : a ≤ pairGap (A * A.transpose))
    (i : Fin 1) (x : Vector p) :
    |∫ z, s.softFaceCoordinateSecond T.activeFaceSet (T.face i).1 (A.mulVec z + x)
      ∂standardGaussian p| ≤
      (2 / (pairGap (A * A.transpose) * a)) *
        s.gaussianSoftFaceMoment A x T.activeFaceSet 2 +
      (2 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
        ((2 / (pairGap (A * A.transpose) * a)) * (T.appendGram f (A * A.transpose)).det *
          s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 +
        (3 / s.bandwidth) * ∑ g ∈ inactiveCoordinateFaces (insert f T.activeFaceSet),
          (2 / (a * pairGap (A * A.transpose))) *
            (T.appendTwoGram f g (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert g (insert f T.activeFaceSet)) 0) := by
  classical
  let c := pairGap (A * A.transpose)
  have hc1 : c ≤ 1 := pairGap_le_one _
  have ha1 : a ≤ 1 := hac.trans hc1
  have hca1 : c * a ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hc1 ha.le
    nlinarith
  have hcoef1 : 2 ≤ 2 / (c * a) := (le_div_iff₀ (mul_pos hc ha)).mpr (by nlinarith)
  have hsqrt1 : Real.sqrt c ≤ 1 := Real.sqrt_le_one.mpr hc1
  have hsqrtpos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hinv1 : 1 ≤ 1 / Real.sqrt c := (le_div_iff₀ hsqrtpos).mpr (by linarith)
  have hbase := s.abs_softFaceCoordinateSecond_singleton_le_moments hp A T hdiag i x
  calc
    _ ≤ 2 * s.gaussianSoftFaceMoment A x T.activeFaceSet 2 +
        (2 / s.bandwidth) * ∑ f ∈ inactiveCoordinateFaces T.activeFaceSet,
          (s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 +
            |∫ z, s.softFaceDirectional (insert f T.activeFaceSet)
              (coordinateDirection (T.face i).1) (A.mulVec z + x) ∂standardGaussian p|) := by
      convert hbase using 1
      rw [Finset.sum_add_distrib]
      ring
    _ ≤ _ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hcoef1
          (s.gaussianSoftFaceMoment_nonneg A x T.activeFaceSet 2)
      · apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) s.bandwidth_pos.le)
        apply Finset.sum_le_sum
        intro f hf
        let U := T.appendFace f (T.distinct_coordinate_of_inactive hf)
        have hUset : U.activeFaceSet = insert f T.activeFaceSet := T.activeFaceSet_appendFace f _
        have hUi : (U.face i.castSucc).1 = (T.face i).1 := by simp [U]
        have hdir := s.abs_softFaceDirectional_pair_le_det_moments hp A U hQ ha
          hdiag hc hac i.castSucc x
        rw [hUset, hUi] at hdir
        have hsym : ∀ j k, (A * A.transpose) j k = (A * A.transpose) k j := by
          intro j k
          simp only [Matrix.mul_apply, Matrix.transpose_apply]
          exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
        have hUdet : 0 < (U.gram (A * A.transpose)).det :=
          hc.trans_le (U.gram_two_det_ge_pairGap hsym hdiag hc.le)
        have hUcoef : 1 ≤ (1 / (c * a)) * (U.gram (A * A.transpose)).det :=
          hinv1.trans ((div_le_iff₀ hUdet).mp
            (U.pair_inverse_sqrt_weight_div_det_le A hdiag hc ha hac))
        have hmoment : s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 ≤
            (1 / (c * a)) * (U.gram (A * A.transpose)).det *
              s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hUcoef
            (s.gaussianSoftFaceMoment_nonneg A x (insert f T.activeFaceSet) 1)
        refine (add_le_add hmoment hdir).trans_eq ?_
        change (1 / (c * a)) * (U.gram (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 +
          ((1 / (c * a)) * (U.gram (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 +
            (3 / s.bandwidth) * ∑ g ∈ inactiveCoordinateFaces (insert f T.activeFaceSet),
              (2 / (a * c)) * (U.appendGram g (A * A.transpose)).det *
                s.gaussianSoftFaceMoment A x (insert g (insert f T.activeFaceSet)) 0) = _
        change _ = (2 / (c * a)) * (U.gram (A * A.transpose)).det *
            s.gaussianSoftFaceMoment A x (insert f T.activeFaceSet) 1 +
          (3 / s.bandwidth) * ∑ g ∈ inactiveCoordinateFaces (insert f T.activeFaceSet),
            (2 / (a * c)) * (U.appendGram g (A * A.transpose)).det *
              s.gaussianSoftFaceMoment A x (insert g (insert f T.activeFaceSet)) 0
        ring

end FaceSmoother
end
end RectangleCLT
