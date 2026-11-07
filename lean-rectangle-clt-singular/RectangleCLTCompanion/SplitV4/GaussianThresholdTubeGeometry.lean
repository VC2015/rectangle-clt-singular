import RectangleCLTCompanion.SplitV4.GaussianThresholdPairData
import RectangleCLTCompanion.SplitV4.GaussianThresholdMixedDerivatives

/-! Actual native-coordinate pair frames and the corresponding adaptive
Gaussian outward-tube geometry for Appendix B.5. -/

open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {r m : ℕ}

theorem thresholdPairBisector_euclidean (u : Fin m → Vector r) (j l : Fin m) :
    projectionEuclideanVector (thresholdPairBisector u j l) =
      SignedSurface.bisector (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l)) := by
  ext k
  rfl

theorem thresholdPairDifference_euclidean (u : Fin m → Vector r) (j l : Fin m) :
    projectionEuclideanVector (thresholdPairDifference u j l) =
      SignedSurface.differenceDirection (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l)) := by
  ext k
  rfl

theorem thresholdPairBisector_unit (u : Fin m → Vector r) (j l : Fin m)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0) :
    vectorNormSq (thresholdPairBisector u j l) = 1 := by
  rw [SignedSurface.vectorNormSq_eq_euclidean_norm_sq]
  change ‖projectionEuclideanVector (thresholdPairBisector u j l)‖ ^ 2 = 1
  rw [thresholdPairBisector_euclidean, SignedSurface.norm_bisector _ _ hp, one_pow]

theorem thresholdPairDifference_unit (u : Fin m → Vector r) (j l : Fin m)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    vectorNormSq (thresholdPairDifference u j l) = 1 := by
  rw [SignedSurface.vectorNormSq_eq_euclidean_norm_sq]
  change ‖projectionEuclideanVector (thresholdPairDifference u j l)‖ ^ 2 = 1
  rw [thresholdPairDifference_euclidean, SignedSurface.norm_differenceDirection _ _ hm, one_pow]

theorem thresholdPair_frame_orthogonal (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1) :
    faceDot (thresholdPairBisector u j l) (thresholdPairDifference u j l) = 0 := by
  rw [SignedSurface.faceDot_eq_euclidean_inner]
  change ⟪projectionEuclideanVector (thresholdPairBisector u j l),
    projectionEuclideanVector (thresholdPairDifference u j l)⟫_ℝ = 0
  rw [thresholdPairBisector_euclidean, thresholdPairDifference_euclidean]
  exact SignedSurface.inner_bisector_differenceDirection _ _
    ((thresholdEuclideanNormal_unit _ hu).trans (thresholdEuclideanNormal_unit _ hv).symm)

theorem thresholdPair_left_expansion (u : Fin m → Vector r) (j l : Fin m)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    u j = (‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖ / 2) •
        thresholdPairBisector u j l +
      (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ / 2) •
        thresholdPairDifference u j l := by
  funext k
  change u j k =
    (‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖ / 2) *
      (‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖⁻¹ * (u j k + u l k)) +
    (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ / 2) *
      (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖⁻¹ * (u j k - u l k))
  field_simp [norm_ne_zero_iff.mpr hp, norm_ne_zero_iff.mpr hm]
  <;> ring

theorem thresholdPair_right_expansion (u : Fin m → Vector r) (j l : Fin m)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    u l = (‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖ / 2) •
        thresholdPairBisector u j l -
      (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ / 2) •
        thresholdPairDifference u j l := by
  funext k
  change u l k =
    (‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖ / 2) *
      (‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖⁻¹ * (u j k + u l k)) -
    (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ / 2) *
      (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖⁻¹ * (u j k - u l k))
  field_simp [norm_ne_zero_iff.mpr hp, norm_ne_zero_iff.mpr hm]
  <;> ring

theorem faceDot_affine_combination {r : ℕ} (u v z : Vector r) (a b : ℝ) :
    faceDot (a • u + b • v) z = a * faceDot u z + b * faceDot v z := by
  simp only [faceDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem faceDot_gaussianSectionPoint {r : ℕ} (u v : Vector r) (a : ℝ) (g : Vector r) :
    faceDot u (SignedSurface.gaussianSectionPoint v a g) =
      faceDot u g + (a - faceDot v g) * faceDot u v := by
  rw [SignedSurface.gaussianSectionPoint_eq]
  simp only [faceDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem gaussianPairSectionPoint_levels {r : ℕ} (e f : Vector r) (a c : ℝ) (g : Vector r)
    (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1) (hef : faceDot e f = 0) :
    faceDot e (gaussianPairSectionPoint e f a c g) = a ∧
      faceDot f (gaussianPairSectionPoint e f a c g) = c := by
  constructor
  · exact SignedSurface.gaussianSectionPoint_on_hyperplane e a he _
  · rw [gaussianPairSectionPoint, faceDot_gaussianSectionPoint, faceDot_comm f e, hef,
      mul_zero, add_zero]
    exact SignedSurface.gaussianSectionPoint_on_hyperplane f c hf g

theorem gaussianPairBase_left_level (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) (g : Vector r) :
    faceDot (u j) (gaussianPairBase u b j l g) = b j := by
  have hh := gaussianPairSectionPoint_levels (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) g
    (thresholdPairBisector_unit u j l hp) (thresholdPairDifference_unit u j l hm)
    (thresholdPair_frame_orthogonal u j l hu hv)
  conv_lhs => lhs; rw [thresholdPair_left_expansion u j l hp hm]
  rw [faceDot_affine_combination]
  change _ * faceDot _ (gaussianPairSectionPoint _ _ _ _ g) +
    _ * faceDot _ (gaussianPairSectionPoint _ _ _ _ g) = _
  rw [hh.1, hh.2]
  dsimp only [thresholdPairFirstLevel, thresholdPairSecondLevel]
  field_simp [norm_ne_zero_iff.mpr hp, norm_ne_zero_iff.mpr hm]
  <;> ring

theorem gaussianPairBase_right_level (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) (g : Vector r) :
    faceDot (u l) (gaussianPairBase u b j l g) = b l := by
  have hh := gaussianPairSectionPoint_levels (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) g
    (thresholdPairBisector_unit u j l hp) (thresholdPairDifference_unit u j l hm)
    (thresholdPair_frame_orthogonal u j l hu hv)
  conv_lhs => lhs; rw [thresholdPair_right_expansion u j l hp hm]
  have hd : faceDot ((‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖ / 2) •
      thresholdPairBisector u j l -
      (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ / 2) • thresholdPairDifference u j l)
      (gaussianPairBase u b j l g) =
      (‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖ / 2) * faceDot
        (thresholdPairBisector u j l) (gaussianPairBase u b j l g) -
      (‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ / 2) * faceDot
        (thresholdPairDifference u j l) (gaussianPairBase u b j l g) := by
    simp only [faceDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rw [hd]
  change _ * faceDot _ (gaussianPairSectionPoint _ _ _ _ g) -
    _ * faceDot _ (gaussianPairSectionPoint _ _ _ _ g) = _
  rw [hh.1, hh.2]
  dsimp only [thresholdPairFirstLevel, thresholdPairSecondLevel]
  field_simp [norm_ne_zero_iff.mpr hp, norm_ne_zero_iff.mpr hm]
  <;> ring

theorem gaussianPairBase_frame_levels (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) (g : Vector r) :
    faceDot (thresholdPairBisector u j l) (gaussianPairBase u b j l g) = thresholdPairFirstLevel u b j l ∧
      faceDot (thresholdPairDifference u j l) (gaussianPairBase u b j l g) = thresholdPairSecondLevel u b j l :=
  gaussianPairSectionPoint_levels _ _ _ _ g (thresholdPairBisector_unit u j l hp)
    (thresholdPairDifference_unit u j l hm) (thresholdPair_frame_orthogonal u j l hu hv)

def thresholdPairFirstCoefficient (u : Fin m → Vector r) (j l : Fin m) : ℝ :=
  ‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖ / 2

def thresholdPairSecondCoefficient (u : Fin m → Vector r) (j l : Fin m) : ℝ :=
  ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ / 2

theorem thresholdPair_coefficients_sq (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1) :
    thresholdPairFirstCoefficient u j l ^ 2 + thresholdPairSecondCoefficient u j l ^ 2 = 1 ∧
      thresholdPairFirstCoefficient u j l ^ 2 - thresholdPairSecondCoefficient u j l ^ 2 = faceDot (u j) (u l) := by
  have he := norm_add_sq_real (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
  have hd := norm_sub_sq_real (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
  rw [thresholdEuclideanNormal_unit _ hu, thresholdEuclideanNormal_unit _ hv] at he hd
  have hdot : ⟪projectionEuclideanVector (u j), projectionEuclideanVector (u l)⟫_ℝ = faceDot (u j) (u l) :=
    (SignedSurface.faceDot_eq_euclidean_inner _ _).symm
  rw [hdot] at he hd
  dsimp only [thresholdPairFirstCoefficient, thresholdPairSecondCoefficient]
  constructor <;> nlinarith

theorem thresholdPair_residualScale_eq (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    gaussianThresholdResidualScale u j l =
      2 * thresholdPairFirstCoefficient u j l * thresholdPairSecondCoefficient u j l := by
  have hh := SignedSurface.norm_sum_mul_norm_sub (projectionEuclideanVector (u j))
    (projectionEuclideanVector (u l)) (thresholdEuclideanNormal_unit _ hu)
    (thresholdEuclideanNormal_unit _ hv) hp hm
  have hdot : ⟪projectionEuclideanVector (u j), projectionEuclideanVector (u l)⟫_ℝ = faceDot (u j) (u l) :=
    (SignedSurface.faceDot_eq_euclidean_inner _ _).symm
  rw [hdot, ← gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv] at hh
  dsimp only [thresholdPairFirstCoefficient, thresholdPairSecondCoefficient]
  nlinarith

theorem thresholdPair_residualNormal_eq (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    (gaussianThresholdResidualScale u j l)⁻¹ • gaussianNormalProjection (u j) (u l) =
      thresholdPairSecondCoefficient u j l • thresholdPairBisector u j l -
        thresholdPairFirstCoefficient u j l • thresholdPairDifference u j l := by
  have hab := thresholdPair_coefficients_sq u j l hu hv
  have hA : 0 < thresholdPairFirstCoefficient u j l := div_pos (norm_pos_iff.mpr hp) (by norm_num)
  have hB : 0 < thresholdPairSecondCoefficient u j l := div_pos (norm_pos_iff.mpr hm) (by norm_num)
  have hdot : faceDot (u l) (u j) = thresholdPairFirstCoefficient u j l ^ 2 -
      thresholdPairSecondCoefficient u j l ^ 2 := by rw [faceDot_comm]; exact hab.2.symm
  have hu' := thresholdPair_left_expansion u j l hp hm
  have hv' := thresholdPair_right_expansion u j l hp hm
  change u j = thresholdPairFirstCoefficient u j l • thresholdPairBisector u j l +
    thresholdPairSecondCoefficient u j l • thresholdPairDifference u j l at hu'
  change u l = thresholdPairFirstCoefficient u j l • thresholdPairBisector u j l -
    thresholdPairSecondCoefficient u j l • thresholdPairDifference u j l at hv'
  rw [gaussianNormalProjection, hdot]
  conv_lhs => arg 2; lhs; rw [hv']
  conv_lhs => arg 2; rhs; arg 2; rw [hu']
  rw [thresholdPair_residualScale_eq u j l hu hv hp hm]
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  field_simp [hA.ne', hB.ne']
  nlinarith [congrArg (fun t : ℝ => t * thresholdPairFirstCoefficient u j l *
    thresholdPairBisector u j l i) hab.1,
    congrArg (fun t : ℝ => t * thresholdPairSecondCoefficient u j l *
      thresholdPairDifference u j l i) hab.1]

theorem gaussianPairSectionPoint_reconstruct {r : ℕ} (e f : Vector r) (a c : ℝ) (g : Vector r)
    (hef : faceDot e f = 0) :
    g = gaussianPairSectionPoint e f a c g + (faceDot e g - a) • e + (faceDot f g - c) • f := by
  have hp : gaussianPairSectionPoint e f a c g =
      g + (c - faceDot f g) • f + (a - faceDot e g) • e := by
    rw [gaussianPairSectionPoint, SignedSurface.gaussianSectionPoint_eq,
      faceDot_gaussianSectionPoint, hef, mul_zero, add_zero,
      SignedSurface.gaussianSectionPoint_eq]
  rw [hp]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem gaussianPairBase_reconstruct (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1) (g : Vector r) :
    projectionEuclideanVector g = projectionEuclideanVector (gaussianPairBase u b j l g) +
      SignedSurface.ridgeDisplacement (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (faceDot (thresholdPairBisector u j l) g - thresholdPairFirstLevel u b j l,
          faceDot (thresholdPairDifference u j l) g - thresholdPairSecondLevel u b j l) := by
  have hn := gaussianPairSectionPoint_reconstruct (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) g
    (thresholdPair_frame_orthogonal u j l hu hv)
  ext i
  have hi := congrFun hn i
  simpa only [gaussianPairBase, SignedSurface.ridgeDisplacement, Pi.add_apply, Pi.smul_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_assoc,
    thresholdPairBisector, thresholdPairDifference] using hi

theorem gaussianPairBase_exactStratum (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (g : Vector r)
    (hstrict : ∀ k, k ≠ j → k ≠ l → faceDot (u k) (gaussianPairBase u b j l g) < b k) :
    projectionEuclideanVector (gaussianPairBase u b j l g) ∈
      SignedSurface.exactStratum (fun k => projectionEuclideanVector (u k)) b {j, l} := by
  have hj := gaussianPairBase_left_level u b j l hu hv hp hm g
  have hl := gaussianPairBase_right_level u b j l hu hv hp hm g
  have hd (k : Fin m) : ⟪projectionEuclideanVector (u k),
      projectionEuclideanVector (gaussianPairBase u b j l g)⟫_ℝ =
      faceDot (u k) (gaussianPairBase u b j l g) := (SignedSurface.faceDot_eq_euclidean_inner _ _).symm
  change (∀ k, ⟪_, _⟫_ℝ ≤ b k) ∧ (∀ k, ⟪_, _⟫_ℝ = b k ↔ k ∈ ({j, l} : Finset (Fin m)))
  simp only [hd, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro k
    by_cases hkj : k = j
    · simpa only [hkj] using hj.le
    by_cases hkl : k = l
    · simpa only [hkl] using hl.le
    exact (hstrict k hkj hkl).le
  · intro k
    constructor
    · intro hk
      by_contra hn
      have hkj : k ≠ j := fun h => hn (Or.inl h)
      have hkl : k ≠ l := fun h => hn (Or.inr h)
      have hh := hstrict k hkj hkl
      linarith
    · rintro (rfl | rfl)
      · exact hj
      · exact hl

theorem gaussianPairEvent_mem_adaptiveOutwardTube (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hv : vectorNormSq (u l) = 1)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    {g : Vector r} (hg : g ∈ gaussianPairEvent u b j l) :
    projectionEuclideanVector g ∈ adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b
      (euclideanThresholdRadius u) {j, l} := by
  have hx := gaussianPairBase_exactStratum u b j l hu hv hp hm g hg.1
  have hmemb := ridgeRectangle_mem_adaptiveOutwardTube (fun k => projectionEuclideanVector (u k))
    b (euclideanThresholdRadius u) (euclideanThresholdRadius_ge_one u) {j, l}
    (j := j) (k := l) (by simp) (by simp) hx
    (thresholdEuclideanNormal_unit _ hu) (thresholdEuclideanNormal_unit _ hv) hp hm hg.2
  rw [← gaussianPairBase_reconstruct u b j l hu hv g] at hmemb
  exact hmemb

theorem gaussianFacetBase_exactStratum (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (g : Vector r)
    (hstrict : ∀ l, l ≠ j → faceDot (u l) (gaussianFacetBase u b j g) < b l) :
    projectionEuclideanVector (gaussianFacetBase u b j g) ∈
      SignedSurface.exactStratum (fun k => projectionEuclideanVector (u k)) b {j} := by
  have hj : faceDot (u j) (gaussianFacetBase u b j g) = b j :=
    SignedSurface.gaussianSectionPoint_on_hyperplane (u j) (b j) hu g
  have hd (k : Fin m) : ⟪projectionEuclideanVector (u k),
      projectionEuclideanVector (gaussianFacetBase u b j g)⟫_ℝ =
      faceDot (u k) (gaussianFacetBase u b j g) := (SignedSurface.faceDot_eq_euclidean_inner _ _).symm
  change (∀ k, ⟪_, _⟫_ℝ ≤ b k) ∧ (∀ k, ⟪_, _⟫_ℝ = b k ↔ k ∈ ({j} : Finset (Fin m)))
  simp only [hd, Finset.mem_singleton]
  constructor
  · intro k
    by_cases hkj : k = j
    · simpa only [hkj] using hj.le
    · exact (hstrict k hkj).le
  · intro k
    constructor
    · intro hk
      by_contra hkj
      have hh := hstrict k hkj
      linarith
    · rintro rfl
      exact hj

theorem gaussianFacetBase_reconstruct (u : Fin m → Vector r) (b : Vector m) (j : Fin m) (g : Vector r) :
    projectionEuclideanVector g = projectionEuclideanVector (gaussianFacetBase u b j g) +
      (faceDot (u j) g - b j) • projectionEuclideanVector (u j) := by
  have he := SignedSurface.gaussianSectionPoint_eq (u j) (b j) g
  ext i
  have hi := congrFun he i
  change g i = SignedSurface.gaussianSectionPoint (u j) (b j) g i + (faceDot (u j) g - b j) * u j i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
  linarith

theorem gaussianFacetEvent_mem_adaptiveOutwardTube (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) {g : Vector r} (hg : g ∈ gaussianFacetEvent u b j) :
    projectionEuclideanVector g ∈ adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b
      (euclideanThresholdRadius u) {j} := by
  let t := faceDot (u j) g - b j
  let c : Fin m → ℝ := fun k => if k = j then t else 0
  have hx := gaussianFacetBase_exactStratum u b j hu g hg.1
  have he : SignedSurface.coneDisplacement (fun k => projectionEuclideanVector (u k)) {j} c =
      t • projectionEuclideanVector (u j) := by simp [SignedSurface.coneDisplacement, c]
  have ht : 0 < t := hg.2.1
  have hnorm := thresholdEuclideanNormal_unit _ hu
  have hn : projectionEuclideanVector (u j) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  refine ⟨projectionEuclideanVector (gaussianFacetBase u b j g), hx, c, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hkj := Finset.mem_singleton.mp hk
    simpa only [c, hkj, if_pos rfl] using ht.le
  · rw [he]
    exact smul_ne_zero ht.ne' hn
  · rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hnorm, mul_one]
    exact hg.2.2
  · rw [he]
    exact gaussianFacetBase_reconstruct u b j g

theorem adaptiveThresholdTube_mem_outerLayer (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (active : Finset (Fin m)) {g : Vector r}
    (hg : projectionEuclideanVector g ∈ adaptiveOutwardTube (fun k => projectionEuclideanVector (u k))
      b (euclideanThresholdRadius u) active) :
    g ∈ thresholdOuterLayer u b (1 / thresholdProjectionRadius u g) := by
  have hh := adaptiveOutwardTube_subset_outerLayer (fun k => projectionEuclideanVector (u k)) b
    (fun j => thresholdEuclideanNormal_unit _ (hu j)) (euclideanThresholdRadius u)
    (euclideanThresholdRadius_ge_one u) (euclideanThresholdRadius_add_le u) active hg
  have hd (k : Fin m) : ⟪projectionEuclideanVector (u k), projectionEuclideanVector g⟫_ℝ =
      faceDot (u k) g := (SignedSurface.faceDot_eq_euclidean_inner _ _).symm
  change (∀ k, ⟪_, _⟫_ℝ ≤ b k + _) ∧ ¬(∀ k, ⟪_, _⟫_ℝ ≤ b k) at hh
  simp only [hd] at hh
  exact hh

theorem gaussianFacetEvent_mem_outerLayer (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (j : Fin m) {g : Vector r}
    (hg : g ∈ gaussianFacetEvent u b j) :
    g ∈ thresholdOuterLayer u b (1 / thresholdProjectionRadius u g) :=
  adaptiveThresholdTube_mem_outerLayer u b hu {j} (gaussianFacetEvent_mem_adaptiveOutwardTube u b j (hu j) hg)

theorem gaussianPairEvent_mem_outerLayer (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (j l : Fin m)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    {g : Vector r} (hg : g ∈ gaussianPairEvent u b j l) :
    g ∈ thresholdOuterLayer u b (1 / thresholdProjectionRadius u g) :=
  adaptiveThresholdTube_mem_outerLayer u b hu {j, l}
    (gaussianPairEvent_mem_adaptiveOutwardTube u b j l (hu j) (hu l) hp hm hg)

theorem gaussianFacetEvent_disjoint (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) {j l : Fin m} (hjl : j ≠ l) :
    Disjoint (gaussianFacetEvent u b j) (gaussianFacetEvent u b l) := by
  rw [Set.disjoint_left]
  intro g hgj hgl
  have hj := gaussianFacetEvent_mem_adaptiveOutwardTube u b j (hu j) hgj
  have hl := gaussianFacetEvent_mem_adaptiveOutwardTube u b l (hu l) hgl
  have hn : ({j} : Finset (Fin m)) ≠ {l} := by simpa only [ne_eq, Finset.singleton_inj] using hjl
  exact Set.disjoint_left.mp (adaptiveOutwardTube_disjoint (fun k => projectionEuclideanVector (u k)) b
    (euclideanThresholdRadius u) hn) hj hl

theorem gaussianPairEvent_disjoint_of_active_ne (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (j l j' l' : Fin m)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (hp' : projectionEuclideanVector (u j') + projectionEuclideanVector (u l') ≠ 0)
    (hm' : projectionEuclideanVector (u j') - projectionEuclideanVector (u l') ≠ 0)
    (hne : ({j, l} : Finset (Fin m)) ≠ {j', l'}) :
    Disjoint (gaussianPairEvent u b j l) (gaussianPairEvent u b j' l') := by
  rw [Set.disjoint_left]
  intro g hg hg'
  exact Set.disjoint_left.mp (adaptiveOutwardTube_disjoint (fun k => projectionEuclideanVector (u k)) b
    (euclideanThresholdRadius u) hne)
    (gaussianPairEvent_mem_adaptiveOutwardTube u b j l (hu j) (hu l) hp hm hg)
    (gaussianPairEvent_mem_adaptiveOutwardTube u b j' l' (hu j') (hu l') hp' hm' hg')

theorem gaussianFacetEvent_pairEvent_disjoint (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (k j l : Fin m) (hjl : j ≠ l)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0) :
    Disjoint (gaussianFacetEvent u b k) (gaussianPairEvent u b j l) := by
  have hne : ({k} : Finset (Fin m)) ≠ {j, l} := by
    intro he
    have hj : j = k := by
      have hh : j ∈ ({k} : Finset (Fin m)) := by rw [he]; simp
      exact Finset.mem_singleton.mp hh
    have hl : l = k := by
      have hh : l ∈ ({k} : Finset (Fin m)) := by rw [he]; simp
      exact Finset.mem_singleton.mp hh
    exact hjl (hj.trans hl.symm)
  rw [Set.disjoint_left]
  intro g hg hg'
  exact Set.disjoint_left.mp (adaptiveOutwardTube_disjoint (fun i => projectionEuclideanVector (u i)) b
    (euclideanThresholdRadius u) hne)
    (gaussianFacetEvent_mem_adaptiveOutwardTube u b k (hu k) hg)
    (gaussianPairEvent_mem_adaptiveOutwardTube u b j l (hu j) (hu l) hp hm hg')

/-- Diagonal pairs represent facets, and off-diagonal pairs represent the
actual ordered ridge events. An unordered active pair has at most two such
representatives. -/
def gaussianThresholdStratumEvent (u : Fin m → Vector r) (b : Vector m) (q : Fin m × Fin m) : Set (Vector r) :=
  if q.1 = q.2 then gaussianFacetEvent u b q.1 else gaussianPairEvent u b q.1 q.2

theorem gaussianThresholdStratumEvent_mem_tube (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (q : Fin m × Fin m) {g : Vector r} (hg : g ∈ gaussianThresholdStratumEvent u b q) :
    projectionEuclideanVector g ∈ adaptiveOutwardTube (fun k => projectionEuclideanVector (u k)) b
      (euclideanThresholdRadius u) {q.1, q.2} := by
  by_cases hq : q.1 = q.2
  · simp only [gaussianThresholdStratumEvent, if_pos hq] at hg
    simpa only [hq, Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using
      gaussianFacetEvent_mem_adaptiveOutwardTube u b q.1 (hu q.1) hg
  · simp only [gaussianThresholdStratumEvent, if_neg hq] at hg
    exact gaussianPairEvent_mem_adaptiveOutwardTube u b q.1 q.2 (hu q.1) (hu q.2)
      (hp _ _ hq) (hm _ _ hq) hg

theorem gaussianThresholdStratumEvent_shared_point (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (q q' : Fin m × Fin m) {g : Vector r}
    (hg : g ∈ gaussianThresholdStratumEvent u b q) (hg' : g ∈ gaussianThresholdStratumEvent u b q') :
    q = q' ∨ q = q'.swap := by
  have hq := gaussianThresholdStratumEvent_mem_tube u b hu hp hm q hg
  have hq' := gaussianThresholdStratumEvent_mem_tube u b hu hp hm q' hg'
  have he : ({q.1, q.2} : Finset (Fin m)) = {q'.1, q'.2} := by
    by_contra hn
    exact Set.disjoint_left.mp (adaptiveOutwardTube_disjoint (fun k => projectionEuclideanVector (u k)) b
      (euclideanThresholdRadius u) hn) hq hq'
  have hs : ({q.1, q.2} : Set (Fin m)) = {q'.1, q'.2} := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      congrArg (fun s : Finset (Fin m) => (s : Set (Fin m))) he
  rcases Set.pair_eq_pair_iff.mp hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl (Prod.ext h₁ h₂)
  · exact Or.inr (Prod.ext h₁ h₂)

/-- The actual finite incidence bound: all facets plus ordered pair-ridges
contribute at most twice the adaptive outer-layer indicator at every point.
The constant two only counts the two orders of a pair, never the faces. -/
theorem gaussianThresholdStratumEvent_indicator_sum_le (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (g : Vector r) :
    (∑ q : Fin m × Fin m, (gaussianThresholdStratumEvent u b q).indicator (fun _ => (1 : ℝ)) g) ≤
      2 * (thresholdOuterLayer u b (1 / thresholdProjectionRadius u g)).indicator (fun _ => (1 : ℝ)) g := by
  by_cases hex : ∃ q, g ∈ gaussianThresholdStratumEvent u b q
  · obtain ⟨q₀, hq₀⟩ := hex
    have houter := adaptiveThresholdTube_mem_outerLayer u b hu {q₀.1, q₀.2}
      (gaussianThresholdStratumEvent_mem_tube u b hu hp hm q₀ hq₀)
    rw [Set.indicator_of_mem houter, mul_one]
    have hpoint (q : Fin m × Fin m) :
        (gaussianThresholdStratumEvent u b q).indicator (fun _ => (1 : ℝ)) g ≤
          (if q = q₀ then 1 else 0) + (if q = q₀.swap then 1 else 0) := by
      by_cases hq : g ∈ gaussianThresholdStratumEvent u b q
      · rw [Set.indicator_of_mem hq]
        rcases gaussianThresholdStratumEvent_shared_point u b hu hp hm q q₀ hq hq₀ with h | h
        · subst q
          simp
          split_ifs <;> norm_num
        · subst q
          simp
          split_ifs <;> norm_num
      · rw [Set.indicator_of_not_mem hq]
        split_ifs <;> norm_num
    calc
      _ ≤ ∑ q : Fin m × Fin m, ((if q = q₀ then (1 : ℝ) else 0) +
          (if q = q₀.swap then 1 else 0)) := Finset.sum_le_sum (fun q _ => hpoint q)
      _ = 2 := by norm_num [Finset.sum_add_distrib]
  · have hn (q : Fin m × Fin m) : g ∉ gaussianThresholdStratumEvent u b q := fun h => hex ⟨q, h⟩
    simp only [Set.indicator_of_not_mem (hn _), Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (Set.indicator_nonneg (fun _ _ => by norm_num) g)

theorem gaussianThresholdStratumEvent_indicator_sum_eq (u : Fin m → Vector r) (b : Vector m)
    (P : Vector r → ℝ) (g : Vector r) :
    (∑ q : Fin m × Fin m, (gaussianThresholdStratumEvent u b q).indicator P g) =
      (∑ j, (gaussianFacetEvent u b j).indicator P g) +
        ∑ j, ∑ l, if j = l then 0 else (gaussianPairEvent u b j l).indicator P g := by
  rw [Fintype.sum_prod_type]
  have hrow (j : Fin m) : (∑ l, (gaussianThresholdStratumEvent u b (j, l)).indicator P g) =
      (gaussianFacetEvent u b j).indicator P g +
        ∑ l, if j = l then 0 else (gaussianPairEvent u b j l).indicator P g := by
    calc
      _ = ∑ l, ((if j = l then (gaussianFacetEvent u b j).indicator P g else 0) +
          (if j = l then 0 else (gaussianPairEvent u b j l).indicator P g)) := by
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : j = l <;> simp [gaussianThresholdStratumEvent, h]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [eq_comm]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]

theorem gaussianThreshold_facet_pair_indicator_sum_le (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (g : Vector r) :
    (∑ j, (gaussianFacetEvent u b j).indicator (fun _ => (1 : ℝ)) g) +
      (∑ j, ∑ l, if j = l then 0 else (gaussianPairEvent u b j l).indicator (fun _ => (1 : ℝ)) g) ≤
      2 * (thresholdOuterLayer u b (1 / thresholdProjectionRadius u g)).indicator (fun _ => (1 : ℝ)) g := by
  rw [← gaussianThresholdStratumEvent_indicator_sum_eq]
  exact gaussianThresholdStratumEvent_indicator_sum_le u b hu hp hm g

theorem gaussianThreshold_facet_pair_weighted_sum_le (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1)
    (hp : ∀ j l, j ≠ l → projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : ∀ j l, j ≠ l → projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (P : Vector r → ℝ) (hP : ∀ g, 0 ≤ P g) (g : Vector r) :
    (∑ j, (gaussianFacetEvent u b j).indicator P g) +
      (∑ j, ∑ l, if j = l then 0 else (gaussianPairEvent u b j l).indicator P g) ≤
      2 * (thresholdOuterLayer u b (1 / thresholdProjectionRadius u g)).indicator P g := by
  have he (S : Set (Vector r)) : S.indicator P g = P g * S.indicator (fun _ => (1 : ℝ)) g := by
    by_cases hg : g ∈ S <;> simp [hg]
  rw [← gaussianThresholdStratumEvent_indicator_sum_eq]
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (gaussianThresholdStratumEvent_indicator_sum_le u b hu hp hm g) (hP g)
  convert hh using 1 <;> ring

end

end RectangleCLT.Companion.SplitV4
