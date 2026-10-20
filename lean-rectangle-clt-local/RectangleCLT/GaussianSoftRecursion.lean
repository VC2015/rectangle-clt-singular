import RectangleCLT.GaussianTriple

/-! Exact sparse dual-normal recursions for the actual smooth face kernels.
Opposite faces of every active coordinate are excluded together. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def inactiveCoordinateFaces {p : ℕ} (S : Finset (Face p)) : Finset (Face p) := by
  classical
  exact Finset.univ.filter (fun f => f.1 ∉ S.image Prod.fst)

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- Replace an active coordinate derivative by a direction agreeing on all
active coordinates. The correction involves only newly activated coordinates,
so the two opposite faces of one coordinate never appear together. -/
theorem softFaceDirectional_active_coordinate (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (y x : Vector p)
    (hy : ∀ f ∈ S, y f.1 = coordinateDirection j f.1) :
    s.softFaceDirectional S (coordinateDirection j) x =
      s.softFaceDirectional S y x + ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S,
          normalDot f y * s.softFaceWeight (insert f S) x := by
  classical
  have hinactive (f : Face p) (hf : f ∈ inactiveCoordinateFaces S) :
      normalDot f (coordinateDirection j) = 0 := by
    have hfj : f.1 ≠ j := by
      intro h
      exact (Finset.mem_filter.mp hf).2 (h ▸ hj)
    cases hb : f.2 <;> simp [normalDot, hb, coordinateDirection, hfj]
  have hactive (f : Face p) (hf : f ∉ inactiveCoordinateFaces S) :
      normalDot f y = normalDot f (coordinateDirection j) := by
    have hcoord : f.1 ∈ S.image Prod.fst := by
      by_contra h
      exact hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    obtain ⟨g, hg, hgf⟩ := Finset.mem_image.mp hcoord
    have hh := hy g hg
    rw [hgf] at hh
    cases hb : f.2 <;> simp [normalDot, hb, hh]
  have hmean : (s.weights x).directionalMean y =
      (s.weights x).directionalMean (coordinateDirection j) +
        ∑ f ∈ inactiveCoordinateFaces S, (s.weights x).pi f * normalDot f y := by
    change (∑ f, (s.weights x).pi f * normalDot f y) =
      (∑ f, (s.weights x).pi f * normalDot f (coordinateDirection j)) + _
    simp only [inactiveCoordinateFaces, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : f.1 ∉ S.image Prod.fst
    · have hfi : f ∈ inactiveCoordinateFaces S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩
      simp only [if_pos hf, hinactive f hfi, mul_zero, zero_add]
    · have hfi : f ∉ inactiveCoordinateFaces S := by simpa only [inactiveCoordinateFaces,
        Finset.mem_filter, Finset.mem_univ, true_and] using hf
      simp only [if_neg hf, add_zero, hactive f hfi]
  have hsum : (∑ f ∈ S, normalDot f y) =
      ∑ f ∈ S, normalDot f (coordinateDirection j) := by
    apply Finset.sum_congr rfl
    intro f hf
    cases hb : f.2 <;> simp [normalDot, hb, hy f hf]
  have hcorrection : (∑ f ∈ inactiveCoordinateFaces S,
      normalDot f y * s.softFaceWeight (insert f S) x) =
      s.softFaceWeight S x *
        ∑ f ∈ inactiveCoordinateFaces S, (s.weights x).pi f * normalDot f y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    have hfS : f ∉ S := by
      intro h
      exact (Finset.mem_filter.mp hf).2 (Finset.mem_image_of_mem Prod.fst h)
    rw [s.softFaceWeight_insert S x f hfS]
    ring
  rw [hcorrection]
  unfold softFaceDirectional
  rw [hmean, hsum]
  ring

theorem integrable_softFaceWeight_gaussian (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x : Vector p) :
    Integrable (fun z => s.softFaceWeight S (A.mulVec z + x)) (standardGaussian p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((s.continuous_softFaceWeight S).comp
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
      s.softFaceWeight_le_one S (A.mulVec z + x))

theorem integrable_softFaceDirectional_gaussian (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x y : Vector p) :
    Integrable (fun z => s.softFaceDirectional S y (A.mulVec z + x)) (standardGaussian p) := by
  apply (integrable_const (((∑ f ∈ S, |normalDot f y|) + ((S.card : ℝ) + 1) * ‖y‖) /
    s.bandwidth)).mono'
    (((s.continuous_softFaceDirectional S y).comp
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using s.abs_softFaceDirectional_le S y (A.mulVec z + x))

theorem integrable_linear_softFaceWeight_gaussian (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x v : Vector p) :
    Integrable (fun z => faceDot v z * s.softFaceWeight S (A.mulVec z + x))
      (standardGaussian p) := by
  simpa only [mul_comm] using
    (standardGaussian_integrable_faceDot v).bdd_mul
      (s.integrable_softFaceWeight_gaussian A S x).aestronglyMeasurable
      ⟨1, fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
          s.softFaceWeight_le_one S (A.mulVec z + x)⟩

theorem integrable_linear_softFaceDirectional_gaussian (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x y v : Vector p) :
    Integrable (fun z => faceDot v z * s.softFaceDirectional S y (A.mulVec z + x))
      (standardGaussian p) := by
  simpa only [mul_comm] using
    (standardGaussian_integrable_faceDot v).bdd_mul
      (s.integrable_softFaceDirectional_gaussian A S x y).aestronglyMeasurable
      ⟨((∑ f ∈ S, |normalDot f y|) + ((S.card : ℝ) + 1) * ‖y‖) / s.bandwidth,
        fun z => s.abs_softFaceDirectional_le S y (A.mulVec z + x)⟩

theorem integrable_bilinear_softFaceWeight_gaussian (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x u v : Vector p) :
    Integrable (fun z => faceDot u z * faceDot v z * s.softFaceWeight S (A.mulVec z + x))
      (standardGaussian p) := by
  simpa only [mul_comm] using
    (standardGaussian_integrable_faceDot_product u v).bdd_mul
      (s.integrable_softFaceWeight_gaussian A S x).aestronglyMeasurable
      ⟨1, fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
          s.softFaceWeight_le_one S (A.mulVec z + x)⟩

/-- Exact integrated active-coordinate recursion; Gaussian integration by
parts is proved for the actual concrete product law. -/
theorem softFaceDirectional_gaussian_active_coordinate (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (j : Fin p) (hj : j ∈ S.image Prod.fst) (x u : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    (∫ z, s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x)
      ∂standardGaussian p) =
      (∫ z, faceDot u z * s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) +
        ((S.card : ℝ) + 1) / s.bandwidth *
          ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
            (∫ z, s.softFaceWeight (insert f S) (A.mulVec z + x) ∂standardGaussian p) := by
  have hpoint (z : Vector p) := s.softFaceDirectional_active_coordinate S j hj
    (A.mulVec u) (A.mulVec z + x) hu
  simp_rw [hpoint]
  rw [integral_add (s.integrable_softFaceDirectional_gaussian A S x (A.mulVec u))]
  · rw [integral_const_mul, integral_finset_sum]
    · simp_rw [integral_const_mul]
      rw [← s.softFaceWeight_gaussian_directional_stein A S x u]
    · intro f _
      exact (s.integrable_softFaceWeight_gaussian A (insert f S) x).const_mul _
  · apply Integrable.const_mul
    exact integrable_finset_sum _ (fun f _ =>
      (s.integrable_softFaceWeight_gaussian A (insert f S) x).const_mul _)

/-- The same recursion with a linear Gaussian weight. The correction
`u·v` is exact; it is obtained by differentiating that linear weight in the
proved Gaussian Stein formula. -/
theorem softFaceDirectional_gaussian_weighted_active_coordinate
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u v : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    (∫ z, faceDot v z * s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x)
      ∂standardGaussian p) =
      (∫ z, faceDot u z * (faceDot v z * s.softFaceWeight S (A.mulVec z + x))
        ∂standardGaussian p) -
      faceDot u v * (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) +
        ((S.card : ℝ) + 1) / s.bandwidth *
          ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
            (∫ z, faceDot v z * s.softFaceWeight (insert f S) (A.mulVec z + x)
              ∂standardGaussian p) := by
  have hpoint (z : Vector p) :
      faceDot v z * s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x) =
      faceDot v z * s.softFaceDirectional S (A.mulVec u) (A.mulVec z + x) +
        ((S.card : ℝ) + 1) / s.bandwidth *
          ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
            (faceDot v z * s.softFaceWeight (insert f S) (A.mulVec z + x)) := by
    rw [s.softFaceDirectional_active_coordinate S j hj (A.mulVec u) (A.mulVec z + x) hu]
    simp only [mul_add, Finset.mul_sum]
    ring
  simp_rw [hpoint]
  rw [integral_add (s.integrable_linear_softFaceDirectional_gaussian A S x (A.mulVec u) v)]
  · rw [integral_const_mul, integral_finset_sum]
    · simp_rw [integral_const_mul]
      have hs := s.softFaceWeight_gaussian_weighted_stein A S x u v
      linarith
    · intro f _
      exact (s.integrable_linear_softFaceWeight_gaussian A (insert f S) x v).const_mul _
  · apply Integrable.const_mul
    exact integrable_finset_sum _ (fun f _ =>
      (s.integrable_linear_softFaceWeight_gaussian A (insert f S) x v).const_mul _)

end FaceSmoother

open FaceSmoother

theorem faceDot_signedRowNormal_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Face p) (u : Vector p) :
    faceDot (signedRowNormal A f) u = normalDot f (A.mulVec u) := by
  cases hb : f.2 <;>
    simp [faceDot, signedRowNormal, faceSign, normalDot, hb, Matrix.mulVec, dotProduct,
      Finset.sum_neg_distrib]

namespace CompatibleFaceTuple

variable {p q : ℕ} (S : CompatibleFaceTuple p q)

def activeFaceSet : Finset (Face p) := by
  classical
  exact Finset.univ.image S.face

/-- A coordinate dual direction constructed using only the active Gram
matrix. Full covariance invertibility is unnecessary. -/
def coordinateDual (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) : Vector p :=
  S.regressionMean A (fun i => normalDot (S.face i) (FaceSmoother.coordinateDirection j))

theorem coordinateDual_agrees (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) (j : Fin p) (i : Fin q) :
    A.mulVec (S.coordinateDual A j) (S.face i).1 =
      FaceSmoother.coordinateDirection j (S.face i).1 := by
  have h := congrFun (S.activeScores_regressionMean A hd
    (fun i => normalDot (S.face i) (FaceSmoother.coordinateDirection j))) i
  change faceDot (signedRowNormal A (S.face i)) (S.coordinateDual A j) = _ at h
  rw [faceDot_signedRowNormal_eq] at h
  cases hb : (S.face i).2 <;> simpa [normalDot, hb] using h

theorem coordinateDual_agrees_on_activeFaceSet (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) (j : Fin p) :
    ∀ f ∈ S.activeFaceSet, A.mulVec (S.coordinateDual A j) f.1 =
      FaceSmoother.coordinateDirection j f.1 := by
  classical
  intro f hf
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
  exact S.coordinateDual_agrees A hd j i

theorem coordinate_mem_activeFaceSet (i : Fin q) :
    (S.face i).1 ∈ S.activeFaceSet.image Prod.fst := by
  classical
  exact Finset.mem_image_of_mem Prod.fst (Finset.mem_image_of_mem S.face (Finset.mem_univ i))

theorem softFace_gaussian_coordinate_recursion (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (S.gram (A * A.transpose)).det)
    (i : Fin q) (x : Vector p) :
    (∫ z, s.softFaceDirectional S.activeFaceSet
      (FaceSmoother.coordinateDirection (S.face i).1) (A.mulVec z + x)
      ∂standardGaussian p) =
      (∫ z, faceDot (S.coordinateDual A (S.face i).1) z *
        s.softFaceWeight S.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) +
      ((S.activeFaceSet.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S.activeFaceSet,
          normalDot f (A.mulVec (S.coordinateDual A (S.face i).1)) *
          (∫ z, s.softFaceWeight (insert f S.activeFaceSet) (A.mulVec z + x)
            ∂standardGaussian p) :=
  s.softFaceDirectional_gaussian_active_coordinate A S.activeFaceSet (S.face i).1
    (S.coordinate_mem_activeFaceSet i) x (S.coordinateDual A (S.face i).1)
    (S.coordinateDual_agrees_on_activeFaceSet A hd (S.face i).1)

theorem softFace_gaussian_weighted_coordinate_recursion (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (S.gram (A * A.transpose)).det)
    (i : Fin q) (x v : Vector p) :
    (∫ z, faceDot v z * s.softFaceDirectional S.activeFaceSet
      (FaceSmoother.coordinateDirection (S.face i).1) (A.mulVec z + x)
      ∂standardGaussian p) =
      (∫ z, faceDot (S.coordinateDual A (S.face i).1) z *
        (faceDot v z * s.softFaceWeight S.activeFaceSet (A.mulVec z + x))
        ∂standardGaussian p) -
      faceDot (S.coordinateDual A (S.face i).1) v *
        (∫ z, s.softFaceWeight S.activeFaceSet (A.mulVec z + x) ∂standardGaussian p) +
      ((S.activeFaceSet.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S.activeFaceSet,
          normalDot f (A.mulVec (S.coordinateDual A (S.face i).1)) *
          (∫ z, faceDot v z * s.softFaceWeight (insert f S.activeFaceSet) (A.mulVec z + x)
            ∂standardGaussian p) :=
  s.softFaceDirectional_gaussian_weighted_active_coordinate A S.activeFaceSet (S.face i).1
    (S.coordinate_mem_activeFaceSet i) x (S.coordinateDual A (S.face i).1) v
    (S.coordinateDual_agrees_on_activeFaceSet A hd (S.face i).1)

end CompatibleFaceTuple
end
end RectangleCLT
