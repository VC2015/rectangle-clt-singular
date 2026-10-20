import RectangleCLT.GaussianFourthBound
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Actual Gaussian integration by parts with quadratic polynomial weights,
as required by the repeated-coordinate fourth derivatives. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem standardGaussian_integrable_faceDot_triple {p : ℕ} (u v w : Vector p) :
    Integrable (fun z => faceDot u z * (faceDot v z * faceDot w z))
      (standardGaussian p) := by
  let a : Fin 3 → Vector p := ![u, v, w]
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      MemLp (faceDot (a i)) (3 : ENNReal) (standardGaussian p) := by
    intro i _
    simpa using standardGaussian_memLp_faceDot (a i) 3
  have hh := MemLp.prod' (p := fun _ : Fin 3 => (3 : ENNReal)) hm
  have he : ((∑ _i : Fin 3, (3 : ENNReal)⁻¹)⁻¹) = 1 := by
    norm_num [Fin.sum_univ_succ]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [he] at hh
  have hi := memLp_one_iff_integrable.mp hh
  simpa [a, Fin.prod_univ_succ, mul_assoc] using hi

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem integrable_bilinear_softFaceDirectional_gaussian (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x y v w : Vector p) :
    Integrable (fun z => faceDot v z * faceDot w z * s.softFaceDirectional S y (A.mulVec z + x))
      (standardGaussian p) := by
  simpa only [mul_comm] using
    (standardGaussian_integrable_faceDot_product v w).bdd_mul
      (s.integrable_softFaceDirectional_gaussian A S x y).aestronglyMeasurable
      ⟨((∑ f ∈ S, |normalDot f y|) + ((S.card : ℝ) + 1) * ‖y‖) / s.bandwidth,
        fun z => s.abs_softFaceDirectional_le S y (A.mulVec z + x)⟩

theorem integrable_trilinear_softFaceWeight_gaussian (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x u v w : Vector p) :
    Integrable (fun z => (faceDot u z * (faceDot v z * faceDot w z)) *
      s.softFaceWeight S (A.mulVec z + x)) (standardGaussian p) := by
  simpa only [mul_comm] using
    (standardGaussian_integrable_faceDot_triple u v w).bdd_mul
      (s.integrable_softFaceWeight_gaussian A S x).aestronglyMeasurable
      ⟨1, fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
          s.softFaceWeight_le_one S (A.mulVec z + x)⟩

/-- Gaussian Stein for a soft face with two linear weights. Both derivative
corrections are exact, and all cubic Gaussian integrability is proved above. -/
theorem softFaceWeight_gaussian_quadratic_weighted_stein
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (x u v w : Vector p) :
    (∫ z, faceDot u z * (faceDot v z * (faceDot w z *
      s.softFaceWeight S (A.mulVec z + x))) ∂standardGaussian p) =
      faceDot u v * (∫ z, faceDot w z * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) +
      faceDot u w * (∫ z, faceDot v z * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) +
      (∫ z, faceDot v z * (faceDot w z *
        s.softFaceDirectional S (A.mulVec u) (A.mulVec z + x)) ∂standardGaussian p) := by
  let P : Vector p → ℝ := fun z => s.softFaceWeight S (A.mulVec z + x)
  let D : Fin p → Vector p → ℝ :=
    fun j z => s.softFaceDirectional S (fun k => A k j) (A.mulVec z + x)
  have hP := s.integrable_softFaceWeight_gaussian A S x
  have hD (j : Fin p) := s.integrable_softFaceDirectional_gaussian A S x (fun k => A k j)
  have hbP : ∃ C : ℝ, ∀ z, ‖P z‖ ≤ C := ⟨1, fun z => by
    simpa only [P, Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
      s.softFaceWeight_le_one S (A.mulVec z + x)⟩
  have hg : Integrable (fun z => faceDot v z * (faceDot w z * P z))
      (standardGaussian p) := by
    simpa only [P, mul_assoc] using s.integrable_bilinear_softFaceWeight_gaussian A S x v w
  have hxg (j : Fin p) : Integrable
      (fun z => z j * (faceDot v z * (faceDot w z * P z))) (standardGaussian p) := by
    have hi := (standardGaussian_integrable_faceDot_triple (localBasisVector j) v w).bdd_mul
      hP.aestronglyMeasurable hbP
    have heq : faceDot (localBasisVector j) = (fun z : Vector p => z j) := by
      funext z
      simp [faceDot, localBasisVector]
    simp_rw [heq] at hi
    simpa only [P, mul_comm, mul_left_comm, mul_assoc] using hi
  have hgrad (j : Fin p) : Integrable (fun z =>
      v j * faceDot w z * P z + w j * faceDot v z * P z +
        faceDot v z * faceDot w z * D j z) (standardGaussian p) := by
    have hi := ((s.integrable_linear_softFaceWeight_gaussian A S x w).const_mul (v j)).add
      ((s.integrable_linear_softFaceWeight_gaussian A S x v).const_mul (w j))
    have hj := s.integrable_bilinear_softFaceDirectional_gaussian A S x (fun k => A k j) v w
    simpa only [D, P, mul_assoc] using hi.add hj
  have hs := standardGaussian_directional_stein_of_integrable u
    (g := fun z => faceDot v z * (faceDot w z * P z))
    (g' := fun j z => v j * faceDot w z * P z + w j * faceDot v z * P z +
      faceDot v z * faceDot w z * D j z)
    (fun j z => by
      convert (hasDerivAt_faceDot_update v z j).mul
        ((hasDerivAt_faceDot_update w z j).mul
          (s.hasDerivAt_softFaceWeight_gaussian_slice A S x z j)) using 1
      simp only [P, D, Function.update_eq_self]
      ring) hg hgrad hxg
  have hpoint (z : Vector p) :
      (∑ j, u j * (v j * faceDot w z * P z + w j * faceDot v z * P z +
        faceDot v z * faceDot w z * D j z)) =
      faceDot u v * (faceDot w z * P z) + faceDot u w * (faceDot v z * P z) +
        faceDot v z * (faceDot w z *
          s.softFaceDirectional S (A.mulVec u) (A.mulVec z + x)) := by
    calc
      _ = (∑ j, u j * v j) * (faceDot w z * P z) +
          (∑ j, u j * w j) * (faceDot v z * P z) +
          faceDot v z * faceDot w z * (∑ j, u j * D j z) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
        congr 1
        · congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
        · apply Finset.sum_congr rfl
          intro j _
          ring
      _ = _ := by
        simp only [D, ← s.softFaceDirectional_mulVec]
        change faceDot u v * (faceDot w z * P z) + faceDot u w * (faceDot v z * P z) + _ = _
        ring
  rw [hs]
  simp_rw [hpoint]
  rw [integral_add]
  · rw [integral_add]
    · simp only [P, integral_const_mul]
    · exact (s.integrable_linear_softFaceWeight_gaussian A S x w).const_mul _
    · exact (s.integrable_linear_softFaceWeight_gaussian A S x v).const_mul _
  · exact ((s.integrable_linear_softFaceWeight_gaussian A S x w).const_mul _).add
      ((s.integrable_linear_softFaceWeight_gaussian A S x v).const_mul _)
  · simpa only [mul_assoc] using
      s.integrable_bilinear_softFaceDirectional_gaussian A S x (A.mulVec u) v w

/-- Exact active-coordinate recursion with two Gaussian linear weights.
This is the third Hermite step used by the all-equal fourth derivative. -/
theorem softFaceDirectional_gaussian_quadratic_active_coordinate
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u v w : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    (∫ z, faceDot v z * (faceDot w z *
      s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x)) ∂standardGaussian p) =
      (∫ z, faceDot u z * (faceDot v z * (faceDot w z *
        s.softFaceWeight S (A.mulVec z + x))) ∂standardGaussian p) -
      faceDot u v * (∫ z, faceDot w z * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) -
      faceDot u w * (∫ z, faceDot v z * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
          (∫ z, faceDot v z * (faceDot w z *
            s.softFaceWeight (insert f S) (A.mulVec z + x)) ∂standardGaussian p) := by
  have hpoint (z : Vector p) :
      faceDot v z * (faceDot w z *
        s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x)) =
      faceDot v z * (faceDot w z *
        s.softFaceDirectional S (A.mulVec u) (A.mulVec z + x)) +
        ((S.card : ℝ) + 1) / s.bandwidth *
          ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
            (faceDot v z * (faceDot w z *
              s.softFaceWeight (insert f S) (A.mulVec z + x))) := by
    rw [s.softFaceDirectional_active_coordinate S j hj (A.mulVec u) (A.mulVec z + x) hu]
    simp only [mul_add, Finset.mul_sum]
    ring
  have hint (f : Face p) : Integrable (fun z => faceDot v z * (faceDot w z *
      s.softFaceWeight (insert f S) (A.mulVec z + x))) (standardGaussian p) := by
    simpa only [mul_assoc] using s.integrable_bilinear_softFaceWeight_gaussian A (insert f S) x v w
  have hdir : Integrable (fun z => faceDot v z * (faceDot w z *
      s.softFaceDirectional S (A.mulVec u) (A.mulVec z + x))) (standardGaussian p) := by
    simpa only [mul_assoc] using s.integrable_bilinear_softFaceDirectional_gaussian A S x (A.mulVec u) v w
  simp_rw [hpoint]
  rw [integral_add hdir]
  · rw [integral_const_mul, integral_finset_sum]
    · simp_rw [integral_const_mul]
      have hs := s.softFaceWeight_gaussian_quadratic_weighted_stein A S x u v w
      linarith
    · intro f _
      exact (hint f).const_mul _
  · exact (integrable_finset_sum _ (fun f _ => (hint f).const_mul _)).const_mul _

theorem hasDerivAt_integral_softFaceDirectional_mixed_coordinate
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (x : Vector p)
    (j k : Fin p) (W : Vector p → ℝ) (hW : Integrable W (standardGaussian p)) :
    HasDerivAt (fun t => ∫ z, W z * s.softFaceDirectional S (coordinateDirection j)
      (A.mulVec z + line x (coordinateDirection k) t) ∂standardGaussian p)
      (∫ z, W z * s.softFaceMixedSecond S j k (A.mulVec z + x) ∂standardGaussian p) 0 := by
  obtain ⟨C, hC⟩ := s.softFaceMixedSecond_bounded S j k
  apply hasDerivAt_weighted_gaussian_shift_integral A x (coordinateDirection k) W
    (s.softFaceDirectional S (coordinateDirection j)) (s.softFaceMixedSecond S j k)
    hW (s.continuous_softFaceDirectional S (coordinateDirection j)).measurable
    (s.continuous_softFaceMixedSecond S j k).measurable
    (((∑ f ∈ S, |normalDot f (coordinateDirection j)|) +
      ((S.card : ℝ) + 1) * ‖coordinateDirection j‖) / s.bandwidth) C
  · intro u
    exact s.abs_softFaceDirectional_le S (coordinateDirection j) u
  · exact hC
  · exact s.hasDerivAt_softFaceMixedSecond S j k

theorem hasDerivAt_integral_softFaceCoordinateSecond_coordinate
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (x : Vector p)
    (j : Fin p) (W : Vector p → ℝ) (hW : Integrable W (standardGaussian p)) :
    HasDerivAt (fun t => ∫ z, W z * s.softFaceCoordinateSecond S j
      (A.mulVec z + line x (coordinateDirection j) t) ∂standardGaussian p)
      (∫ z, W z * s.softFaceCoordinateThird S j (A.mulVec z + x) ∂standardGaussian p) 0 := by
  obtain ⟨C, hC⟩ := s.softFaceCoordinateThird_bounded S j
  apply hasDerivAt_weighted_gaussian_shift_integral A x (coordinateDirection j) W
    (s.softFaceCoordinateSecond S j) (s.softFaceCoordinateThird S j)
    hW (s.continuous_softFaceCoordinateSecond S j).measurable
    (s.continuous_softFaceCoordinateThird S j).measurable
    (((|(∑ f ∈ S, normalDot f (coordinateDirection j))| + ((S.card : ℝ) + 1)) ^ 2 +
      2 * ((S.card : ℝ) + 1)) / s.bandwidth ^ 2) C
  · intro u
    exact s.abs_softFaceCoordinateSecond_le S j u
  · exact hC
  · exact s.hasDerivAt_softFaceCoordinateThird S j

theorem softFaceMixedSecond_gaussian_active_coordinate
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j k : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    (∫ z, s.softFaceMixedSecond S j k (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot u z * s.softFaceDirectional S (coordinateDirection k)
        (A.mulVec z + x) ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
          (∫ z, s.softFaceDirectional (insert f S) (coordinateDirection k)
            (A.mulVec z + x) ∂standardGaussian p) := by
  have hleft := s.hasDerivAt_integral_softFaceDirectional_mixed_coordinate A S x j k
    (fun _ => 1) (integrable_const 1)
  simp only [one_mul] at hleft
  have hright₁ := s.hasDerivAt_integral_softFaceWeight_line A S x (coordinateDirection k)
    (faceDot u) (standardGaussian_integrable_faceDot u)
  have hright₂ := HasDerivAt.sum (u := inactiveCoordinateFaces S) (fun f _ =>
    (s.hasDerivAt_integral_softFaceWeight_line A (insert f S) x (coordinateDirection k)
      (fun _ => 1) (integrable_const 1)).const_mul (normalDot f (A.mulVec u)))
  simp only [one_mul] at hright₂
  have hright := hright₁.add (hright₂.const_mul (((S.card : ℝ) + 1) / s.bandwidth))
  have hright' := hright.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t =>
      (s.softFaceDirectional_gaussian_active_coordinate A S j hj
        (line x (coordinateDirection k) t) u hu)))
  exact hleft.unique hright'

theorem softFaceCoordinateSecond_gaussian_linear_weighted_recursion
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u v : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    (∫ z, faceDot v z * s.softFaceCoordinateSecond S j (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot u z * (faceDot v z *
        s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x)) ∂standardGaussian p) -
      faceDot u v * (∫ z, s.softFaceDirectional S (coordinateDirection j)
        (A.mulVec z + x) ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
          (∫ z, faceDot v z * s.softFaceDirectional (insert f S) (coordinateDirection j)
            (A.mulVec z + x) ∂standardGaussian p) := by
  have hleft := s.hasDerivAt_integral_softFaceDirectional_coordinate A S x j
    (faceDot v) (standardGaussian_integrable_faceDot v)
  have hright₁ := s.hasDerivAt_integral_softFaceWeight_line A S x (coordinateDirection j)
    (fun z => faceDot u z * faceDot v z) (standardGaussian_integrable_faceDot_product u v)
  have hright₂ := (s.hasDerivAt_integral_softFaceWeight_line A S x (coordinateDirection j)
    (fun _ => 1) (integrable_const 1)).const_mul (faceDot u v)
  have hright₃ := HasDerivAt.sum (u := inactiveCoordinateFaces S) (fun f _ =>
    (s.hasDerivAt_integral_softFaceWeight_line A (insert f S) x (coordinateDirection j)
      (faceDot v) (standardGaussian_integrable_faceDot v)).const_mul (normalDot f (A.mulVec u)))
  simp only [one_mul] at hright₂
  have hright := (hright₁.sub hright₂).add
    (hright₃.const_mul (((S.card : ℝ) + 1) / s.bandwidth))
  have hright' := hright.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun t => by
    simpa only [mul_assoc] using
      (s.softFaceDirectional_gaussian_weighted_active_coordinate A S j hj
        (line x (coordinateDirection j) t) u v hu)))
  simpa only [mul_assoc] using hleft.unique hright'

theorem softFaceCoordinateThird_gaussian_active_coordinate
    (A : Matrix (Fin p) (Fin p) ℝ) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) (x u : Vector p)
    (hu : ∀ f ∈ S, A.mulVec u f.1 = coordinateDirection j f.1) :
    (∫ z, s.softFaceCoordinateThird S j (A.mulVec z + x) ∂standardGaussian p) =
      (∫ z, faceDot u z * s.softFaceCoordinateSecond S j (A.mulVec z + x) ∂standardGaussian p) +
      ((S.card : ℝ) + 1) / s.bandwidth *
        ∑ f ∈ inactiveCoordinateFaces S, normalDot f (A.mulVec u) *
          (∫ z, s.softFaceCoordinateSecond (insert f S) j (A.mulVec z + x)
            ∂standardGaussian p) := by
  have hleft := s.hasDerivAt_integral_softFaceCoordinateSecond_coordinate A S x j
    (fun _ => 1) (integrable_const 1)
  simp only [one_mul] at hleft
  have hright₁ := s.hasDerivAt_integral_softFaceDirectional_coordinate A S x j
    (faceDot u) (standardGaussian_integrable_faceDot u)
  have hright₂ := HasDerivAt.sum (u := inactiveCoordinateFaces S) (fun f _ =>
    (s.hasDerivAt_integral_softFaceDirectional_coordinate A (insert f S) x j
      (fun _ => 1) (integrable_const 1)).const_mul (normalDot f (A.mulVec u)))
  simp only [one_mul] at hright₂
  have hright := hright₁.add (hright₂.const_mul (((S.card : ℝ) + 1) / s.bandwidth))
  have hright' := hright.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t =>
      (s.softFaceCoordinateSecond_gaussian_active_coordinate A S j hj
        (line x (coordinateDirection j) t) u hu)))
  exact hleft.unique hright'

end FaceSmoother

end
end RectangleCLT
