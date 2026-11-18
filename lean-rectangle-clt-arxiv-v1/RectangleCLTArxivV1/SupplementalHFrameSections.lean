import RectangleCLTArxivV1.SupplementalHSectionTrace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual affine Gaussian section points and normal densities are
independent of the orthonormal frame of their normal space. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def gaussianFrameProjection {q : ℕ} (v : Fin q → E) (g : E) : E :=
  ∑ i, ⟪v i,g⟫_ℝ • v i

def gaussianFrameSectionPoint {q : ℕ} (v : Fin q → E) (a : Fin q → ℝ) (g : E) : E :=
  (∑ i, a i • v i)+g-gaussianFrameProjection v g

/-- The finite orthonormal-coordinate projection is the actual
orthogonal projection onto the generated normal space. -/
theorem gaussianFrameProjection_eq_orthogonalProjection {q : ℕ}
    (v : Fin q → E) (hv : Orthonormal ℝ v) (g : E) :
    gaussianFrameProjection v g=
      (Submodule.span ℝ (Set.range v)).orthogonalProjection g := by
  let S := Submodule.span ℝ (Set.range v)
  have hm : gaussianFrameProjection v g∈S := by
    apply S.sum_mem
    intro i _
    exact S.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
  let ℓ : E →ₗ[ℝ] ℝ := (innerSL ℝ (g-gaussianFrameProjection v g)).toLinearMap
  have hker : S≤LinearMap.ker ℓ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change ⟪g-gaussianFrameProjection v g,v i⟫_ℝ=0
    rw [inner_sub_left]
    have hinner : ⟪gaussianFrameProjection v g,v i⟫_ℝ=⟪g,v i⟫_ℝ := by
      calc
        _ = ⟪v i,g⟫_ℝ := by
          simpa only [gaussianFrameProjection,conj_trivial] using hv.inner_left_fintype (fun j => ⟪v j,g⟫_ℝ) i
        _ = _ := real_inner_comm _ _
    exact sub_eq_zero.mpr hinner.symm
  exact (S.eq_orthogonalProjection_of_mem_of_inner_eq_zero hm (fun w hw => hker hw)).symm

/-- The actual affine section depends only on its normal space and the
constant normal-space point. -/
theorem gaussianFrameSectionPoint_eq_affine_projection {q : ℕ}
    (v : Fin q → E) (hv : Orthonormal ℝ v) (a : Fin q → ℝ) (g : E) :
    gaussianFrameSectionPoint v a g=(∑ i, a i • v i)+g-
      (Submodule.span ℝ (Set.range v)).orthogonalProjection g := by
  rw [gaussianFrameSectionPoint,gaussianFrameProjection_eq_orthogonalProjection v hv]

theorem gaussianFrameSectionPoint_frame_independent {q k : ℕ}
    (v : Fin q → E) (w : Fin k → E) (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w)
    (a : Fin q → ℝ) (b : Fin k → ℝ)
    (hspan : Submodule.span ℝ (Set.range v)=Submodule.span ℝ (Set.range w))
    (hz : (∑ i, a i • v i)=∑ j, b j • w j) (g : E) :
    gaussianFrameSectionPoint v a g=gaussianFrameSectionPoint w b g := by
  rw [gaussianFrameSectionPoint_eq_affine_projection v hv,
    gaussianFrameSectionPoint_eq_affine_projection w hw,hspan,hz]

omit [FiniteDimensional ℝ E] in
/-- The squared normal-space length is the sum of squared orthonormal
coordinates, without any ambient dimension factor. -/
theorem gaussianFrame_normalPoint_normSq {q : ℕ}
    (v : Fin q → E) (hv : Orthonormal ℝ v) (a : Fin q → ℝ) :
    ‖∑ i, a i • v i‖^2=∑ i, (a i)^2 := by
  have h := hv.inner_sum a a Finset.univ
  simpa only [real_inner_self_eq_norm_sq,conj_trivial,pow_two] using h

omit [FiniteDimensional ℝ E] in
/-- A product of actual scalar Gaussian densities is the canonical
normal-space density of the actual affine normal point. -/
theorem gaussianFrame_density_eq_normalKernel {q : ℕ}
    (v : Fin q → E) (hv : Orthonormal ℝ v) (a : Fin q → ℝ) :
    (∏ i, gaussianPDFReal 0 1 (a i))=
      ((Real.sqrt (2*Real.pi))⁻¹)^q*Real.exp (-‖∑ i, a i • v i‖^2/2) := by
  rw [gaussianFrame_normalPoint_normSq v hv]
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←Real.exp_sum]
  congr 2
  simp only [Finset.sum_div,←Finset.sum_neg_distrib]

omit [FiniteDimensional ℝ E] in
theorem gaussianFrame_density_frame_independent {q : ℕ}
    (v w : Fin q → E) (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w)
    (a b : Fin q → ℝ) (hz : (∑ i, a i • v i)=∑ j, b j • w j) :
    (∏ i, gaussianPDFReal 0 1 (a i))=∏ j, gaussianPDFReal 0 1 (b j) := by
  rw [gaussianFrame_density_eq_normalKernel v hv,gaussianFrame_density_eq_normalKernel w hw,hz]

end
end RectangleCLTArxivV1
