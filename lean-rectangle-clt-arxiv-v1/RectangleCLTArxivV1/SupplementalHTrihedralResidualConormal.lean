import RectangleCLTArxivV1.SupplementalHTrihedralBalance
import RectangleCLTArxivV1.SupplementalHSurfaceGeometry

/-! The actual normalized double residual of the third normal is the
constructed inward conormal of its trihedral normal-cone facet. -/
namespace RectangleCLTArxivV1
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

def trihedralPairBisector (e : Basis (Fin 3) ℝ E) (i : Fin 3) : E :=
  bisector (e (i.succAbove 0)) (e (i.succAbove 1))

def trihedralPairDifference (e : Basis (Fin 3) ℝ E) (i : Fin 3) : E :=
  differenceDirection (e (i.succAbove 0)) (e (i.succAbove 1))

def trihedralDoubleResidual (e : Basis (Fin 3) ℝ E) (i : Fin 3) : E :=
  e i-⟪trihedralPairBisector e i,e i⟫_ℝ • trihedralPairBisector e i-
    ⟪trihedralPairDifference e i,e i⟫_ℝ • trihedralPairDifference e i

def trihedralResidualUnitNormal (e : Basis (Fin 3) ℝ E) (i : Fin 3) : E :=
  ‖trihedralDoubleResidual e i‖⁻¹ • trihedralDoubleResidual e i

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem trihedral_other_pair_nondegenerate (e : Basis (Fin 3) ℝ E) (i : Fin 3) :
    e (i.succAbove 0)+e (i.succAbove 1)≠0 ∧
      e (i.succAbove 0)-e (i.succAbove 1)≠0 := by
  have hjk : i.succAbove (0:Fin 2)≠i.succAbove 1 := (Fin.succAboveEmb i).injective.ne (by decide)
  constructor
  · intro hz
    have he : (1:ℝ) • e (i.succAbove 0)=(-1:ℝ) • e (i.succAbove 1) := by
      simpa only [one_smul,neg_one_smul] using eq_neg_of_add_eq_zero_left hz
    exact hjk (e.linearIndependent.eq_of_smul_apply_eq_smul_apply 1 (-1) _ _ (by norm_num) he)
  · intro hz
    exact hjk (e.linearIndependent.injective (sub_eq_zero.mp hz))

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem trihedralDoubleResidual_orthogonal_pair (e : Basis (Fin 3) ℝ E)
    (hunit : ∀ j, ‖e j‖=1) (i : Fin 3) :
    ⟪trihedralDoubleResidual e i,trihedralPairBisector e i⟫_ℝ=0 ∧
      ⟪trihedralDoubleResidual e i,trihedralPairDifference e i⟫_ℝ=0 := by
  obtain ⟨hp,hm⟩ := trihedral_other_pair_nondegenerate e i
  have he : ‖trihedralPairBisector e i‖=1 := norm_bisector _ _ hp
  have hf : ‖trihedralPairDifference e i‖=1 := norm_differenceDirection _ _ hm
  have hef : ⟪trihedralPairBisector e i,trihedralPairDifference e i⟫_ℝ=0 :=
    inner_bisector_differenceDirection _ _ ((hunit _).trans (hunit _).symm)
  have hfe : ⟪trihedralPairDifference e i,trihedralPairBisector e i⟫_ℝ=0 := by
    rw [real_inner_comm]
    exact hef
  have hee : ⟪trihedralPairBisector e i,trihedralPairBisector e i⟫_ℝ=1 := by
    rw [real_inner_self_eq_norm_sq,he,one_pow]
  have hff : ⟪trihedralPairDifference e i,trihedralPairDifference e i⟫_ℝ=1 := by
    rw [real_inner_self_eq_norm_sq,hf,one_pow]
  constructor
  · unfold trihedralDoubleResidual
    rw [inner_sub_left,inner_sub_left,inner_smul_left,inner_smul_left]
    simp only [conj_trivial,hee,hfe,mul_one,mul_zero,sub_zero]
    rw [real_inner_comm]
    ring
  · unfold trihedralDoubleResidual
    rw [inner_sub_left,inner_sub_left,inner_smul_left,inner_smul_left]
    simp only [conj_trivial,hef,hff,mul_one,mul_zero,sub_zero]
    rw [real_inner_comm]
    ring

theorem trihedralDoubleResidual_ne_zero (e : Basis (Fin 3) ℝ E) (i : Fin 3) :
    trihedralDoubleResidual e i≠0 := by
  have h0 := trihedralInwardNormal_orthogonal_other e i (i.succAbove 0) (Fin.succAbove_ne i 0)
  have h1 := trihedralInwardNormal_orthogonal_other e i (i.succAbove 1) (Fin.succAbove_ne i 1)
  have he : ⟪trihedralInwardNormal e i,trihedralPairBisector e i⟫_ℝ=0 := by
    simp only [trihedralPairBisector,bisector,inner_smul_right,inner_add_right,h0,h1,add_zero,mul_zero]
  have hf : ⟪trihedralInwardNormal e i,trihedralPairDifference e i⟫_ℝ=0 := by
    simp only [trihedralPairDifference,differenceDirection,inner_smul_right,inner_sub_right,h0,h1,sub_zero,mul_zero]
  intro hz
  have hp := trihedralInwardNormal_positive_own e i
  have hh : ⟪trihedralInwardNormal e i,trihedralDoubleResidual e i⟫_ℝ=⟪trihedralInwardNormal e i,e i⟫_ℝ := by
    simp only [trihedralDoubleResidual,inner_sub_right,inner_smul_right,he,hf,mul_zero,sub_zero]
  rw [hz,inner_zero_right] at hh
  linarith

/-- The genuinely normalized third residual is the actual oriented
trihedral conormal used in the spherical balance identity. -/
theorem trihedralResidualUnitNormal_eq_inward (e : Basis (Fin 3) ℝ E)
    (hunit : ∀ j, ‖e j‖=1) (i : Fin 3) :
    trihedralResidualUnitNormal e i=trihedralInwardNormal e i := by
  obtain ⟨hp,hm⟩ := trihedral_other_pair_nondegenerate e i
  obtain ⟨hre,hrf⟩ := trihedralDoubleResidual_orthogonal_pair e hunit i
  have hpos : 0<‖trihedralDoubleResidual e i‖ := norm_pos_iff.mpr (trihedralDoubleResidual_ne_zero e i)
  have hr0 : ⟪trihedralDoubleResidual e i,e (i.succAbove 0)⟫_ℝ=0 := by
    have hs := hre
    have hd := hrf
    simp only [trihedralPairBisector,bisector,inner_smul_right,inner_add_right] at hs
    simp only [trihedralPairDifference,differenceDirection,inner_smul_right,inner_sub_right] at hd
    have hs' := (mul_eq_zero.mp hs).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hp))
    have hd' := (mul_eq_zero.mp hd).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hm))
    linarith
  have hr1 : ⟪trihedralDoubleResidual e i,e (i.succAbove 1)⟫_ℝ=0 := by
    have hs := hre
    have hd := hrf
    simp only [trihedralPairBisector,bisector,inner_smul_right,inner_add_right] at hs
    simp only [trihedralPairDifference,differenceDirection,inner_smul_right,inner_sub_right] at hd
    have hs' := (mul_eq_zero.mp hs).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hp))
    have hd' := (mul_eq_zero.mp hd).resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hm))
    linarith
  have hnorm : ‖trihedralResidualUnitNormal e i‖=1 := by
    simp only [trihedralResidualUnitNormal,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hpos]
    exact inv_mul_cancel₀ hpos.ne'
  have hinner : ⟪trihedralDoubleResidual e i,e i⟫_ℝ=‖trihedralDoubleResidual e i‖^2 := by
    have hw : e i=trihedralDoubleResidual e i+
        ⟪trihedralPairBisector e i,e i⟫_ℝ • trihedralPairBisector e i+
        ⟪trihedralPairDifference e i,e i⟫_ℝ • trihedralPairDifference e i := by
      unfold trihedralDoubleResidual
      abel
    calc
      _ = ⟪trihedralDoubleResidual e i,trihedralDoubleResidual e i+
          ⟪trihedralPairBisector e i,e i⟫_ℝ • trihedralPairBisector e i+
          ⟪trihedralPairDifference e i,e i⟫_ℝ • trihedralPairDifference e i⟫_ℝ := by rw [←hw]
      _ = _ := by simp only [inner_add_right,inner_smul_right,hre,hrf,mul_zero,add_zero,real_inner_self_eq_norm_sq]
  apply trihedralInwardNormal_unique e i _ hnorm
  · intro j hji
    obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
    fin_cases k
    · change ⟪trihedralResidualUnitNormal e i,e (i.succAbove (0:Fin 2))⟫_ℝ=0
      rw [trihedralResidualUnitNormal,inner_smul_left,conj_trivial,hr0,mul_zero]
    · change ⟪trihedralResidualUnitNormal e i,e (i.succAbove (1:Fin 2))⟫_ℝ=0
      rw [trihedralResidualUnitNormal,inner_smul_left,conj_trivial,hr1,mul_zero]
  · rw [trihedralResidualUnitNormal,inner_smul_left,conj_trivial,hinner]
    exact mul_pos (inv_pos.mpr hpos) (sq_pos_of_pos hpos)

end
end RectangleCLTArxivV1
