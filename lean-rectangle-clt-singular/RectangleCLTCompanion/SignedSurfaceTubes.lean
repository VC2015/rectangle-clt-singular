import RectangleCLTCompanion.SignedSurfaceGeometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual Gaussian-kernel integrals over the rectangular normal fibers used
by the paired-ridge tube argument. These do not assume any surface estimate. -/

open MeasureTheory
open scoped InnerProductSpace

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussianKernel (z : E) : ℝ := Real.exp (-‖z‖ ^ 2 / 2)

omit [InnerProductSpace ℝ E] in
@[fun_prop] theorem continuous_gaussianKernel : Continuous (gaussianKernel : E → ℝ) := by
  unfold gaussianKernel
  fun_prop

@[fun_prop] theorem continuous_ridgeDisplacement (u v : E) :
    Continuous (ridgeDisplacement u v) := by
  unfold ridgeDisplacement
  fun_prop

/-- The density ratio uses only the projection onto the normal plane, never
an ambient-dimensional bound on the length of the base point. -/
theorem gaussianKernel_shift_lower (z y : E)
    (hinner : ⟪z, y⟫_ℝ ≤ 1) (hy : ‖y‖ ≤ 1) :
    Real.exp (-(3 : ℝ) / 2) * gaussianKernel z ≤ gaussianKernel (z + y) := by
  unfold gaussianKernel
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y]
  nlinarith [norm_add_sq_real z y]

theorem abs_inner_ridgeDisplacement_le (u v z : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hb : |⟪z, bisector u v⟫_ℝ| ≤ R)
    (hc : |⟪z, differenceDirection u v⟫_ℝ| ≤ R)
    {st : ℝ × ℝ} (hst : st ∈ ridgeRectangle u v ε) :
    |⟪z, ridgeDisplacement u v st⟫_ℝ| ≤ R * ε := by
  have hd2 : ‖u - v‖ ≤ 2 := by
    have hh := norm_sub_le u v
    rw [hu, hv] at hh
    linarith
  have hs0 : 0 ≤ st.1 := (div_nonneg hε (by norm_num)).trans hst.1.1
  have ht : |st.2| ≤ ε * ‖u - v‖ / 8 :=
    abs_le.mpr ⟨by nlinarith [hst.2.1], hst.2.2⟩
  have htε : |st.2| ≤ ε / 4 := by nlinarith [mul_le_mul_of_nonneg_left hd2 hε]
  simp only [ridgeDisplacement, inner_add_right, inner_smul_right]
  calc
    _ ≤ |st.1 * ⟪z, bisector u v⟫_ℝ| +
        |st.2 * ⟪z, differenceDirection u v⟫_ℝ| := abs_add _ _
    _ = st.1 * |⟪z, bisector u v⟫_ℝ| +
        |st.2| * |⟪z, differenceDirection u v⟫_ℝ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hs0]
    _ ≤ st.1 * R + |st.2| * R :=
      add_le_add (mul_le_mul_of_nonneg_left hb hs0)
        (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
    _ ≤ R * ε := by nlinarith [hst.1.2]

theorem gaussianKernel_ridgeRectangle_lower (u v z : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hb : |⟪z, bisector u v⟫_ℝ| ≤ R)
    (hc : |⟪z, differenceDirection u v⟫_ℝ| ≤ R)
    {st : ℝ × ℝ} (hst : st ∈ ridgeRectangle u v ε) :
    Real.exp (-(3 : ℝ) / 2) * gaussianKernel z ≤
      gaussianKernel (z + ridgeDisplacement u v st) := by
  apply gaussianKernel_shift_lower
  · exact (le_abs_self _).trans
      ((abs_inner_ridgeDisplacement_le u v z hu hv hR hε hb hc hst).trans hRε)
  · exact (ridgeRectangle_displacement_norm_le u v hu hv hp hm hε hst).trans hε1

omit [InnerProductSpace ℝ E] in
theorem ridgeRectangle_real_area (u v : E) {ε : ℝ} (hε : 0 ≤ ε) :
    ((volume : Measure ℝ).prod volume).real (ridgeRectangle u v ε) =
      ε ^ 2 * ‖u - v‖ / 16 := by
  rw [measureReal_def, ridgeRectangle_area u v hε,
    ENNReal.toReal_ofReal (by positivity)]

/-- An actual two-dimensional Gaussian normal-fiber integral. The prefactor
`‖u-v‖` matches the paired ridge coefficient, even close to degeneracy. -/
theorem ridgeRectangle_gaussian_integral_lower (u v z : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hb : |⟪z, bisector u v⟫_ℝ| ≤ R)
    (hc : |⟪z, differenceDirection u v⟫_ℝ| ≤ R) :
    Real.exp (-(3 : ℝ) / 2) * gaussianKernel z * (ε ^ 2 * ‖u - v‖ / 16) ≤
      ∫ st in ridgeRectangle u v ε,
        gaussianKernel (z + ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume) := by
  have hcompact : IsCompact (ridgeRectangle u v ε) :=
    isCompact_Icc.prod isCompact_Icc
  have hfun : Continuous (fun st => gaussianKernel (z + ridgeDisplacement u v st)) := by
    fun_prop
  have hconst : Continuous (fun _ : ℝ × ℝ => Real.exp (-(3 : ℝ) / 2) * gaussianKernel z) :=
    continuous_const
  have hmono := integral_mono_ae
    (hconst.continuousOn.integrableOn_compact hcompact
      (μ := (volume : Measure ℝ).prod volume))
    (hfun.continuousOn.integrableOn_compact hcompact
      (μ := (volume : Measure ℝ).prod volume))
    ((ae_restrict_mem hcompact.measurableSet).mono fun st hst =>
      gaussianKernel_ridgeRectangle_lower u v z hu hv hp hm hR hε hε1 hRε hb hc hst)
  rw [setIntegral_const, ridgeRectangle_real_area u v hε] at hmono
  simpa only [smul_eq_mul, mul_comm] using hmono

/-- Actual one-dimensional normal-fiber estimate at a facet. -/
theorem facet_gaussian_integral_lower (u z : E) (hu : ‖u‖ = 1)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hz : |⟪z, u⟫_ℝ| ≤ R) :
    Real.exp (-(3 : ℝ) / 2) * gaussianKernel z * ε ≤
      ∫ t in Set.Icc (0 : ℝ) ε, gaussianKernel (z + t • u) := by
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) ε) :
      Real.exp (-(3 : ℝ) / 2) * gaussianKernel z ≤ gaussianKernel (z + t • u) := by
    apply gaussianKernel_shift_lower
    · rw [inner_smul_right]
      calc
        t * ⟪z, u⟫_ℝ ≤ t * R :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hz) ht.1
        _ ≤ ε * R := mul_le_mul_of_nonneg_right ht.2 hR
        _ ≤ 1 := by simpa only [mul_comm] using hRε
    · rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_of_nonneg ht.1]
      exact ht.2.trans hε1
  have hf : Continuous (fun t : ℝ => gaussianKernel (z + t • u)) := by fun_prop
  have hc : Continuous (fun _ : ℝ => Real.exp (-(3 : ℝ) / 2) * gaussianKernel z) :=
    continuous_const
  have hm := integral_mono_ae (hc.continuousOn.integrableOn_Icc (μ := volume))
    (hf.continuousOn.integrableOn_Icc (μ := volume))
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht => hpoint t ht)
  rw [setIntegral_const] at hm
  have hmeasure : (volume : Measure ℝ).real (Set.Icc (0 : ℝ) ε) = ε := by
    rw [measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hε]
  rw [hmeasure, smul_eq_mul, mul_comm] at hm
  exact hm

/-- Paired ridge score dominated by the actual Gaussian tube-fiber mass.
The normal-angle factor cancels exactly; no lower bound on the angle is used. -/
theorem pairedRidge_gaussian_integral_bound (u v z : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hb : |⟪z, bisector u v⟫_ℝ| ≤ R)
    (hc : |⟪z, differenceDirection u v⟫_ℝ| ≤ R) :
    |pairedRidgeCoefficient u v z| * gaussianKernel z ≤
      (16 * Real.exp ((3 : ℝ) / 2) * R / ε ^ 2) *
      ∫ st in ridgeRectangle u v ε,
        gaussianKernel (z + ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume) := by
  have hcoeff : |pairedRidgeCoefficient u v z| ≤ ‖u - v‖ * R := by
    rw [pairedRidgeCoefficient_eq u v z hu hv hp hm, abs_mul, abs_norm]
    exact mul_le_mul_of_nonneg_left (by simpa only [real_inner_comm] using hb) (norm_nonneg _)
  have hbase := ridgeRectangle_gaussian_integral_lower u v z hu hv hp hm hR hε.le hε1 hRε hb hc
  have hmult := mul_le_mul_of_nonneg_left hbase
    (by positivity : 0 ≤ 16 * Real.exp ((3 : ℝ) / 2) * R / ε ^ 2)
  have hcancel :
      (16 * Real.exp ((3 : ℝ) / 2) * R / ε ^ 2) *
        (Real.exp (-(3 : ℝ) / 2) * gaussianKernel z * (ε ^ 2 * ‖u - v‖ / 16)) =
      ‖u - v‖ * R * gaussianKernel z := by
    have hexp : Real.exp ((3 : ℝ) / 2) * Real.exp (-(3 : ℝ) / 2) = 1 := by
      rw [← Real.exp_add]
      norm_num
    field_simp [hε.ne']
    nlinarith only [congrArg (fun t => t * (ε ^ 2 * R * gaussianKernel z * ‖u - v‖)) hexp]
  rw [hcancel] at hmult
  exact (mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)).trans hmult

def tubeRadius (R : ℝ) : ℝ := (1 + R)⁻¹

theorem tubeRadius_pos {R : ℝ} (hR : 0 ≤ R) : 0 < tubeRadius R := by
  unfold tubeRadius
  positivity

theorem tubeRadius_le_one {R : ℝ} (hR : 0 ≤ R) : tubeRadius R ≤ 1 := by
  unfold tubeRadius
  exact (inv_le_one₀ (by linarith)).mpr (by linarith)

theorem mul_tubeRadius_le_one {R : ℝ} (hR : 0 ≤ R) : R * tubeRadius R ≤ 1 := by
  change R / (1 + R) ≤ 1
  exact (div_le_one (by linarith)).mpr (by linarith)

theorem pairedRidge_gaussian_integral_bound_cubic (u v z : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : u + v ≠ 0) (hm : u - v ≠ 0)
    {R : ℝ} (hR : 1 ≤ R)
    (hb : |⟪z, bisector u v⟫_ℝ| ≤ R)
    (hc : |⟪z, differenceDirection u v⟫_ℝ| ≤ R) :
    |pairedRidgeCoefficient u v z| * gaussianKernel z ≤
      (64 * Real.exp ((3 : ℝ) / 2) * R ^ 3) *
      ∫ st in ridgeRectangle u v (tubeRadius R),
        gaussianKernel (z + ridgeDisplacement u v st)
        ∂((volume : Measure ℝ).prod volume) := by
  have hR0 : 0 ≤ R := by linarith
  have hh := pairedRidge_gaussian_integral_bound u v z hu hv hp hm hR0
    (tubeRadius_pos hR0) (tubeRadius_le_one hR0) (mul_tubeRadius_le_one hR0) hb hc
  have hcoef : 16 * Real.exp ((3 : ℝ) / 2) * R / tubeRadius R ^ 2 ≤
      64 * Real.exp ((3 : ℝ) / 2) * R ^ 3 := by
    simp only [tubeRadius, inv_pow, div_inv_eq_mul]
    have hs : (1 + R) ^ 2 ≤ (2 * R) ^ 2 := by nlinarith
    calc
      _ ≤ (16 * Real.exp ((3 : ℝ) / 2) * R) * (2 * R) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  apply hh.trans
  apply mul_le_mul_of_nonneg_right hcoef
  exact integral_nonneg (fun _ => Real.exp_nonneg _)

end
end RectangleCLT.Companion.SignedSurface
