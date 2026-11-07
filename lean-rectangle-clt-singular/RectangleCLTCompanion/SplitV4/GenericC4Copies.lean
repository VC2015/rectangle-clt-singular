import RectangleCLTCompanion.SplitV4.GenericC4CommonPoint
import RectangleCLTCompanion.SplitV4.ArraySlepian

/-! Generic fresh-copy transport, including an independent Gaussian part
of the deleted base. Integrability is retained under the proved equality
of actual joint laws. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem integral_independent_copy_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B T : Ω → Vector p) (hB : Measurable B) (hT : Measurable T) (hind : IndepFun B T μ)
    (K : Vector p × Vector p → ℝ) (hK : Measurable K)
    (hi : Integrable (fun z : Ω × Ω => K (B z.1,T z.2)) (μ.prod μ)) :
    Integrable (fun ω => K (B ω,T ω)) μ ∧
      (∫ ω, K (B ω,T ω) ∂μ) = ∫ ω, (∫ ω', K (B ω,T ω') ∂μ) ∂μ := by
  have hact : μ.map (fun ω => (B ω,T ω)) = (μ.map B).prod (μ.map T) :=
    (indepFun_iff_map_prod_eq_prod_map_map hB.aemeasurable hT.aemeasurable).mp hind
  have hprod : (μ.map B).prod (μ.map T) = (μ.prod μ).map (fun z : Ω × Ω => (B z.1,T z.2)) :=
    Measure.map_prod_map μ μ hB hT
  have hmap := hact.trans hprod
  have hmprod : Measurable (fun z : Ω × Ω => (B z.1,T z.2)) :=
    (hB.comp measurable_fst).prodMk (hT.comp measurable_snd)
  have hiMap : Integrable K ((μ.prod μ).map (fun z : Ω × Ω => (B z.1,T z.2))) :=
    (integrable_map_measure hK.aestronglyMeasurable hmprod.aemeasurable).mpr hi
  have hiAct : Integrable (fun ω => K (B ω,T ω)) μ := by
    rw [← hmap] at hiMap
    exact (integrable_map_measure hK.aestronglyMeasurable (hB.prodMk hT).aemeasurable).mp hiMap
  refine ⟨hiAct, ?_⟩
  calc
    _ = ∫ z, K z ∂μ.map (fun ω => (B ω,T ω)) :=
      (integral_map (hB.prodMk hT).aemeasurable hK.aestronglyMeasurable).symm
    _ = ∫ z : Ω × Ω, K (B z.1,T z.2) ∂μ.prod μ := by
      rw [hmap, integral_map hmprod.aemeasurable hK.aestronglyMeasurable]
    _ = _ := integral_prod _ hi

theorem indepFun_first_and_deleted_product_base
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν]
    (T V : Ω → Vector p) (hT : Measurable T) (hV : Measurable V) (hind : IndepFun T V μ) :
    IndepFun (fun z : Ω × E => T z.1) (fun z : Ω × E => (V z.1,z.2)) (μ.prod ν) := by
  have hpair := (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hV.aemeasurable).mp hind
  have hmrow : Measurable (fun z : Ω × E => T z.1) := hT.comp measurable_fst
  have hmbase : Measurable (fun z : Ω × E => (V z.1,z.2)) :=
    (hV.comp measurable_fst).prodMk measurable_snd
  apply (indepFun_iff_map_prod_eq_prod_map_map hmrow.aemeasurable hmbase.aemeasurable).mpr
  have hrow : (μ.prod ν).map (fun z : Ω × E => T z.1) = μ.map T := by
    change (μ.prod ν).map (T ∘ Prod.fst) = _
    rw [← Measure.map_map hT measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have hbase : (μ.prod ν).map (fun z : Ω × E => (V z.1,z.2)) = (μ.map V).prod ν := by
    simpa only [Measure.map_id] using (Measure.map_prod_map μ ν hV measurable_id).symm
  rw [hrow, hbase]
  calc
    _ = Measure.map MeasurableEquiv.prodAssoc
        ((μ.prod ν).map (fun z : Ω × E => ((T z.1,V z.1),z.2))) := by
      rw [Measure.map_map (f := fun z : Ω × E => ((T z.1,V z.1),z.2)) MeasurableEquiv.prodAssoc.measurable
        (((hT.prodMk hV).comp measurable_fst).prodMk measurable_snd)]
      rfl
    _ = Measure.map MeasurableEquiv.prodAssoc ((μ.map (fun ω => (T ω,V ω))).prod ν) := by
      rw [show ((μ.prod ν).map (fun z : Ω × E => ((T z.1,V z.1),z.2))) =
          (μ.map (fun ω => (T ω,V ω))).prod ν by
        simpa only [Measure.map_id] using (Measure.map_prod_map μ ν (hT.prodMk hV) measurable_id).symm]
    _ = _ := by rw [hpair, Measure.prodAssoc_prod]

theorem indepFun_row_deleted_gaussian_base
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (A : Matrix (Fin p) (Fin p) ℝ) (mask : Kane.Cube n) (i : Fin n)
    (x : Vector p) (a b : ℝ) :
    IndepFun (fun z : Ω × Vector p => ξ i z.1)
      (fun z : Ω × Vector p => x+a • maskObservationSum ξ (Function.update mask i false) z.1+b • z.2)
      (μ.prod (gaussianLaw A)) := by
  have hV := measurable_maskObservationSum ξ hξ (Function.update mask i false)
  have hi := indepFun_first_and_deleted_product_base μ (gaussianLaw A) (ξ i)
    (maskObservationSum ξ (Function.update mask i false)) (hξ i) hV
    (indepFun_maskObservationSum_leaveOne μ ξ hξ hind mask i)
  exact hi.comp measurable_id
    ((measurable_const.add (measurable_const.smul measurable_fst)).add (measurable_const.smul measurable_snd))

theorem integral_canonical_independent_copy
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) (hk : k ≤ 4)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hjet : ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (B T : Ω → Vector p) (hB : Measurable B) (hT : Measurable T)
    (hind : IndepFun B T μ) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (a : ℝ) :
    Integrable (fun ω => canonicalDiagonal F k (B ω+a • T ω) (T ω)) μ ∧
      (∫ ω, canonicalDiagonal F k (B ω+a • T ω) (T ω) ∂μ) =
        ∫ ω, (∫ ω', canonicalDiagonal F k (B ω+a • T ω') (T ω') ∂μ) ∂μ := by
  have hK : Measurable (fun z : Vector p × Vector p => canonicalDiagonal F k (z.1+a • z.2) z.2) := by
    exact (((hF.continuous_iteratedFDeriv (m := k) (by exact_mod_cast hk)).comp
      (continuous_fst.add (continuous_const.smul continuous_snd))).eval
        (continuous_pi (fun _ => continuous_snd))).measurable
  have hi : Integrable (fun z : Ω × Ω => canonicalDiagonal F k (B z.1+a • T z.2) (T z.2)) (μ.prod μ) :=
    integrable_canonicalDiagonal_bounded (μ.prod μ) hF hk _ _
      ((hB.comp measurable_fst).add (measurable_const.smul (hT.comp measurable_snd)))
      (hT.comp measurable_snd) hC hδ hjet (Measure.quasiMeasurePreserving_snd.ae hbound)
  exact integral_independent_copy_of_integrable μ B T hB hT hind _ hK hi

namespace C4Test
variable {p : ℕ} (f : C4Test p)

theorem integral_value_independent_copy
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B T : Ω → Vector p) (hB : Measurable B) (hT : Measurable T)
    (hind : IndepFun B T μ) (hiB : Integrable (fun ω => ‖B ω‖) μ)
    (hiT : Integrable (fun ω => ‖T ω‖) μ) (a : ℝ) :
    Integrable (fun ω => f.value (B ω+a • T ω)) μ ∧
      (∫ ω, f.value (B ω+a • T ω) ∂μ) =
        ∫ ω, (∫ ω', f.value (B ω+a • T ω') ∂μ) ∂μ := by
  have hiBprod : Integrable (fun z : Ω × Ω => ‖B z.1‖) (μ.prod μ) := by
    simpa only [mul_one] using hiB.mul_prod (integrable_const (1 : ℝ))
  have hiTprod : Integrable (fun z : Ω × Ω => ‖T z.2‖) (μ.prod μ) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).mul_prod hiT
  have hm : Measurable (fun z : Ω × Ω => B z.1+a • T z.2) :=
    (hB.comp measurable_fst).add (measurable_const.smul (hT.comp measurable_snd))
  have hnorm : Integrable (fun z : Ω × Ω => ‖B z.1+a • T z.2‖) (μ.prod μ) := by
    apply (hiBprod.add (hiTprod.const_mul |a|)).mono' hm.norm.aestronglyMeasurable
    apply ae_of_all
    intro z
    rw [norm_norm]
    calc
      _ ≤ ‖B z.1‖+‖a • T z.2‖ := norm_add_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs, Pi.add_apply]
  have hi := f.integrable_value_of_norm (μ.prod μ) _ hm hnorm
  exact integral_independent_copy_of_integrable μ B T hB hT hind _
    (f.continuous_value.measurable.comp (measurable_fst.add (measurable_const.smul measurable_snd))) hi

end C4Test

end
end RectangleCLT.Companion.SplitV4
