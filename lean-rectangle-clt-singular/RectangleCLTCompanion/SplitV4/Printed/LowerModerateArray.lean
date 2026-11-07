import RectangleCLTCompanion.SplitV4.ModerateTailGeneral

/-! The literal independent-copy step in F.1. The stronger baseline
variance-minimization argument is retained, but is not used here. -/
open MeasureTheory ProbabilityTheory Set
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω→ℝ} {δ : ℝ}

theorem independent_copy_inner (hX : Measurable X) (hδ : 0≤δ)
    (hb : ∀ᵐ x ∂μ,|X x|≤δ) (x : Ω) :
    (∫y,(X x-X y)^2 ∂μ)=variance X μ+((∫y,X y ∂μ)-X x)^2 := by
  simpa only [sub_sq_comm (X x)] using moderate_integral_shift_sq hX hδ hb (X x)

theorem integrable_independent_copy_inner (hX : Measurable X) (hδ : 0≤δ)
    (hb : ∀ᵐ x ∂μ,|X x|≤δ)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν,|X x|≤δ) :
    Integrable (fun x => ∫y,(X x-X y)^2 ∂μ) ν := by
  have he : (fun x => ∫y,(X x-X y)^2 ∂μ)=
      (fun x => variance X μ+(X x-(∫y,X y ∂μ))^2) := by
    funext x
    rw [independent_copy_inner hX hδ hb x,sub_sq_comm]
  rw [he]
  exact (integrable_const _).add (moderate_integrable_shift_pow hX hδ hν _ 2)

theorem independent_copy_variance_integral (hX : Measurable X) (hδ : 0≤δ)
    (hb : ∀ᵐ x ∂μ,|X x|≤δ) :
    (∫z : Ω×Ω,(X z.1-X z.2)^2 ∂μ.prod μ)=2*variance X μ := by
  have hM : Measurable (fun z : Ω×Ω => (X z.1-X z.2)^2) :=
    ((hX.comp measurable_fst).sub (hX.comp measurable_snd)).pow_const 2
  have hI : Integrable (fun z : Ω×Ω => (X z.1-X z.2)^2) (μ.prod μ) := by
    apply (integrable_prod_iff hM.aestronglyMeasurable).mpr
    constructor
    · apply ae_of_all
      intro x
      simpa only [sub_sq_comm (X x)] using moderate_integrable_shift_pow hX hδ hb (X x) 2
    · simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using
        integrable_independent_copy_inner hX hδ hb μ hb
  rw [integral_prod _ hI]
  simp_rw [independent_copy_inner hX hδ hb]
  have hsq : Integrable (fun x => ((∫y,X y ∂μ)-X x)^2) μ := by
    simpa only [sub_sq_comm] using moderate_integrable_shift_pow hX hδ hb (∫y,X y ∂μ) 2
  rw [integral_add (integrable_const _) hsq]
  have he : (∫x,((∫y,X y ∂μ)-X x)^2 ∂μ)=variance X μ := by
    simp_rw [sub_sq_comm (∫y,X y ∂μ)]
    exact (variance_eq_integral hX.aemeasurable).symm
  rw [he]
  simp
  ring

/-- Two applications of the one-copy density bounds give the literal
two-copy density factor exp(±4 delta |t|), before taking variances. -/
theorem independent_copy_tilt_integral_bounds (hX : Measurable X) (hδ : 0≤δ)
    (hb : ∀ᵐ x ∂μ,|X x|≤δ) (t : ℝ) :
    Real.exp (-4*|t| *δ)*(∫x,∫y,(X x-X y)^2 ∂μ ∂μ)≤
        (∫x,∫y,(X x-X y)^2 ∂moderateScalarTilt μ X t ∂moderateScalarTilt μ X t) ∧
    (∫x,∫y,(X x-X y)^2 ∂moderateScalarTilt μ X t ∂moderateScalarTilt μ X t)≤
        Real.exp (4*|t| *δ)*(∫x,∫y,(X x-X y)^2 ∂μ ∂μ) := by
  let ν := moderateScalarTilt μ X t
  letI : IsProbabilityMeasure ν := moderateScalarTilt_probability hX hb t
  have hν : ∀ᵐ x ∂ν,|X x|≤δ := moderateScalarTilt_bound hb t
  let g := fun x => ∫y,(X x-X y)^2 ∂μ
  let q := fun x => ∫y,(X x-X y)^2 ∂ν
  have hgi := integrable_independent_copy_inner hX hδ hb ν hν
  have hqi := integrable_independent_copy_inner (μ:=ν) hX hδ hν ν hν
  have hinner (x) : Real.exp (-2*|t| *δ)*g x≤q x ∧ q x≤Real.exp (2*|t| *δ)*g x := by
    have hf : Integrable (fun y => (X x-X y)^2) μ := by
      simpa only [sub_sq_comm (X x)] using moderate_integrable_shift_pow hX hδ hb (X x) 2
    exact moderateTilt_integral_nonneg_bounds hX hb t hf (ae_of_all _ (fun _ => sq_nonneg _))
  have houter := moderateTilt_integral_nonneg_bounds hX hb t
    (integrable_independent_copy_inner hX hδ hb μ hb)
    (ae_of_all _ (fun _ => integral_nonneg (fun _ => sq_nonneg _)))
  have hl := integral_mono (hgi.const_mul (Real.exp (-2*|t| *δ))) hqi (fun x => (hinner x).1)
  have hu := integral_mono hqi (hgi.const_mul (Real.exp (2*|t| *δ))) (fun x => (hinner x).2)
  rw [integral_const_mul] at hl hu
  constructor
  · have hh := (mul_le_mul_of_nonneg_left houter.1 (Real.exp_pos (-2*|t| *δ)).le).trans hl
    convert hh using 1
    rw [←mul_assoc,←Real.exp_add]
    congr 2
    ring
  · have hh := hu.trans (mul_le_mul_of_nonneg_left houter.2 (Real.exp_pos (2*|t| *δ)).le)
    convert hh using 1
    rw [←mul_assoc,←Real.exp_add]
    congr 2
    ring

theorem moderateTiltVariance_printed_copy_bounds (hX : Measurable X) (hδ : 0≤δ)
    (hb : ∀ᵐ x ∂μ,|X x|≤δ) (t : ℝ) :
    Real.exp (-4*|t| *δ)*variance X μ≤moderateTiltVariance μ X t ∧
      moderateTiltVariance μ X t≤Real.exp (4*|t| *δ)*variance X μ := by
  letI := moderateScalarTilt_probability hX hb t
  have hν := moderateScalarTilt_bound hb t
  have hc := independent_copy_tilt_integral_bounds hX hδ hb t
  have hi := independent_copy_variance_integral hX hδ hb
  have ht := independent_copy_variance_integral (μ:=moderateScalarTilt μ X t) hX hδ hν
  have hp (κ : Measure Ω) [IsProbabilityMeasure κ] (hk : ∀ᵐ x ∂κ,|X x|≤δ) :
      (∫x,∫y,(X x-X y)^2 ∂κ ∂κ)=2*variance X κ := by
    have hm : Measurable (fun z : Ω×Ω => (X z.1-X z.2)^2) :=
      ((hX.comp measurable_fst).sub (hX.comp measurable_snd)).pow_const 2
    have hI : Integrable (fun z : Ω×Ω => (X z.1-X z.2)^2) (κ.prod κ) := by
      apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
      constructor
      · apply ae_of_all; intro x
        simpa only [sub_sq_comm (X x)] using moderate_integrable_shift_pow hX hδ hk (X x) 2
      · simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using
          integrable_independent_copy_inner hX hδ hk κ hk
    rw [←integral_prod _ hI]
    exact independent_copy_variance_integral hX hδ hk
  rw [hp μ hb,hp (moderateScalarTilt μ X t) hν] at hc
  rw [moderateTiltVariance_eq_variance hX hb]
  constructor <;> nlinarith [hc.1,hc.2]

end
end RectangleCLT.Companion.SplitV4.Printed
