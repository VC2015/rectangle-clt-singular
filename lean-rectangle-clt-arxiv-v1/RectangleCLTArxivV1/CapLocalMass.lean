import RectangleCLTArxivV1.CapSmallBox
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Converting actual local probabilities into integrals of localized weights.
This is the continuous unit-cell averaging step in Supplemental G.2. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- A local comparison of a nonnegative integrable weight converts a uniform
actual translated-box estimate into a bound for its expectation. -/
theorem integral_weight_le_of_local_probability
    {G Ω : Type*} [MeasurableSpace G] [MeasurableSpace Ω] [AddCommGroup G]
    [MeasurableAdd G] [MeasurableNeg G] [MeasurableSub₂ G]
    (mG : Measure G) [SFinite mG] [mG.IsNegInvariant] [mG.IsAddLeftInvariant]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → G) (hf : Measurable f)
    (B : Set G) (hB : MeasurableSet B) (hBfinite : mG B ≠ ⊤)
    (Q : G → ℝ) (hQ : Integrable Q mG) (hQm : Measurable Q)
    (hQ0 : ∀ t, 0 ≤ Q t) (C M : ℝ) (hC : 0 ≤ C) (_hM : 0 ≤ M)
    (hlocal : ∀ x t, x-t ∈ B → Q x ≤ C*Q t)
    (hsmall : ∀ t, μ.real {ω | f ω-t ∈ B} ≤ M)
    (hQi : Integrable (fun ω => Q (f ω)) μ) :
    (mG B).toReal*(∫ ω, Q (f ω) ∂μ) ≤ C*M*(∫ t, Q t ∂mG) := by
  let H : G × Ω → ℝ := fun z =>
    {w : G × Ω | f w.2-w.1 ∈ B}.indicator (fun w => Q w.1) z
  have hS : MeasurableSet {w : G × Ω | f w.2-w.1 ∈ B} :=
    (hf.comp measurable_snd |>.sub measurable_fst) hB
  have hHm : Measurable H := (hQm.comp measurable_fst).indicator hS
  have hHi : Integrable H (mG.prod μ) := by
    apply (hQ.mul_prod (integrable_const (1:ℝ))).mono' hHm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      change ‖H z‖ ≤ Q z.1*1
      dsimp only [H]
      by_cases hz : f z.2-z.1 ∈ B <;> simp [Set.indicator_apply,hz,Real.norm_eq_abs,abs_of_nonneg (hQ0 _),hQ0 _])
  have hpoint (ω : Ω) : (mG B).toReal*Q (f ω) ≤ C*(∫ t, H (t,ω) ∂mG) := by
    let S : Set G := {t | f ω-t ∈ B}
    have hSm : MeasurableSet S := (measurable_const.sub measurable_id) hB
    have hSvol : mG S = mG B := by
      exact (Measure.measurePreserving_sub_left mG (f ω)).measure_preimage hB.nullMeasurableSet
    have hSi : Integrable (S.indicator (fun _ => Q (f ω))) mG := by
      apply IntegrableOn.integrable_indicator _ hSm
      exact integrableOn_const.mpr (Or.inr (hSvol ▸ lt_top_iff_ne_top.mpr hBfinite))
    have hHti : Integrable (fun t => H (t,ω)) mG := by
      apply hQ.mono' ((hQm.indicator hSm).aestronglyMeasurable)
      exact ae_of_all _ (fun t => by
        change ‖S.indicator Q t‖ ≤ Q t
        by_cases ht : t ∈ S <;> simp [ht,Real.norm_eq_abs,abs_of_nonneg (hQ0 _),hQ0 t])
    have hle : ∀ t, S.indicator (fun _ => Q (f ω)) t ≤ C*H (t,ω) := by
      intro t
      by_cases ht : t ∈ S
      · rw [Set.indicator_of_mem ht]
        have hmem : (t,ω) ∈ {w : G × Ω | f w.2-w.1 ∈ B} := ht
        simpa only [H,Set.indicator_of_mem hmem] using hlocal (f ω) t ht
      · have hmem : (t,ω) ∉ {w : G × Ω | f w.2-w.1 ∈ B} := ht
        simp only [Set.indicator_of_not_mem ht,H,Set.indicator_of_not_mem hmem,mul_zero,le_refl]
    have hi := integral_mono hSi (hHti.const_mul C) hle
    simpa [integral_const_mul,integral_indicator hSm,measureReal_def,hSvol,smul_eq_mul] using hi
  have hleft := integral_mono (hQi.const_mul (mG B).toReal)
    (hHi.swap.integral_prod_left.const_mul C) hpoint
  rw [integral_const_mul,integral_const_mul] at hleft
  have hswap : (∫ ω, ∫ t, H (t,ω) ∂mG ∂μ) = ∫ t, ∫ ω, H (t,ω) ∂μ ∂mG :=
    (integral_integral_swap hHi).symm
  change (mG B).toReal * (∫ a, Q (f a) ∂μ) ≤ C*(∫ ω, ∫ t, H (t,ω) ∂mG ∂μ) at hleft
  rw [hswap] at hleft
  have hright : (∫ t, ∫ ω, H (t,ω) ∂μ ∂mG) ≤ M*(∫ t, Q t ∂mG) := by
    have heq (t : G) : (∫ ω, H (t,ω) ∂μ) = Q t*μ.real {ω | f ω-t ∈ B} := by
      have hm : MeasurableSet {ω | f ω-t ∈ B} := (hf.sub_const t) hB
      change (∫ ω, {ω | f ω-t ∈ B}.indicator (fun _ => Q t) ω ∂μ) = _
      rw [integral_indicator hm,setIntegral_const]
      simp [smul_eq_mul,mul_comm]
    calc
      _ ≤ ∫ t, M*Q t ∂mG := by
        apply integral_mono hHi.integral_prod_left (hQ.const_mul M)
        intro t
        change (∫ ω, H (t,ω) ∂μ) ≤ M*Q t
        rw [heq]
        nlinarith [mul_le_mul_of_nonneg_left (hsmall t) (hQ0 t)]
      _ = _ := integral_const_mul _ _
  exact hleft.trans ((mul_le_mul_of_nonneg_left hright hC).trans_eq (by ring))

/-- A fixed integrable majorant for both single- and pair-face weights. -/
def capLaplace (x : ℝ) : ℝ := Real.exp (-(|x|/2))

theorem integrable_capLaplace : Integrable capLaplace := by
  have hp : IntegrableOn capLaplace (Set.Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (by norm_num : (-1/2:ℝ)<0) 0).congr_fun _ measurableSet_Ioi
    intro x hx
    simp [capLaplace,abs_of_pos (show 0 < x from hx)]
    ring
  have hn : IntegrableOn capLaplace (Set.Iic 0) := by
    apply (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<1/2) 0).congr_fun _ measurableSet_Iic
    intro x hx
    simp [capLaplace,abs_of_nonpos (show x ≤ 0 from hx)]
    ring
  rw [← integrableOn_univ,← Set.Iic_union_Ioi (a := (0:ℝ)),integrableOn_union]
  exact ⟨hn,hp⟩

theorem integral_capLaplace : (∫ x, capLaplace x) = 4 := by
  have hp : (∫ x in Set.Ioi (0:ℝ), capLaplace x) = 2 := by
    calc
      _ = ∫ x in Set.Ioi (0:ℝ), Real.exp ((-1/2)*x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        unfold capLaplace
        rw [abs_of_pos (show 0 < x from hx)]
        congr 1
        ring
      _ = 2 := by rw [integral_exp_mul_Ioi (by norm_num : (-1/2:ℝ)<0)]; norm_num
  have hn : (∫ x in Set.Iic (0:ℝ), capLaplace x) = 2 := by
    calc
      _ = ∫ x in Set.Iic (0:ℝ), Real.exp ((1/2)*x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x hx
        unfold capLaplace
        rw [abs_of_nonpos (show x ≤ 0 from hx)]
        congr 1
        ring
      _ = 2 := by rw [integral_exp_mul_Iic (by norm_num : (0:ℝ)<1/2)]; norm_num
  have hi := integral_add_compl (μ := volume) (s := Set.Iic (0:ℝ)) measurableSet_Iic integrable_capLaplace
  norm_num [Set.compl_Iic,hn,hp] at hi ⊢
  exact hi.symm

theorem capLaplace_local (x t : ℝ) (hxt : |x-t| ≤ 1) :
    capLaplace x ≤ Real.exp (1/2)*capLaplace t := by
  rw [capLaplace,capLaplace,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht : |t-x| ≤ 1 := by simpa only [abs_sub_comm] using hxt
  have he : t-x+x=t := by ring
  have hh := abs_add (t-x) x
  rw [he] at hh
  linarith

end
end RectangleCLTArxivV1
