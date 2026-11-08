import RectangleCLTCompanion.SplitV4.ModerateTailGeneral
import RectangleCLTCompanion.SplitV4.Printed.LowerModerateGeneral
import RectangleCLTCompanion.LowerSkewTail

/-! The current generic F.1 estimate applied to an ACTUAL iid scalar product
law, before specialization to the printed two-point construction. This
bridge also applies to symmetric signs. It never invokes the specialized
two-point Cramer estimate. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem iid_normalized_coordinate_power_integral
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {n : ℕ} (i : Fin n) (k : ℕ) :
    (∫ z : Fin n → ℝ, (z i/Real.sqrt n)^k ∂Measure.pi (fun _ : Fin n => ν)) =
      (∫ y : ℝ, y^k ∂ν)/(Real.sqrt n)^k := by
  rw [moderateProduct_coordinate_integral (fun _ : Fin n => ν) i
    (fun y => (y/Real.sqrt n)^k) (by fun_prop)]
  simp_rw [div_pow]
  exact integral_div _ _

theorem iid_normalized_third_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {n : ℕ} (hn : 1 ≤ n) :
    (∑ i : Fin n, ∫ z : Fin n → ℝ, (z i/Real.sqrt n)^3
      ∂Measure.pi (fun _ : Fin n => ν)) = (∫ y : ℝ, y^3 ∂ν)/Real.sqrt n := by
  simp_rw [iid_normalized_coordinate_power_integral ν]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hN : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs := Real.sqrt_pos.mpr hN
  rw [← Real.sq_sqrt hN.le]
  field_simp [hs.ne']
  rw [show (Real.sqrt (n : ℝ))^3=(n : ℝ)*Real.sqrt n by rw [pow_succ,Real.sq_sqrt hN.le]]
  ring

/-- Exact generic Lemma F.1 application at the normalized iid law. The
third moment is computed, rather than assumed as a tail coefficient. -/
theorem iid_normalized_moderate_tail
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {B : ℝ} (hB : 0 < B)
    (hb : ∀ᵐ y ∂ν, |y| ≤ B) (hc : (∫ y : ℝ, y ∂ν)=0)
    (hv : (∫ y : ℝ, y^2 ∂ν)=1) {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : 0 ≤ x)
    (hsmall : moderateTailSmallConstant*((B/Real.sqrt n)*(1+x)) ≤ 1) :
    0 < (Measure.pi (fun _ : Fin n => ν)).real
      {z | x < (∑ i : Fin n, z i)/Real.sqrt n} ∧
    |Real.log ((Measure.pi (fun _ : Fin n => ν)).real
        {z | x < (∑ i : Fin n, z i)/Real.sqrt n}/standardNormalUpperTail x) -
        (∫ y : ℝ, y^3 ∂ν)*x^3/(6*Real.sqrt n)| ≤
      moderateTailRemainderConstant*
        ((B/Real.sqrt n)*(1+x)+(B/Real.sqrt n)^2*x^4) := by
  let μ := Measure.pi (fun _ : Fin n => ν)
  let η : Fin n → (Fin n → ℝ) → ℝ := fun i z => z i/Real.sqrt n
  have hN : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs := Real.sqrt_pos.mpr hN
  have hm (i : Fin n) : Measurable (η i) := (measurable_pi_apply i).div_const _
  have hind : iIndepFun η μ := (lowerScalarPi_iIndepFun (fun _ : Fin n => ν)).comp
    (fun _ y => y/Real.sqrt n) (fun _ => measurable_id.div_const _)
  have hbound (i : Fin n) : ∀ᵐ z ∂μ, |η i z| ≤ B/Real.sqrt n := by
    have hb' : ∀ᵐ y ∂μ.map (fun z => z i), |y| ≤ B := by
      rw [lowerScalarPi_map_eval (fun _ : Fin n => ν)]
      exact hb
    have hbi := (ae_map_iff (measurable_pi_apply i).aemeasurable
      (measurableSet_le measurable_id.abs measurable_const)).mp hb'
    filter_upwards [hbi] with z hz
    dsimp only [η]
    rw [abs_div,abs_of_pos hs]
    exact div_le_div_of_nonneg_right hz hs.le
  have hcenter (i : Fin n) : (∫ z, η i z ∂μ)=0 := by
    change (∫ z : Fin n → ℝ, z i/Real.sqrt n ∂μ)=0
    rw [integral_div]
    change (∫ z : Fin n → ℝ,z i ∂Measure.pi (fun _ : Fin n => ν))/Real.sqrt n=0
    have hci := moderateProduct_coordinate_integral (fun _ : Fin n => ν) i id measurable_id
    change (∫ z : Fin n → ℝ,z i ∂Measure.pi (fun _ : Fin n => ν))=(∫ y : ℝ,y ∂ν) at hci
    rw [hci,hc,zero_div]
  have hvariance : (∑ i, ∫ z, η i z^2 ∂μ)=1 := by
    change (∑ i : Fin n, ∫ z : Fin n → ℝ, (z i/Real.sqrt n)^2
      ∂Measure.pi (fun _ : Fin n => ν))=1
    simp_rw [iid_normalized_coordinate_power_integral ν,hv,Real.sq_sqrt hN.le]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have ht := moderateScalarTail_bound_printed hn hm hind (div_pos hB hs).le hbound hcenter hvariance hx hsmall
  have hsum : moderateScalarSum η=fun z : Fin n → ℝ => (∑ i,z i)/Real.sqrt n := by
    funext z
    simp only [moderateScalarSum,η,Finset.sum_div]
  have hgamma : moderateArrayGamma μ η=(∫ y : ℝ,y^3 ∂ν)/Real.sqrt n :=
    iid_normalized_third_moment ν hn
  rw [hsum,hgamma] at ht
  have hcube : ((∫ y : ℝ,y^3 ∂ν)/Real.sqrt n)*x^3/6 =
      (∫ y : ℝ,y^3 ∂ν)*x^3/(6*Real.sqrt n) := by ring
  rw [hcube] at ht
  exact ht

end
end RectangleCLT.Companion.SplitV4.Printed
