import RectangleCLTCompanion.SplitV4.SymmetricFamilyAllActive
import RectangleCLTCompanion.SplitV4.SymmetricFamilyRareCalibration

/-! The printed all-active-column bound at an arbitrary real cutoff.
The baseline natural-cutoff theorem is retained and specialized using
the exact integer-valued count; no rounding loss enters the exponent. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem familyMaskedSignMaximum_all_active_real_bound
    (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] {b : ℝ} (hb : 0≤b) :
    (familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z≠familyActivationCount z} ≤
      (familyRestArrayLaw P n m).real {z | b<familyActivationCount z}+
        Real.exp (-(m:ℝ)*(P.pi/2)^b) := by
  have hc := familyMaskedSignMaximum_all_active_bound P n m (Nat.floor b)
  have he : {z : Fin n→FamilyRestSeed m | (Nat.floor b:ℝ)<familyActivationCount z}=
      {z | b<familyActivationCount z} := by
    ext z
    change ((Nat.floor b:ℝ)<familyActivationCount z) ↔ b<familyActivationCount z
    rw [familyActivationCount_columns]
    rw [Nat.cast_lt]
    exact Nat.floor_lt hb
  rw [he] at hc
  have hbase0 : 0<P.pi/2 := by linarith [P.pi_pos]
  have hbase1 : P.pi/2≤1 := by linarith [P.pi_le_one]
  have hp := Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1 (Nat.floor_le hb)
  rw [Real.rpow_natCast] at hp
  have hex : Real.exp (-(m:ℝ)*(P.pi/2)^Nat.floor b)≤Real.exp (-(m:ℝ)*(P.pi/2)^b) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr (Nat.cast_nonneg m))
  exact hc.trans (add_le_add_left hex _)

/-- The count and maximum estimates actually used after the printed
all-active event. The integrals and failure probability are actual laws. -/
theorem familyMaskedSignMaximum_printed_moments
    (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] :
    (∫z,familyMaskedSignMaximum z^2 ∂familyRestArrayLaw P n m)≤((n:ℝ)*P.theta)^2+(n:ℝ)*P.theta ∧
    (n:ℝ)*P.theta-(∫z,familyMaskedSignMaximum z ∂familyRestArrayLaw P n m)≤
      2*Real.sqrt (((n:ℝ)*P.theta)^2+(n:ℝ)*P.theta)*
        Real.sqrt ((familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z≠familyActivationCount z}) := by
  refine ⟨integral_familyMaskedSignMaximum_sq_le P n m, ?_⟩
  convert familyMaskedSignMaximum_mean_deficit P n m using 1 <;> ring

/-- The exact finite unmasked bound printed at b=log m. -/
theorem familyUnmasked_printed_failure_bound
    (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m]
    (hθ : (n:ℝ)*P.theta=Real.log (m:ℝ)/2) (hπ : P.pi=1)
    (hL : 0<Real.log (m:ℝ)) :
    (familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z≠familyActivationCount z}≤
      2/Real.log (m:ℝ)+Real.exp (-Real.exp ((1-Real.log 2)*Real.log (m:ℝ))) := by
  have hc := familyMaskedSignMaximum_all_active_real_bound P n m hL.le
  have htail := familyActivationCount_upper_tail P n m (show (n:ℝ)*P.theta<Real.log (m:ℝ) by rw [hθ]; linarith)
  rw [hθ] at htail
  have hfrac : (Real.log (m:ℝ)/2)/(Real.log (m:ℝ)-Real.log (m:ℝ)/2)^2=2/Real.log (m:ℝ) := by
    rw [show Real.log (m:ℝ)-Real.log (m:ℝ)/2=Real.log (m:ℝ)/2 by ring]
    field_simp [hL.ne']
    ring
  rw [hfrac] at htail
  have hm : (0:ℝ)<m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have hpow : (m:ℝ)*(P.pi/2)^Real.log (m:ℝ)=Real.exp ((1-Real.log 2)*Real.log (m:ℝ)) := by
    rw [hπ,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<1/2)]
    rw [show Real.log ((1:ℝ)/2) = -Real.log 2 by simp]
    rw [←Real.exp_log hm,←Real.exp_add]
    simp only [Real.log_exp]
    congr 1
    ring
  rw [show -(m:ℝ)*(P.pi/2)^Real.log (m:ℝ) = -Real.exp ((1-Real.log 2)*Real.log (m:ℝ)) by rw [←hpow]; ring] at hc
  exact hc.trans (add_le_add_right htail _)

/-- The exact finite masked bound printed at b=2k. -/
theorem familyMasked_printed_failure_bound
    (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m]
    (hk : 0<(n:ℝ)*P.theta) :
    (familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z≠familyActivationCount z}≤
      1/((n:ℝ)*P.theta)+Real.exp (-(m:ℝ)*(P.pi/2)^(2*((n:ℝ)*P.theta))) := by
  have hc := familyMaskedSignMaximum_all_active_real_bound P n m (by positivity : 0≤2*((n:ℝ)*P.theta))
  have ht := familyActivationCount_upper_tail P n m (show (n:ℝ)*P.theta<2*((n:ℝ)*P.theta) by linarith)
  have he : ((n:ℝ)*P.theta)/(2*((n:ℝ)*P.theta)-(n:ℝ)*P.theta)^2=1/((n:ℝ)*P.theta) := by
    rw [show 2*((n:ℝ)*P.theta)-(n:ℝ)*P.theta=(n:ℝ)*P.theta by ring]
    rw [pow_two,div_mul_eq_div_div,div_self hk.ne']
  rw [he] at ht
  exact hc.trans (add_le_add_right ht _)

theorem familyMasked_printed_failure_coverage_bound
    (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] {ell : ℝ}
    (hk : 0<(n:ℝ)*P.theta)
    (hcover : Real.exp (ell/4)≤(m:ℝ)*(P.pi/2)^(2*((n:ℝ)*P.theta))) :
    (familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z≠familyActivationCount z}≤
      1/((n:ℝ)*P.theta)+Real.exp (-Real.exp (ell/4)) := by
  apply (familyMasked_printed_failure_bound P n m hk).trans
  apply add_le_add_left
  apply Real.exp_le_exp.mpr
  nlinarith

end
end RectangleCLT.Companion.SplitV4.Printed
