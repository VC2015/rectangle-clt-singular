import RectangleCLTCompanion.SplitV4.SymmetricFamilyUnmasked
import RectangleCLTCompanion.SplitV4.LowerCalibrationScales

/-! The actual parameter sequence for the bounded symmetric lower construction. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def unmaskedUnitParameters (θ : ℝ) (hθ0 : 0 < θ) (hθhalf : θ < 1 / 2) : SymmetricFamilyParameters where
  theta := θ
  pi := 1
  amplitude := 1
  theta_pos := hθ0
  theta_le_one := by linarith
  pi_pos := by norm_num
  pi_le_one := le_rfl
  amplitude_pos := by norm_num
  variance_lt_half := by simpa only [one_pow, mul_one] using hθhalf

def boundedFamilyParameters (n m : ℕ) : SymmetricFamilyParameters :=
  if h : 0 < Real.log (m : ℝ) / (2 * n) ∧ Real.log (m : ℝ) / (2 * n) < 1 / 2 then
    unmaskedUnitParameters (Real.log (m : ℝ) / (2 * n)) h.1 h.2
  else unmaskedUnitParameters (1 / 4) (by norm_num) (by norm_num)

theorem boundedFamilyParameters_pi (n m : ℕ) : (boundedFamilyParameters n m).pi = 1 := by
  unfold boundedFamilyParameters
  split_ifs <;> rfl

theorem boundedFamilyParameters_amplitude (n m : ℕ) : (boundedFamilyParameters n m).amplitude = 1 := by
  unfold boundedFamilyParameters
  split_ifs <;> rfl

theorem boundedFamilyParameters_theta {n m : ℕ}
    (hθ0 : 0 < Real.log (m : ℝ) / (2 * n)) (hθhalf : Real.log (m : ℝ) / (2 * n) < 1 / 2) :
    (boundedFamilyParameters n m).theta = Real.log (m : ℝ) / (2 * n) := by
  have hgood : 0 < Real.log (m : ℝ) / (2 * n) ∧ Real.log (m : ℝ) / (2 * n) < 1 / 2 := ⟨hθ0, hθhalf⟩
  simp only [boundedFamilyParameters, dif_pos hgood, unmaskedUnitParameters]

theorem boundedFamilyParameters_variance (n m : ℕ) :
    (boundedFamilyParameters n m).variance = (boundedFamilyParameters n m).theta := by
  simp only [SymmetricFamilyParameters.variance, boundedFamilyParameters_pi,
    boundedFamilyParameters_amplitude, one_pow, mul_one]

theorem familyScale_le_one (P : SymmetricFamilyParameters) : P.scale ≤ 1 := by
  have hs := P.scale_sq
  nlinarith only [P.scale_pos, P.variance_pos, hs]

theorem boundedFamily_observations_envelope (n m : ℕ) (i : Fin n) (z : Fin n → FamilySeed m) :
    ‖familyRawObservations (boundedFamilyParameters n m) i z‖ ≤ 2 := by
  exact (familyObservation_envelope (boundedFamilyParameters n m) (z i)).trans
    (by rw [boundedFamilyParameters_amplitude]; have := familyScale_le_one (boundedFamilyParameters n m); linarith)

theorem boundedFamilyParameters_eventually_theta {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, (boundedFamilyParameters n (m n)).theta = Real.log (m n : ℝ) / (2 * n) := by
  have hEll : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hθ := tendsto_lower_activation_probability hEll hsmall
  filter_upwards [eventually_ge_atTop 1, hθ.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with n hn hhalf
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hmp : (1 : ℝ) < m n := by exact_mod_cast hm n
  exact boundedFamilyParameters_theta (div_pos (Real.log_pos hmp) (by positivity)) hhalf

theorem tendsto_boundedFamily_variance {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (boundedFamilyParameters n (m n)).variance) atTop (𝓝 0) := by
  have hEll : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  apply (tendsto_lower_activation_probability hEll hsmall).congr'
  filter_upwards [boundedFamilyParameters_eventually_theta hm hmTop hsmall] with n hn
  rw [boundedFamilyParameters_variance, hn]

theorem tendsto_boundedFamily_scale {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (boundedFamilyParameters n (m n)).scale) atTop (𝓝 1) := by
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_boundedFamily_variance hm hmTop hsmall))
  simpa only [sub_zero, Real.sqrt_one, SymmetricFamilyParameters.scale, Function.comp_apply] using hh

theorem boundedFamilyParameters_eventually_count {m : ℕ → ℕ} (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ) ^ 3 / n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) * (boundedFamilyParameters n (m n)).theta = Real.log (m n : ℝ) / 2 := by
  filter_upwards [boundedFamilyParameters_eventually_theta hm hmTop hsmall, eventually_ge_atTop 1] with n hn hn1
  rw [hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn1)
  field_simp
  ring

end
end RectangleCLT.Companion.SplitV4
