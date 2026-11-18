import RectangleCLTArxivV1.LowerLeadingDensity

/-! The upper half of the printed uniform leading-density calibration.
Only a convergent density asymptotic and its finite prefix are needed. -/
namespace RectangleCLTArxivV1
open Filter RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped Topology
noncomputable section
set_option autoImplicit false

theorem positive_global_upper_of_eventual {f : ℕ → ℝ} {c : ℝ}
    (he : ∀ᶠ n in atTop, f n ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  let S := Finset.range (N+1)
  have hS : S.Nonempty := ⟨0,Finset.mem_range.mpr (by omega)⟩
  let b := S.sup' hS f
  refine ⟨max 1 (max c b), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro n
  by_cases hn : n < N+1
  · exact (Finset.le_sup' f (Finset.mem_range.mpr hn)).trans
      ((le_max_right c b).trans (le_max_right 1 (max c b)))
  · exact (hN n (by omega)).trans
      ((le_max_left c b).trans (le_max_right 1 (max c b)))

theorem eventually_leadingDensity_sqrt_upper :
    ∀ᶠ r : ℕ in atTop,
      normalMaximumDensity r (lowerLeadingThreshold r) ≤
        (2*(Real.exp (-1)+1))*Real.sqrt (dimensionLog r) := by
  have hd := Printed.tendsto_normalMaximumDensity_at_printed_threshold_div_sqrt_log.eventually
    (eventually_lt_nhds (lt_add_one (Real.exp (-1))))
  filter_upwards [hd,eventually_ge_atTop 2] with r hr hr2
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0<r)
  have hr1 : (1:ℝ) < r := by exact_mod_cast (by omega : 1<r)
  have hlog : 0 < Real.log (r:ℝ) := Real.log_pos hr1
  have hroot : 0 < Real.sqrt (2*Real.log (r:ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hh := (div_le_iff₀ hroot).mp hr.le
  have hdim : dimensionLog r = 1+Real.log (r:ℝ) := by
    rw [dimensionLog,Real.log_mul (Real.exp_ne_zero _) hr0.ne',Real.log_exp]
  have hs : Real.sqrt (2*Real.log (r:ℝ)) ≤ 2*Real.sqrt (dimensionLog r) := by
    have hL0 : 0≤dimensionLog r := by rw [hdim]; positivity
    nlinarith [Real.sqrt_nonneg (2*Real.log (r:ℝ)),
      Real.sqrt_nonneg (dimensionLog r), Real.sq_sqrt hL0,
      Real.sq_sqrt (show 0≤2*Real.log (r:ℝ) by positivity)]
  rw [lowerLeadingThreshold,if_neg (by omega : r≠1)]
  calc
    _ ≤ (Real.exp (-1)+1)*(2*Real.sqrt (dimensionLog r)) :=
      hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    _ = _ := by ring

theorem exists_leadingDensity_sqrt_upper :
    ∃ C : ℝ, 0<C ∧ ∀ r, 1≤r →
      normalMaximumDensity r (lowerLeadingThreshold r) ≤ C*Real.sqrt (dimensionLog r) := by
  have he : ∀ᶠ r : ℕ in atTop,
      normalMaximumDensity r (lowerLeadingThreshold r)/Real.sqrt (dimensionLog r) ≤
        2*(Real.exp (-1)+1) := by
    filter_upwards [eventually_leadingDensity_sqrt_upper,eventually_ge_atTop 1] with r hr hr1
    exact (div_le_iff₀ (Real.sqrt_pos.mpr
      (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hr1)))).mpr hr
  obtain ⟨C,hC,hbound⟩ := positive_global_upper_of_eventual he
  refine ⟨C,hC,?_⟩
  intro r hr
  exact (div_le_iff₀ (Real.sqrt_pos.mpr
    (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hr)))).mp (hbound r)

theorem exists_leadingDensity_width_upper :
    ∃ C : ℝ, 0<C ∧ ∀ r, 1≤r →
      normalMaximumDensity r (lowerLeadingThreshold r) ≤ C*independentAbsGaussianMean r := by
  obtain ⟨C,hC,hupper⟩ := exists_leadingDensity_sqrt_upper
  obtain ⟨c,hc,hlower⟩ := exists_absoluteGaussianMean_sqrt_lower
  refine ⟨C/c,div_pos hC hc,?_⟩
  intro r hr
  have h := mul_le_mul_of_nonneg_left (hlower r hr) (div_nonneg hC.le hc.le)
  have he : C/c*(c*Real.sqrt (dimensionLog r))=C*Real.sqrt (dimensionLog r) := by
    field_simp [hc.ne']
    ring
  exact (hupper r hr).trans (he ▸ h)

theorem exists_leadingDensity_width_comparable :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ r, 1≤r →
      c*independentAbsGaussianMean r ≤ normalMaximumDensity r (lowerLeadingThreshold r) ∧
      normalMaximumDensity r (lowerLeadingThreshold r) ≤ C*independentAbsGaussianMean r := by
  obtain ⟨c,hc,hlo⟩ := exists_leadingDensity_width_lower
  obtain ⟨C,hC,hhi⟩ := exists_leadingDensity_width_upper
  exact ⟨c,C,hc,hC,fun r hr => ⟨hlo r hr,hhi r hr⟩⟩
end
end RectangleCLTArxivV1
