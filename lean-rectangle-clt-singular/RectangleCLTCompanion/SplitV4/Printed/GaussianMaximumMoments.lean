import RectangleCLTCompanion.SplitV4.GaussianExtremeMoments
import RectangleCLTCompanion.SubexponentialGaussian
import RectangleCLTCompanion.SplitV4.Printed.Bernstein

/-! Printed Gaussian maximum moment argument at `sym:eq:gaussian-max`:
Mills/CDF concentration, actual integration of the `2m` union tail, a
uniform squared-moment bound, uniform integrability, and convergence of
expectations. The earlier one-sided-expectation/MGF proof is preserved. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- Elementary integrability from the finite sum of coordinate second
moments, before the sharper tail integral is evaluated. -/
theorem integrable_gaussian_norm_sq_direct (m : ℕ) :
    Integrable (fun z : Vector m => ‖z‖ ^ 2) (standardGaussian m) := by
  have hi : Integrable (fun z : Vector m => ∑ j, z j ^ 2) (standardGaussian m) :=
    integrable_finset_sum _ (fun j _ => standardGaussian_integrable_coordinate_pow m j 2)
  apply hi.mono' (measurable_norm.pow_const 2).aestronglyMeasurable
  refine ae_of_all _ (fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z‖)]
  have hs : 0 ≤ ∑ j : Fin m, z j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : ‖z‖ ≤ Real.sqrt (∑ j : Fin m, z j ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    have hj : z j ^ 2 ≤ ∑ k : Fin m, z k ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (z k)) (Finset.mem_univ j)
    have hjabs : |z j| ^ 2 ≤ ∑ k : Fin m, z k ^ 2 := by simpa only [sq_abs] using hj
    have hh := Real.le_sqrt_of_sq_le hjabs
    simpa only [Real.norm_eq_abs] using hh
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ j : Fin m, z j ^ 2), norm_nonneg z]

theorem integrable_finiteGaussianMaximum_sq_direct (m : ℕ) [NeZero m] :
    Integrable (fun z : Vector m => finiteMaximum z ^ 2) (standardGaussian m) := by
  apply (integrable_gaussian_norm_sq_direct m).mono'
    ((measurable_finiteMaximum (fun j (z : Vector m) => z j)
      (fun j => measurable_pi_apply j)).pow_const 2).aestronglyMeasurable
  refine ae_of_all _ (fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_finiteMaximum_le_norm z) 2

theorem integrable_finiteGaussianMaximum_direct (m : ℕ) [NeZero m] :
    Integrable (fun z : Vector m => finiteMaximum z) (standardGaussian m) := by
  apply ((integrable_const (1 : ℝ)).add (integrable_finiteGaussianMaximum_sq_direct m)).mono'
    (measurable_finiteMaximum (fun j (z : Vector m) => z j)
      (fun j => measurable_pi_apply j)).aestronglyMeasurable
  refine ae_of_all _ (fun z => ?_)
  rw [Real.norm_eq_abs]
  change |finiteMaximum z| ≤ 1 + finiteMaximum z ^ 2
  nlinarith [sq_nonneg (|finiteMaximum z| - 1), sq_abs (finiteMaximum z)]

/-- The actual union bound printed before integrating the second moment. -/
theorem gaussian_norm_tail_union (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (standardGaussian m).real {z : Vector m | y < ‖z‖} ≤
      min 1 ((2 * (m : ℝ)) * Real.exp (-(y ^ 2) / 2)) := by
  have hh := standardGaussian_rectangular_norm_tail
    (1 : Matrix (Fin m) (Fin m) ℝ) (τ := 1) (s := y ^ 2 / 2)
    (by norm_num) (by positivity)
    (fun j => by
      classical
      simp [Matrix.one_apply])
  have he : Real.sqrt (2 * (y ^ 2 / 2)) = y := by
    rw [show 2 * (y ^ 2 / 2) = y ^ 2 by ring, Real.sqrt_sq hy]
  simp only [one_mul, Matrix.one_mulVec, he] at hh
  exact le_min measureReal_le_one (by simpa only [neg_div] using hh)

/-- Apply the preceding tail bound to the squared supremum norm. -/
theorem gaussian_norm_sq_tail_union (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (standardGaussian m).real {z : Vector m | r < ‖z‖ ^ 2} ≤
      min 1 ((2 * (m : ℝ)) * Real.exp (-r / 2)) := by
  have he : {z : Vector m | r < ‖z‖ ^ 2} = {z : Vector m | Real.sqrt r < ‖z‖} := by
    ext z
    exact (Real.sqrt_lt hr (norm_nonneg z)).symm
  rw [he]
  simpa only [Real.sq_sqrt hr] using gaussian_norm_tail_union m (Real.sqrt_nonneg r)

/-- Literal layer-cake integration of `min(1,2m exp(-y²/2))`. -/
theorem integral_gaussian_norm_sq_by_union_tail {m : ℕ} (hm : 1 ≤ m) :
    (∫ z : Vector m, ‖z‖ ^ 2 ∂standardGaussian m) ≤
      2 * Real.log (2 * (m : ℝ)) + 2 := by
  let a := 2 * Real.log (2 * (m : ℝ))
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha : 0 ≤ a := mul_nonneg (by norm_num) (Real.log_nonneg (by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith))
  let E : Vector m → ℝ := fun z => max (‖z‖ ^ 2 - a) 0
  have hi := integrable_gaussian_norm_sq_direct m
  have hE : Integrable E (standardGaussian m) :=
    (hi.sub (integrable_const a)).sup (integrable_const 0)
  have htail (r : ℝ) (hr : 0 < r) :
      (standardGaussian m).real {z | r < E z} ≤ Real.exp (-(1 / 2 : ℝ) * r) := by
    have hsub : {z : Vector m | r < E z} ⊆ {z | a + r < ‖z‖ ^ 2} := by
      intro z hz
      have h : r < ‖z‖ ^ 2 - a := (lt_max_iff.mp hz).resolve_right (not_lt.mpr hr.le)
      change a + r < ‖z‖ ^ 2
      linarith
    have ht := (measureReal_mono hsub).trans
      ((gaussian_norm_sq_tail_union m (by linarith : 0 ≤ a + r)).trans (min_le_right _ _))
    have he : (2 * (m : ℝ)) * Real.exp (-(a + r) / 2) =
        Real.exp (-(1 / 2 : ℝ) * r) := by
      rw [← Real.exp_log (by positivity : 0 < 2 * (m : ℝ)), ← Real.exp_add]
      congr 1
      dsimp [a]
      ring
    exact ht.trans_eq he
  have hint : (∫ r in Ioi (0 : ℝ), (standardGaussian m).real {z | r < E z}) ≤ 2 := by
    have h := integral_mono_of_nonneg (ae_of_all _ (fun _ => measureReal_nonneg))
      (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0)
      ((ae_restrict_mem measurableSet_Ioi).mono (fun r hr => htail r hr))
    have he : (∫ r in Ioi (0 : ℝ), Real.exp (-(1 / 2 : ℝ) * r)) = 2 := by
      rw [integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0]
      norm_num
    exact h.trans_eq he
  have hEb : (∫ z, E z ∂standardGaussian m) ≤ 2 := by
    rw [hE.integral_eq_integral_meas_lt (ae_of_all _ (fun _ => le_max_right _ _))]
    exact hint
  have hu := integral_mono hi ((integrable_const a).add hE)
    (fun z : Vector m => by change ‖z‖ ^ 2 ≤ a + E z; dsimp [E]; linarith [le_max_left (‖z‖ ^ 2 - a) 0])
  change (∫ z, ‖z‖ ^ 2 ∂standardGaussian m) ≤ ∫ z, a + E z ∂standardGaussian m at hu
  rw [integral_add (integrable_const a) hE] at hu
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hu
  exact hu.trans (add_le_add_left hEb a)

/-- A dimension-uniform logarithmic second moment from the printed tail. -/
theorem integral_gaussian_norm_sq_le_four_dimensionLog {m : ℕ} (hm : 1 ≤ m) :
    (∫ z : Vector m, ‖z‖ ^ 2 ∂standardGaussian m) ≤ 4 * dimensionLog m := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  apply (integral_gaussian_norm_sq_by_union_tail hm).trans
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmp.ne']
  unfold dimensionLog
  rw [Real.log_mul (Real.exp_pos 1).ne' hmp.ne', Real.log_exp]
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlm := Real.log_nonneg (show (1 : ℝ) ≤ m by exact_mod_cast hm)
  linarith

/-- The CDF-power inequality in the printed maximum convergence argument. -/
theorem one_sub_pow_le_nat_mul_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    1 - x ^ m ≤ (m : ℝ) * (1 - x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hh := mul_le_mul_of_nonneg_left ih hx0
    have hnonneg : 0 ≤ (m : ℝ) * (1 - x) ^ 2 := by positivity
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Above a fixed factor larger than the Mills threshold the tail mass
vanishes, complementing the preserved below-threshold divergence proof. -/
theorem tendsto_normalTail_mass_above_max_threshold {a : ℝ} (ha : 1 < a) :
    Tendsto (fun m : ℕ => (m : ℝ) * standardNormalUpperTail (a * normalMaxThreshold m))
      atTop (𝓝 0) := by
  have hapos : 0 < a := zero_lt_one.trans ha
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_log_normalTail_below_max_threshold hapos)
  have hr' : Tendsto (fun m : ℕ => Real.log ((m : ℝ) *
      standardNormalUpperTail (a * normalMaxThreshold m)) / Real.log (m : ℝ))
      atTop (𝓝 (1 - a ^ 2)) := by
    apply hr.congr'
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [Real.log_mul hmp.ne' (standardNormalUpperTail_pos _).ne']
    have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    field_simp
  have hh := hlog.atTop_mul_neg (by nlinarith : 1 - a ^ 2 < 0) hr'
  have hh' : Tendsto (fun m : ℕ => Real.log ((m : ℝ) *
      standardNormalUpperTail (a * normalMaxThreshold m))) atTop atBot := by
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 2] with m hm
    have hl : Real.log (m : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
    field_simp
  apply (Real.tendsto_exp_atBot.comp hh').congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact Real.exp_log (mul_pos (by exact_mod_cast (show 0 < m by omega)) (standardNormalUpperTail_pos _))

theorem tendsto_normalMaximumCDF_tail_above_threshold {a : ℝ} (ha : 1 < a) :
    Tendsto (fun m : ℕ => 1 - normalMaximumCDF m (a * normalMaxThreshold m)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_normalTail_mass_above_max_threshold ha)
  · exact Eventually.of_forall (fun m => sub_nonneg.mpr
      (pow_le_one₀ (standardNormalCDF_nonneg _) (standardNormalCDF_le_one _) ))
  · exact Eventually.of_forall (fun m => by
      simpa only [normalMaximumCDF, standardNormalUpperTail_eq_one_sub] using
        one_sub_pow_le_nat_mul_one_sub (standardNormalCDF_nonneg (a * normalMaxThreshold m))
          (standardNormalCDF_le_one _) m)

end
end RectangleCLT.Companion.SplitV4.Printed
