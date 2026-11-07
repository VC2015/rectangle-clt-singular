import RectangleCLTCompanion.SplitV4.GaussianExtremeCalibration
import RectangleCLTCompanion.SplitV4.SymmetricFamilyMaximum
import RectangleCLTCompanion.LowerMaxCDFProduct

/-! Genuine moments of finite independent standard Gaussian maxima. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

private theorem linearProjectionFamily_identity (m : ℕ) (z : Vector m) :
    linearProjectionFamily (1 : Matrix (Fin m) (Fin m) ℝ) z = z := by
  simpa only [linearProjectionFamily, Matrix.mulVec, dotProduct] using Matrix.one_mulVec z

private theorem identity_projection_row_variance (m : ℕ) (i : Fin m) :
    (∑ j, (1 : Matrix (Fin m) (Fin m) ℝ) i j ^ 2) ≤ 1 := by
  classical
  simp [Matrix.one_apply]

private theorem gaussian_norm_sq_weighted_bound {m : ℕ} (hm : 1 ≤ m) :
    Integrable (fun z : Vector m => Real.exp (‖z‖/Real.sqrt (dimensionLog m))*(1+‖z‖)^2)
      (standardGaussian m) ∧
    (∫ z : Vector m, Real.exp (‖z‖/Real.sqrt (dimensionLog m))*(1+‖z‖)^2
      ∂standardGaussian m) ≤ dimensionLog m*Real.exp (11/2) := by
  letI : NeZero m := ⟨by omega⟩
  have hL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one hm
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hcard : 2*(Fintype.card (Fin m) : ℝ) ≤ Real.exp (1*dimensionLog m) := by
    rw [one_mul, dimensionLog, Real.exp_log (mul_pos (Real.exp_pos _) hmp), Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right he hmp.le
  have hh := projectionMaximum_weighted_moment_le (1 : Matrix (Fin m) (Fin m) ℝ)
    (identity_projection_row_variance m) (fun z : Vector m => ‖z‖) measurable_norm
    (fun _ => norm_nonneg _) hL hcard
    (d := 1) (fun z => by simp [linearProjectionFamily_identity])
    (M := Real.sqrt (dimensionLog m)) le_rfl 2
  norm_num only [Nat.cast_ofNat, one_mul] at hh
  have hL0 : 0 ≤ dimensionLog m := by linarith
  rw [Real.sq_sqrt hL0] at hh
  norm_num at hh
  exact hh

theorem integrable_gaussian_norm_sq {m : ℕ} (hm : 1 ≤ m) :
    Integrable (fun z : Vector m => ‖z‖^2) (standardGaussian m) := by
  have hh := (gaussian_norm_sq_weighted_bound hm).1
  apply hh.mono' (measurable_norm.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have he : 1 ≤ Real.exp (‖z‖/Real.sqrt (dimensionLog m)) :=
      Real.one_le_exp_iff.mpr (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    have hs : ‖z‖^2 ≤ (1+‖z‖)^2 := by nlinarith [norm_nonneg z]
    exact hs.trans (le_mul_of_one_le_left (sq_nonneg _) he)

theorem integral_gaussian_norm_sq_le {m : ℕ} (hm : 1 ≤ m) :
    (∫ z : Vector m, ‖z‖^2 ∂standardGaussian m) ≤ dimensionLog m*Real.exp (11/2) := by
  apply le_trans (integral_mono (integrable_gaussian_norm_sq hm)
    (gaussian_norm_sq_weighted_bound hm).1 ?_) (gaussian_norm_sq_weighted_bound hm).2
  intro z
  have he : 1 ≤ Real.exp (‖z‖/Real.sqrt (dimensionLog m)) :=
    Real.one_le_exp_iff.mpr (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hs : ‖z‖^2 ≤ (1+‖z‖)^2 := by nlinarith [norm_nonneg z]
  exact hs.trans (le_mul_of_one_le_left (sq_nonneg _) he)

theorem abs_finiteMaximum_le_norm {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ) :
    |finiteMaximum z| ≤ ‖z‖ := by
  obtain ⟨i, hi⟩ := finiteMaximum_attains z
  rw [← hi]
  exact (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i)

theorem integrable_finiteGaussianMaximum_sq (m : ℕ) [NeZero m] :
    Integrable (fun z : Vector m => (finiteMaximum z)^2) (standardGaussian m) := by
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  apply (integrable_gaussian_norm_sq hm).mono'
    ((measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j)).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_finiteMaximum_le_norm z) 2

theorem integral_finiteGaussianMaximum_sq_le (m : ℕ) [NeZero m] :
    (∫ z : Vector m, (finiteMaximum z)^2 ∂standardGaussian m) ≤ dimensionLog m*Real.exp (11/2) := by
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  apply le_trans (integral_mono (integrable_finiteGaussianMaximum_sq m)
    (integrable_gaussian_norm_sq hm) ?_) (integral_gaussian_norm_sq_le hm)
  intro z
  dsimp only
  rw [← sq_abs (finiteMaximum z)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_finiteMaximum_le_norm z) 2

theorem integrable_finiteGaussianMaximum (m : ℕ) [NeZero m] :
    Integrable (fun z : Vector m => finiteMaximum z) (standardGaussian m) := by
  apply ((integrable_const (1 : ℝ)).add (integrable_finiteGaussianMaximum_sq m)).mono'
    (measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j)).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs]
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg (|finiteMaximum z|-1), sq_abs (finiteMaximum z)]

theorem finiteGaussianMaximum_cdf (m : ℕ) [NeZero m] (t : ℝ) :
    (standardGaussian m).real {z : Vector m | finiteMaximum z ≤ t} = normalMaximumCDF m t := by
  have he : {z : Vector m | finiteMaximum z ≤ t} = {z : Vector m | ∀ j, z j ≤ t} := by
    ext z
    exact ⟨fun h j => (le_finiteMaximum z j).trans h, finiteMaximum_le z⟩
  rw [he]
  exact standardGaussian_maximum_CDF m t


private theorem integrable_exp_finiteGaussianMaximum (m : ℕ) [NeZero m] (t : ℝ) :
    Integrable (fun z : Vector m => Real.exp (t*finiteMaximum z)) (standardGaussian m) := by
  have hi (j : Fin m) : Integrable (fun z : Vector m => Real.exp (t*z j)) (standardGaussian m) :=
    mgf_pos_iff.mp (by rw [standardGaussian_mgf_coordinate]; positivity)
  apply (integrable_finset_sum Finset.univ (fun j _ => hi j)).mono'
    (((measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j)).const_mul t).exp).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    obtain ⟨j, hj⟩ := finiteMaximum_attains z
    rw [← hj]
    exact Finset.single_le_sum (fun k _ => Real.exp_nonneg (t*z k)) (Finset.mem_univ j)

theorem integral_exp_finiteGaussianMaximum_le (m : ℕ) [NeZero m] (t : ℝ) :
    (∫ z : Vector m, Real.exp (t*finiteMaximum z) ∂standardGaussian m) ≤
      (m : ℝ)*Real.exp (t^2/2) := by
  have hi (j : Fin m) : Integrable (fun z : Vector m => Real.exp (t*z j)) (standardGaussian m) :=
    mgf_pos_iff.mp (by rw [standardGaussian_mgf_coordinate]; positivity)
  calc
    _ ≤ ∫ z : Vector m, ∑ j, Real.exp (t*z j) ∂standardGaussian m := by
      apply integral_mono (integrable_exp_finiteGaussianMaximum m t)
        (integrable_finset_sum Finset.univ (fun j _ => hi j))
      intro z
      obtain ⟨j, hj⟩ := finiteMaximum_attains z
      dsimp only
      rw [← hj]
      exact Finset.single_le_sum (fun k _ => Real.exp_nonneg (t*z k)) (Finset.mem_univ j)
    _ = (m : ℝ)*Real.exp (t^2/2) := by
      rw [integral_finset_sum _ (fun j _ => hi j)]
      have he (j : Fin m) : (∫ z : Vector m, Real.exp (t*z j) ∂standardGaussian m) = Real.exp (t^2/2) :=
        standardGaussian_mgf_coordinate m j t
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The sharp first-order upper bound has coefficient one. -/
theorem integral_finiteGaussianMaximum_le_sqrt_log {m : ℕ} (hm : 2 ≤ m) :
    letI : NeZero m := ⟨by omega⟩
    (∫ z : Vector m, finiteMaximum z ∂standardGaussian m) ≤ Real.sqrt (2*Real.log (m : ℝ)) := by
  letI : NeZero m := ⟨by omega⟩
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hl : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  let t := Real.sqrt (2*Real.log (m : ℝ))
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht2 : t^2 = 2*Real.log (m : ℝ) := Real.sq_sqrt (by positivity)
  have hj := exp_integral_le_integral_exp ((integrable_finiteGaussianMaximum m).const_mul t)
    (integrable_exp_finiteGaussianMaximum m t)
  rw [integral_const_mul] at hj
  have hh := hj.trans (integral_exp_finiteGaussianMaximum_le m t)
  have he : (m : ℝ)*Real.exp (t^2/2) = Real.exp (Real.log (m : ℝ)+t^2/2) := by
    rw [Real.exp_add, Real.exp_log hmp]
  rw [he] at hh
  have hh' := Real.exp_le_exp.mp hh
  change (∫ z : Vector m, finiteMaximum z ∂standardGaussian m) ≤ t
  nlinarith

theorem integral_abs_standardGaussian_coordinate_le_one (m : ℕ) (j : Fin m) :
    (∫ z : Vector m, |z j| ∂standardGaussian m) ≤ 1 := by
  have hh := integral_mono (standardGaussian_integrable_coordinate m j).abs
    (((integrable_const (1 : ℝ)).add (standardGaussian_integrable_coordinate_pow m j 2)).div_const 2)
    (fun z => show |z j| ≤ (1+(z j)^2)/2 by nlinarith [sq_nonneg (|z j|-1), sq_abs (z j)])
  simpa only [Pi.add_apply, integral_div, integral_add (integrable_const (1 : ℝ))
    (standardGaussian_integrable_coordinate_pow m j 2), integral_const,
    measureReal_univ_eq_one, one_smul, standardGaussian_integral_coordinate_sq, one_add_one_eq_two,
    div_self (by norm_num : (2 : ℝ) ≠ 0)] using hh

theorem finiteGaussianMaximum_tail (m : ℕ) [NeZero m] (t : ℝ) :
    (standardGaussian m).real {z : Vector m | t < finiteMaximum z} = 1-normalMaximumCDF m t := by
  have hm := measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j)
  have he : {z : Vector m | t < finiteMaximum z} = {z : Vector m | finiteMaximum z ≤ t}ᶜ := by
    ext z; simp
  rw [he, measureReal_compl (measurableSet_le hm measurable_const), measureReal_univ_eq_one,
    finiteGaussianMaximum_cdf]

theorem integral_finiteGaussianMaximum_lower (m : ℕ) [NeZero m] (t : ℝ) :
    t*(1-normalMaximumCDF m t)-1 ≤ ∫ z : Vector m, finiteMaximum z ∂standardGaussian m := by
  let j : Fin m := ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩
  let S := {z : Vector m | t < finiteMaximum z}
  have hS : MeasurableSet S := measurableSet_lt measurable_const
    (measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j))
  have hi := integral_mono ((integrable_const t).indicator hS)
    ((integrable_finiteGaussianMaximum m).add (standardGaussian_integrable_coordinate m j).abs)
    (fun z => show S.indicator (fun _ => t) z ≤ finiteMaximum z+|z j| by
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz]
        exact (le_of_lt hz).trans (le_add_of_nonneg_right (abs_nonneg _))
      · rw [Set.indicator_of_not_mem hz]
        have hh := le_finiteMaximum z j
        have hh' := neg_abs_le (z j)
        linarith)
  simp only [Pi.add_apply] at hi
  rw [integral_indicator_const t hS,
    integral_add (integrable_finiteGaussianMaximum m) (standardGaussian_integrable_coordinate m j).abs,
    smul_eq_mul] at hi
  dsimp only [S] at hi
  rw [finiteGaussianMaximum_tail] at hi
  have ha := integral_abs_standardGaussian_coordinate_le_one m j
  nlinarith

def gaussianMaximumMean (m : ℕ) : ℝ :=
  if hm : 1 ≤ m then
    letI : NeZero m := ⟨by omega⟩
    ∫ z : Vector m, finiteMaximum z ∂standardGaussian m
  else 0

theorem gaussianMaximumMean_eq_integral (m : ℕ) [NeZero m] :
    gaussianMaximumMean m = ∫ z : Vector m, finiteMaximum z ∂standardGaussian m := by
  simp only [gaussianMaximumMean, dif_pos (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m))]

theorem tendsto_gaussianMaximumMean_div_sqrt_log :
    Tendsto (fun m : ℕ => gaussianMaximumMean m / Real.sqrt (2*Real.log (m : ℝ)))
      atTop (𝓝 1) := by
  have htop : Tendsto (fun m : ℕ => 2*Real.log (m : ℝ)) atTop atTop :=
    tendsto_const_nhds.pos_mul_atTop (by norm_num : (0 : ℝ) < 2)
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun m : ℕ => Real.sqrt (2*Real.log (m : ℝ))) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [htop.eventually (eventually_ge_atTop (b^2))] with m hm
    exact Real.le_sqrt_of_sq_le hm
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨a, ha, ha1⟩ := exists_between (show max b 0 < (1 : ℝ) from max_lt hb zero_lt_one)
    have ha0 : 0 < a := lt_of_le_of_lt (le_max_right b 0) ha
    have hba : b < a := lt_of_le_of_lt (le_max_left b 0) ha
    have hk : Tendsto (fun m : ℕ => a*(normalMaxThreshold m/Real.sqrt (2*Real.log (m : ℝ)))*
        (1-normalMaximumCDF m (a*normalMaxThreshold m))-1/Real.sqrt (2*Real.log (m : ℝ)))
        atTop (𝓝 a) := by
      have hh := ((tendsto_normalMaxThreshold_div_sqrt_two_log.const_mul a).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_normalMaximumCDF_below_threshold ha0 ha1))).sub
        ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hs)
      simpa using hh
    filter_upwards [hk.eventually (eventually_gt_nhds hba), eventually_ge_atTop 2] with m hm hm2
    letI : NeZero m := ⟨by omega⟩
    have hs0 : 0 < Real.sqrt (2*Real.log (m : ℝ)) := Real.sqrt_pos.mpr
      (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast (show 1 < m by omega))))
    have hl := div_le_div_of_nonneg_right (integral_finiteGaussianMaximum_lower m (a*normalMaxThreshold m)) hs0.le
    rw [← gaussianMaximumMean_eq_integral] at hl
    apply hm.trans_le
    convert hl using 1 <;> ring
  · intro b hb
    filter_upwards [eventually_ge_atTop 2] with m hm
    letI : NeZero m := ⟨by omega⟩
    have hs0 : 0 < Real.sqrt (2*Real.log (m : ℝ)) := Real.sqrt_pos.mpr
      (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast (show 1 < m by omega))))
    have hh := (div_le_one hs0).mpr (integral_finiteGaussianMaximum_le_sqrt_log hm)
    rw [← gaussianMaximumMean_eq_integral] at hh
    exact hh.trans_lt hb

end
end RectangleCLT.Companion.SplitV4
