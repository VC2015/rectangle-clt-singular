import RectangleCLTArxivV1.GaussianIdentityWidth
import RectangleCLTCompanion.LowerConstruction
import RectangleCLTCompanion.SplitV4.Printed.SkewLowerMaintext

/-! Theorem 3: the genuine independent-coordinate two-point construction,
with the exact actual Gaussian-width normalization and lower constant.
Only the intrinsic rate is assumed to vanish; the old logarithmic rate is
derived from the proved Gaussian mean asymptotic. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion Filter
open scoped BigOperators Topology
noncomputable section

def skewIntrinsicRate (B : ℝ) (p n : ℕ) : ℝ :=
  (B/Real.sqrt (n:ℝ))*independentAbsGaussianMean p*dimensionLog p

/-- The intrinsic parameter is exactly the actual Gaussian width for the
identity covariance, with the normalization used in the paper. -/
theorem skewIntrinsicRate_eq_gaussianWidth (B : ℝ) (p n : ℕ) :
    skewIntrinsicRate B p n = B*gaussianMaximumMean (1:Matrix (Fin p) (Fin p) ℝ)*
      dimensionLog p/Real.sqrt (n:ℝ) := by
  rw [skewIntrinsicRate,independentAbsGaussianMean_eq]
  ring

theorem skewIntrinsicRate_pos {B : ℝ} (hB : 2 ≤ B) {p n : ℕ}
    (hp : 1 ≤ p) (hn : 1 ≤ n) : 0 < skewIntrinsicRate B p n := by
  have hg : 0 < independentAbsGaussianMean p :=
    (by positivity : (0:ℝ) < Real.sqrt (2/Real.pi)).trans_le (independentAbsGaussianMean_lower hp)
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  exact mul_pos (mul_pos (div_pos (by linarith) (Real.sqrt_pos.mpr hn0)) hg)
    (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp))

theorem skewIntrinsicRate_div_old_tendsto {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop) :
    Tendsto (fun n => skewIntrinsicRate (B n) (p n) n/lowerSkewRate (B n) (p n) n)
      atTop (𝓝 (Real.sqrt 2)) := by
  have hw := tendsto_independentAbsGaussianMean_div_sqrt_two_log.comp hp
  have hL := RectangleCLT.Companion.SplitV4.Printed.dimensionLog_nat_log_ratio.comp hp
  have hh := (hw.mul hL).mul_const (Real.sqrt 2)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 2),eventually_ge_atTop 1] with n hpn hn
  have hlog : 0 < Real.log (p n:ℝ) := Real.log_pos (by exact_mod_cast hpn)
  have hBn : B n ≠ 0 := by have := hB n; linarith
  have hN : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hn : (0:ℝ) < n)).ne'
  have hroot : Real.sqrt (Real.log (p n:ℝ)) ≠ 0 := (Real.sqrt_pos.mpr hlog).ne'
  have htwo : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  dsimp only [Function.comp_apply]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  unfold skewIntrinsicRate lowerSkewRate
  rw [lower_log_power_three_half hlog.le]
  field_simp [hBn,hN,hroot,htwo,hlog.ne']
  ring

theorem old_skew_rate_tendsto_zero_of_intrinsic {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (he : Tendsto (fun n => skewIntrinsicRate (B n) (p n) n) atTop (𝓝 0)) :
    Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0) := by
  have hh := he.div (skewIntrinsicRate_div_old_tendsto hB hp)
    (by positivity : Real.sqrt (2:ℝ) ≠ 0)
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1] with n hpn hn
  change skewIntrinsicRate (B n) (p n) n/
    (skewIntrinsicRate (B n) (p n) n/lowerSkewRate (B n) (p n) n)=_
  exact div_div_cancel₀ (skewIntrinsicRate_pos (hB n) hpn hn).ne'

theorem skew_intrinsic_distance_liminf {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (he : Tendsto (fun n => skewIntrinsicRate (B n) (p n) n) atTop (𝓝 0)) :
    ((1/(4*Real.exp 1):ℝ):EReal) ≤ liminf (fun n =>
      ((lowerConstructionDistance (B n) n (p n)/skewIntrinsicRate (B n) (p n) n:ℝ):EReal)) atTop := by
  have hr := old_skew_rate_tendsto_zero_of_intrinsic hB hp he
  have hratio := skewIntrinsicRate_div_old_tendsto hB hp
  apply le_of_forall_lt
  intro c hc
  obtain ⟨b,hcb,hba⟩ := EReal.exists_between_coe_real hc
  have hb : b < 1/(4*Real.exp 1) := by exact_mod_cast hba
  have htwo : 0 < Real.sqrt (2:ℝ) := by positivity
  have hbc : b*Real.sqrt 2 < Real.sqrt 2/(4*Real.exp 1) := by
    convert mul_lt_mul_of_pos_right hb htwo using 1
    ring
  obtain ⟨a,hba',hac⟩ := exists_between hbc
  have hD := RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_eventual_lower_from_F1 hB hp hr hac
  have hlim := (tendsto_const_nhds (x:=b)).mul hratio
  apply hcb.trans_le
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hD,hlim.eventually (eventually_lt_nhds hba'),
    lowerSkewRate_eventually_pos hB hp,hp.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1]
    with n hn hrat hold hpn hnpos
  have hnew := skewIntrinsicRate_pos (hB n) hpn hnpos
  have hm := mul_lt_mul_of_pos_right hrat hold
  have hmeq : (b*(skewIntrinsicRate (B n) (p n) n/lowerSkewRate (B n) (p n) n))*
      lowerSkewRate (B n) (p n) n = b*skewIntrinsicRate (B n) (p n) n := by
    field_simp [hold.ne']
  rw [hmeq] at hm
  have hcross := hm.trans ((lt_div_iff₀ hold).mp hn)
  have hfinal : b ≤ lowerConstructionDistance (B n) n (p n)/skewIntrinsicRate (B n) (p n) n :=
    ((lt_div_iff₀ hnew).mpr hcross).le
  exact_mod_cast hfinal

/-- The canonical raw observations have exactly the requested genuine
finite-product laws, iid rows, independent coordinates, unit row covariance,
and positive probability of attaining the raw envelope. -/
theorem skew_intrinsic_construction_properties {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (n : ℕ) (hn : 1 ≤ n) (hp : 1 ≤ p n) :
    LowerConstructionProperties (B n) n (p n) :=
  lowerConstructionProperties (by linarith [hB n]) hn hp

/-- The asymptotic lower bound needs no extra dimension-rate assumption.
All construction properties hold eventually from `p_n → ∞`. -/
theorem theorem_3_intrinsic_canonical {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (he : Tendsto (fun n => skewIntrinsicRate (B n) (p n) n) atTop (𝓝 0)) :
    (∀ᶠ n in atTop, LowerConstructionProperties (B n) n (p n)) ∧
    ((1/(4*Real.exp 1):ℝ):EReal) ≤ liminf (fun n =>
      ((lowerConstructionDistance (B n) n (p n)/skewIntrinsicRate (B n) (p n) n:ℝ):EReal)) atTop := by
  refine ⟨?_,skew_intrinsic_distance_liminf hB hp he⟩
  filter_upwards [hp.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1] with n hpn hn
  exact skew_intrinsic_construction_properties hB n hn hpn


/-- The Gaussian comparison uses the exact normalized sum of raw rows. -/
theorem lowerNormalizedRows_sum_eq_raw_normalized (n p : ℕ) :
    sumVector (lowerNormalizedRows (n:=n) (p:=p)) =
      normalizedObservationSum (lowerRawRows (n:=n) (p:=p)) := by
  funext z
  simp only [sumVector,lowerNormalizedRows,normalizedObservationSum,one_div]
  rw [Finset.smul_sum]

/-- Actual observation properties on the explicitly constructed product
law. The normalization is part of the conclusion, rather than a supplied
Gaussian comparison or covariance premise. -/
def SkewIndependentRawData (B : ℝ) (n p : ℕ)
    (X : Fin n → (Fin n → Vector p) → Vector p) : Prop :=
  BoundedIndependentHypotheses (lowerArrayLaw B n p) X B ∧
  (∀ i, (lowerArrayLaw B n p).map (X i)=Measure.pi (fun _ : Fin p => lowerTwoPointLaw B)) ∧
  (∀ i, iIndepFun (fun j z => X i z j) (lowerArrayLaw B n p)) ∧
  (∀ i, covariance (lowerArrayLaw B n p) (X i)=1) ∧
  (∀ i, 0<(lowerArrayLaw B n p).real {z | ‖X i z‖=B}) ∧
  covariance (lowerArrayLaw B n p) (normalizedObservationSum X)=1

/-- Theorem 3 as a constructive existential statement about raw arrays.
Positive dimensions are required only where the finite-row properties and
raw envelope attainment are asserted; the asymptotic assumptions alone
ensure these hold eventually. -/
theorem theorem_3_intrinsic {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (he : Tendsto (fun n => skewIntrinsicRate (B n) (p n) n) atTop (𝓝 0)) :
    ∃ X : ∀ n, Fin n → (Fin n → Vector (p n)) → Vector (p n),
      (∀ n, 1≤n → 1≤p n → SkewIndependentRawData (B n) n (p n) (X n)) ∧
      ((1/(4*Real.exp 1):ℝ):EReal) ≤ liminf (fun n =>
        ((rectangleDistance (lowerArrayLaw (B n) n (p n)) (normalizedObservationSum (X n)) 1/
          skewIntrinsicRate (B n) (p n) n:ℝ):EReal)) atTop := by
  refine ⟨fun _ => lowerRawRows,?_,?_⟩
  · intro n hn hpn
    have h := skew_intrinsic_construction_properties hB n hn hpn
    refine ⟨h.data,h.iid,h.independent_coordinates,h.row_covariance,h.attained,?_⟩
    rw [←lowerNormalizedRows_sum_eq_raw_normalized]
    exact h.normalized_covariance
  · simpa only [lowerConstructionDistance,lowerNormalizedRows_sum_eq_raw_normalized] using
      skew_intrinsic_distance_liminf hB hp he


/-- The literal positive-dimension convention gives all finite-row
properties for every positive sample size, as well as the exact liminf. -/
theorem theorem_3_intrinsic_positive_dimensions {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hpdim : ∀ n, 1≤n → 1≤p n) (hp : Tendsto p atTop atTop)
    (he : Tendsto (fun n => skewIntrinsicRate (B n) (p n) n) atTop (𝓝 0)) :
    ∃ X : ∀ n, Fin n → (Fin n → Vector (p n)) → Vector (p n),
      (∀ n, 1≤n → SkewIndependentRawData (B n) n (p n) (X n)) ∧
      ((1/(4*Real.exp 1):ℝ):EReal) ≤ liminf (fun n =>
        ((rectangleDistance (lowerArrayLaw (B n) n (p n)) (normalizedObservationSum (X n)) 1/
          skewIntrinsicRate (B n) (p n) n:ℝ):EReal)) atTop := by
  obtain ⟨X,hX,hlim⟩ := theorem_3_intrinsic hB hp he
  exact ⟨X,fun n hn => hX n hn (hpdim n hn),hlim⟩

end
end RectangleCLTArxivV1
