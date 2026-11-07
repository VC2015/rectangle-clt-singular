import RectangleCLTCompanion.SplitV4.DenseMomentCalibration

/-! The literal dense amplitude `(B/2) θ^(-1/q)` from the printed proof.
The existing genuine common family is instantiated at the auxiliary budget
`1+B/2`; its older amplitude and records are preserved. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def printedDenseBudget (B : ℝ) : ℝ := 1+B/2
def printedDenseAmplitude (n : ℕ) (ell q B : ℝ) : ℝ :=
  (B/2)*(fourthLowerTheta n ell)^(-1/q)
def printedDenseScale (n : ℕ) (ell q B : ℝ) : ℝ :=
  printedDenseAmplitude n ell q B*ell^(3/2 : ℝ)/(2*Real.sqrt n)
def printedDenseParameters (q B : ℝ) (n m : ℕ) : SymmetricFamilyParameters :=
  denseFamilyParameters q (printedDenseBudget B) n m
def printedDenseRateConversion (q : ℝ) : ℝ := 2^(7/2-2/q)
def printedDenseConstant (q : ℝ) : ℝ := Real.sqrt 2*Real.exp (-1)/printedDenseRateConversion q

theorem printedDenseBudget_bounds {B : ℝ} (hB : 2≤B) :
    2≤printedDenseBudget B ∧ printedDenseBudget B≤B := by
  unfold printedDenseBudget
  constructor <;> linarith

theorem printedDenseAmplitude_eq (n : ℕ) (ell q B : ℝ) :
    printedDenseAmplitude n ell q B=denseLowerAmplitude n ell q (printedDenseBudget B) := by
  unfold printedDenseAmplitude denseLowerAmplitude printedDenseBudget
  ring

theorem printedDenseScale_eq (n : ℕ) (ell q B : ℝ) :
    printedDenseScale n ell q B=denseLowerScale n ell q (printedDenseBudget B) := by
  unfold printedDenseScale denseLowerScale
  rw [printedDenseAmplitude_eq]

theorem dense_rate_budget_rescale (n m : ℕ) (q : ℝ) {B : ℝ} (hB : B≠0) :
    denseMomentLowerRate n m q (printedDenseBudget B)=
      (printedDenseBudget B/B)*denseMomentLowerRate n m q B := by
  unfold denseMomentLowerRate
  simp only [mul_div_assoc]
  rw [←mul_assoc,div_mul_cancel₀ _ hB]

theorem printed_dense_auxiliary_rate_tendsto {m : ℕ → ℕ} {q B : ℝ}
    (hB : 2≤B)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => denseMomentLowerRate n (m n) q (printedDenseBudget B)) atTop (𝓝 0) := by
  have hh := hrate.const_mul (printedDenseBudget B/B)
  simp only [mul_zero] at hh
  apply hh.congr
  intro n
  exact (dense_rate_budget_rescale n (m n) q (by linarith : B≠0)).symm

theorem eventually_printedDense_parameters {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,(printedDenseParameters q B n (m n)).theta=fourthLowerTheta n (Real.log (m n : ℝ)) ∧
      (printedDenseParameters q B n (m n)).amplitude=printedDenseAmplitude n (Real.log (m n : ℝ)) q B := by
  have hh := eventually_denseFamily_parameters hq (printedDenseBudget_bounds hB).1 hm hmTop
    (printed_dense_auxiliary_rate_tendsto hB hrate)
  simpa only [printedDenseParameters,printedDenseAmplitude_eq] using hh

/-- The exact coefficient of the printed deterministic proof scale. -/
theorem printedDenseScale_factor {n : ℕ} (hn : 0<n) {ell q B : ℝ} (he : 0<ell) :
    printedDenseScale n ell q B=
      2^(1/q-2)*B*ell^(3/2-1/q)/(n : ℝ)^(1/2-1/q) := by
  rw [printedDenseScale_eq,denseLowerScale_factor hn he]
  unfold printedDenseBudget
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<2)]
  norm_num only [Real.rpow_two]
  ring

theorem printedDense_amplitude_fourth {θ : ℝ} (hθ : 0<θ) (q B : ℝ) :
    θ*((B/2)*θ^(-1/q))^4=(B^4/16)*θ^(1-4/q) := by
  have hh := dense_amplitude_fourth_identity hθ q (printedDenseBudget B)
  unfold printedDenseBudget at hh
  convert hh using 1 <;> ring

theorem printed_dense_moment_factors_tendsto {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => (printedDenseParameters q B n (m n)).variance) atTop (𝓝 0) ∧
    Tendsto (fun n => (printedDenseParameters q B n (m n)).theta*
      (printedDenseParameters q B n (m n)).amplitude^4) atTop (𝓝 0) := by
  have haux := printed_dense_auxiliary_rate_tendsto hB hrate
  have hD := (printedDenseBudget_bounds hB).1
  refine ⟨tendsto_denseFamily_variance hq hD hm hmTop haux,?_⟩
  have hEll : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hr : Tendsto (fun n => denseLowerEnvelopeRate n (Real.log (m n : ℝ)) q (printedDenseBudget B)) atTop (𝓝 0) :=
    haux.congr' (Eventually.of_forall (fun n => denseMomentLowerRate_eq n (m n) (hm n) q _))
  apply (tendsto_denseLowerAmplitude_fourth_theta _ hEll hq (by linarith : 1<printedDenseBudget B) hr).congr'
  filter_upwards [eventually_printedDense_parameters hq hB hm hmTop hrate] with n hn
  rw [hn.1,hn.2,printedDenseAmplitude_eq]

/-- The printed envelope budget and coordinate fourth-moment formula,
both for the actual probability space of the common family. -/
theorem eventually_printedDense_moments {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      (printedDenseParameters q B n (m n)).scale+
        (printedDenseParameters q B n (m n)).amplitude*
          (printedDenseParameters q B n (m n)).theta^(1/q)≤1+B/2 ∧
      (1+4*(printedDenseParameters q B n (m n)).variance-
        5*(printedDenseParameters q B n (m n)).variance^2+
        (printedDenseParameters q B n (m n)).theta*(printedDenseParameters q B n (m n)).amplitude^4)=
      1+4*(printedDenseParameters q B n (m n)).variance-
        5*(printedDenseParameters q B n (m n)).variance^2+
        (B^4/16)*(fourthLowerTheta n (Real.log (m n : ℝ)))^(1-4/q) := by
  filter_upwards [eventually_printedDense_parameters hq hB hm hmTop hrate,eventually_ge_atTop 1] with n hn hnn
  have hlog : 0<Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (show 1<m n by have := hm n; omega))
  have ht := fourthLowerTheta_pos (by omega : 0<n) hlog
  constructor
  · have hs := familyScale_le_one (printedDenseParameters q B n (m n))
    rw [hn.1,hn.2]
    unfold printedDenseAmplitude
    have hi := dense_amplitude_inverse_identity ht q (printedDenseBudget B)
    unfold printedDenseBudget at hi
    have hi' : ((B/2)*(fourthLowerTheta n (Real.log (m n : ℝ)))^(-1/q))*
      (fourthLowerTheta n (Real.log (m n : ℝ)))^(1/q)=B/2 := by convert hi using 1 <;> ring
    rw [hi']
    linarith
  · rw [hn.1,hn.2]
    unfold printedDenseAmplitude
    rw [printedDense_amplitude_fourth ht]

/-- At the exact printed amplitude the fourth moment tends to one. -/
theorem printed_dense_fourth_tendsto_one {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    Tendsto (fun n => 1+4*(printedDenseParameters q B n (m n)).variance-
      5*(printedDenseParameters q B n (m n)).variance^2+
      (printedDenseParameters q B n (m n)).theta*(printedDenseParameters q B n (m n)).amplitude^4)
      atTop (𝓝 1) := by
  obtain ⟨hv,ha⟩ := printed_dense_moment_factors_tendsto hq hB hm hmTop hrate
  have hh := (((tendsto_const_nhds (x:=(1:ℝ))).add (hv.const_mul 4)).sub ((hv.pow 2).const_mul 5)).add ha
  simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero,sub_zero] using hh

theorem eventually_printedDense_polynomialIndependent {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,PolynomialIndependentHypotheses
      (familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))
      (familyRawObservations (printedDenseParameters q B n (m n))) q B := by
  filter_upwards [eventually_printedDense_moments hq hB hm hmTop hrate,
    (printed_dense_fourth_tendsto_one hq hB hm hmTop hrate).eventually
      (eventually_le_nhds (by norm_num : (1:ℝ)<2)),eventually_ge_atTop 1] with n hn hfour hnn
  apply symmetricFamily_polynomialIndependent _ hnn (by linarith : 1≤q)
  · exact hn.1.trans (by linarith)
  · simpa only [printedDenseParameters,denseFamilyParameters_pi,mul_one] using
      hfour.trans (by nlinarith only [hB,sq_nonneg (B-2)] : (2:ℝ)≤B^2)

theorem eventually_printedDense_actual_moments {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,∀ i : Fin n,
      (∫ z, ‖familyRawObservations (printedDenseParameters q B n (m n)) i z‖^q
        ∂familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))^(1/q)≤B ∧
      ∀ j : Fin (m n*m n),
      (∫ z, familyRawObservations (printedDenseParameters q B n (m n)) i z j^4
        ∂familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))=
      1+4*(printedDenseParameters q B n (m n)).variance-
        5*(printedDenseParameters q B n (m n)).variance^2+
        (B^4/16)*(fourthLowerTheta n (Real.log (m n : ℝ)))^(1-4/q) := by
  filter_upwards [eventually_printedDense_moments hq hB hm hmTop hrate] with n hn
  intro i
  constructor
  · exact (familyRawObservations_Lq_envelope _ i (by linarith : 1≤q)).trans
      (hn.1.trans (by linarith))
  · intro j
    rw [familyRawObservations_fourth]
    simpa only [printedDenseParameters,denseFamilyParameters_pi,mul_one] using hn.2

theorem eventually_printedDense_rank_and_gap {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hm : ∀ n,2≤m n) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      Matrix.rank (covariance (familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))
        (sumVector (familyNormalizedObservations (printedDenseParameters q B n (m n)))))=2*m n-1 ∧
      pairGap (covariance (familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))
        (sumVector (familyNormalizedObservations (printedDenseParameters q B n (m n)))))=
        (B^2/4)*(fourthLowerTheta n (Real.log (m n : ℝ)))^(1-2/q) := by
  filter_upwards [eventually_printedDense_parameters hq hB hm hmTop hrate,eventually_ge_atTop 1] with n hn hnn
  refine ⟨familyNormalizedObservations_rank _ hnn (by have := hm n; omega),?_⟩
  rw [familyNormalizedObservations_pairGap _ hnn (hm n)]
  change (printedDenseParameters q B n (m n)).theta*(printedDenseParameters q B n (m n)).pi*
    (printedDenseParameters q B n (m n)).amplitude^2=_
  have hπ : (printedDenseParameters q B n (m n)).pi=1 := denseFamilyParameters_pi _ _ _ _
  rw [hπ,mul_one,hn.1,hn.2]
  have hlog : 0<Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (show 1<m n by have := hm n; omega))
  have hh := dense_amplitude_square_identity (fourthLowerTheta_pos (by omega : 0<n) hlog) q (printedDenseBudget B)
  unfold printedDenseAmplitude
  unfold printedDenseBudget at hh
  convert hh using 1 <;> ring

end
end RectangleCLT.Companion.SplitV4.Printed
