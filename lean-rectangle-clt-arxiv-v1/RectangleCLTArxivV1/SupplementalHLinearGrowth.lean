import RectangleCLTArxivV1.SupplementalHWeightScaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The Gaussian matrix reduction for unbounded log-concave weights.
The cap approximations preserve log-concavity; all limit assumptions below
are ordinary Gaussian moments, rather than the desired covariance bound. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section

/-- An upper cap preserves nonnegative multiplicative log-concavity. -/
theorem NonnegativeLogConcave_min_const {r : ℕ} {w : Vector r → ℝ}
    (hw0 : ∀ g, 0 ≤ w g) (hlog : Printed.NonnegativeLogConcave w)
    {M : ℝ} (hM : 0 < M) : Printed.NonnegativeLogConcave (fun x => min (w x) M) := by
  intro x y t ht0 ht1
  have hx0 : 0 ≤ min (w x) M := le_min (hw0 x) hM.le
  have hy0 : 0 ≤ min (w y) M := le_min (hw0 y) hM.le
  have ht : 0 ≤ 1-t := by linarith
  apply le_min
  · exact (mul_le_mul
      (Real.rpow_le_rpow hx0 (min_le_left _ _) ht)
      (Real.rpow_le_rpow hy0 (min_le_left _ _) ht0.le)
      (Real.rpow_nonneg hy0 _) (Real.rpow_nonneg (hw0 x) _)).trans
        (hlog x y t ht0 ht1)
  · have he : M^(1-t)*M^t=M := by
      rw [←Real.rpow_add hM,show (1-t)+t=1 by ring,Real.rpow_one]
    exact (mul_le_mul
      (Real.rpow_le_rpow hx0 (min_le_right _ _) ht)
      (Real.rpow_le_rpow hy0 (min_le_right _ _) ht0.le)
      (Real.rpow_nonneg hy0 _) (Real.rpow_nonneg hM.le _)).trans_eq he

/-- The increasing caps used to pass from bounded weights to Gaussian moments. -/
def gaussianWeightCap {Ω : Type*} (w : Ω → ℝ) (n : ℕ) (x : Ω) : ℝ :=
  min (w x) ((n:ℝ)+1)

theorem gaussianWeightCap_tendsto {Ω : Type*} (w : Ω → ℝ) (x : Ω) :
    Tendsto (fun n => gaussianWeightCap w n x) atTop (𝓝 (w x)) := by
  have he : ∀ᶠ n : ℕ in atTop, gaussianWeightCap w n x = w x := by
    obtain ⟨N,hN⟩ := exists_nat_gt (w x)
    filter_upwards [eventually_ge_atTop N] with n hn
    unfold gaussianWeightCap
    exact min_eq_left (by exact (le_of_lt hN).trans (by exact_mod_cast Nat.le_succ_of_le hn))
  exact tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm))

/-- Clipping a nonnegative weight does not change its positive support. -/
theorem weightMass_gaussianWeightCap_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → ℝ) (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hwi : Integrable w μ)
    (hp : 0 < weightMass μ w) (n : ℕ) :
    0 < weightMass μ (gaussianWeightCap w n) := by
  have hc0 (x : Ω) : 0 ≤ gaussianWeightCap w n x :=
    le_min (hw0 x) (by positivity)
  have hci : Integrable (gaussianWeightCap w n) μ := by
    apply hwi.mono' (hw.min measurable_const).aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (hw0 x) (by positivity))]
      exact min_le_left _ _)
  have hs : Function.support (gaussianWeightCap w n) = Function.support w := by
    ext x
    simp only [Function.mem_support,ne_eq,gaussianWeightCap]
    have hm : 0 < (n:ℝ)+1 := by positivity
    constructor
    · intro hne hwz
      exact hne (by simp [hwz,hm.le])
    · intro hne
      exact (lt_min (lt_of_le_of_ne (hw0 x) (Ne.symm hne)) hm).ne'
  change 0 < ∫ x, gaussianWeightCap w n x ∂μ
  rw [integral_pos_iff_support_of_nonneg hc0 hci,hs]
  exact (integral_pos_iff_support_of_nonneg hw0 hwi).mp hp

/-- Every integrable weighted observable converges under these caps. -/
theorem integral_mul_gaussianWeightCap_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w P : Ω → ℝ) (hw : Measurable w) (hP : Measurable P)
    (hw0 : ∀ x, 0 ≤ w x) (hPi : Integrable (fun x => P x*w x) μ) :
    Tendsto (fun n => ∫ x, P x*gaussianWeightCap w n x ∂μ) atTop
      (𝓝 (∫ x, P x*w x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖P x*w x‖)
  · intro n
    exact (hP.mul (hw.min measurable_const)).aestronglyMeasurable
  · exact hPi.norm
  · intro n
    exact ae_of_all _ (fun x => by
      simp only [norm_mul,Real.norm_eq_abs,gaussianWeightCap]
      rw [abs_of_nonneg (le_min (hw0 x) (by positivity)),abs_of_nonneg (hw0 x)]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (abs_nonneg _))
  · exact ae_of_all _ (fun x => (gaussianWeightCap_tendsto w x).const_mul (P x))


/-- The matrix reduction holds for any nonnegative log-concave weight with
finite ordinary Gaussian moments. The truncations supply covariance
contraction rather than requiring it as a hypothesis. -/
theorem gaussian_logConcave_matrix_reduction_of_moments {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hw0 : ∀ g, 0 ≤ w g)
    (hwi : Integrable w (standardGaussian r))
    (hfirst : ∀ j, Integrable (fun g => g j*w g) (standardGaussian r))
    (hscore : ∀ j k, Integrable
      (fun g => (g j*g k-if j=k then 1 else 0)*w g) (standardGaussian r))
    (htrace : Integrable (fun g => (vectorNormSq g-(r:ℝ))*w g) (standardGaussian r))
    (hp : 0 < weightMass (standardGaussian r) w) (hlog : Printed.NonnegativeLogConcave w) :
    symmetricNuclearNorm (weightedScore (standardGaussian r) id w) ≤
      2*weightMass (standardGaussian r) w*vectorNormSq (weightMean (standardGaussian r) id w)-
        ∫ g, (vectorNormSq g-(r:ℝ))*w g ∂standardGaussian r := by
  have hmass : Tendsto (fun n => weightMass (standardGaussian r) (gaussianWeightCap w n))
      atTop (𝓝 (weightMass (standardGaussian r) w)) := by
    simpa only [weightMass,one_mul] using
      integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w (fun _ => 1)
        hw measurable_const hw0 (by simpa only [one_mul] using hwi)
  have hmean : Tendsto (fun n => weightMean (standardGaussian r) id (gaussianWeightCap w n))
      atTop (𝓝 (weightMean (standardGaussian r) id w)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact (integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w (fun g => g j)
      hw (measurable_pi_apply j) hw0 (hfirst j)).div hmass hp.ne'
  have hmatrix : Tendsto (fun n => weightedScore (standardGaussian r) id (gaussianWeightCap w n))
      atTop (𝓝 (weightedScore (standardGaussian r) id w)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro k
    exact integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w
      (fun g => g j*g k-if j=k then 1 else 0) hw (by fun_prop) hw0 (hscore j k)
  have hleft := (continuous_symmetricNuclearNorm.tendsto _).comp hmatrix
  have hnorm : Tendsto (fun n => vectorNormSq (weightMean (standardGaussian r) id (gaussianWeightCap w n)))
      atTop (𝓝 (vectorNormSq (weightMean (standardGaussian r) id w))) := by
    have hc : Continuous (vectorNormSq : Vector r → ℝ) := by unfold vectorNormSq; fun_prop
    exact (hc.tendsto _).comp hmean
  have htr := integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w
    (fun g => vectorNormSq g-(r:ℝ)) hw (by unfold vectorNormSq; fun_prop) hw0 htrace
  apply le_of_tendsto_of_tendsto hleft (((hmass.const_mul 2).mul hnorm).sub htr)
  exact Eventually.of_forall (fun n => gaussian_logConcave_matrix_reduction_of_bound
    (gaussianWeightCap w n) (hw.min measurable_const)
    (fun g => le_min (hw0 g) (by positivity)) (by positivity : 0 < (n:ℝ)+1)
    (fun g => min_le_right _ _)
    (weightMass_gaussianWeightCap_pos (standardGaussian r) w hw hw0 hwi hp n)
    (NonnegativeLogConcave_min_const hw0 hlog (by positivity)))


/-- Finite mass and the ordinary squared-norm moment supply every coordinate
moment used by the Gaussian matrix identity. -/
theorem gaussian_weighted_coordinate_moments {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hw0 : ∀ g, 0 ≤ w g)
    (hwi : Integrable w (standardGaussian r))
    (hsecond : Integrable (fun g => vectorNormSq g*w g) (standardGaussian r)) :
    (∀ j, Integrable (fun g => g j*w g) (standardGaussian r)) ∧
      (∀ j k, Integrable (fun g => g j*g k*w g) (standardGaussian r)) := by
  have hsq (g : Vector r) (j : Fin r) : (g j)^2 ≤ vectorNormSq g := by
    exact Finset.single_le_sum (fun k _ => sq_nonneg (g k)) (Finset.mem_univ j)
  have hfirst (j : Fin r) : Integrable (fun g => g j*w g) (standardGaussian r) := by
    apply (hwi.add hsecond).mono' ((measurable_pi_apply j).mul hw).aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hw0 g)]
      have hj : |g j| ≤ 1+vectorNormSq g := by
        nlinarith [sq_nonneg (|g j|-1),sq_abs (g j),hsq g j]
      calc
        |g j| *w g ≤ (1+vectorNormSq g)*w g := mul_le_mul_of_nonneg_right hj (hw0 g)
        _ = w g+vectorNormSq g*w g := by ring)
  refine ⟨hfirst,?_⟩
  intro j k
  apply hsecond.mono' (((measurable_pi_apply j).mul (measurable_pi_apply k)).mul hw).aestronglyMeasurable
  exact ae_of_all _ (fun g => by
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (hw0 g),abs_mul]
    apply mul_le_mul_of_nonneg_right _ (hw0 g)
    nlinarith [sq_nonneg (|g j|-|g k|),sq_abs (g j),sq_abs (g k),hsq g j,hsq g k])

/-- Scaling a positive weight leaves its actual normalized covariance unchanged. -/
theorem weightCovariance_const_mul {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) (V : Ω → Vector r) (w : Ω → ℝ) {c : ℝ} (hc : c ≠ 0) :
    weightCovariance μ V (fun x => c*w x) = weightCovariance μ V w := by
  ext j k
  unfold weightCovariance
  rw [weightMean_const_mul _ _ _ hc,weightMass_const_mul]
  have he : (∫ x, V x j*V x k*(c*w x) ∂μ) = c*(∫ x, V x j*V x k*w x ∂μ) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ (fun x => by ring))
  rw [he]
  by_cases hp : weightMass μ w=0
  · simp [hp]
  · field_simp
    ring

theorem gaussian_logConcave_covariance_contraction_of_bound {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hw0 : ∀ g, 0 ≤ w g)
    {M : ℝ} (hM : 0 < M) (hwM : ∀ g, w g ≤ M)
    (hp : 0 < weightMass (standardGaussian r) w) (hlog : Printed.NonnegativeLogConcave w) :
    (1-weightCovariance (standardGaussian r) id w).PosSemidef := by
  let c : ℝ := M⁻¹
  have hc : 0 < c := inv_pos.mpr hM
  have hb (g : Vector r) : c*w g ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hwM g) hc.le
    simpa only [c,inv_mul_cancel₀ hM.ne'] using hh
  have hh := Printed.gaussian_weightCovariance_contraction_nonnegative (fun g => c*w g)
    (measurable_const.mul hw) (fun g => mul_nonneg hc.le (hw0 g)) hb
    (by change 0 < weightMass (standardGaussian r) (fun g => c*w g)
        rw [weightMass_const_mul]; exact mul_pos hc hp)
    (NonnegativeLogConcave_const_mul hw0 hlog hc)
  rwa [weightCovariance_const_mul _ _ _ hc.ne'] at hh

/-- The first assertion of Lemma H.2, with the printed finite-second-moment
hypothesis. The extra linear growth restriction is unnecessary for this
cap-limit proof. -/
theorem gaussian_logConcave_covariance_contraction_of_moments {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hw0 : ∀ g, 0 ≤ w g)
    (hwi : Integrable w (standardGaussian r))
    (hsecond : Integrable (fun g => vectorNormSq g*w g) (standardGaussian r))
    (hp : 0 < weightMass (standardGaussian r) w) (hlog : Printed.NonnegativeLogConcave w) :
    (1-weightCovariance (standardGaussian r) id w).PosSemidef := by
  obtain ⟨hfirst,hpair⟩ := gaussian_weighted_coordinate_moments w hw hw0 hwi hsecond
  have hmass : Tendsto (fun n => weightMass (standardGaussian r) (gaussianWeightCap w n))
      atTop (𝓝 (weightMass (standardGaussian r) w)) := by
    simpa only [weightMass,one_mul] using
      integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w (fun _ => 1)
        hw measurable_const hw0 (by simpa only [one_mul] using hwi)
  have hmean (j : Fin r) : Tendsto
      (fun n => weightMean (standardGaussian r) id (gaussianWeightCap w n) j)
      atTop (𝓝 (weightMean (standardGaussian r) id w j)) :=
    (integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w (fun g => g j)
      hw (measurable_pi_apply j) hw0 (hfirst j)).div hmass hp.ne'
  have hmatrix : Tendsto (fun n => weightCovariance (standardGaussian r) id (gaussianWeightCap w n))
      atTop (𝓝 (weightCovariance (standardGaussian r) id w)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro k
    exact ((integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w
      (fun g => g j*g k) hw (by fun_prop) hw0 (hpair j k)).div hmass hp.ne').sub
        ((hmean j).mul (hmean k))
  have hcap (n : ℕ) :
      (1-weightCovariance (standardGaussian r) id (gaussianWeightCap w n)).PosSemidef :=
    gaussian_logConcave_covariance_contraction_of_bound
      (gaussianWeightCap w n) (hw.min measurable_const)
      (fun g => le_min (hw0 g) (by positivity)) (by positivity : 0 < (n:ℝ)+1)
      (fun g => min_le_right _ _)
      (weightMass_gaussianWeightCap_pos (standardGaussian r) w hw hw0 hwi hp n)
      (NonnegativeLogConcave_min_const hw0 hlog (by positivity))
  refine ⟨Matrix.isHermitian_one.sub (weightCovariance_isHermitian _ w),?_⟩
  intro u
  have hc : Continuous (fun M : Matrix (Fin r) (Fin r) ℝ =>
      dotProduct u ((1-M).mulVec u)) := by
    simp only [dotProduct,Matrix.mulVec,Matrix.sub_apply]
    fun_prop
  exact ge_of_tendsto ((hc.tendsto _).comp hmatrix)
    (Eventually.of_forall (fun n => by simpa using (hcap n).2 u))

/-- The two log-concave conclusions in Lemma H.2. -/
theorem lemma_H2_gaussian_matrix {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hw0 : ∀ g, 0 ≤ w g)
    (hwi : Integrable w (standardGaussian r))
    (hsecond : Integrable (fun g => vectorNormSq g*w g) (standardGaussian r))
    (hp : 0 < weightMass (standardGaussian r) w) (hlog : Printed.NonnegativeLogConcave w) :
    (1-weightCovariance (standardGaussian r) id w).PosSemidef ∧
      symmetricNuclearNorm (weightedScore (standardGaussian r) id w) ≤
        2*weightMass (standardGaussian r) w*vectorNormSq (weightMean (standardGaussian r) id w)-
          ∫ g, (vectorNormSq g-(r:ℝ))*w g ∂standardGaussian r := by
  obtain ⟨hfirst,hpair⟩ := gaussian_weighted_coordinate_moments w hw hw0 hwi hsecond
  refine ⟨gaussian_logConcave_covariance_contraction_of_moments w hw hw0 hwi hsecond hp hlog,?_⟩
  apply gaussian_logConcave_matrix_reduction_of_moments w hw hw0 hwi hfirst
  · intro j k
    simpa only [sub_mul] using (hpair j k).sub (hwi.const_mul (if j=k then 1 else 0))
  · simpa only [sub_mul] using hsecond.sub (hwi.const_mul (r:ℝ))
  · exact hp
  · exact hlog


/-- The projected-reference conclusion of Lemma H.2. Only the reference
mass is assumed finite; the reference need not be bounded or log-concave. -/
theorem lemma_H2_projected_reference {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (hPt : P.transpose=P) (hPP : P*P=P)
    (β : Vector r → ℝ) (hβ : Measurable β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβi : Integrable (fun g => β (P.mulVec g)) (standardGaussian r))
    (w : Vector r → ℝ) (hw : Measurable w)
    (hwb : ∀ g, 0 ≤ w g ∧ w g ≤ β (P.mulVec g))
    (hwi : Integrable w (standardGaussian r))
    (hsecond : Integrable (fun g => vectorNormSq g*w g) (standardGaussian r))
    (hp : 0 < weightMass (standardGaussian r) w) :
    weightMass (standardGaussian r) w*vectorNormSq (weightMean (standardGaussian r) id w) ≤
      (∫ g, w g*vectorNormSq (P.mulVec g) ∂standardGaussian r)+
        2*weightMass (standardGaussian r) w*
          Real.log ((∫ g, β (P.mulVec g) ∂standardGaussian r)/weightMass (standardGaussian r) w) := by
  have hw0 (g : Vector r) : 0 ≤ w g := (hwb g).1
  obtain ⟨hfirst,_⟩ := gaussian_weighted_coordinate_moments w hw hw0 hwi hsecond
  have hmass : Tendsto (fun n => weightMass (standardGaussian r) (gaussianWeightCap w n))
      atTop (𝓝 (weightMass (standardGaussian r) w)) := by
    simpa only [weightMass,one_mul] using
      integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w (fun _ => 1)
        hw measurable_const hw0 (by simpa only [one_mul] using hwi)
  have hmean : Tendsto (fun n => weightMean (standardGaussian r) id (gaussianWeightCap w n))
      atTop (𝓝 (weightMean (standardGaussian r) id w)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact (integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w (fun g => g j)
      hw (measurable_pi_apply j) hw0 (hfirst j)).div hmass hp.ne'
  have hnorm : Tendsto (fun n => vectorNormSq (weightMean (standardGaussian r) id (gaussianWeightCap w n)))
      atTop (𝓝 (vectorNormSq (weightMean (standardGaussian r) id w))) := by
    have hc : Continuous (vectorNormSq : Vector r → ℝ) := by unfold vectorNormSq; fun_prop
    exact (hc.tendsto _).comp hmean
  have hprojecti : Integrable (fun g => vectorNormSq (P.mulVec g)*w g) (standardGaussian r) := by
    apply hsecond.mono' ((show Measurable (fun g => vectorNormSq (P.mulVec g)) by
      unfold vectorNormSq; fun_prop).mul hw).aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by unfold vectorNormSq; positivity) (hw0 g))]
      apply mul_le_mul_of_nonneg_right _ (hw0 g)
      rw [projection_normSq_decomposition P hPt hPP g]
      have hh : 0 ≤ vectorNormSq (g-P.mulVec g) := by unfold vectorNormSq; positivity
      linarith)
  have hproject := integral_mul_gaussianWeightCap_tendsto (standardGaussian r) w
    (fun g => vectorNormSq (P.mulVec g)) hw (by unfold vectorNormSq; fun_prop) hw0 hprojecti
  have hreference : Tendsto
      (fun n => ∫ g, gaussianWeightCap β n (P.mulVec g) ∂standardGaussian r)
      atTop (𝓝 (∫ g, β (P.mulVec g) ∂standardGaussian r)) := by
    simpa only [one_mul] using
      integral_mul_gaussianWeightCap_tendsto (standardGaussian r)
        (fun g => β (P.mulVec g)) (fun _ => 1)
        (hβ.comp (by fun_prop)) measurable_const (fun g => hβ0 _) (by simpa using hβi)
  have hpb : 0 < ∫ g, β (P.mulVec g) ∂standardGaussian r :=
    hp.trans_le (integral_mono hwi hβi (fun g => (hwb g).2))
  have hratio := hreference.div hmass hp.ne'
  have hlog := (Real.continuousAt_log (div_pos hpb hp).ne').tendsto.comp hratio
  have hh : weightMass (standardGaussian r) w*vectorNormSq (weightMean (standardGaussian r) id w) ≤
      (∫ g, vectorNormSq (P.mulVec g)*w g ∂standardGaussian r)+
        2*weightMass (standardGaussian r) w*
          Real.log ((∫ g, β (P.mulVec g) ∂standardGaussian r)/weightMass (standardGaussian r) w) := by
    apply le_of_tendsto_of_tendsto (hmass.mul hnorm) (hproject.add ((hmass.const_mul 2).mul hlog))
    apply Eventually.of_forall
    intro n
    have hcap := gaussian_projected_mean_of_bounded_reference P hPt hPP
      (gaussianWeightCap β n) (hβ.min measurable_const) (by positivity : 0 < (n:ℝ)+1)
      (fun x => ⟨le_min (hβ0 x) (by positivity),min_le_right _ _⟩)
      (gaussianWeightCap w n) (hw.min measurable_const)
      (fun g => ⟨le_min (hw0 g) (by positivity),min_le_min_right _ (hwb g).2⟩)
      (weightMass_gaussianWeightCap_pos (standardGaussian r) w hw hw0 hwi hp n)
    simpa only [mul_comm] using hcap
  simpa only [mul_comm] using hh

end
end RectangleCLTArxivV1
