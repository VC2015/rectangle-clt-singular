import RectangleCLTCompanion.SplitV4.Printed.WeightedSignRates

/-! Actual independent copies of an arbitrary centered sign-vector law.
Coordinates of each sign vector may have any dependence. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

instance iid_sign_pi_isProbability {p n : ℕ} (ν : Measure (Vector p)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (Measure.pi (fun _ : Fin n => ν)) := by
  constructor
  simp [Measure.pi_univ]

theorem iid_sign_pi_map_eval {p n : ℕ} (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (i : Fin n) :
    (Measure.pi (fun _ : Fin n => ν)).map (fun z => z i)=ν := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs,←Set.univ_pi_update_univ,Measure.pi_pi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Function.update_of_ne hji]
  · simp

theorem iid_sign_pi_independent {p n : ℕ} (ν : Measure (Vector p)) [IsProbabilityMeasure ν] :
    iIndepFun (fun i (z : Fin n → Vector p) => z i) (Measure.pi (fun _ : Fin n => ν)) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp_rw [iid_sign_pi_map_eval ν]
  exact Measure.map_id

theorem iid_sign_pi_integral {p n : ℕ} (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (i : Fin n) (f : Vector p → ℝ) (hf : Measurable f) :
    (∫z,f (z i) ∂Measure.pi (fun _ : Fin n => ν))=∫x,f x ∂ν := by
  have hm := integral_map (μ:=Measure.pi (fun _ : Fin n => ν)) (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
  rw [iid_sign_pi_map_eval ν i] at hm
  exact hm.symm

theorem iid_sign_pi_signs {p n : ℕ} (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (hsign : ∀j,∀ᵐ x ∂ν,(x j)^2=1) (i : Fin n) (j : Fin p) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => ν),(z i j)^2=1 := by
  have hh : ∀ᵐ x ∂(Measure.pi (fun _ : Fin n => ν)).map (fun z => z i),(x j)^2=1 := by
    rw [iid_sign_pi_map_eval]
    exact hsign j
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (measurableSet_eq_fun ((measurable_pi_apply j).pow_const 2) measurable_const)).mp hh

theorem iid_sign_pi_bounded {p n : ℕ} (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (hc : ∀j,(∫x,x j ∂ν)=0) (hsign : ∀j,∀ᵐ x ∂ν,(x j)^2=1) :
    BoundedIndependentHypotheses (Measure.pi (fun _ : Fin n => ν)) (fun i z => z i) 1 := by
  refine ⟨fun i => measurable_pi_apply i,iid_sign_pi_independent ν,?_,?_,by norm_num⟩
  · intro i j
    exact (iid_sign_pi_integral ν i (fun x => x j) (measurable_pi_apply j)).trans (hc j)
  · intro i
    have hh : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => ν),∀j,(z i j)^2=1 :=
      ae_all_iff.mpr (fun j => iid_sign_pi_signs ν hsign i j)
    filter_upwards [hh] with z hz
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤1)).mpr
    intro j
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [sq_abs,hz j]
    norm_num

theorem iid_sign_pi_covariance {p n : ℕ} (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (i : Fin n) :
    covariance (Measure.pi (fun _ : Fin n => ν)) (fun z => z i)=covariance ν id := by
  ext j k
  simp only [covariance,id_eq]
  rw [iid_sign_pi_integral ν i (fun x => x j*x k) ((measurable_pi_apply j).mul (measurable_pi_apply k)),
    iid_sign_pi_integral ν i (fun x => x j) (measurable_pi_apply j),
    iid_sign_pi_integral ν i (fun x => x k) (measurable_pi_apply k)]

/-- The exceptional-weight example on the actual product law of copies,
with its exact two fourth matrices and its current relative CLT bound. -/
theorem exceptional_sign_actual_model {p n : ℕ} (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (hc : ∀j,(∫x,x j ∂ν)=0) (hsign : ∀j,∀ᵐ x ∂ν,(x j)^2=1)
    (hn : 2≤n) (hlog : 1≤Real.log (n : ℝ)) (hp : 1≤p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance ν id) :
    (∀j,relativeFourthMatrix (Measure.pi (fun _ : Fin n => ν))
        (weightedSignRows (exceptionalSignWeight n) (fun i z => z i)) j=
      exceptionalSignFourth n•covariance ν id) ∧
    (∀j,relativeFreshFourthMatrix (Measure.pi (fun _ : Fin n => ν))
        (weightedSignRows (exceptionalSignWeight n) (fun i z => z i)) j=
      exceptionalSignFourth n•covariance ν id) ∧
    rectangleDistance (Measure.pi (fun _ : Fin n => ν))
      (sumVector (weightedSignRows (exceptionalSignWeight n) (fun i z => z i))) A≤relativeUniversalConstant*
        min 1 (relativeRate (exceptionalSignEnvelope n) (exceptionalSignFourth n) (dimensionLog p)) := by
  have hR : BoundedIndependentHypotheses (Measure.pi (fun _ : Fin n => ν)) (fun i z => z i) 1 :=
    iid_sign_pi_bounded ν hc hsign
  have hs : ∀i j,∀ᵐ z ∂Measure.pi (fun _ : Fin n => ν),(z i j)^2=1 := iid_sign_pi_signs ν hsign
  have hcov : ∀i,covariance (Measure.pi (fun _ : Fin n => ν)) (fun z => z i)=covariance ν id :=
    iid_sign_pi_covariance ν
  obtain ⟨hδ,ha⟩ := exceptional_weight_envelope hn hlog
  obtain ⟨ha2,ha4⟩ := exceptional_weight_normalization hn
  refine ⟨?_,?_,?_⟩
  · intro j
    simpa only [ha4] using (weighted_sign_fourth_matrices hR.centered hs (covariance ν id) hcov (exceptionalSignWeight n) j).1
  · intro j
    simpa only [ha4] using (weighted_sign_fourth_matrices hR.centered hs (covariance ν id) hcov (exceptionalSignWeight n) j).2
  · simpa only [ha4] using weighted_sign_current_relative_bound hR hs (covariance ν id) hcov (by omega)
      hp (exceptionalSignWeight n) ha2 hδ.le ha A hA

end
end RectangleCLT.Companion.SplitV4.Printed
