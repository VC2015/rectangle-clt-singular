import RectangleCLTCompanion.SplitV4.LogisticGammaTrace

/-! Actual individual-offset derivatives of the soft power. The signed
Gaussian test is kept intact when differentiating under its integral. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem supplementalH_hasDerivAt_logistic_power_offset {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0<h)
    (x : Vector r) (j : Fin m) (q : ℕ) (c : ℝ) :
    HasDerivAt (fun t => logisticNullWeight u (Function.update a j t) h x^(q+1))
      (((q:ℝ)+1)/h*(logisticNullWeight u (Function.update a j c) h x^(q+1)*
        logisticFaceWeight u (Function.update a j c) h x j)) c := by
  classical
  let T := fun t => ∑ k, Real.exp ((faceDot (u k) x-Function.update a j t k)/h)
  have hd (k : Fin m) : HasDerivAt
      (fun t => Real.exp ((faceDot (u k) x-Function.update a j t k)/h))
      (if k=j then -Real.exp ((faceDot (u j) x-c)/h)/h else 0) c := by
    by_cases hk : k=j
    · subst k
      simp only [Function.update_self,ite_true]
      convert ((((hasDerivAt_const c (faceDot (u j) x)).sub (hasDerivAt_id c)).div_const h).exp) using 1 <;> simp only [id_eq] <;> ring
    · simp only [Function.update_of_ne hk,if_neg hk]
      exact hasDerivAt_const c _
  have hT : HasDerivAt T (-Real.exp ((faceDot (u j) x-c)/h)/h) c := by
    simpa only [Finset.sum_ite_eq',Finset.mem_univ,if_true] using
      HasDerivAt.sum (fun k (_ : k∈Finset.univ) => hd k)
  have hpos : 0<1+T c := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun k _ => Real.exp_nonneg _))
  have h := (((hasDerivAt_const c (1:ℝ)).add hT).inv hpos.ne').pow (q+1)
  convert h using 1
  · funext t
    simp only [logisticNullWeight,one_div,T]
  · dsimp only [logisticNullWeight,logisticFaceWeight,T]
    simp only [Function.update_self,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,zero_add]
    field_simp
    ring

/-- The actual individual-offset derivative under an integrable signed
test. No hard-threshold derivative or final rate is assumed. -/
theorem supplementalH_hasDerivAt_integral_logistic_power_offset
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m r : ℕ} (X : Ω → Vector r) (hX : Measurable X)
    (P : Ω → ℝ) (hP : Integrable P μ) (u : Fin m → Vector r)
    (a : Vector m) {h : ℝ} (hh : 0<h) (j : Fin m) (q : ℕ) (c : ℝ) :
    HasDerivAt (fun t => ∫ ω, P ω*logisticNullWeight u (Function.update a j t) h (X ω)^(q+1) ∂μ)
      (((q:ℝ)+1)/h*(∫ ω, P ω*
        (logisticNullWeight u (Function.update a j c) h (X ω)^(q+1)*
          logisticFaceWeight u (Function.update a j c) h (X ω) j) ∂μ)) c := by
  classical
  let F := fun t ω => P ω*logisticNullWeight u (Function.update a j t) h (X ω)^(q+1)
  let D := fun t ω => (((q:ℝ)+1)/h)*(P ω*
    (logisticNullWeight u (Function.update a j t) h (X ω)^(q+1)*
      logisticFaceWeight u (Function.update a j t) h (X ω) j))
  have hfm (t : ℝ) : Measurable (fun ω => logisticNullWeight u (Function.update a j t) h (X ω)) := by
    unfold logisticNullWeight faceDot
    fun_prop
  have hpm (t : ℝ) : Measurable (fun ω => logisticFaceWeight u (Function.update a j t) h (X ω) j) := by
    unfold logisticFaceWeight logisticNullWeight faceDot
    fun_prop
  have hfb (t : ℝ) (ω : Ω) : 0≤logisticNullWeight u (Function.update a j t) h (X ω) ∧
      logisticNullWeight u (Function.update a j t) h (X ω)≤1 := by
    rw [←upperFaceSmoother_F u _ h hh]
    exact ⟨(FaceSmoother.F_pos _ _).le,FaceSmoother.F_le_one _ _⟩
  have hpb (t : ℝ) (ω : Ω) : 0≤logisticFaceWeight u (Function.update a j t) h (X ω) j ∧
      logisticFaceWeight u (Function.update a j t) h (X ω) j≤1 := by
    rw [←upperFaceSmoother_pi u _ h hh]
    exact ⟨(FaceSmoother.weights _ _).pi_nonneg _,
      ((FaceSmoother.weights _ _).pi_le_theta _).trans (FaceSmoother.weights _ _).theta_lt_one.le⟩
  have hi (t : ℝ) : Integrable (F t) μ := by
    apply hP.norm.mono' (hP.aestronglyMeasurable.mul ((hfm t).pow_const _).aestronglyMeasurable)
    exact ae_of_all _ (fun ω => by
      change |P ω*logisticNullWeight u (Function.update a j t) h (X ω)^(q+1)|≤|P ω|
      rw [abs_mul,abs_of_nonneg (pow_nonneg (hfb t ω).1 _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (hfb t ω).1 (hfb t ω).2))
  have hc0 : 0≤((q:ℝ)+1)/h := div_nonneg (by positivity) hh.le
  have hd (ω : Ω) (t : ℝ) : HasDerivAt (fun t => F t ω) (D t ω) t := by
    have h := (supplementalH_hasDerivAt_logistic_power_offset u a hh (X ω) j q t).const_mul (P ω)
    convert h using 1 <;> dsimp only [D] <;> ring
  have ht := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (ε := 1) (bound := fun ω => (((q:ℝ)+1)/h)*‖P ω‖) (F := F) (F' := D) (x₀ := c)
    (by norm_num) (Eventually.of_forall (fun t => (hi t).aestronglyMeasurable)) (hi c)
    ((hP.aestronglyMeasurable.mul (((hfm c).pow_const _).mul (hpm c)).aestronglyMeasurable).const_mul _)
    (ae_of_all _ (fun ω t _ => by
      dsimp only [D]
      change |(((q:ℝ)+1)/h)*(P ω*(logisticNullWeight u (Function.update a j t) h (X ω)^(q+1)*
        logisticFaceWeight u (Function.update a j t) h (X ω) j))|≤(((q:ℝ)+1)/h)*|P ω|
      rw [abs_mul,abs_of_nonneg hc0,abs_mul,
        abs_of_nonneg (mul_nonneg (pow_nonneg (hfb t ω).1 _) (hpb t ω).1)]
      apply mul_le_mul_of_nonneg_left _ hc0
      apply mul_le_of_le_one_right (abs_nonneg _)
      exact mul_le_one₀ (pow_le_one₀ (hfb t ω).1 (hfb t ω).2) (hpb t ω).1 (hpb t ω).2))
    (hP.norm.const_mul _) (ae_of_all _ (fun ω t _ => hd ω t))
  convert ht.2 using 1
  exact (integral_const_mul _ _).symm

end
end RectangleCLTArxivV1
