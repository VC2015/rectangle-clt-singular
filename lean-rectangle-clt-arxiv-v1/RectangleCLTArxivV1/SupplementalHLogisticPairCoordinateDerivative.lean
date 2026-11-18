import RectangleCLTArxivV1.SupplementalHLogisticCoordinateDerivative

/-! Actual distinct-coordinate derivative of a soft power times one
face weight. An arbitrary integrable signed test is preserved under the
integral, using the genuine uniform logistic-factor domination. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem supplementalH_hasDerivAt_logistic_power_face_offset {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0<h)
    (x : Vector r) (j l : Fin m) (hjl : j≠l) (q : ℕ) (c : ℝ) :
    HasDerivAt (fun t => logisticNullWeight u (Function.update a l t) h x^(q+1)*
      logisticFaceWeight u (Function.update a l t) h x j)
      (((q:ℝ)+2)/h*(logisticNullWeight u (Function.update a l c) h x^(q+1)*
        logisticFaceWeight u (Function.update a l c) h x j*
        logisticFaceWeight u (Function.update a l c) h x l)) c := by
  let E := Real.exp ((faceDot (u j) x-a j)/h)
  have hfun (t : ℝ) : E*logisticNullWeight u (Function.update a l t) h x^((q+1)+1)=
      logisticNullWeight u (Function.update a l t) h x^(q+1)*
        logisticFaceWeight u (Function.update a l t) h x j := by
    rw [pow_succ]
    unfold logisticFaceWeight
    rw [Function.update_of_ne hjl]
    dsimp only [E]
    ring
  have hd := (supplementalH_hasDerivAt_logistic_power_offset u a hh x l (q+1) c).const_mul E
  convert hd using 1
  · funext t
    exact (hfun t).symm
  · rw [← hfun c]
    push_cast
    ring

theorem supplementalH_hasDerivAt_integral_logistic_power_face_offset
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m r : ℕ} (X : Ω → Vector r) (hX : Measurable X)
    (P : Ω → ℝ) (hP : Integrable P μ) (u : Fin m → Vector r)
    (a : Vector m) {h : ℝ} (hh : 0<h) (j l : Fin m) (hjl : j≠l) (q : ℕ) (c : ℝ) :
    HasDerivAt (fun t => ∫ ω,P ω*
      (logisticNullWeight u (Function.update a l t) h (X ω)^(q+1)*
        logisticFaceWeight u (Function.update a l t) h (X ω) j) ∂μ)
      (((q:ℝ)+2)/h*(∫ ω,P ω*
        (logisticNullWeight u (Function.update a l c) h (X ω)^(q+1)*
          logisticFaceWeight u (Function.update a l c) h (X ω) j*
          logisticFaceWeight u (Function.update a l c) h (X ω) l) ∂μ)) c := by
  let F := fun t ω => P ω*(logisticNullWeight u (Function.update a l t) h (X ω)^(q+1)*
    logisticFaceWeight u (Function.update a l t) h (X ω) j)
  let D := fun t ω => (((q:ℝ)+2)/h)*(P ω*
    (logisticNullWeight u (Function.update a l t) h (X ω)^(q+1)*
      logisticFaceWeight u (Function.update a l t) h (X ω) j*
      logisticFaceWeight u (Function.update a l t) h (X ω) l))
  have hfm (t : ℝ) : Measurable (fun ω => logisticNullWeight u (Function.update a l t) h (X ω)) := by
    unfold logisticNullWeight faceDot
    fun_prop
  have hpm (t : ℝ) (i : Fin m) : Measurable (fun ω => logisticFaceWeight u (Function.update a l t) h (X ω) i) := by
    unfold logisticFaceWeight logisticNullWeight faceDot
    fun_prop
  have hfb (t : ℝ) (ω : Ω) : 0≤logisticNullWeight u (Function.update a l t) h (X ω) ∧
      logisticNullWeight u (Function.update a l t) h (X ω)≤1 := by
    rw [← upperFaceSmoother_F u _ h hh]
    exact ⟨(FaceSmoother.F_pos _ _).le,FaceSmoother.F_le_one _ _⟩
  have hpb (t : ℝ) (ω : Ω) (i : Fin m) : 0≤logisticFaceWeight u (Function.update a l t) h (X ω) i ∧
      logisticFaceWeight u (Function.update a l t) h (X ω) i≤1 := by
    rw [← upperFaceSmoother_pi u _ h hh]
    exact ⟨(FaceSmoother.weights _ _).pi_nonneg _,
      ((FaceSmoother.weights _ _).pi_le_theta _).trans (FaceSmoother.weights _ _).theta_lt_one.le⟩
  have hwb (t : ℝ) (ω : Ω) :
      0≤logisticNullWeight u (Function.update a l t) h (X ω)^(q+1)*
        logisticFaceWeight u (Function.update a l t) h (X ω) j ∧
      logisticNullWeight u (Function.update a l t) h (X ω)^(q+1)*
        logisticFaceWeight u (Function.update a l t) h (X ω) j≤1 :=
    ⟨mul_nonneg (pow_nonneg (hfb t ω).1 _) (hpb t ω j).1,
      mul_le_one₀ (pow_le_one₀ (hfb t ω).1 (hfb t ω).2) (hpb t ω j).1 (hpb t ω j).2⟩
  have hi (t : ℝ) : Integrable (F t) μ := by
    apply hP.norm.mono'
      (hP.aestronglyMeasurable.mul (((hfm t).pow_const _).mul (hpm t j)).aestronglyMeasurable)
    exact ae_of_all _ (fun ω => by
      change |P ω*(logisticNullWeight u (Function.update a l t) h (X ω)^(q+1)*
        logisticFaceWeight u (Function.update a l t) h (X ω) j)|≤|P ω|
      rw [abs_mul,abs_of_nonneg (hwb t ω).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (hwb t ω).2)
  have hc0 : 0≤((q:ℝ)+2)/h := div_nonneg (by positivity) hh.le
  have hd (ω : Ω) (t : ℝ) : HasDerivAt (fun t => F t ω) (D t ω) t := by
    have hd := (supplementalH_hasDerivAt_logistic_power_face_offset u a hh (X ω) j l hjl q t).const_mul (P ω)
    convert hd using 1
    dsimp only [D]
    ring
  have ht := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (ε := 1) (bound := fun ω => (((q:ℝ)+2)/h)*‖P ω‖) (F := F) (F' := D) (x₀ := c)
    (by norm_num) (Eventually.of_forall (fun t => (hi t).aestronglyMeasurable)) (hi c)
    ((hP.aestronglyMeasurable.mul ((((hfm c).pow_const _).mul (hpm c j)).mul
      (hpm c l)).aestronglyMeasurable).const_mul _)
    (ae_of_all _ (fun ω t _ => by
      dsimp only [D]
      change |(((q:ℝ)+2)/h)*(P ω*(logisticNullWeight u (Function.update a l t) h (X ω)^(q+1)*
        logisticFaceWeight u (Function.update a l t) h (X ω) j*
        logisticFaceWeight u (Function.update a l t) h (X ω) l))|≤(((q:ℝ)+2)/h)*|P ω|
      rw [abs_mul,abs_of_nonneg hc0,abs_mul,
        abs_of_nonneg (mul_nonneg (hwb t ω).1 (hpb t ω l).1)]
      apply mul_le_mul_of_nonneg_left _ hc0
      exact mul_le_of_le_one_right (abs_nonneg _)
        (mul_le_one₀ (hwb t ω).2 (hpb t ω l).1 (hpb t ω l).2)))
    (hP.norm.const_mul _) (ae_of_all _ (fun ω t _ => hd ω t))
  convert ht.2 using 1
  exact (integral_const_mul _ _).symm

end
end RectangleCLTArxivV1
