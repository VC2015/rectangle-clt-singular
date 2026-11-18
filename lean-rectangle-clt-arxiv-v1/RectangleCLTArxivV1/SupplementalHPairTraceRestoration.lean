import RectangleCLTArxivV1.SupplementalHPairPowerTrace

/-! Signed binomial restoration of every extra pair selector factor.
The complete angle-weighted radial trace is assembled before absolute
values; the original concentrated base and all face labels are kept. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def supplementalHSoftPairTrace {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h σ : ℝ) (K : ℕ) (x : Vector r) : ℝ :=
  ∫ g, ∑ jl : Fin m × Fin m,correlationAngleWeight (faceDot (u jl.1) (u jl.2))*
    ((vectorNormSq g-(r:ℝ))*(logisticNullWeight u a h (x+σ • g)*
      logisticFaceWeight u a h (x+σ • g) jl.1*logisticFaceWeight u a h (x+σ • g) jl.2*
      (1-logisticNullWeight u a h (x+σ • g))^K)) ∂standardGaussian r

private theorem pair_one_sub_pow (z : ℝ) (K : ℕ) :
    (1-z)^K=∑ q∈Finset.range (K+1), (-1:ℝ)^q*(K.choose q:ℝ)*z^q := by
  calc
    _ = (-z+1)^K := by congr 1; ring
    _ = _ := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro q _
      rw [one_pow,mul_one,neg_pow]
      ring

theorem supplementalHSoftPairTrace_eq_binomial {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0<h)
    (σ : ℝ) (K : ℕ) (x : Vector r) :
    supplementalHSoftPairTrace u a h σ K x=
      ∑ q∈Finset.range (K+1),(-1:ℝ)^q*(K.choose q:ℝ)*supplementalHSoftPairPowerTrace u a h σ q x := by
  classical
  have hpoint (g : Vector r) :
      (∑ jl : Fin m × Fin m,correlationAngleWeight (faceDot (u jl.1) (u jl.2))*
        ((vectorNormSq g-(r:ℝ))*(logisticNullWeight u a h (x+σ • g)*
          logisticFaceWeight u a h (x+σ • g) jl.1*logisticFaceWeight u a h (x+σ • g) jl.2*
          (1-logisticNullWeight u a h (x+σ • g))^K))) =
      ∑ q∈Finset.range (K+1),(-1:ℝ)^q*(K.choose q:ℝ)*
        (∑ jl : Fin m × Fin m,correlationAngleWeight (faceDot (u jl.1) (u jl.2))*
          ((vectorNormSq g-(r:ℝ))*(logisticNullWeight u a h (x+σ • g)^(q+1)*
            logisticFaceWeight u a h (x+σ • g) jl.1*logisticFaceWeight u a h (x+σ • g) jl.2))) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro jl _
    rw [pair_one_sub_pow]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [pow_succ]
    ring
  unfold supplementalHSoftPairTrace
  rw [integral_congr_ae (ae_of_all _ hpoint),integral_finset_sum _ (fun q _ =>
    (integrable_finset_sum _ (fun jl _ =>
      (integrable_gaussian_logistic_power_pair u a hh σ x jl.1 jl.2 q).const_mul _)).const_mul _)]
  apply Finset.sum_congr rfl
  intro q _
  exact integral_const_mul _ _

theorem supplementalH_softPairTrace_concentrated_base {p m n : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (U : Face p → Vector (n+1)) (f : Fin m → Face p) (a : Vector m)
    {C δ σ h : ℝ} (hC : 0≤C) (hδ : 0≤δ) (hσ : 0<σ) (hh : 0<h)
    (hu : ∀ j,vectorNormSq (U (f j))=1)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0<s →
      ν.real (faceLayer (fun k => U (f k)) b s)≤C*(s+δ))
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) (K : ℕ) :
    Integrable (supplementalHSoftPairTrace (fun j => U (f j)) a h σ K) ν ∧
    (∫ x, |supplementalHSoftPairTrace (fun j => U (f j)) a h σ K x| ∂ν) ≤
      (2:ℝ)^K*(supplementalHPairTraceConstant C*h^2/σ*dimensionLog p*Real.sqrt (dimensionLog p)) := by
  classical
  let B := supplementalHPairTraceConstant C*h^2/σ*dimensionLog p*Real.sqrt (dimensionLog p)
  let T := fun q => supplementalHSoftPairPowerTrace (fun j => U (f j)) a h σ q
  let c := fun q => (-1:ℝ)^q*(K.choose q:ℝ)
  have hT (q) := supplementalH_softPairPowerTrace_concentrated_base hp ν U f a hC hδ hσ hh hu hbase hδσ q
  have hc (q : ℕ) : |c q|=(K.choose q:ℝ) := by
    dsimp [c]
    rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  have he : supplementalHSoftPairTrace (fun j => U (f j)) a h σ K=
      fun x => ∑ q∈Finset.range (K+1), c q*T q x := by
    funext x
    exact supplementalHSoftPairTrace_eq_binomial _ a hh σ K x
  have hTi : Integrable (supplementalHSoftPairTrace (fun j => U (f j)) a h σ K) ν := by
    rw [he]
    exact integrable_finset_sum _ (fun q _ => (hT q).1.const_mul _)
  refine ⟨hTi,?_⟩
  have hbound := integral_mono hTi.abs
    (integrable_finset_sum _ (fun q _ => (hT q).1.abs.const_mul (|c q|)))
    (fun x => by
      rw [he]
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl
        (fun q _ => abs_mul (c q) (T q x))))
  have hIeq : (∫ x, ∑ q∈Finset.range (K+1), |c q| * |T q x| ∂ν)=
      ∑ q∈Finset.range (K+1), |c q| *(∫ x, |T q x| ∂ν) := by
    rw [integral_finset_sum _ (fun q _ => (hT q).1.abs.const_mul (|c q|))]
    exact Finset.sum_congr rfl (fun q _ => integral_const_mul _ _)
  rw [hIeq] at hbound
  have hsum : (∑ q∈Finset.range (K+1), (K.choose q:ℝ))=(2:ℝ)^K := by
    simpa only [one_pow,mul_one,one_mul,show (1:ℝ)+1=2 by norm_num] using (add_pow (1:ℝ) 1 K).symm
  calc
    _ ≤ ∑ q∈Finset.range (K+1), |c q| *(∫ x, |T q x| ∂ν) := hbound
    _ ≤ ∑ q∈Finset.range (K+1), |c q| *B := Finset.sum_le_sum
      (fun q _ => mul_le_mul_of_nonneg_left (hT q).2 (abs_nonneg _))
    _ = _ := by simp_rw [hc]; rw [←Finset.sum_mul,hsum]


end
end RectangleCLTArxivV1
