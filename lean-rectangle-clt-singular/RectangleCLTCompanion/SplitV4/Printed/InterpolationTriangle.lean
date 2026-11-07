import RectangleCLTCompanion.SplitV4.Printed.InterpolationSignedHessian
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The actual triangular Fubini transition in printed B.1, lines
2103--2110. Both integrations are on the triangle 0≤s≤v≤1. This is
separate from sample/interval Fubini and does not use a fourth-order
value/gradient Taylor identity. -/

open MeasureTheory Set
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem weighted_triangle_integral_swap (K g : ℝ → ℝ) (hK : Continuous K) (hg : Continuous g) :
    (∫ v in (0 : ℝ)..1, K v*(∫ s in (0 : ℝ)..v, (v-s)*g s)) =
      ∫ s in (0 : ℝ)..1, (∫ v in s..1, (v-s)*K v)*g s := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let D : Set (ℝ × ℝ) := {z | z.2 ≤ z.1}
  let f : ℝ × ℝ → ℝ := D.indicator (fun z => K z.1*(z.1-z.2)*g z.2)
  have hD : MeasurableSet D := measurableSet_le measurable_snd measurable_fst
  have hbase : Integrable (fun z : ℝ × ℝ => K z.1*(z.1-z.2)*g z.2) (ν.prod ν) := by
    dsimp only [ν]
    rw [Measure.prod_restrict, Icc_prod_Icc]
    exact ((hK.comp continuous_fst).mul (continuous_fst.sub continuous_snd) |>.mul
      (hg.comp continuous_snd)).integrableOn_Icc
  have hi : Integrable f (ν.prod ν) := hbase.indicator hD
  have hleft (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      (∫ s, f (v,s) ∂ν) = K v*(∫ s in (0 : ℝ)..v, (v-s)*g s) := by
    have he : (fun s => f (v,s)) = (Iic v).indicator (fun s => K v*((v-s)*g s)) := by
      funext s
      by_cases hs : s ≤ v <;> simp [f,D,hs] <;> ring
    rw [he,integral_indicator measurableSet_Iic]
    change (∫ s, K v*((v-s)*g s) ∂(volume.restrict (Icc (0 : ℝ) 1)).restrict (Iic v)) = _
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hset : Iic v ∩ Icc (0 : ℝ) 1 = Icc 0 v := by
      ext s
      simp only [mem_inter_iff,mem_Iic,mem_Icc]
      constructor
      · intro h; exact ⟨h.2.1,h.1⟩
      · intro h; exact ⟨h.2,h.1,h.2.trans hv.2⟩
    rw [hset,integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hv.1]
  have hright (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (∫ v, f (v,s) ∂ν) = (∫ v in s..1, (v-s)*K v)*g s := by
    have he : (fun v => f (v,s)) = (Ici s).indicator (fun v => ((v-s)*K v)*g s) := by
      funext v
      by_cases hv : s ≤ v
      · dsimp only [f]
        rw [indicator_of_mem (show (v,s) ∈ D from hv),indicator_of_mem (show v ∈ Ici s from hv)]
        ring
      · dsimp only [f]
        rw [indicator_of_not_mem (show (v,s) ∉ D from hv),indicator_of_not_mem (show v ∉ Ici s from hv)]
    rw [he,integral_indicator measurableSet_Ici]
    change (∫ v, ((v-s)*K v)*g s ∂(volume.restrict (Icc (0 : ℝ) 1)).restrict (Ici s)) = _
    rw [Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici s ∩ Icc (0 : ℝ) 1 = Icc s 1 := by
      ext v
      simp only [mem_inter_iff,mem_Ici,mem_Icc]
      constructor
      · intro h; exact ⟨h.1,h.2.2⟩
      · intro h; exact ⟨h.1,hs.1.trans h.1,h.2⟩
    rw [hset,integral_mul_const,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hs.2]
  have hswap := integral_integral_swap (μ := ν) (ν := ν) (f := fun v s => f (v,s)) hi
  have hL : (∫ v, (∫ s, f (v,s) ∂ν) ∂ν) =
      ∫ v in (0 : ℝ)..1, K v*(∫ s in (0 : ℝ)..v, (v-s)*g s) := by
    calc
      _ = ∫ v, K v*(∫ s in (0 : ℝ)..v, (v-s)*g s) ∂ν := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
        exact hleft v hv
      _ = _ := by dsimp only [ν]; rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one]
  have hR : (∫ s, (∫ v, f (v,s) ∂ν) ∂ν) =
      ∫ s in (0 : ℝ)..1, (∫ v in s..1, (v-s)*K v)*g s := by
    calc
      _ = ∫ s, (∫ v in s..1, (v-s)*K v)*g s ∂ν := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact hright s hs
      _ = _ := by dsimp only [ν]; rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one]
  rw [← hL,← hR]
  exact hswap

theorem canonical_hessian_taylor_triangle {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x z : Vector p) (a v : ℝ) :
    canonicalDiagonal F 2 (x+(a*v) • z) z-
      (canonicalDiagonal F 2 x z+v*a*canonicalDiagonal F 3 x z) =
      a^2*∫ s in (0 : ℝ)..v, (v-s)*canonicalDiagonal F 4 (x+(a*s) • z) z := by
  let H : ℝ → ℝ := fun s => canonicalDiagonal F 2 (x+(a*s) • z) z
  let H1 : ℝ → ℝ := fun s => a*canonicalDiagonal F 3 (x+(a*s) • z) z
  let H2 : ℝ → ℝ := fun s => a^2*canonicalDiagonal F 4 (x+(a*s) • z) z
  have hd0 (s : ℝ) : HasDerivAt H (H1 s) s := hasDerivAt_canonicalDiagonal_segment hF (by decide) x z a s
  have hd1 (s : ℝ) : HasDerivAt H1 (H2 s) s := by
    convert (hasDerivAt_canonicalDiagonal_segment hF (k := 3) (by decide) x z a s).const_mul a using 1
    dsimp only [H1,H2]
    ring
  have hd (s : ℝ) : HasDerivAt (fun t => H t+(v-t)*H1 t) ((v-s)*H2 s) s := by
    convert (hd0 s).add (((hasDerivAt_const s v).sub (hasDerivAt_id s)).mul (hd1 s)) using 1
    simp only [id_eq]
    ring
  have hc4 : Continuous (fun s => canonicalDiagonal F 4 (x+(a*s) • z) z) :=
    ((hF.continuous_iteratedFDeriv (m := 4) (by norm_num)).comp (by fun_prop)).eval continuous_const
  have hi : IntervalIntegrable (fun s => (v-s)*H2 s) volume 0 v :=
    ((continuous_const.sub continuous_id).mul (continuous_const.mul hc4)).intervalIntegrable 0 v
  have he := (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi).symm
  dsimp only [H,H1,H2] at he
  simp only [sub_self,zero_mul,add_zero,mul_zero,zero_smul] at he
  rw [← intervalIntegral.integral_const_mul]
  convert he using 1 <;> congr 1 <;> first | ring | (funext s; ring)

/-- Literal signed-Hessian expansion through the triangle, with the
printed fourth kernel and signed cubic coefficient. -/
theorem signed_hessian_fourth_kernel_identity {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x z : Vector p) (a η : ℝ) :
    -(1/2 : ℝ)*(∫ v in (0 : ℝ)..1, signedDensity η v*
      canonicalDiagonal F 2 (x+(a*v) • z) z) =
      -(1/2 : ℝ)*canonicalDiagonal F 2 x z-
        a*(1-η)/6*canonicalDiagonal F 3 x z+
        ∫ s in (0 : ℝ)..1, seededFourthKernel a η s*
          canonicalDiagonal F 4 (x+(a*s) • z) z := by
  let H : ℝ → ℝ := fun v => canonicalDiagonal F 2 (x+(a*v) • z) z
  let g : ℝ → ℝ := fun s => canonicalDiagonal F 4 (x+(a*s) • z) z
  let J : ℝ → ℝ := fun v => ∫ s in (0 : ℝ)..v, (v-s)*g s
  let R : ℝ → ℝ := fun v => signedDensity η v*(a^2*J v)
  have hcH : Continuous H :=
    ((hF.continuous_iteratedFDeriv (m := 2) (by exact_mod_cast (by decide : (2 : ℕ) ≤ 4))).comp
      (by fun_prop)).eval continuous_const
  have hcg : Continuous g :=
    ((hF.continuous_iteratedFDeriv (m := 4) (by norm_num)).comp (by fun_prop)).eval continuous_const
  have hcν : Continuous (signedDensity η) := by unfold signedDensity; fun_prop
  have hpoint (v : ℝ) : a^2*J v = H v-(canonicalDiagonal F 2 x z+v*a*canonicalDiagonal F 3 x z) :=
    (canonical_hessian_taylor_triangle hF x z a v).symm
  have hR : Continuous R := by
    have he : R = fun v => signedDensity η v*(H v-(canonicalDiagonal F 2 x z+v*a*canonicalDiagonal F 3 x z)) := by
      funext v
      dsimp only [R]
      rw [hpoint]
    rw [he]
    exact hcν.mul (hcH.sub (by fun_prop))
  have hsum : (∫ v in (0 : ℝ)..1, signedDensity η v*H v) =
      canonicalDiagonal F 2 x z+
      ((1-η)/3)*(a*canonicalDiagonal F 3 x z)+∫ v in (0 : ℝ)..1, R v := by
    have he (v : ℝ) : signedDensity η v*H v =
        signedDensity η v*canonicalDiagonal F 2 x z+
        (v*signedDensity η v)*(a*canonicalDiagonal F 3 x z)+R v := by
      dsimp only [R]
      rw [hpoint]
      ring
    simp_rw [he]
    have hi0 : IntervalIntegrable (fun v => signedDensity η v*canonicalDiagonal F 2 x z) volume 0 1 :=
      (hcν.mul continuous_const).intervalIntegrable 0 1
    have hi1 : IntervalIntegrable (fun v : ℝ => (v*signedDensity η v)*(a*canonicalDiagonal F 3 x z)) volume 0 1 :=
      ((by fun_prop : Continuous (fun v : ℝ => v*signedDensity η v)).mul continuous_const).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add
        (f := fun v => signedDensity η v*canonicalDiagonal F 2 x z+(v*signedDensity η v)*(a*canonicalDiagonal F 3 x z))
        (g := R) (hi0.add hi1) (hR.intervalIntegrable 0 1),
      intervalIntegral.integral_add (f := fun v => signedDensity η v*canonicalDiagonal F 2 x z)
        (g := fun v => (v*signedDensity η v)*(a*canonicalDiagonal F 3 x z)) hi0 hi1,
      intervalIntegral.integral_mul_const,intervalIntegral.integral_mul_const,
      signedDensity_mass,signedDensity_first_moment,one_mul]
  have hres : -(1/2 : ℝ)*(∫ v in (0 : ℝ)..1, R v) =
      ∫ s in (0 : ℝ)..1, seededFourthKernel a η s*g s := by
    have he : (∫ v in (0 : ℝ)..1, R v) =
        a^2*(∫ v in (0 : ℝ)..1, signedDensity η v*J v) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only [R]
      ring
    rw [he,weighted_triangle_integral_swap (signedDensity η) g hcν hcg,
      ← mul_assoc,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [← seededFourthKernel_eq_integral a η s]
    ring
  change -(1/2 : ℝ)*(∫ v in (0 : ℝ)..1, signedDensity η v*H v) = _
  rw [hsum]
  change _ = -(1/2 : ℝ)*canonicalDiagonal F 2 x z-a*(1-η)/6*canonicalDiagonal F 3 x z+
    ∫ s in (0 : ℝ)..1, seededFourthKernel a η s*g s
  rw [← hres]
  ring

/-- The same signed-Hessian-to-fourth transition under the actual copy
law, with genuine joint integrability and both required Fubini swaps. -/
theorem signed_hessian_fourth_kernel_expectation
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (x : Vector p) (a η : ℝ) :
    -(1/2 : ℝ)*(∫ v in (0 : ℝ)..1, signedDensity η v*
      (∫ u, canonicalDiagonal F 2 (x+(a*v) • T u) (T u) ∂μ)) =
      -(1/2 : ℝ)*(∫ u, canonicalDiagonal F 2 x (T u) ∂μ)-
        a*(1-η)/6*(∫ u, canonicalDiagonal F 3 x (T u) ∂μ)+
        ∫ s in (0 : ℝ)..1, seededFourthKernel a η s*
          (∫ u, canonicalDiagonal F 4 (x+(a*s) • T u) (T u) ∂μ) := by
  let D2 : Ω → ℝ := fun u => canonicalDiagonal F 2 x (T u)
  let D3 : Ω → ℝ := fun u => canonicalDiagonal F 3 x (T u)
  let J : Ω → ℝ := fun u => ∫ v in (0 : ℝ)..1, signedDensity η v*
    canonicalDiagonal F 2 (x+(a*v) • T u) (T u)
  let R : Ω → ℝ := fun u => ∫ s in (0 : ℝ)..1, seededFourthKernel a η s*
    canonicalDiagonal F 4 (x+(a*s) • T u) (T u)
  have hi2 : Integrable D2 μ := integrable_canonicalDiagonal_bounded μ hF (by decide)
    (fun _ => x) T measurable_const hT hC hδ (hjet 2 (by decide) (by decide)) hbound
  have hi3 : Integrable D3 μ := integrable_canonicalDiagonal_bounded μ hF (by decide)
    (fun _ => x) T measurable_const hT hC hδ (hjet 3 (by decide) (by decide)) hbound
  have hcν : Continuous (signedDensity η) := by unfold signedDensity; fun_prop
  have hcK : Continuous (seededFourthKernel a η) := by unfold seededFourthKernel; fun_prop
  have hJprod := integrable_canonicalDiagonal_interval_prod μ hF (by decide) hC hδ
    (hjet 2 (by decide) (by decide)) T hT hbound x a (signedDensity η) hcν
  have hRprod := integrable_canonicalDiagonal_interval_prod μ hF (by decide) hC hδ
    (hjet 4 (by decide) (by decide)) T hT hbound x a (seededFourthKernel a η) hcK
  have hiJ : Integrable J μ := by
    simpa only [J,intervalIntegral.integral_of_le zero_le_one] using hJprod.integral_prod_left
  have hiR : Integrable R μ := by
    simpa only [R,intervalIntegral.integral_of_le zero_le_one] using hRprod.integral_prod_left
  have he : (∫ u, -(1/2 : ℝ)*J u ∂μ) =
      ∫ u, -(1/2 : ℝ)*D2 u-a*(1-η)/6*D3 u+R u ∂μ :=
    integral_congr_ae (ae_of_all _ fun u => signed_hessian_fourth_kernel_identity hF x (T u) a η)
  rw [integral_const_mul,
    integral_add (f := fun u => -(1/2 : ℝ)*D2 u-a*(1-η)/6*D3 u) (g := R)
      ((hi2.const_mul _).sub (hi3.const_mul _)) hiR,
    integral_sub (f := fun u => -(1/2 : ℝ)*D2 u) (g := fun u => a*(1-η)/6*D3 u)
      (hi2.const_mul _) (hi3.const_mul _),integral_const_mul,integral_const_mul] at he
  dsimp only [J,R,D2,D3] at he
  rw [canonicalDiagonal_interval_fubini μ hF (by decide) hC hδ (hjet 2 (by decide) (by decide))
      T hT hbound x a (signedDensity η) hcν,
    canonicalDiagonal_interval_fubini μ hF (by decide) hC hδ (hjet 4 (by decide) (by decide))
      T hT hbound x a (seededFourthKernel a η) hcK] at he
  exact he

theorem genericRowOperator_fourth_from_signed_hessian
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x : Vector p)
    (γ γ' : ℝ → ℝ) {t : ℝ} (hγ : γ t ≠ 0) :
    genericRowOperator μ F T x (γ t) (variableRetentionDerivative γ γ' t)
      (variableRetention γ t*γ' t) =
      -(1/2 : ℝ)*(∫ u, canonicalDiagonal F 2 x (T u) ∂μ)-
        (γ t)*(1-variableEta γ γ' t)/6*(∫ u, canonicalDiagonal F 3 x (T u) ∂μ)+
        ∫ s in (0 : ℝ)..1, seededFourthKernel (γ t) (variableEta γ γ' t) s*
          (∫ u, canonicalDiagonal F 4 (x+(γ t*s) • T u) (T u) ∂μ) := by
  rw [genericRowOperator_eq_signed_hessian μ hF hC hδ hjet T hT hbound hc x γ γ' hγ]
  exact signed_hessian_fourth_kernel_expectation μ hF hC hδ hjet T hT hbound x (γ t) (variableEta γ γ' t)

end
end RectangleCLT.Companion.SplitV4.Printed
