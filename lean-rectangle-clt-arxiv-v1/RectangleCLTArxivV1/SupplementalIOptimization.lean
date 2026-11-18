import RectangleCLTArxivV1.SupplementalIIntegration
import RectangleCLTArxivV1.IntrinsicOptimization

/-! Scalar optimization after the actual separated and exceptional estimates.
The small-width comparison is an explicit input, not a CLT theorem. -/
namespace RectangleCLTArxivV1
noncomputable section
set_option autoImplicit false

def exceptionalBudgetRoot (δ K B : ℝ) : ℝ := (δ^2*B/K)^((1:ℝ)/3)
def exceptionalBudgetBandwidth (A δ K c B : ℝ) : ℝ :=
  A*max (δ*Real.sqrt (exceptionalCutoffLog c)) (exceptionalBudgetRoot δ K B)
def exceptionalBudgetRate (δ K c B : ℝ) : ℝ :=
  δ*K*Real.sqrt (exceptionalCutoffLog c)+K*exceptionalBudgetRoot δ K B

theorem exceptionalBudgetRoot_nonneg {δ K B : ℝ} (hK : 0 < K) (hB : 0 ≤ B) :
    0 ≤ exceptionalBudgetRoot δ K B :=
  Real.rpow_nonneg (by positivity) _

theorem exceptionalBudgetRoot_cube {δ K B : ℝ} (hK : 0 < K) (hB : 0 ≤ B) :
    (exceptionalBudgetRoot δ K B)^3=δ^2*B/K := by
  have hq : 0 ≤ δ^2*B/K := by positivity
  have ht := Real.rpow_mul_natCast hq ((1:ℝ)/3) 3
  norm_num at ht
  exact ht.symm

theorem exceptionalBudgetBandwidth_admissible {A δ K c B : ℝ}
    (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hc : 0 < c) (hc1 : c ≤ 1) :
    A*δ ≤ exceptionalBudgetBandwidth A δ K c B := by
  have hs : 1 ≤ Real.sqrt (exceptionalCutoffLog c) :=
    Real.one_le_sqrt.mpr (one_le_exceptionalCutoffLog hc hc1)
  exact mul_le_mul_of_nonneg_left
    ((le_mul_of_one_le_right hδ hs).trans (le_max_left _ _)) hA

theorem exceptionalBudgetBandwidth_pos {A δ K c B : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (hc : 0 < c) (hc1 : c ≤ 1) :
    0 < exceptionalBudgetBandwidth A δ K c B :=
  (mul_pos hA hδ).trans_le (exceptionalBudgetBandwidth_admissible hA.le hδ.le hc hc1)

/-- The two literal inverse-bandwidth comparisons in the printed proof. -/
theorem exceptionalBudgetBandwidth_inverse_costs {A δ K c B : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (hK : 0 < K) (hB : 0 ≤ B)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    δ^2*K*exceptionalCutoffLog c/exceptionalBudgetBandwidth A δ K c B ≤
      K*exceptionalBudgetBandwidth A δ K c B/A^2 ∧
    δ^2*B/(exceptionalBudgetBandwidth A δ K c B)^2 ≤
      K*exceptionalBudgetBandwidth A δ K c B/A^3 := by
  let u := δ*Real.sqrt (exceptionalCutoffLog c)
  let v := exceptionalBudgetRoot δ K B
  let h := exceptionalBudgetBandwidth A δ K c B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := exceptionalBudgetRoot_nonneg hK hB
  have hh : 0 < h := exceptionalBudgetBandwidth_pos hA hδ hc hc1
  have hAu : A*u ≤ h := mul_le_mul_of_nonneg_left (le_max_left u v) hA.le
  have hAv : A*v ≤ h := mul_le_mul_of_nonneg_left (le_max_right u v) hA.le
  have hAu2 := pow_le_pow_left₀ (mul_nonneg hA.le hu) hAu 2
  have hAv3 := pow_le_pow_left₀ (mul_nonneg hA.le hv) hAv 3
  rw [mul_pow] at hAu2 hAv3
  have husq : u^2=δ^2*exceptionalCutoffLog c := by
    dsimp [u]
    rw [mul_pow,Real.sq_sqrt (by linarith [one_le_exceptionalCutoffLog hc hc1])]
  have he : K*v^3=δ^2*B := by rw [exceptionalBudgetRoot_cube hK hB]; field_simp
  constructor
  · apply (div_le_div_iff₀ hh (sq_pos_of_pos hA)).mpr
    change δ^2*K*exceptionalCutoffLog c*A^2 ≤ K*h*h
    calc
      _ = K*(A^2*u^2) := by rw [husq]; ring
      _ ≤ K*h^2 := mul_le_mul_of_nonneg_left hAu2 hK.le
      _ = _ := by ring
  · apply (div_le_div_iff₀ (sq_pos_of_pos hh) (pow_pos hA 3)).mpr
    change δ^2*B*A^3 ≤ K*h*h^2
    calc
      _ = K*(A^3*v^3) := by rw [← he]; ring
      _ ≤ K*h^3 := mul_le_mul_of_nonneg_left hAv3 hK.le
      _ = _ := by ring

/-- Both positive costs are controlled by the larger bandwidth. This includes
B=0 without dividing by the exceptional budget. -/
theorem exceptionalBudgetBandwidth_total_cost {A δ K c B : ℝ}
    (hA : 1 ≤ A) (hδ : 0 < δ) (hK : 0 < K) (hB : 0 ≤ B)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    K*exceptionalBudgetBandwidth A δ K c B+
      δ^2*K*exceptionalCutoffLog c/exceptionalBudgetBandwidth A δ K c B+
      δ^2*B/(exceptionalBudgetBandwidth A δ K c B)^2 ≤
      3*A*exceptionalBudgetRate δ K c B := by
  let u := δ*Real.sqrt (exceptionalCutoffLog c)
  let v := exceptionalBudgetRoot δ K B
  let h := exceptionalBudgetBandwidth A δ K c B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := exceptionalBudgetRoot_nonneg hK hB
  have hh : 0 < h := exceptionalBudgetBandwidth_pos (zero_lt_one.trans_le hA) hδ hc hc1
  have hum : u ≤ max u v := le_max_left _ _
  have hvm : v ≤ max u v := le_max_right _ _
  have hmax : 0 ≤ max u v := hu.trans hum
  have hmult : max u v ≤ h := le_mul_of_one_le_left hmax hA
  have huh : u ≤ h := hum.trans hmult
  have hvh : v ≤ h := hvm.trans hmult
  have husq : u^2=δ^2*exceptionalCutoffLog c := by
    dsimp [u]
    rw [mul_pow,Real.sq_sqrt (by linarith [one_le_exceptionalCutoffLog hc hc1])]
  have hvcube : v^3=δ^2*B/K := exceptionalBudgetRoot_cube hK hB
  have hucost : δ^2*K*exceptionalCutoffLog c/h ≤ K*h := by
    apply (div_le_iff₀ hh).mpr
    have hu2 : u^2 ≤ h^2 := pow_le_pow_left₀ hu huh 2
    nlinarith [mul_le_mul_of_nonneg_left hu2 hK.le]
  have hvcost : δ^2*B/h^2 ≤ K*h := by
    apply (div_le_iff₀ (sq_pos_of_pos hh)).mpr
    have hv3 : v^3 ≤ h^3 := pow_le_pow_left₀ hv hvh 3
    have he : K*v^3=δ^2*B := by rw [hvcube]; field_simp
    nlinarith [mul_le_mul_of_nonneg_left hv3 hK.le]
  have hwidth : h ≤ A*(u+v) := by
    change A*max u v ≤ A*(u+v)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hA)
    exact max_le (by linarith) (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hwidth hK.le
  have hrate : K*(u+v)=exceptionalBudgetRate δ K c B := by
    dsimp [u,v,exceptionalBudgetRate]
    ring
  change K*h+_+_ ≤ _
  nlinarith [hucost,hvcost,hscaled]

/-- A large seed is handled by the unit probability bound. -/
theorem exceptionalBudget_large_bandwidth_rate {A κ δ L c B : ℝ}
    (hA : 1 ≤ A) (hκ : 1 ≤ κ) (hδ : 0 < δ) (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hlarge : 1/4 ≤ L*(exceptionalBudgetBandwidth A δ (κ*L) c B)^2) :
    1 ≤ 2*A*exceptionalBudgetRate δ (κ*L) c B := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hh := exceptionalBudgetBandwidth_pos (zero_lt_one.trans_le hA) hδ hc hc1 (K := κ*L) (B := B)
  have hs : Real.sqrt L ≤ L := (Real.sqrt_le_iff).mpr ⟨hLp.le,by nlinarith⟩
  have hk : Real.sqrt L ≤ κ*L := hs.trans (le_mul_of_one_le_left hLp.le hκ)
  have hsq : (Real.sqrt L*exceptionalBudgetBandwidth A δ (κ*L) c B)^2=
      L*(exceptionalBudgetBandwidth A δ (κ*L) c B)^2 := by rw [mul_pow,Real.sq_sqrt hLp.le]
  have hhalf : 1/2 ≤ Real.sqrt L*exceptionalBudgetBandwidth A δ (κ*L) c B := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg L) hh.le]
  have hu : 0 ≤ δ*Real.sqrt (exceptionalCutoffLog c) := by positivity
  have hv := exceptionalBudgetRoot_nonneg (δ := δ) (mul_pos (zero_lt_one.trans_le hκ) hLp) hB
  have hm : max (δ*Real.sqrt (exceptionalCutoffLog c)) (exceptionalBudgetRoot δ (κ*L) B) ≤
      δ*Real.sqrt (exceptionalCutoffLog c)+exceptionalBudgetRoot δ (κ*L) B :=
    max_le (by linarith) (by linarith)
  have hw := mul_le_mul_of_nonneg_left hm (zero_le_one.trans hA)
  have hscale := mul_le_mul_of_nonneg_right hk hh.le
  unfold exceptionalBudgetBandwidth exceptionalBudgetRate at *
  nlinarith only [hhalf,hscale,mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ κ*L)]


def exceptionalBudgetOptimizationConstant (A C : ℝ) : ℝ := 1+2*A+3*A*C

/-- Capped scalar reduction of the genuine small-width comparison. No
concentration or CLT conclusion is hidden in the bandwidth optimizer. -/
theorem exceptionalBudget_rate_of_small_bandwidth_estimate
    {A C κ δ L c B error : ℝ}
    (hA : 1 ≤ A) (hC : 0 ≤ C) (hκ : 1 ≤ κ) (hδ : 0 < δ)
    (hL : 1 ≤ L) (hB : 0 ≤ B) (hc : 0 < c) (hc1 : c ≤ 1)
    (hone : error ≤ 1)
    (hsmall : L*(exceptionalBudgetBandwidth A δ (κ*L) c B)^2 < 1/4 →
      error ≤ C*(κ*L*exceptionalBudgetBandwidth A δ (κ*L) c B+
        δ^2*(κ*L)*exceptionalCutoffLog c/exceptionalBudgetBandwidth A δ (κ*L) c B+
        δ^2*B/(exceptionalBudgetBandwidth A δ (κ*L) c B)^2)) :
    error ≤ exceptionalBudgetOptimizationConstant A C*
      min 1 (exceptionalBudgetRate δ (κ*L) c B) := by
  have hK : 0 < κ*L := mul_pos (zero_lt_one.trans_le hκ) (zero_lt_one.trans_le hL)
  have hC1 : 1 ≤ exceptionalBudgetOptimizationConstant A C := by
    unfold exceptionalBudgetOptimizationConstant
    nlinarith [mul_nonneg (zero_le_one.trans hA) hC]
  have hCA : 2*A ≤ exceptionalBudgetOptimizationConstant A C := by
    unfold exceptionalBudgetOptimizationConstant
    nlinarith [mul_nonneg (zero_le_one.trans hA) hC]
  have hCC : C*(3*A) ≤ exceptionalBudgetOptimizationConstant A C := by
    unfold exceptionalBudgetOptimizationConstant
    linarith
  have hr : 0 ≤ exceptionalBudgetRate δ (κ*L) c B := by
    unfold exceptionalBudgetRate
    exact add_nonneg (by positivity) (mul_nonneg hK.le (exceptionalBudgetRoot_nonneg hK hB))
  have hraw : error ≤ exceptionalBudgetOptimizationConstant A C*exceptionalBudgetRate δ (κ*L) c B := by
    by_cases hs : L*(exceptionalBudgetBandwidth A δ (κ*L) c B)^2 < 1/4
    · have hb := exceptionalBudgetBandwidth_total_cost hA hδ hK hB hc hc1
      have he := (hsmall hs).trans (mul_le_mul_of_nonneg_left hb hC)
      exact he.trans (by nlinarith [mul_le_mul_of_nonneg_right hCC hr])
    · exact hone.trans ((exceptionalBudget_large_bandwidth_rate hA hκ hδ hL hB hc hc1 (le_of_not_gt hs)).trans
        (mul_le_mul_of_nonneg_right hCA hr))
  by_cases hs : exceptionalBudgetRate δ (κ*L) c B ≤ 1
  · simpa only [min_eq_right hs] using hraw
  · simpa only [min_eq_left (le_of_not_ge hs),mul_one] using hone.trans hC1

/-- The cube-root width gives precisely the printed two-thirds powers. -/
theorem exceptionalBudgetRoot_scaled {δ K B : ℝ} (hδ : 0 ≤ δ) (hK : 0 < K) (hB : 0 ≤ B) :
    K*exceptionalBudgetRoot δ K B=
      δ^((2:ℝ)/3)*K^((2:ℝ)/3)*B^((1:ℝ)/3) := by
  have hq : 0 ≤ δ^2*B := by positivity
  have hδpow : (δ^2)^((1:ℝ)/3)=δ^((2:ℝ)/3) := by
    convert (Real.rpow_natCast_mul hδ 2 ((1:ℝ)/3)).symm using 1 <;> norm_num
  have hKpow : K^((1:ℝ)/3) ≠ 0 := (Real.rpow_pos_of_pos hK _).ne'
  have hprod : K^((2:ℝ)/3)*K^((1:ℝ)/3)=K := by
    rw [← Real.rpow_add hK]
    norm_num
  have hquot : K/K^((1:ℝ)/3)=K^((2:ℝ)/3) := (div_eq_iff hKpow).mpr hprod.symm
  unfold exceptionalBudgetRoot
  rw [Real.div_rpow hq hK.le,Real.mul_rpow (sq_nonneg δ) hB,hδpow]
  calc
    _ = δ^((2:ℝ)/3)*(K/K^((1:ℝ)/3))*B^((1:ℝ)/3) := by ring
    _ = _ := by rw [hquot]

theorem exceptionalBudgetRate_eq_printed {δ K c B : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 < K) (hB : 0 ≤ B) :
    exceptionalBudgetRate δ K c B=δ*K*Real.sqrt (exceptionalCutoffLog c)+
      δ^((2:ℝ)/3)*K^((2:ℝ)/3)*B^((1:ℝ)/3) := by
  exact congrArg (fun z => δ*K*Real.sqrt (exceptionalCutoffLog c)+z)
    (exceptionalBudgetRoot_scaled hδ hK hB)


/-- The intrinsic coefficient can be replaced after optimization, including
its two-thirds power in the exceptional cost. -/
theorem exceptionalBudgetRate_le_coefficient {κ C g δ L c B : ℝ}
    (hκ : 0 < κ) (hg : 0 < g) (hC : 1 ≤ C) (hcoef : κ ≤ C*g)
    (hδ : 0 ≤ δ) (hL : 0 < L) (hB : 0 ≤ B) :
    exceptionalBudgetRate δ (κ*L) c B ≤ C*exceptionalBudgetRate δ (g*L) c B := by
  have hKκ : 0 < κ*L := mul_pos hκ hL
  have hKg : 0 < g*L := mul_pos hg hL
  have hK : κ*L ≤ C*(g*L) := by nlinarith [mul_le_mul_of_nonneg_right hcoef hL.le]
  have hp := Real.rpow_le_rpow hKκ.le hK (by norm_num : (0:ℝ) ≤ 2/3)
  rw [Real.mul_rpow (zero_le_one.trans hC) hKg.le] at hp
  have hCp : C^((2:ℝ)/3) ≤ C := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hC (by norm_num : (2:ℝ)/3 ≤ 1))
  have hp' : (κ*L)^((2:ℝ)/3) ≤ C*(g*L)^((2:ℝ)/3) :=
    hp.trans (mul_le_mul_of_nonneg_right hCp (Real.rpow_nonneg hKg.le _))
  have hfirst := mul_le_mul_of_nonneg_left hK
    (mul_nonneg hδ (Real.sqrt_nonneg (exceptionalCutoffLog c)))
  have hsecond := mul_le_mul_of_nonneg_left hp'
    (mul_nonneg (Real.rpow_nonneg hδ ((2:ℝ)/3)) (Real.rpow_nonneg hB ((1:ℝ)/3)))
  rw [exceptionalBudgetRate_eq_printed hδ hKκ hB,exceptionalBudgetRate_eq_printed hδ hKg hB]
  nlinarith only [hfirst,hsecond]

theorem exceptionalBudget_trivial_large_envelope {error g δ L c B : ℝ}
    (hone : error ≤ 1) (hg : Real.sqrt (2/Real.pi) ≤ g)
    (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hc : 0 < c) (hc1 : c ≤ 1) (hlarge : g < δ*L) :
    error ≤ (Real.pi/2)*exceptionalBudgetRate δ (g*L) c B := by
  have hp : 0 < Real.sqrt (2/Real.pi) := by positivity
  have hgp : 0 < g := hp.trans_le hg
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hgsq : 2/Real.pi ≤ g^2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2/Real.pi by positivity),sq_nonneg (g-Real.sqrt (2/Real.pi))]
  have hs : 1 ≤ Real.sqrt (exceptionalCutoffLog c) := Real.one_le_sqrt.mpr (one_le_exceptionalCutoffLog hc hc1)
  have hlinear : g^2 ≤ δ*(g*L)*Real.sqrt (exceptionalCutoffLog c) := by
    have h0 : 0 ≤ δ*(g*L) := by positivity
    have hle := le_mul_of_one_le_right h0 hs
    nlinarith [mul_le_mul_of_nonneg_left hlarge.le hgp.le]
  have hroot := mul_nonneg (mul_pos hgp hLp).le
    (exceptionalBudgetRoot_nonneg (δ := δ) (mul_pos hgp hLp) hB)
  have hrate : 2/Real.pi ≤ exceptionalBudgetRate δ (g*L) c B := by
    unfold exceptionalBudgetRate
    linarith
  have hr := mul_le_mul_of_nonneg_left hrate (show 0 ≤ Real.pi/2 by positivity)
  have he : (Real.pi/2)*(2/Real.pi)=1 := by field_simp
  exact hone.trans (by simpa only [he] using hr)

end
end RectangleCLTArxivV1
