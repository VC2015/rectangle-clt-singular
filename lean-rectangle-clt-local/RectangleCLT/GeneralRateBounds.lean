import RectangleCLT.GeneralStatement
import RectangleCLT.CombinedCoefficients
import RectangleCLT.GaussianComponentClosureLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Order and continuity of the exact general moment alternatives. These
are scalar lemmas used by the covariance-preserving Gaussian limit and the
combined proxy consequences. They do not assert an approximation bound. -/

open Filter
open scoped Topology

namespace RectangleCLT

noncomputable section

theorem optionalMin_mono {parameter candidate candidate' fallback fallback' : ℝ}
    (hfall : fallback ≤ fallback') (hcand : 0 < parameter → candidate ≤ candidate') :
    optionalMin parameter candidate fallback ≤ optionalMin parameter candidate' fallback' := by
  unfold optionalMin
  split_ifs with hp
  · exact min_le_min (hcand hp) hfall
  · exact hfall

theorem generalFourthRate_mono {γ₄ γ₄' L b c a₃ a₄ : ℝ}
    (hγ₄ : 0 ≤ γ₄) (hγ : γ₄ ≤ γ₄') (hL : 0 ≤ L) (hc : 0 < c) :
    generalFourthRate γ₄ L b c a₃ a₄ ≤ generalFourthRate γ₄' L b c a₃ a₄ := by
  have hs := Real.sqrt_le_sqrt hγ
  unfold generalFourthRate
  apply optionalMin_mono
  · apply optionalMin_mono
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hγ₄ hγ (by norm_num))
          (Real.sqrt_nonneg L)) (Real.rpow_nonneg hc.le _)
    · intro ha
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs hL)
        (mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg ha.le _))
  · intro hb
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs hL)
      (mul_nonneg hb.le (Real.sqrt_nonneg c))

theorem generalCoefficientRate_mono {δ δ' γ₃ γ₄ γ₄' L b c a₃ a₄ : ℝ}
    (hδ : δ ≤ δ') (hγ₄ : 0 ≤ γ₄) (hγ : γ₄ ≤ γ₄')
    (hL : 0 ≤ L) (hc : 0 < c) :
    generalCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ ≤
      generalCoefficientRate δ' γ₃ γ₄' L b c a₃ a₄ :=
  add_le_add (add_le_add_left (generalFourthRate_mono hγ₄ hγ hL hc) _)
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hδ (Real.sqrt_nonneg L)) hc.le)

theorem generalFourthRate_tendsto {α : Type*} {l : Filter α}
    {f : α → ℝ} {γ₄ : ℝ} (hf : Tendsto f l (𝓝 γ₄)) (L b c a₃ a₄ : ℝ) :
    Tendsto (fun i => generalFourthRate (f i) L b c a₃ a₄) l
      (𝓝 (generalFourthRate γ₄ L b c a₃ a₄)) := by
  have hs := hf.sqrt
  have hr := hf.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
  unfold generalFourthRate optionalMin
  split_ifs <;>
    first
    | exact ((hs.mul_const L).div_const (b * Real.sqrt c)).min
        (((hs.mul_const L).div_const _).min ((hr.mul_const _).div_const _))
    | exact ((hs.mul_const L).div_const (b * Real.sqrt c)).min
        ((hr.mul_const _).div_const _)
    | exact ((hs.mul_const L).div_const _).min ((hr.mul_const _).div_const _)
    | exact (hr.mul_const _).div_const _

theorem generalCoefficientRate_tendsto {α : Type*} {l : Filter α}
    {d g : α → ℝ} {δ γ₄ : ℝ}
    (hd : Tendsto d l (𝓝 δ)) (hg : Tendsto g l (𝓝 γ₄))
    (γ₃ L b c a₃ a₄ : ℝ) :
    Tendsto (fun i => generalCoefficientRate (d i) γ₃ (g i) L b c a₃ a₄) l
      (𝓝 (generalCoefficientRate δ γ₃ γ₄ L b c a₃ a₄)) := by
  exact ((tendsto_const_nhds (x := generalThirdRate γ₃ L b c a₃)).add
    (generalFourthRate_tendsto hg L b c a₃ a₄)).add
    ((hd.mul_const (Real.sqrt L)).div_const c)

theorem generalGaussianComponent_bound_passage
    {error C δ γ₃ γ₄ L b c a₃ a₄ M : ℝ} (p : ℕ) (hδ : 0 ≤ δ)
    (hbound : ∀ k : ℕ, 1 ≤ k →
      error ≤ C * min 1
        (generalCoefficientRate (gaussianComponentEnvelopeUpper δ M k) γ₃
          (gaussianComponentFourthUpper γ₄ M k) L b c a₃ a₄) +
        gaussianComponentCouplingUpper p M k) :
    error ≤ C * min 1 (generalCoefficientRate δ γ₃ γ₄ L b c a₃ a₄) := by
  have hr := generalCoefficientRate_tendsto
    (gaussianComponentEnvelopeUpper_tendsto δ M hδ)
    (gaussianComponentFourthUpper_tendsto γ₄ M) γ₃ L b c a₃ a₄
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).min hr).const_mul C).add
    (gaussianComponentCouplingUpper_tendsto p M)
  have he : ∀ᶠ k : ℕ in atTop,
      error ≤ C * min 1
        (generalCoefficientRate (gaussianComponentEnvelopeUpper δ M k) γ₃
          (gaussianComponentFourthUpper γ₄ M k) L b c a₃ a₄) +
        gaussianComponentCouplingUpper p M k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hbound k hk
  simpa only [add_zero] using ge_of_tendsto hlim he

theorem generalThirdRate_le_combined {γ₃ L b c a₃ : ℝ}
    (hγ₃ : 0 ≤ γ₃) (hL : 0 ≤ L) (hc : 0 < c) (ha₃ : 0 < a₃) :
    generalThirdRate γ₃ L b c a₃ ≤
      γ₃ * L * Real.sqrt L * combinedThirdCoefficient b c a₃ := by
  have hn : 0 ≤ γ₃ * L * Real.sqrt L := by positivity
  unfold generalThirdRate
  have hh : optionalMin b (γ₃ * L * Real.sqrt L / b ^ 2)
      (optionalMin a₃ (γ₃ * L * Real.sqrt L / (c * a₃))
        (γ₃ ^ (1 / 3 : ℝ) * Real.sqrt L / c ^ (2 / 3 : ℝ))) ≤
      optionalMin b (γ₃ * L * Real.sqrt L / b ^ 2)
        (γ₃ * L * Real.sqrt L / (c * a₃)) :=
    optionalMin_mono (optionalMin_le_candidate ha₃ _ _) (fun _ => le_rfl)
  apply hh.trans_eq
  unfold optionalMin combinedThirdCoefficient
  split_ifs
  · rw [mul_min_of_nonneg _ _ hn]
    simp only [div_eq_mul_inv, one_mul]
  · simp only [div_eq_mul_inv, one_mul]

theorem generalFourthRate_le_combined {γ₄ L b c a₃ a₄ : ℝ}
    (hγ₄ : 0 ≤ γ₄) (hL : 0 ≤ L)
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    generalFourthRate γ₄ L b c a₃ a₄ ≤
      Real.sqrt γ₄ * L / Real.sqrt c * combinedFourthCoefficient b c a₃ a₄ := by
  have hn : 0 ≤ Real.sqrt γ₄ * L / Real.sqrt c := by positivity
  have ha₃₄ := mul_pos ha₃ ha₄
  unfold generalFourthRate
  have hh : optionalMin b (Real.sqrt γ₄ * L / (b * Real.sqrt c))
      (optionalMin (a₃ * a₄)
        (Real.sqrt γ₄ * L / (c ^ (5 / 6 : ℝ) * (a₃ * a₄) ^ (1 / 3 : ℝ)))
        (γ₄ ^ (1 / 4 : ℝ) * Real.sqrt L / c ^ (3 / 4 : ℝ))) ≤
      optionalMin b (Real.sqrt γ₄ * L / (b * Real.sqrt c))
        (Real.sqrt γ₄ * L / (c ^ (5 / 6 : ℝ) * (a₃ * a₄) ^ (1 / 3 : ℝ))) :=
    optionalMin_mono (optionalMin_le_candidate ha₃₄ _ _) (fun _ => le_rfl)
  apply hh.trans_eq
  have heq : Real.sqrt γ₄ * L /
      (c ^ (5 / 6 : ℝ) * (a₃ * a₄) ^ (1 / 3 : ℝ)) =
      (Real.sqrt γ₄ * L / Real.sqrt c) * (1 / localFourthScale c a₃ a₄) := by
    have hsqrt := sqrt_mul_localFourthScale hc ha₃ ha₄
    simp only [Real.rpow_eq_pow] at hsqrt
    rw [← hsqrt]
    ring
  unfold optionalMin combinedFourthCoefficient
  split_ifs
  · rw [mul_min_of_nonneg _ _ hn, heq]
    congr 1
    ring
  · exact heq

theorem generalCoefficientRate_le_combined {δ γ₃ γ₄ L b c a₃ a₄ : ℝ}
    (hγ₃ : 0 ≤ γ₃) (hγ₄ : 0 ≤ γ₄) (hL : 0 ≤ L)
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    generalCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ ≤
      combinedCoefficientRate δ γ₃ γ₄ L b c a₃ a₄ :=
  add_le_add_right (add_le_add (generalThirdRate_le_combined hγ₃ hL hc ha₃)
    (generalFourthRate_le_combined hγ₄ hL hc ha₃ ha₄)) _

end

end RectangleCLT
