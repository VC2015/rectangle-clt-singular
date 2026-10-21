import RectangleCLT.UnequalMasterStatement
import RectangleCLT.GeneralRateBounds
import RectangleCLT.CombinedOptimization

/-! Independent optimization of the general cubic and fourth-order
alternatives. All approximation estimates in this scalar file are explicit
premises; the probabilistic assembly supplies them separately. -/

namespace RectangleCLT

noncomputable section

def BandwidthWitness (K : ℝ) (f : ℝ → ℝ) (R : ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ K * t ≤ R ∧ ∀ h : ℝ, 0 < h → t ≤ h → f h ≤ R

theorem BandwidthWitness.optionalMin {K parameter candidate fallback : ℝ}
    {f : ℝ → ℝ} (hfall : BandwidthWitness K f fallback)
    (hcand : 0 < parameter → BandwidthWitness K f candidate) :
    BandwidthWitness K f (optionalMin parameter candidate fallback) := by
  unfold RectangleCLT.optionalMin
  split_ifs with hp
  · by_cases hcf : candidate ≤ fallback
    · simpa only [min_eq_left hcf] using hcand hp
    · simpa only [min_eq_right (le_of_not_ge hcf)] using hfall
  · exact hfall

theorem rate_of_two_bandwidth_witnesses {error δ K R₃ R₄ C : ℝ}
    {f₃ f₄ : ℝ → ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h₃ : BandwidthWitness K f₃ R₃) (h₄ : BandwidthWitness K f₄ R₄)
    (hunit : error ≤ 1)
    (hmaster : ∀ h : ℝ, 12 * δ ≤ h →
      error ≤ C * (f₃ h + f₄ h + K * h)) :
    error ≤ max 1 (12 * C) * min 1 (R₃ + R₄ + K * δ) := by
  obtain ⟨t₃, ht₃, hK₃, hterm₃⟩ := h₃
  obtain ⟨t₄, ht₄, hK₄, hterm₄⟩ := h₄
  have hR₃ : 0 ≤ R₃ := (mul_nonneg hK ht₃).trans hK₃
  have hR₄ : 0 ≤ R₄ := (mul_nonneg hK ht₄).trans hK₄
  have hband : 12 * δ ≤ 12 * δ + t₃ + t₄ := by linarith
  have hh : 0 < 12 * δ + t₃ + t₄ := by positivity
  have hthird := hterm₃ _ hh (by linarith : t₃ ≤ 12 * δ + t₃ + t₄)
  have hfourth := hterm₄ _ hh (by linarith : t₄ ≤ 12 * δ + t₃ + t₄)
  apply le_max_mul_min_of_le_one (by positivity) hunit
  calc
    error ≤ C * (f₃ (12 * δ + t₃ + t₄) + f₄ (12 * δ + t₃ + t₄) +
        K * (12 * δ + t₃ + t₄)) := hmaster _ hband
    _ ≤ C * (R₃ + R₄ + K * (12 * δ + t₃ + t₄)) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (add_le_add hthird hfourth) _) hC
    _ ≤ C * (12 * (R₃ + R₄ + K * δ)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      nlinarith only [hK₃, hK₄, hR₃, hR₄]
    _ = _ := by ring

theorem positive_root_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

theorem positive_root_fourth {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

theorem general_root_cube_balance {c γ : ℝ} (hc : 0 < c) (hγ : 0 ≤ γ) :
    (c * γ) ^ (1 / 3 : ℝ) / c = γ ^ (1 / 3 : ℝ) / c ^ (2 / 3 : ℝ) := by
  have htwo : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  apply (div_eq_div_iff hc.ne' htwo.ne').mpr
  rw [Real.mul_rpow hc.le hγ]
  have hp : c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ) = c := by
    rw [← Real.rpow_add hc]
    norm_num
  calc
    _ = γ ^ (1 / 3 : ℝ) * (c ^ (1 / 3 : ℝ) * c ^ (2 / 3 : ℝ)) := by ring
    _ = _ := by rw [hp]

theorem general_root_fourth_balance {c γ : ℝ} (hc : 0 < c) (hγ : 0 ≤ γ) :
    (c * γ) ^ (1 / 4 : ℝ) / c = γ ^ (1 / 4 : ℝ) / c ^ (3 / 4 : ℝ) := by
  have hthree : 0 < c ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hc _
  apply (div_eq_div_iff hc.ne' hthree.ne').mpr
  rw [Real.mul_rpow hc.le hγ]
  have hp : c ^ (1 / 4 : ℝ) * c ^ (3 / 4 : ℝ) = c := by
    rw [← Real.rpow_add hc]
    norm_num
  calc
    _ = γ ^ (1 / 4 : ℝ) * (c ^ (1 / 4 : ℝ) * c ^ (3 / 4 : ℝ)) := by ring
    _ = _ := by rw [hp]

theorem cubic_bandwidth_witness {γ L c : ℝ}
    (hγ : 0 ≤ γ) (hL : 0 ≤ L) (hc : 0 < c) :
    BandwidthWitness (Real.sqrt L / c) (fun h => γ * Real.sqrt L / h ^ 2)
      (γ ^ (1 / 3 : ℝ) * Real.sqrt L / c ^ (2 / 3 : ℝ)) := by
  let t := (c * γ) ^ (1 / 3 : ℝ)
  have ht : 0 ≤ t := Real.rpow_nonneg (mul_nonneg hc.le hγ) _
  have ht3 : t ^ 3 = c * γ := positive_root_cube (mul_nonneg hc.le hγ)
  have hbalance : Real.sqrt L / c * t =
      γ ^ (1 / 3 : ℝ) * Real.sqrt L / c ^ (2 / 3 : ℝ) := by
    calc
      _ = (t / c) * Real.sqrt L := by ring
      _ = _ := by rw [show t / c = _ from general_root_cube_balance hc hγ]; ring
  refine ⟨t, ht, hbalance.le, ?_⟩
  intro h hh hth
  rw [← hbalance]
  have hsq : t ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ ht hth 2
  have hmain : c * γ ≤ t * h ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hsq ht]
  have hdiv : γ / h ^ 2 ≤ t / c := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hh) hc).mpr
    nlinarith only [hmain]
  calc
    _ = (γ / h ^ 2) * Real.sqrt L := by ring
    _ ≤ (t / c) * Real.sqrt L := mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg L)
    _ = _ := by ring

theorem quartic_bandwidth_witness {γ L c : ℝ}
    (hγ : 0 ≤ γ) (hL : 0 ≤ L) (hc : 0 < c) :
    BandwidthWitness (Real.sqrt L / c) (fun h => γ * Real.sqrt L / h ^ 3)
      (γ ^ (1 / 4 : ℝ) * Real.sqrt L / c ^ (3 / 4 : ℝ)) := by
  let t := (c * γ) ^ (1 / 4 : ℝ)
  have ht : 0 ≤ t := Real.rpow_nonneg (mul_nonneg hc.le hγ) _
  have ht4 : t ^ 4 = c * γ := positive_root_fourth (mul_nonneg hc.le hγ)
  have hbalance : Real.sqrt L / c * t =
      γ ^ (1 / 4 : ℝ) * Real.sqrt L / c ^ (3 / 4 : ℝ) := by
    calc
      _ = (t / c) * Real.sqrt L := by ring
      _ = _ := by rw [show t / c = _ from general_root_fourth_balance hc hγ]; ring
  refine ⟨t, ht, hbalance.le, ?_⟩
  intro h hh hth
  rw [← hbalance]
  have hcube : t ^ 3 ≤ h ^ 3 := pow_le_pow_left₀ ht hth 3
  have hmain : c * γ ≤ t * h ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hcube ht]
  have hdiv : γ / h ^ 3 ≤ t / c := by
    apply (div_le_div_iff₀ (pow_pos hh 3) hc).mpr
    nlinarith only [hmain]
  calc
    _ = (γ / h ^ 3) * Real.sqrt L := by ring
    _ ≤ (t / c) * Real.sqrt L := mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg L)
    _ = _ := by ring

theorem square_root_bandwidth_witness {F K : ℝ} (hF : 0 ≤ F) (hK : 0 < K) :
    BandwidthWitness K (fun h => F / h) (Real.sqrt (F * K)) := by
  have hsK := Real.sqrt_pos.mpr hK
  let t := Real.sqrt F / Real.sqrt K
  have ht : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) hsK.le
  have hbalance : K * t = Real.sqrt (F * K) := by
    rw [Real.sqrt_mul hF]
    dsimp only [t]
    rw [← mul_div_assoc]
    apply (div_eq_iff hsK.ne').mpr
    calc
      K * Real.sqrt F = Real.sqrt F * (Real.sqrt K) ^ 2 := by
        rw [Real.sq_sqrt hK.le]
        ring
      _ = _ := by ring
  have hprod : Real.sqrt (F * K) * t = F := by
    rw [Real.sqrt_mul hF]
    dsimp only [t]
    calc
      _ = (Real.sqrt F) ^ 2 * (Real.sqrt K / Real.sqrt K) := by ring
      _ = (Real.sqrt F) ^ 2 := by rw [div_self hsK.ne', mul_one]
      _ = F := Real.sq_sqrt hF
  refine ⟨t, ht, hbalance.le, ?_⟩
  intro h hh hth
  apply (div_le_iff₀ hh).mpr
  calc
    F = Real.sqrt (F * K) * t := hprod.symm
    _ ≤ Real.sqrt (F * K) * h := mul_le_mul_of_nonneg_left hth (Real.sqrt_nonneg _)

theorem BandwidthWitness.of_le {K R : ℝ} {f g : ℝ → ℝ}
    (hg : BandwidthWitness K g R) (hfg : ∀ h : ℝ, 0 < h → f h ≤ g h) :
    BandwidthWitness K f R := by
  obtain ⟨t, ht, hKt, hbound⟩ := hg
  exact ⟨t, ht, hKt, fun h hh hth => (hfg h hh).trans (hbound h hh hth)⟩

theorem BandwidthWitness.constant {K R : ℝ} {f : ℝ → ℝ}
    (hR : 0 ≤ R) (hf : ∀ h : ℝ, 0 < h → f h ≤ R) :
    BandwidthWitness K f R :=
  ⟨0, le_rfl, by simpa only [mul_zero] using hR, fun h hh _ => hf h hh⟩

theorem generalThird_bandwidth_witness {γ L b c a₃ : ℝ}
    (hγ : 0 ≤ γ) (hL : 0 ≤ L) (hc : 0 < c) :
    BandwidthWitness (Real.sqrt L / c)
      (fun h => γ * Real.sqrt L * masterThirdCoefficient L b c a₃ h)
      (generalThirdRate γ L b c a₃) := by
  have hγs : 0 ≤ γ * Real.sqrt L := by positivity
  unfold generalThirdRate
  apply BandwidthWitness.optionalMin
  · apply BandwidthWitness.optionalMin
    · apply (cubic_bandwidth_witness hγ hL hc).of_le
      intro h hh
      have hcoef : masterThirdCoefficient L b c a₃ h ≤ 1 / h ^ 2 :=
        (optionalMin_le_fallback _ _ _).trans (optionalMin_le_fallback _ _ _)
      exact (mul_le_mul_of_nonneg_left hcoef hγs).trans_eq (by ring)
    · intro ha₃
      apply BandwidthWitness.constant (by positivity)
      intro h hh
      have hcoef : masterThirdCoefficient L b c a₃ h ≤ L / (c * a₃) :=
        (optionalMin_le_fallback _ _ _).trans (optionalMin_le_candidate ha₃ _ _)
      exact (mul_le_mul_of_nonneg_left hcoef hγs).trans_eq (by ring)
  · intro hb
    apply BandwidthWitness.constant (by positivity)
    intro h hh
    have hcoef : masterThirdCoefficient L b c a₃ h ≤ L / b ^ 2 :=
      optionalMin_le_candidate hb _ _
    exact (mul_le_mul_of_nonneg_left hcoef hγs).trans_eq (by ring)

theorem linear_fourth_bandwidth_witness {γ L c η : ℝ}
    (hγ : 0 ≤ γ) (hL : 0 < L) (hc : 0 < c) (hη : 0 ≤ η) :
    BandwidthWitness (Real.sqrt L / c)
      (fun h => γ * L * Real.sqrt L * η ^ 2 / h)
      (Real.sqrt γ * L / Real.sqrt c * η) := by
  have hh := square_root_bandwidth_witness
    (show 0 ≤ γ * L * Real.sqrt L * η ^ 2 by positivity)
    (div_pos (Real.sqrt_pos.mpr hL) hc)
  rw [combined_fourth_balance hγ hL.le hη hc] at hh
  exact hh

private theorem generalLocalFourthScale_square {c a₃ a₄ : ℝ}
    (hc : 0 < c) (ha : 0 < a₃ * a₄) :
    ((c * a₃ * a₄) ^ (1 / 3 : ℝ)) ^ 2 = (c * a₃ * a₄) ^ (2 / 3 : ℝ) := by
  have hp : 0 ≤ c * a₃ * a₄ := by simpa only [mul_assoc] using mul_nonneg hc.le ha.le
  rw [← Real.rpow_mul_natCast hp]
  norm_num

private theorem generalLocalFourthScale_product {c a₃ a₄ : ℝ}
    (hc : 0 < c) (ha : 0 < a₃ * a₄) :
    Real.sqrt c * (c * a₃ * a₄) ^ (1 / 3 : ℝ) =
      c ^ (5 / 6 : ℝ) * (a₃ * a₄) ^ (1 / 3 : ℝ) := by
  rw [mul_assoc c a₃ a₄, Real.mul_rpow hc.le ha.le,
    Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hc]
  norm_num

theorem generalFourth_bandwidth_witness {γ L b c a₃ a₄ : ℝ}
    (hγ : 0 ≤ γ) (hL : 0 < L) (hc : 0 < c) :
    BandwidthWitness (Real.sqrt L / c)
      (fun h => γ * Real.sqrt L * masterFourthCoefficient L b c a₃ a₄ h)
      (generalFourthRate γ L b c a₃ a₄) := by
  have hγs : 0 ≤ γ * Real.sqrt L := by positivity
  unfold generalFourthRate
  apply BandwidthWitness.optionalMin
  · apply BandwidthWitness.optionalMin
    · apply (quartic_bandwidth_witness hγ hL.le hc).of_le
      intro h hh
      have hcoef : masterFourthCoefficient L b c a₃ a₄ h ≤ 1 / h ^ 3 :=
        (optionalMin_le_fallback _ _ _).trans (optionalMin_le_fallback _ _ _)
      exact (mul_le_mul_of_nonneg_left hcoef hγs).trans_eq (by ring)
    · intro ha
      let d := (c * a₃ * a₄) ^ (1 / 3 : ℝ)
      have hd : 0 < d := Real.rpow_pos_of_pos (by simpa only [mul_assoc] using mul_pos hc ha) _
      have hlin := linear_fourth_bandwidth_witness hγ hL hc (one_div_nonneg.mpr hd.le)
      have hrate : Real.sqrt γ * L / Real.sqrt c * (1 / d) =
          Real.sqrt γ * L / (c ^ (5 / 6 : ℝ) * (a₃ * a₄) ^ (1 / 3 : ℝ)) := by
        rw [← generalLocalFourthScale_product hc ha]
        dsimp only [d]
        ring
      rw [hrate] at hlin
      apply hlin.of_le
      intro h hh
      have hcoef : masterFourthCoefficient L b c a₃ a₄ h ≤
          L / ((c * a₃ * a₄) ^ (2 / 3 : ℝ) * h) :=
        (optionalMin_le_fallback _ _ _).trans (optionalMin_le_candidate ha _ _)
      calc
        _ ≤ γ * Real.sqrt L * (L / ((c * a₃ * a₄) ^ (2 / 3 : ℝ) * h)) :=
          mul_le_mul_of_nonneg_left hcoef hγs
        _ = _ := by
          rw [← generalLocalFourthScale_square hc ha]
          dsimp only [d]
          ring
  · intro hb
    have hlin := linear_fourth_bandwidth_witness hγ hL hc (one_div_nonneg.mpr hb.le)
    have hrate : Real.sqrt γ * L / Real.sqrt c * (1 / b) =
        Real.sqrt γ * L / (b * Real.sqrt c) := by ring
    rw [hrate] at hlin
    apply hlin.of_le
    intro h hh
    have hcoef : masterFourthCoefficient L b c a₃ a₄ h ≤ L / (b ^ 2 * h) :=
      optionalMin_le_candidate hb _ _
    exact (mul_le_mul_of_nonneg_left hcoef hγs).trans_eq (by ring)

/-- The exact independent selection of all three cubic and fourth-order
alternatives. Degenerate local submatrices and vanishing moments are
included. The master estimate remains an explicit scalar premise here. -/
theorem general_rate_of_master {error δ γ₃ γ₄ L b c a₃ a₄ C : ℝ}
    (hδ : 0 < δ) (hγ₃ : 0 ≤ γ₃) (hγ₄ : 0 ≤ γ₄) (hL : 1 ≤ L)
    (hc : 0 < c) (hC : 0 ≤ C) (hunit : error ≤ 1)
    (hmaster : ∀ h : ℝ, 12 * δ ≤ h →
      error ≤ C * Real.sqrt L *
        (γ₃ * masterThirdCoefficient L b c a₃ h +
          γ₄ * masterFourthCoefficient L b c a₃ a₄ h + h / c)) :
    error ≤ max 1 (12 * C) * min 1
      (generalCoefficientRate δ γ₃ γ₄ L b c a₃ a₄) := by
  have hL0 : 0 < L := by linarith
  have hb := rate_of_two_bandwidth_witnesses hδ
    (div_nonneg (Real.sqrt_nonneg L) hc.le) hC
    (generalThird_bandwidth_witness hγ₃ hL0.le hc)
    (generalFourth_bandwidth_witness hγ₄ hL0 hc) hunit (fun h hh => by
      convert hmaster h hh using 1 <;> ring)
  convert hb using 1
  unfold generalCoefficientRate
  ring

end

end RectangleCLT
