import RectangleCLTCompanion.WeightedGaussianTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace RectangleCLT.Companion

lemma tendsto_mul_normalWeightedTail :
    Tendsto (fun s : ℝ => s * normalWeightedTail s) atTop (𝓝 (standardNormalPDF 0)) := by
  have hd : Tendsto (fun s : ℝ => s^2+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have hl : Tendsto (fun s : ℝ => standardNormalPDF 0 - standardNormalPDF 0 / (s^2+1))
      atTop (𝓝 (standardNormalPDF 0)) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using
      tendsto_const_nhds.sub ((tendsto_inv_atTop_zero.comp hd).const_mul (standardNormalPDF 0))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hm := mul_le_mul_of_nonneg_left (normalWeightedTail_mills_lower hs) hs.le
    have he : standardNormalPDF 0 - standardNormalPDF 0 / (s^2+1) =
        s * (standardNormalPDF 0 * s / (s^2+1)) := by
      field_simp
      <;> ring
    rw [he]
    exact hm
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hm := (le_div_iff₀ hs).mp (normalWeightedTail_le hs)
    simpa only [mul_comm] using hm

lemma tendsto_normalWeightedTail_ratio {ι : Type*} {l : Filter ι}
    {s x : ι → ℝ} (hs : Tendsto s l atTop) (hx : Tendsto x l atTop)
    (hratio : Tendsto (fun i => s i / x i) l (𝓝 (1 : ℝ))) :
    Tendsto (fun i => normalWeightedTail (s i) / normalWeightedTail (x i)) l (𝓝 (1 : ℝ)) := by
  have hp := (tendsto_mul_normalWeightedTail.comp hs).div
    (tendsto_mul_normalWeightedTail.comp hx) (standardNormalPDF_pos 0).ne'
  have hh := hp.div hratio (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_self (standardNormalPDF_pos 0).ne', div_one] at hh
  apply hh.congr'
  filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ)),
    hx.eventually (eventually_gt_atTop (0 : ℝ))] with i hsi hxi
  dsimp only [Function.comp_def, Pi.div_apply]
  field_simp [hsi.ne', hxi.ne', (normalWeightedTail_pos (x i)).ne']
  <;> ring

end RectangleCLT.Companion
