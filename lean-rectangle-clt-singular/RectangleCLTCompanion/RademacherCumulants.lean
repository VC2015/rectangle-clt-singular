import RectangleCLTCompanion.LowerScalarTilt
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The fourth-order Rademacher rate function

These formulas concern the actual symmetric two-point law (`B = 1`).
The fourth-order coefficient is computed from elementary derivatives, rather
than assumed as a moderate-deviation expansion.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

def rademacherTiltParameter (u : ℝ) : ℝ :=
  (Real.log (1+u) - Real.log (1-u)) / 2

def rademacherRateFunction (u : ℝ) : ℝ :=
  ((1+u)*Real.log (1+u) + (1-u)*Real.log (1-u)) / 2

@[simp] lemma rademacherTiltParameter_zero : rademacherTiltParameter 0 = 0 := by
  simp [rademacherTiltParameter]

@[simp] lemma rademacherRateFunction_zero : rademacherRateFunction 0 = 0 := by
  simp [rademacherRateFunction]

lemma hasDerivAt_rademacherTiltParameter {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt rademacherTiltParameter (1 / (1-u^2)) u := by
  have hplus : 1+u ≠ 0 := by linarith [hu.1]
  have hminus : 1-u ≠ 0 := by linarith [hu.2]
  have hd := (((hasDerivAt_id u).const_add 1).log hplus).sub
    (((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).log hminus) |>.div_const 2
  convert hd using 1
  change 1 / (1-u^2) = _
  have hden : 1-u^2 ≠ 0 := by nlinarith [hu.1, hu.2]
  field_simp
  <;> ring

lemma hasDerivAt_rademacherRateFunction {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt rademacherRateFunction (rademacherTiltParameter u) u := by
  have hplus : 1+u ≠ 0 := by linarith [hu.1]
  have hminus : 1-u ≠ 0 := by linarith [hu.2]
  have hp := (hasDerivAt_id u).const_add 1
  have hm := (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)
  have hd := ((hp.mul (hp.log hplus)).add (hm.mul (hm.log hminus))).div_const 2
  convert hd using 1
  unfold rademacherTiltParameter
  field_simp
  <;> ring

lemma tendsto_rademacherTiltParameter_div :
    Tendsto (fun u : ℝ => rademacherTiltParameter u / u) (𝓝[>] 0) (𝓝 1) := by
  have hd := hasDerivAt_rademacherTiltParameter (u := 0) (by constructor <;> norm_num)
  have hs := hd.tendsto_slope_zero_right
  simpa [smul_eq_mul, inv_mul_eq_div] using hs

lemma tendsto_rademacherTiltParameter_cubic :
    Tendsto (fun u : ℝ => (rademacherTiltParameter u - u) / u^3)
      (𝓝[>] 0) (𝓝 (1/3 : ℝ)) := by
  have hd : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun u => rademacherTiltParameter u - u) (u^2 / (1-u^2)) u := by
    intro u hu
    have hh := (hasDerivAt_rademacherTiltParameter (by constructor <;> linarith [hu.1, hu.2] : u ∈ Ioo (-1 : ℝ) 1)).sub
      (hasDerivAt_id u)
    convert hh using 1
    have hden : 1-u^2 ≠ 0 := by nlinarith [hu.1, hu.2]
    field_simp
  have hnum : Tendsto (fun u => rademacherTiltParameter u - u) (𝓝[>] 0) (𝓝 0) := by
    have hh := (hasDerivAt_rademacherTiltParameter (u := 0) (by constructor <;> norm_num)).continuousAt
    simpa using (hh.tendsto.sub tendsto_id).mono_left nhdsWithin_le_nhds
  apply HasDerivAt.lhopital_zero_right_on_Ioo (a := 0) (b := 1) (by norm_num) hd
    (fun u _ => (hasDerivAt_id u).pow 3)
    (by intro u hu; have hu0 := hu.1; simp only [Nat.cast_ofNat, Nat.reduceSub, mul_one]; positivity) hnum
    (by simpa using ((continuous_pow 3).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hlim : Tendsto (fun u : ℝ => (1 / (1-u^2)) / 3) (𝓝[>] 0) (𝓝 (1/3 : ℝ)) := by
    have ht : Tendsto (fun u : ℝ => 1 / (1-u^2)) (𝓝 0) (𝓝 1) := by
      convert tendsto_const_nhds.div (tendsto_const_nhds.sub (tendsto_id.pow 2)) (by norm_num : (1 : ℝ)-0^2 ≠ 0) using 1 <;> norm_num
    exact (ht.div_const 3).mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
  have hu0 : u ≠ 0 := ne_of_gt hu.1
  have hden : 1-u^2 ≠ 0 := by nlinarith [hu.1, hu.2]
  field_simp [hu0, hden]
  <;> ring

lemma tendsto_rademacherRateFunction_fourth :
    Tendsto (fun u : ℝ => (rademacherRateFunction u - u^2/2) / u^4)
      (𝓝[>] 0) (𝓝 (1/12 : ℝ)) := by
  have hd : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun u => rademacherRateFunction u - u^2/2)
        (rademacherTiltParameter u - u) u := by
    intro u hu
    have hh := (hasDerivAt_rademacherRateFunction (by constructor <;> linarith [hu.1, hu.2] : u ∈ Ioo (-1 : ℝ) 1)).sub
      (((hasDerivAt_id u).pow 2).div_const 2)
    convert hh using 1 <;> simp <;> ring
  have hnum : Tendsto (fun u : ℝ => rademacherRateFunction u - u^2/2) (𝓝[>] 0) (𝓝 0) := by
    have hh := (hasDerivAt_rademacherRateFunction (u := 0) (by constructor <;> norm_num)).continuousAt
    simpa using (hh.tendsto.sub ((tendsto_id.pow 2).div_const 2)).mono_left nhdsWithin_le_nhds
  apply HasDerivAt.lhopital_zero_right_on_Ioo (a := 0) (b := 1) (by norm_num) hd
    (fun u _ => (hasDerivAt_id u).pow 4)
    (by intro u hu; have hu0 := hu.1; simp only [Nat.cast_ofNat, Nat.reduceSub, mul_one]; positivity) hnum
    (by simpa using ((continuous_pow 4).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hh := tendsto_rademacherTiltParameter_cubic.div_const (4 : ℝ)
  have hh' : Tendsto (fun u : ℝ => ((rademacherTiltParameter u-u)/u^3)/4)
      (𝓝[>] 0) (𝓝 (1/12 : ℝ)) := by convert hh using 1 <;> norm_num
  apply hh'.congr'
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
  rw [div_div, mul_comm]

lemma rademacherRateFunction_legendre (u : ℝ) :
    rademacherRateFunction u = (u-1)*rademacherTiltParameter u + Real.log (1+u) := by
  unfold rademacherRateFunction rademacherTiltParameter
  ring

end

end RectangleCLT.Companion
