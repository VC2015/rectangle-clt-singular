import RectangleCLTArxivV1.LowerBoundedTheorem
import RectangleCLTCompanion.SplitV4.Printed.ObservationRates

/-! Exact bounded-width calibration after the unmasked lower construction. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerBoundedOneParameters (m : ℕ → ℕ) : ℕ → SymmetricFamilyParameters :=
  lowerUnmaskedSequence (fun _ => 1) m

def lowerBoundedOneTarget (m : ℕ → ℕ) (n : ℕ) : ℝ :=
  (2/Real.sqrt n)*gaussianMaximumMean (lowerFamilyGaussianFactor (lowerBoundedOneParameters m n) 1 (m n))*dimensionLog (m n)

theorem independentAbsGaussianMean_one_eq_density :
    independentAbsGaussianMean 1 = 2*standardNormalPDF 0 := by
  rw [independentAbsGaussianMean_one,standardNormalPDF_eq]
  norm_num only [zero_pow (by norm_num : 2 ≠ 0),neg_zero,zero_div,Real.exp_zero,mul_one]
  have hroot : Real.sqrt (2/Real.pi)*Real.sqrt (2*Real.pi) = 2 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2/Real.pi)]
    have he : (2/Real.pi)*(2*Real.pi) = (4 : ℝ) := by field_simp; ring
    rw [he]
    norm_num
  have hs : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  apply (eq_div_iff hs).mpr
  simpa only [div_eq_mul_inv] using hroot

theorem lowerBoundedOne_widthScale_eq (m : ℕ → ℕ) (n : ℕ) :
    lowerFamilyWidthScale (lowerBoundedOneParameters m n) n 1 (m n) =
      ((lowerBoundedOneParameters m n).amplitude*boundedShiftScale n (m n))*(2*independentAbsGaussianMean 1) := by
  unfold lowerFamilyWidthScale boundedShiftScale
  ring

theorem tendsto_lowerBoundedOne_signed_div_widthScale {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale 1 (Real.log (m n : ℝ)) (independentAbsGaussianMean 1) n)
      atTop (𝓝 0)) :
    Tendsto (fun n => lowerFamilyShiftedCDFDifference (lowerBoundedOneParameters m n) n 1 (m n) 0/
      lowerFamilyWidthScale (lowerBoundedOneParameters m n) n 1 (m n)) atTop (𝓝 (1/4)) := by
  have ha : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ 1 := Eventually.of_forall (fun _ => le_rfl)
  have hr : ∀ _ : ℕ, 1 ≤ (1 : ℕ) := fun _ => le_rfl
  have hv := tendsto_lowerUnmaskedSequence_variance hr hm hmTop ha hsmall
  have hcount := eventually_lowerUnmaskedSequence_count hr hm hmTop ha hsmall
  have hpi : ∀ᶠ n in atTop, (lowerBoundedOneParameters m n).pi = 1 :=
    Eventually.of_forall (lowerUnmaskedSequence_pi _ _)
  have hPsmall := tendsto_lowerUnmaskedSequence_widthScale hr hm hmTop ha hsmall
  have haP : ∀ᶠ n in atTop, 1 ≤ (lowerBoundedOneParameters m n).amplitude := by
    filter_upwards [eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hsmall] with n hn
    unfold lowerBoundedOneParameters
    rw [hn.2.1]
  have hRem := tendsto_lowerFamilyMasterRemainder_div_width hr hm (fun n => by have := hm n; omega)
    hmTop haP hpi hcount hPsmall
  have hMean := (tendsto_unmasked_shiftMeanDifference_amplitude_ratio hm hmTop hcount hpi hv).div_const
    (2*independentAbsGaussianMean 1)
  have hMean' : Tendsto (fun n => familyShiftMeanDifference (lowerBoundedOneParameters m n) n (m n)/
      lowerFamilyWidthScale (lowerBoundedOneParameters m n) n 1 (m n)) atTop
        (𝓝 (1/(2*independentAbsGaussianMean 1))) := by
    apply hMean.congr'
    exact Eventually.of_forall (fun n => by
      change familyShiftMeanDifference (lowerBoundedOneParameters m n) n (m n)/
        ((lowerBoundedOneParameters m n).amplitude*boundedShiftScale n (m n))/(2*independentAbsGaussianMean 1) = _
      dsimp only
      rw [div_div,lowerBoundedOne_widthScale_eq])
  have hRange := eventually_lowerFamily_leading_range hr (fun n => by have := hm n; omega) hmTop haP hPsmall
  have hAbs : Tendsto (fun n => |(lowerFamilyShiftedCDFDifference (lowerBoundedOneParameters m n) n 1 (m n) 0-
      standardNormalPDF 0*familyShiftMeanDifference (lowerBoundedOneParameters m n) n (m n))/
        lowerFamilyWidthScale (lowerBoundedOneParameters m n) n 1 (m n)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hRem
    filter_upwards [eventually_lowerFamily_master_comparison,hRange,eventually_ge_atTop 1] with n hnMaster hnRange hn
    have hD := lowerFamilyWidthScale_pos (lowerBoundedOneParameters m n) (r := 1) (m := m n) hn (by norm_num) (hm n)
    have hh := hnMaster (lowerBoundedOneParameters m n) 1 (m n) (by norm_num) (by have := hm n; omega) hnRange 0
    have hd : normalMaximumDensity 1 0 = standardNormalPDF 0 := by norm_num [normalMaximumDensity]
    rw [hd] at hh
    rw [abs_div,abs_of_pos hD]
    exact div_le_div_of_nonneg_right hh hD.le
  have hDiff : Tendsto (fun n => (lowerFamilyShiftedCDFDifference (lowerBoundedOneParameters m n) n 1 (m n) 0-
      standardNormalPDF 0*familyShiftMeanDifference (lowerBoundedOneParameters m n) n (m n))/
        lowerFamilyWidthScale (lowerBoundedOneParameters m n) n 1 (m n)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero,Real.norm_eq_abs] using hAbs
  have hh := hDiff.add (hMean'.const_mul (standardNormalPDF 0))
  have hconst : (0 : ℝ)+standardNormalPDF 0*(1/(2*independentAbsGaussianMean 1)) = 1/4 := by
    rw [independentAbsGaussianMean_one_eq_density]
    field_simp [(standardNormalPDF_pos 0).ne']
    ring
  rw [hconst] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun n => by dsimp only; ring)

end
end RectangleCLTArxivV1
