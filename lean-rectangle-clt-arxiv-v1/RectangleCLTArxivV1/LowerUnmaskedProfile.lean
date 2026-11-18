import RectangleCLTArxivV1.LowerUnmaskedParameters

/-! The width profile of the actual chosen Gaussian covariance factor. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lowerFamilyGaussianMaximumMean_width_profile
    {P : ℕ → SymmetricFamilyParameters} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 1 ≤ m n)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hrare : Tendsto (fun n => Real.sqrt (P n).variance*independentAbsGaussianMean (m n)) atTop (𝓝 0)) :
    Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (P n) (r n) (m n))/
      independentAbsGaussianMean (r n)) atTop (𝓝 1) := by
  have hh := lowerGridGaussianMean_width_profile r m (fun n => (P n).variance) hr hm hv hrare
  apply hh.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only
    rw [lowerFamilyGaussianMaximumMean_eq (P n) _ (lowerFamilyGaussianFactor_gram (P n) (r n) (m n))]
    rfl)

theorem lowerFamilyGaussianMaximumMean_one_tendsto
    {P : ℕ → SymmetricFamilyParameters} {m : ℕ → ℕ} (hm : ∀ n, 1 ≤ m n)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hrare : Tendsto (fun n => Real.sqrt (P n).variance*independentAbsGaussianMean (m n)) atTop (𝓝 0)) :
    Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (P n) 1 (m n))) atTop
      (𝓝 (Real.sqrt (2/Real.pi))) := by
  have hh := lowerFamilyGaussianMaximumMean_width_profile (P := P) (r := fun _ => 1)
    (fun _ => by norm_num) hm hv hrare
  have hp : Real.sqrt (2/Real.pi) ≠ 0 := ne_of_gt (by positivity)
  have he := hh.mul_const (Real.sqrt (2/Real.pi))
  simpa only [independentAbsGaussianMean_one,div_mul_cancel₀ _ hp,one_mul] using he

end
end RectangleCLTArxivV1
