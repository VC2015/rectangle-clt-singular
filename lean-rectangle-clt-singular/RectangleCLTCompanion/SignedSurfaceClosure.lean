import RectangleCLTCompanion.SignedSurfaceShells
import RectangleCLTCompanion.SignedSurfaceTubes
import RectangleCLTCompanion.SignedSurfaceAveraging
import RectangleCLTCompanion.SignedSurfaceShellCaps

/-! Quantitative closure of the actual dyadic surface series. The only
tail estimates used here are the proved moments of the concrete Gaussian
four-face projection radius. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def surfaceSecondMomentConstant : ℝ := 8 * Real.exp 80
def surfaceThirdMomentConstant : ℝ := 16 * Real.exp 136

/-- Explicit universal multiplier, linear in the actual boundary
concentration constant. -/
def surfaceClosureConstant (C : ℝ) : ℝ :=
  160 * Real.exp ((3 : ℝ) / 2) * C * (surfaceSecondMomentConstant + surfaceThirdMomentConstant)

theorem surfaceClosureConstant_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ surfaceClosureConstant C := by
  unfold surfaceClosureConstant surfaceSecondMomentConstant surfaceThirdMomentConstant
  positivity

theorem surfaceClosureConstant_pos {C : ℝ} (hC : 0 < C) : 0 < surfaceClosureConstant C := by
  unfold surfaceClosureConstant surfaceSecondMomentConstant surfaceThirdMomentConstant
  positivity

theorem dyadic_cubic_tube_cost_le (η : ℝ) (n : ℕ) :
    dyadicRadius n ^ 3 * (tubeRadius (dyadicRadius n) + η) ≤
      dyadicRadius n ^ 2 + η * dyadicRadius n ^ 3 := by
  have hR : 0 ≤ dyadicRadius n := by unfold dyadicRadius; positivity
  have hh := mul_le_mul_of_nonneg_left (mul_tubeRadius_le_one hR) (sq_nonneg (dyadicRadius n))
  nlinarith

theorem sum_dyadic_surface_cost_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {η : ℝ} (hη : 0 ≤ η) (N : ℕ) :
    (∑ n ∈ Finset.range N, dyadicRadius n ^ 3 * (tubeRadius (dyadicRadius n) + η) *
      (standardGaussian p).real
        {z | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A z}) ≤
      surfaceSecondMomentConstant * dimensionLog p +
        surfaceThirdMomentConstant * η * dimensionLog p * Real.sqrt (dimensionLog p) := by
  let K := fourFaceProjectionRadius A
  let β := fun n => (standardGaussian p).real {z | dyadicRadius n / 2 - 1 ≤ K z}
  have hL0 : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hs3 : Real.sqrt (dimensionLog p) ^ 3 = dimensionLog p * Real.sqrt (dimensionLog p) := by
    rw [pow_succ, Real.sq_sqrt hL0]
  have hm2 := integrable_fourFaceProjectionRadius_moment hp A 2
  have hm3 := integrable_fourFaceProjectionRadius_moment hp A 3
  have ht2 := sum_dyadic_tail_masses_le (standardGaussian p) K
    (measurable_fourFaceProjectionRadius A) (fourFaceProjectionRadius_nonneg A)
    (by norm_num : 1 ≤ 2) hm2.1 N
  have ht3 := sum_dyadic_tail_masses_le (standardGaussian p) K
    (measurable_fourFaceProjectionRadius A) (fourFaceProjectionRadius_nonneg A)
    (by norm_num : 1 ≤ 3) hm3.1 N
  have hm2' : (∫ z, (1 + K z) ^ 2 ∂standardGaussian p) ≤
      dimensionLog p * Real.exp 80 := by
    simpa only [Nat.cast_ofNat, show (8 : ℝ) + (4 * (2 + 1)) ^ 2 / 2 = 80 by norm_num,
      Real.sq_sqrt hL0] using hm2.2
  have hm3' : (∫ z, (1 + K z) ^ 3 ∂standardGaussian p) ≤
      dimensionLog p * Real.sqrt (dimensionLog p) * Real.exp 136 := by
    simpa only [Nat.cast_ofNat, show (8 : ℝ) + (4 * (3 + 1)) ^ 2 / 2 = 136 by norm_num,
      hs3] using hm3.2
  have hb2 : (∑ n ∈ Finset.range N, dyadicRadius n ^ 2 * β n) ≤
      surfaceSecondMomentConstant * dimensionLog p := by
    calc
      _ ≤ 8 * (∫ z, (1 + K z) ^ 2 ∂standardGaussian p) := by
        convert ht2 using 1; norm_num
      _ ≤ 8 * (dimensionLog p * Real.exp 80) := mul_le_mul_of_nonneg_left hm2' (by norm_num)
      _ = _ := by unfold surfaceSecondMomentConstant; ring
  have hb3 : (∑ n ∈ Finset.range N, dyadicRadius n ^ 3 * β n) ≤
      surfaceThirdMomentConstant * dimensionLog p * Real.sqrt (dimensionLog p) := by
    calc
      _ ≤ 16 * (∫ z, (1 + K z) ^ 3 ∂standardGaussian p) := by
        convert ht3 using 1; norm_num
      _ ≤ 16 * (dimensionLog p * Real.sqrt (dimensionLog p) * Real.exp 136) :=
        mul_le_mul_of_nonneg_left hm3' (by norm_num)
      _ = _ := by unfold surfaceThirdMomentConstant; ring
  calc
    _ ≤ ∑ n ∈ Finset.range N, (dyadicRadius n ^ 2 + η * dyadicRadius n ^ 3) * β n :=
      Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right
        (dyadic_cubic_tube_cost_le η n) measureReal_nonneg)
    _ = (∑ n ∈ Finset.range N, dyadicRadius n ^ 2 * β n) +
        η * ∑ n ∈ Finset.range N, dyadicRadius n ^ 3 * β n := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    _ ≤ surfaceSecondMomentConstant * dimensionLog p +
        η * (surfaceThirdMomentConstant * dimensionLog p * Real.sqrt (dimensionLog p)) :=
      add_le_add hb2 (mul_le_mul_of_nonneg_left hb3 hη)
    _ = _ := by ring

/-- A genuine convergent shell series is bounded using the concrete
Gaussian second and third moments. No tail estimate is an input. -/
theorem hasSum_dyadic_surface_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {η C S : ℝ} (hη : 0 ≤ η) (hC : 0 ≤ C)
    (f : ℕ → ℝ) (hf : HasSum f S)
    (hcap : ∀ n, f n ≤ C *
      (dyadicRadius n ^ 3 * (tubeRadius (dyadicRadius n) + η) *
        (standardGaussian p).real
          {z | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A z})) :
    S ≤ C * (surfaceSecondMomentConstant * dimensionLog p +
      surfaceThirdMomentConstant * η * dimensionLog p * Real.sqrt (dimensionLog p)) := by
  apply le_of_tendsto hf.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro N
  calc
    _ ≤ ∑ n ∈ Finset.range N, C *
        (dyadicRadius n ^ 3 * (tubeRadius (dyadicRadius n) + η) *
          (standardGaussian p).real
            {z | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A z}) :=
      Finset.sum_le_sum (fun n _ => hcap n)
    _ = C * ∑ n ∈ Finset.range N,
        dyadicRadius n ^ 3 * (tubeRadius (dyadicRadius n) + η) *
          (standardGaussian p).real
            {z | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A z} :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_dyadic_surface_cost_le hp A hη N) hC

/-- Raw cubic shell costs from the actual facet and ridge tubes close at
the desired logarithmic rate once the Gaussian scale exceeds the row scale.
The variance floor is the one used by both halves of the actual path. -/
theorem hasSum_dyadic_surface_optimized_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (a : ℕ)
    {C h σ η v S : ℝ} (hC : 0 ≤ C) (hh : 0 ≤ h) (hσ : 0 < σ)
    (hη : 0 ≤ η) (hv : (1 / 4 : ℝ) ≤ v)
    (hcut : η * Real.sqrt (dimensionLog p) ≤ σ)
    (f : ℕ → ℝ) (hf : HasSum f S)
    (hcap : ∀ n, f n ≤
      (80 * Real.exp ((3 : ℝ) / 2) * h * dyadicRadius n ^ 3 / (((a : ℝ) + 1) * σ)) *
        (C * (σ * tubeRadius (dyadicRadius n) + η) * Real.sqrt (dimensionLog p / v) *
          (standardGaussian p).real
            {z | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A z})) :
    S ≤ surfaceClosureConstant C * h / ((a : ℝ) + 1) *
      dimensionLog p * Real.sqrt (dimensionLog p) := by
  let c := 80 * Real.exp ((3 : ℝ) / 2) * h * C * Real.sqrt (dimensionLog p / v) /
    ((a : ℝ) + 1)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ha : (a : ℝ) + 1 ≠ 0 := by positivity
  have hpoint (n : ℕ) : f n ≤ c *
      (dyadicRadius n ^ 3 * (tubeRadius (dyadicRadius n) + η / σ) *
        (standardGaussian p).real
          {z | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A z}) := by
    apply (hcap n).trans_eq
    dsimp [c]
    field_simp [ha, hσ.ne']
    ring
  have hs := hasSum_dyadic_surface_le hp A (div_nonneg hη hσ.le) hc f hf hpoint
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL0 : 0 ≤ dimensionLog p := zero_le_one.trans hL
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hv
  have hroot : Real.sqrt (dimensionLog p / v) ≤ 2 * Real.sqrt (dimensionLog p) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt hL0]
    norm_num
    apply (div_le_iff₀ hv0).mpr
    nlinarith [mul_nonneg hL0 (sub_nonneg.mpr hv)]
  have hratio : η / σ * Real.sqrt (dimensionLog p) ≤ 1 := by
    calc
      _ = (η * Real.sqrt (dimensionLog p)) / σ := by ring
      _ ≤ 1 := (div_le_one hσ).mpr hcut
  have hD2 : 0 ≤ surfaceSecondMomentConstant := by unfold surfaceSecondMomentConstant; positivity
  have hD3 : 0 ≤ surfaceThirdMomentConstant := by unfold surfaceThirdMomentConstant; positivity
  have hb : surfaceSecondMomentConstant * dimensionLog p +
      surfaceThirdMomentConstant * (η / σ) * dimensionLog p * Real.sqrt (dimensionLog p) ≤
        (surfaceSecondMomentConstant + surfaceThirdMomentConstant) * dimensionLog p := by
    have ht := mul_le_mul_of_nonneg_left hratio (mul_nonneg hD3 hL0)
    nlinarith
  calc
    S ≤ c * ((surfaceSecondMomentConstant + surfaceThirdMomentConstant) * dimensionLog p) :=
      hs.trans (mul_le_mul_of_nonneg_left hb hc)
    _ = (80 * Real.exp ((3 : ℝ) / 2) * h * C / ((a : ℝ) + 1) *
        (surfaceSecondMomentConstant + surfaceThirdMomentConstant) * dimensionLog p) *
          Real.sqrt (dimensionLog p / v) := by dsimp [c]; ring
    _ ≤ (80 * Real.exp ((3 : ℝ) / 2) * h * C / ((a : ℝ) + 1) *
        (surfaceSecondMomentConstant + surfaceThirdMomentConstant) * dimensionLog p) *
          (2 * Real.sqrt (dimensionLog p)) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by unfold surfaceClosureConstant; ring

/-- The actual averaged signed power score is controlled by its genuine
surface-shell series. The convergence and positive majorant are proved
from the concrete Gaussian law, without moments on the base distribution. -/
theorem abs_averagedGaussianPowerTrace_le_of_surfaceShell_bound
    {p : ℕ} (hp : 1 ≤ p) (μ : Measure (Vector p)) [IsProbabilityMeasure μ]
    {C η v : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η) (hv : (1 / 4 : ℝ) ≤ v)
    (s : FaceSmoother p) (a : ℕ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {σ : ℝ} (hσ : 0 < σ) (hcut : η * Real.sqrt (dimensionLog p) ≤ σ)
    (hcap : ∀ n, averagedSurfaceShell μ s a A σ n ≤
      (80 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * dyadicRadius n ^ 3 / (((a : ℝ) + 1) * σ)) *
        (C * (σ * tubeRadius (dyadicRadius n) + η) * Real.sqrt (dimensionLog p / v) *
          (standardGaussian p).real
            {z | dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius (σ • A) z})) :
    |averagedGaussianPowerTrace μ s (σ • A) a| ≤
      surfaceClosureConstant C * s.bandwidth / ((a : ℝ) + 1) *
        dimensionLog p * Real.sqrt (dimensionLog p) := by
  exact (abs_averagedGaussianPowerTrace_le_surfaceMoment μ hp s a A hdiag hσ).trans
    (hasSum_dyadic_surface_optimized_le hp (σ • A) a hC s.bandwidth_pos.le hσ hη hv hcut
      (averagedSurfaceShell μ s a A σ) (averagedSurfaceShell_hasSum μ hp s a A σ) hcap)

/-- Actual uniform boundary concentration closes the signed Gaussian power
trace estimate. All surface decompositions, image probabilities, and Gaussian
tail summations in this implication have been proved for the concrete laws;
no full-rank covariance assumption or moment assumption on the base law is
needed. -/
theorem abs_averagedGaussianPowerTrace_le_concentration
    {p : ℕ} (hp : 1 ≤ p) (μ : Measure (Vector p)) [IsProbabilityMeasure μ]
    {C η v : ℝ} (hconc : UniformBoundaryConcentration μ C η v)
    (hC : 0 ≤ C) (hη : 0 ≤ η) (hv : (1 / 4 : ℝ) ≤ v)
    (s : FaceSmoother p) (a : ℕ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {σ : ℝ} (hσ : 0 < σ) (hcut : η * Real.sqrt (dimensionLog p) ≤ σ) :
    |averagedGaussianPowerTrace μ s (σ • A) a| ≤
      surfaceClosureConstant C * s.bandwidth / ((a : ℝ) + 1) *
        dimensionLog p * Real.sqrt (dimensionLog p) := by
  exact abs_averagedGaussianPowerTrace_le_of_surfaceShell_bound hp μ hC hη hv
    s a A hdiag hσ hcut (fun n => averagedSurfaceShell_le_concentration hp μ
      hconc hC hη (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hv)
      s a A hdiag hσ n)

end
end RectangleCLT.Companion.SignedSurface
