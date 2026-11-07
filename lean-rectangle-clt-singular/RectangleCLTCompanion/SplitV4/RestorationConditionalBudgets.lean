import RectangleCLTCompanion.RestorationCoefficients
import RectangleCLTCompanion.RestorationMatrixBound
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.ContinuousOn

/-! Actual conditional coefficient budgets for Lemma B.2. Every displayed
conditional expectation has a genuine integrable input. No independence
between the auxiliary arrays or between their coefficients is used. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem condExp_real_const_mul {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (H : MeasurableSpace Ω) (c : ℝ) (F : Ω → ℝ) :
    μ[(fun ω => c * F ω)|H] =ᵐ[μ] fun ω => c * (μ[F|H]) ω := by
  simpa only [Pi.smul_apply, smul_eq_mul] using condExp_smul c F H

/-- Two-sided conditional domination, with true first moments and a valid
sub-sigmafield explicitly retained in the interface. -/
theorem condExp_abs_le_of_abs_le {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (_hH : H ≤ mΩ)
    (F G : Ω → ℝ) (hF : Integrable F μ) (hG : Integrable G μ)
    (hbound : ∀ᵐ ω ∂μ, |F ω| ≤ G ω) :
    ∀ᵐ ω ∂μ, |(μ[F|H]) ω| ≤ (μ[G|H]) ω := by
  have hupper : F ≤ᵐ[μ] G := hbound.mono (fun ω hω => (le_abs_self _).trans hω)
  have hlower : -F ≤ᵐ[μ] G := hbound.mono (fun ω hω => (neg_le_abs _).trans hω)
  filter_upwards [condExp_mono hF hG hupper, condExp_mono hF.neg hG hlower,
    condExp_neg F H] with ω hu hl hn
  simp only [Pi.neg_apply] at hl hn
  rw [hn] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- The scalar form of the baseline conditional covariance contraction.
For restoration, `Q_i=(u·Z_i)²`, `K=δ^s` times the translation multiplier,
and `B=‖u‖₂²`. The arrays and multipliers may be dependent. -/
theorem conditional_bounded_coefficient_budget {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (Q c : Fin n → Ω → ℝ) (hQ : ∀ i, Integrable (Q i) μ)
    (hcQ : ∀ i, Integrable (fun ω => c i ω * Q i ω) μ)
    (hQpos : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ Q i ω) {K : ℝ} (hK : 0 ≤ K)
    (hc : ∀ i, ∀ᵐ ω ∂μ, |c i ω| ≤ K) (B : Ω → ℝ)
    (hbudget : ∀ᵐ ω ∂μ, (μ[(fun z => ∑ i, Q i z)|H]) ω ≤ B ω) :
    ∀ᵐ ω ∂μ, |(μ[(fun z => ∑ i, c i z * Q i z)|H]) ω| ≤ K * B ω := by
  have hsum := integrable_finset_sum Finset.univ (fun i _ => hQ i)
  have hcsum := integrable_finset_sum Finset.univ (fun i _ => hcQ i)
  have hdom : ∀ᵐ ω ∂μ, |∑ i, c i ω * Q i ω| ≤ K * ∑ i, Q i ω := by
    filter_upwards [ae_all_iff.mpr hQpos, ae_all_iff.mpr hc] with ω hω hωc
    calc
      _ ≤ ∑ i, |c i ω * Q i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, K * Q i ω := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul, abs_of_nonneg (hω i)]
        exact mul_le_mul_of_nonneg_right (hωc i) (hω i))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hCE := condExp_abs_le_of_abs_le (mΩ := mΩ) μ H hH _ _ hcsum (hsum.const_mul K) hdom
  filter_upwards [hCE, condExp_real_const_mul (mΩ := mΩ) μ H K (fun z => ∑ i, Q i z), hbudget] with ω hω hscale hb
  rw [hscale] at hω
  exact hω.trans (mul_le_mul_of_nonneg_left hb hK)

/-- The relative second-order budget retains both face-square hypotheses.
Translation multipliers may depend on all directions, including copies
that also appear in the coefficients. -/
theorem conditional_relative_pair_budget {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (Q Y W d : Fin n → Ω → ℝ)
    (hY₂ : ∀ i, Integrable (fun ω => Q i ω * (Y i ω) ^ 2) μ)
    (hW₂ : ∀ i, Integrable (fun ω => Q i ω * (W i ω) ^ 2) μ)
    (hprod : ∀ i, Integrable (fun ω => Q i ω * Y i ω * W i ω * d i ω) μ)
    (hQpos : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ Q i ω) {T : ℝ} (hT : 0 ≤ T)
    (hd : ∀ i, ∀ᵐ ω ∂μ, |d i ω| ≤ T) (B : Ω → ℝ)
    (hbudgetY : ∀ᵐ ω ∂μ, (μ[(fun z => ∑ i, Q i z * (Y i z) ^ 2)|H]) ω ≤ B ω)
    (hbudgetW : ∀ᵐ ω ∂μ, (μ[(fun z => ∑ i, Q i z * (W i z) ^ 2)|H]) ω ≤ B ω) :
    ∀ᵐ ω ∂μ, |(μ[(fun z => ∑ i, Q i z * Y i z * W i z * d i z)|H]) ω| ≤ T * B ω := by
  let SY : Ω → ℝ := fun ω => ∑ i, Q i ω * (Y i ω) ^ 2
  let SW : Ω → ℝ := fun ω => ∑ i, Q i ω * (W i ω) ^ 2
  have hiY : Integrable SY μ := integrable_finset_sum _ (fun i _ => hY₂ i)
  have hiW : Integrable SW μ := integrable_finset_sum _ (fun i _ => hW₂ i)
  have hiS := integrable_finset_sum Finset.univ (fun i _ => hprod i)
  have hdom : ∀ᵐ ω ∂μ, |∑ i, Q i ω * Y i ω * W i ω * d i ω| ≤ (T / 2) * (SY ω + SW ω) := by
    filter_upwards [ae_all_iff.mpr hQpos, ae_all_iff.mpr hd] with ω hq hdm
    calc
      _ ≤ ∑ i, |Q i ω * Y i ω * W i ω * d i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (T / 2) * (Q i ω * (Y i ω) ^ 2 + Q i ω * (W i ω) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hq i)]
        have hYW : |Y i ω| * |W i ω| ≤ ((Y i ω) ^ 2 + (W i ω) ^ 2) / 2 := by
          nlinarith [sq_nonneg (|Y i ω| - |W i ω|), sq_abs (Y i ω), sq_abs (W i ω)]
        have h₁ := mul_le_mul_of_nonneg_left (hdm i)
          (mul_nonneg (mul_nonneg (hq i) (abs_nonneg (Y i ω))) (abs_nonneg (W i ω)))
        have h₂ := mul_le_mul_of_nonneg_left hYW (mul_nonneg hT (hq i))
        nlinarith
      _ = (T / 2) * (∑ i, (Q i ω * (Y i ω) ^ 2 + Q i ω * (W i ω) ^ 2)) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [Finset.sum_add_distrib]
  have hCE := condExp_abs_le_of_abs_le (mΩ := mΩ) μ H hH _ _ hiS ((hiY.add hiW).const_mul (T / 2)) hdom
  have hscale := condExp_real_const_mul (mΩ := mΩ) μ H (T / 2) (fun ω => SY ω + SW ω)
  have hadd := condExp_add hiY hiW H
  filter_upwards [hCE, hscale, hadd, hbudgetY, hbudgetW] with ω hω hs ha hbY hbW
  change |(μ[(fun z => ∑ i, Q i z * Y i z * W i z * d i z)|H]) ω| ≤
    (μ[(fun z => (T / 2) * (SY z + SW z))|H]) ω at hω
  rw [hs] at hω
  change (μ[(fun z => SY z + SW z)|H]) ω = (μ[SY|H]) ω + (μ[SW|H]) ω at ha
  rw [ha] at hω
  have hb := mul_le_mul_of_nonneg_left (add_le_add hbY hbW) (div_nonneg hT (by norm_num : (0 : ℝ) ≤ 2))
  exact hω.trans (by convert hb using 1; ring)

/-- Zero shifts annihilate all positive translation-series levels. This
is why the signed relative cubic coefficient is used before absolute values. -/
theorem restorationTranslationCoefficient_zero {p k ℓ : ℕ} (s : FaceSmoother p)
    (α : Fin k → Face p) (β : Fin ℓ → Face p) :
    restorationTranslationCoefficient s α β 0 = if ℓ = 0 then 1 else 0 := by
  cases ℓ with
  | zero => simp [restorationTranslationCoefficient, translationIncrement, FaceSmoother.normalDot]
  | succ ℓ => simp [restorationTranslationCoefficient, translationIncrement, FaceSmoother.normalDot]

theorem condExp_real_linear_combination {Ω J : Type*} [mΩ : MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) (H : MeasurableSpace Ω) (a : J → ℝ) (F : J → Ω → ℝ)
    (hF : ∀ j, Integrable (F j) μ) :
    μ[(fun ω => ∑ j, a j * F j ω)|H] =ᵐ[μ]
      fun ω => ∑ j, a j * (μ[F j|H]) ω := by
  have hs := condExp_finset_sum (s := Finset.univ)
    (f := fun j => fun ω => a j * F j ω) (fun j _ => (hF j).const_mul (a j)) H
  have hfun : (∑ j, fun ω => a j * F j ω) = (fun ω => ∑ j, a j * F j ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hfun] at hs
  have hc (j : J) := condExp_real_const_mul (mΩ := mΩ) μ H (a j) (F j)
  filter_upwards [hs, ae_all_iff.mpr hc] with ω hω hωc
  simp only [Finset.sum_apply] at hω
  rw [hω]
  exact Finset.sum_congr rfl (fun j _ => hωc j)

/-- Entrywise actual conditional expectation of a random real matrix. -/
def conditionalMatrixAverage {Ω : Type*} [mΩ : MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) (H : MeasurableSpace Ω) (B : Ω → Matrix (Fin r) (Fin r) ℝ)
    (ω : Ω) : Matrix (Fin r) (Fin r) ℝ := fun j k => (μ[(fun z => B z j k)|H]) ω

theorem matrixQuadratic_eq_pair_sum {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) (u : Vector r) :
    matrixQuadratic B u = ∑ jk : Fin r × Fin r, (u jk.1 * u jk.2) * B jk.1 jk.2 := by
  rw [Fintype.sum_prod_type]
  unfold matrixQuadratic
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A quadratic form commutes with genuine matrix conditional moments.
The equality is proved for each direction and will subsequently be made
simultaneous using the countable dense rational directions. -/
theorem matrixQuadratic_conditionalMatrixAverage {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {r : ℕ} (μ : Measure Ω) (H : MeasurableSpace Ω)
    (B : Ω → Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ j k, Integrable (fun ω => B ω j k) μ) (u : Vector r) :
    ∀ᵐ ω ∂μ, matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H B ω) u =
      (μ[(fun z => matrixQuadratic (B z) u)|H]) ω := by
  have he := condExp_real_linear_combination (mΩ := mΩ) μ H
    (fun jk : Fin r × Fin r => u jk.1 * u jk.2)
    (fun jk ω => B ω jk.1 jk.2) (fun jk => hB jk.1 jk.2)
  have hfun : (fun ω => ∑ jk : Fin r × Fin r, (u jk.1 * u jk.2) * B ω jk.1 jk.2) =
      (fun ω => matrixQuadratic (B ω) u) := by
    funext ω
    exact (matrixQuadratic_eq_pair_sum _ _).symm
  rw [hfun] at he
  filter_upwards [he] with ω hω
  rw [matrixQuadratic_eq_pair_sum]
  exact hω.symm

/-- A countable dense set of rational directions gives one exceptional
null set for the entire operator quadratic bound. -/
theorem ae_forall_matrixQuadratic_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) (B : Ω → Matrix (Fin r) (Fin r) ℝ) (K : Ω → ℝ)
    (hbound : ∀ u : Vector r, ∀ᵐ ω ∂μ, |matrixQuadratic (B ω) u| ≤ K ω * vectorNormSq u) :
    ∀ᵐ ω ∂μ, ∀ u : Vector r, |matrixQuadratic (B ω) u| ≤ K ω * vectorNormSq u := by
  let e : (Fin r → ℚ) → Vector r := fun q j => (q j : ℝ)
  have hd : DenseRange e := DenseRange.piMap (fun _ : Fin r => Rat.denseRange_cast)
  have hq : ∀ q : Fin r → ℚ, ∀ᵐ ω ∂μ, |matrixQuadratic (B ω) (e q)| ≤ K ω * vectorNormSq (e q) :=
    fun q => hbound (e q)
  filter_upwards [ae_all_iff.mpr hq] with ω hω
  have hleft : Continuous (fun u : Vector r => |matrixQuadratic (B ω) u|) := by
    apply Continuous.abs
    unfold matrixQuadratic
    apply continuous_finset_sum
    intro j _
    apply continuous_finset_sum
    intro k _
    exact ((continuous_apply j).mul continuous_const).mul (continuous_apply k)
  have hright : Continuous (fun u : Vector r => K ω * vectorNormSq u) := by
    apply continuous_const.mul
    unfold vectorNormSq
    exact continuous_finset_sum _ (fun j _ => (continuous_apply j).pow 2)
  have hc := isClosed_le hleft hright
  have hrange : Set.range e ⊆ {u | |matrixQuadratic (B ω) u| ≤ K ω * vectorNormSq u} := by
    rintro _ ⟨q, rfl⟩
    exact hω q
  have hclosure := hc.closure_subset_iff.mpr hrange
  intro u
  exact hclosure (hd u)

theorem integrable_matrixQuadratic {Ω : Type*} [mΩ : MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) (B : Ω → Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ j k, Integrable (fun ω => B ω j k) μ) (u : Vector r) :
    Integrable (fun ω => matrixQuadratic (B ω) u) μ :=
  integrable_finset_sum _ (fun j _ => integrable_finset_sum _
    (fun k _ => ((hB j k).const_mul (u j)).mul_const (u k)))

/-- A genuine conditional quadratic budget survives bounded domination
before the conditional average. The conclusion holds simultaneously in
all directions outside one null set, as required by the operator bound. -/
theorem conditionalMatrixAverage_quadratic_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (B D : Ω → Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ j k, Integrable (fun ω => B ω j k) μ)
    (hD : ∀ j k, Integrable (fun ω => D ω j k) μ) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ u, ∀ᵐ ω ∂μ, |matrixQuadratic (B ω) u| ≤ c * matrixQuadratic (D ω) u)
    (K : Ω → ℝ)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H D ω) u ≤ K ω * vectorNormSq u) :
    ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H B ω) u| ≤
        (c * K ω) * vectorNormSq u := by
  apply ae_forall_matrixQuadratic_bound (mΩ := mΩ)
  intro u
  have hCE := condExp_abs_le_of_abs_le (mΩ := mΩ) μ H hH _ _
    (integrable_matrixQuadratic (mΩ := mΩ) μ B hB u)
      ((integrable_matrixQuadratic (mΩ := mΩ) μ D hD u).const_mul c) (hdom u)
  filter_upwards [hCE, matrixQuadratic_conditionalMatrixAverage (mΩ := mΩ) μ H B hB u,
    matrixQuadratic_conditionalMatrixAverage (mΩ := mΩ) μ H D hD u,
    condExp_real_const_mul (mΩ := mΩ) μ H c (fun z => matrixQuadratic (D z) u), hbudget]
    with ω hω hBω hDω hscale hb
  rw [← hBω, hscale, ← hDω] at hω
  exact hω.trans ((mul_le_mul_of_nonneg_left (hb u) hc).trans_eq (by ring))

/-- Relative M2 matrix contraction. Both directional square budgets are
used before taking the conditional average, and no trace/rank bound is
substituted for them. -/
theorem conditionalMatrixAverage_relative_pair_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (B DY DW : Ω → Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ j k, Integrable (fun ω => B ω j k) μ)
    (hDY : ∀ j k, Integrable (fun ω => DY ω j k) μ)
    (hDW : ∀ j k, Integrable (fun ω => DW ω j k) μ) {T : ℝ} (hT : 0 ≤ T)
    (hdom : ∀ u, ∀ᵐ ω ∂μ, |matrixQuadratic (B ω) u| ≤
      (T / 2) * (matrixQuadratic (DY ω) u + matrixQuadratic (DW ω) u))
    (K : Ω → ℝ)
    (hbudgetY : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H DY ω) u ≤ K ω * vectorNormSq u)
    (hbudgetW : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H DW ω) u ≤ K ω * vectorNormSq u) :
    ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H B ω) u| ≤
        (T * K ω) * vectorNormSq u := by
  apply ae_forall_matrixQuadratic_bound (mΩ := mΩ)
  intro u
  let FY : Ω → ℝ := fun z => matrixQuadratic (DY z) u
  let FW : Ω → ℝ := fun z => matrixQuadratic (DW z) u
  have hiY : Integrable FY μ := integrable_matrixQuadratic (mΩ := mΩ) μ DY hDY u
  have hiW : Integrable FW μ := integrable_matrixQuadratic (mΩ := mΩ) μ DW hDW u
  have hCE := condExp_abs_le_of_abs_le (mΩ := mΩ) μ H hH _ _
    (integrable_matrixQuadratic (mΩ := mΩ) μ B hB u) ((hiY.add hiW).const_mul (T / 2)) (hdom u)
  filter_upwards [hCE, matrixQuadratic_conditionalMatrixAverage (mΩ := mΩ) μ H B hB u,
    matrixQuadratic_conditionalMatrixAverage (mΩ := mΩ) μ H DY hDY u,
    matrixQuadratic_conditionalMatrixAverage (mΩ := mΩ) μ H DW hDW u,
    condExp_real_const_mul (mΩ := mΩ) μ H (T / 2) (fun z => FY z + FW z),
    condExp_add hiY hiW H, hbudgetY, hbudgetW]
    with ω hω hBω hYω hWω hscale hadd hbY hbW
  change |(μ[(fun z => matrixQuadratic (B z) u)|H]) ω| ≤
    (μ[(fun z => (T / 2) * (FY z + FW z))|H]) ω at hω
  change (μ[(fun z => FY z + FW z)|H]) ω = (μ[FY|H]) ω + (μ[FW|H]) ω at hadd
  rw [← hBω, hscale, hadd, ← hYω, ← hWω] at hω
  have hb := mul_le_mul_of_nonneg_left (add_le_add (hbY u) (hbW u))
    (div_nonneg hT (by norm_num : (0 : ℝ) ≤ 2))
  exact hω.trans (by convert hb using 1; ring)

def restorationRankOneSum {Ω : Type*} {n r : ℕ}
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) (ω : Ω) : Matrix (Fin r) (Fin r) ℝ :=
  fun j k => ∑ i, c i ω * (Z i ω j * Z i ω k)

def conditionalRestorationCoefficient {Ω : Type*} [mΩ : MeasurableSpace Ω] {n r : ℕ}
    (μ : Measure Ω) (H : MeasurableSpace Ω) (Z : Fin n → Ω → Vector r)
    (c : Fin n → Ω → ℝ) : Ω → Matrix (Fin r) (Fin r) ℝ :=
  conditionalMatrixAverage (mΩ := mΩ) μ H (restorationRankOneSum Z c)

theorem matrixQuadratic_finite_sum {n r : ℕ} (B : Fin n → Matrix (Fin r) (Fin r) ℝ) (u : Vector r) :
    matrixQuadratic (fun j k => ∑ i, B i j k) u = ∑ i, matrixQuadratic (B i) u := by
  simp only [matrixQuadratic, Finset.mul_sum, Finset.sum_mul]
  calc
    _ = ∑ j, ∑ i, ∑ k, u j * B i j k * u k :=
      Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem matrixQuadratic_restorationRankOneSum {Ω : Type*} {n r : ℕ}
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) (ω : Ω) (u : Vector r) :
    matrixQuadratic (restorationRankOneSum Z c ω) u =
      ∑ i, c i ω * (faceDot u (Z i ω)) ^ 2 := by
  change matrixQuadratic (fun j k => ∑ i, c i ω * (Z i ω j * Z i ω k)) u = _
  rw [matrixQuadratic_finite_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← matrixQuadratic_rankOne_eq_square]
  simp only [matrixQuadratic, rankOne, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem integrable_restorationRankOneSum_entry {Ω : Type*} [mΩ : MeasurableSpace Ω] {n r : ℕ}
    (μ : Measure Ω) (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ) {K : ℝ}
    (hcbound : ∀ i, ∀ᵐ ω ∂μ, |c i ω| ≤ K) (j k : Fin r) :
    Integrable (fun ω => restorationRankOneSum Z c ω j k) μ :=
  integrable_finset_sum _ (fun i _ => (hZ i j k).bdd_mul' (hc i)
    (by simpa only [Real.norm_eq_abs] using hcbound i))

/-- Actual conditional covariance budget, with no envelope on the
repeated direction `Z_i` itself. This supplies the baseline `δ^s` factor
after substituting the bounded remaining directional/translation factors. -/
theorem conditional_restoration_coefficient_baseline
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {n r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (hc : ∀ i, AEStronglyMeasurable (m := mΩ) (c i) μ) {K : ℝ} (hK : 0 ≤ K)
    (hcbound : ∀ i, ∀ᵐ ω ∂μ, |c i ω| ≤ K)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u) :
    ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z c ω) u| ≤ K * vectorNormSq u := by
  have hD (j k : Fin r) : Integrable (fun ω => restorationRankOneSum Z (fun _ _ => 1) ω j k) μ := by
    simpa only [restorationRankOneSum, one_mul] using integrable_finset_sum Finset.univ (fun i _ => hZ i j k)
  have hdom (u : Vector r) : ∀ᵐ ω ∂μ,
      |matrixQuadratic (restorationRankOneSum Z c ω) u| ≤
        K * matrixQuadratic (restorationRankOneSum Z (fun _ _ => 1) ω) u := by
    filter_upwards [ae_all_iff.mpr hcbound] with ω hω
    simp only [matrixQuadratic_restorationRankOneSum, one_mul]
    calc
      _ ≤ ∑ i, |c i ω * (faceDot u (Z i ω)) ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, K * (faceDot u (Z i ω)) ^ 2 := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (faceDot u (Z i ω)))]
        exact mul_le_mul_of_nonneg_right (hω i) (sq_nonneg _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hb := conditionalMatrixAverage_quadratic_domination (mΩ := mΩ) μ H hH
    (restorationRankOneSum Z c) (restorationRankOneSum Z (fun _ _ => 1))
    (integrable_restorationRankOneSum_entry (mΩ := mΩ) μ Z c hZ hc hcbound) hD hK hdom (fun _ => 1)
    (by simpa only [one_mul] using hbudget)
  simpa only [conditionalRestorationCoefficient, mul_one] using hb

/-- Entrywise identification with the manuscript's sum of conditional
expectations, justified by genuine integrability of every summand. -/
theorem conditionalRestorationCoefficient_eq_sum_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {n r : ℕ}
    (μ : Measure Ω) (H : MeasurableSpace Ω) (Z : Fin n → Ω → Vector r)
    (c : Fin n → Ω → ℝ)
    (hi : ∀ i j k, Integrable (fun ω => c i ω * (Z i ω j * Z i ω k)) μ) :
    ∀ᵐ ω ∂μ, ∀ j k,
      conditionalRestorationCoefficient (mΩ := mΩ) μ H Z c ω j k =
        ∑ i, (μ[(fun z => c i z * (Z i z j * Z i z k))|H]) ω := by
  have he (j k : Fin r) := condExp_finset_sum (s := Finset.univ)
    (f := fun i => fun ω => c i ω * (Z i ω j * Z i ω k)) (fun i _ => hi i j k) H
  have hall : ∀ᵐ ω ∂μ, ∀ j k, (μ[(fun z => ∑ i, c i z * (Z i z j * Z i z k))|H]) ω =
      ∑ i, (μ[(fun z => c i z * (Z i z j * Z i z k))|H]) ω := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro k
    have hfun : (∑ i, fun z => c i z * (Z i z j * Z i z k)) =
        (fun z => ∑ i, c i z * (Z i z j * Z i z k)) := by
      funext z
      simp only [Finset.sum_apply]
    have hjk := he j k
    rw [hfun] at hjk
    filter_upwards [hjk] with ω hω
    simpa only [Finset.sum_apply] using hω
  exact hall

/-- Actual relative M2 conditional matrix bound for the product of any
two remaining face coordinates. The translation may depend on all arrays. -/
theorem conditional_restoration_coefficient_relative_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {n r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (Z : Fin n → Ω → Vector r) (Y W d : Fin n → Ω → ℝ)
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (hY : ∀ i, AEStronglyMeasurable (m := mΩ) (Y i) μ)
    (hW : ∀ i, AEStronglyMeasurable (m := mΩ) (W i) μ)
    (hd : ∀ i, AEStronglyMeasurable (m := mΩ) (d i) μ) {δ T M : ℝ}
    (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, |W i ω| ≤ δ)
    (hdb : ∀ i, ∀ᵐ ω ∂μ, |d i ω| ≤ T)
    (hbudgetY : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun i z => (Y i z) ^ 2) ω) u ≤
        M * vectorNormSq u)
    (hbudgetW : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun i z => (W i z) ^ 2) ω) u ≤
        M * vectorNormSq u) :
    ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => Y i z * W i z * d i z) ω) u| ≤ (T * M) * vectorNormSq u := by
  have hY₂ (i : Fin n) : ∀ᵐ ω ∂μ, |(Y i ω) ^ 2| ≤ δ ^ 2 := by
    filter_upwards [hYb i] with ω hω
    simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hW₂ (i : Fin n) : ∀ᵐ ω ∂μ, |(W i ω) ^ 2| ≤ δ ^ 2 := by
    filter_upwards [hWb i] with ω hω
    simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hcb (i : Fin n) : ∀ᵐ ω ∂μ, |Y i ω * W i ω * d i ω| ≤ δ ^ 2 * T := by
    filter_upwards [hYb i, hWb i, hdb i] with ω hy hw hdω
    rw [abs_mul, abs_mul]
    have hp : |Y i ω| * |W i ω| ≤ δ ^ 2 := by
      simpa only [pow_two] using mul_le_mul hy hw (abs_nonneg _) hδ
    exact (mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hdω (sq_nonneg _))
  have hBi := integrable_restorationRankOneSum_entry (mΩ := mΩ) μ Z
    (fun i z => Y i z * W i z * d i z) hZ (fun i => ((hY i).mul (hW i)).mul (hd i)) hcb
  have hYi := integrable_restorationRankOneSum_entry (mΩ := mΩ) μ Z
    (fun i z => (Y i z) ^ 2) hZ (fun i => (hY i).pow 2) hY₂
  have hWi := integrable_restorationRankOneSum_entry (mΩ := mΩ) μ Z
    (fun i z => (W i z) ^ 2) hZ (fun i => (hW i).pow 2) hW₂
  have hdom (u : Vector r) : ∀ᵐ ω ∂μ,
      |matrixQuadratic (restorationRankOneSum Z (fun i z => Y i z * W i z * d i z) ω) u| ≤
        (T / 2) * (matrixQuadratic (restorationRankOneSum Z (fun i z => (Y i z) ^ 2) ω) u +
          matrixQuadratic (restorationRankOneSum Z (fun i z => (W i z) ^ 2) ω) u) := by
    filter_upwards [ae_all_iff.mpr hdb] with ω hω
    simp only [matrixQuadratic_restorationRankOneSum]
    calc
      _ ≤ ∑ i, |(Y i ω * W i ω * d i ω) * (faceDot u (Z i ω)) ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (T / 2) * ((Y i ω) ^ 2 * (faceDot u (Z i ω)) ^ 2 +
          (W i ω) ^ 2 * (faceDot u (Z i ω)) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (sq_nonneg (faceDot u (Z i ω))), abs_mul, abs_mul]
        have hyw : |Y i ω| * |W i ω| ≤ ((Y i ω) ^ 2 + (W i ω) ^ 2) / 2 := by
          nlinarith [sq_nonneg (|Y i ω| - |W i ω|), sq_abs (Y i ω), sq_abs (W i ω)]
        have hdω := mul_le_mul_of_nonneg_left (hω i) (mul_nonneg (abs_nonneg (Y i ω)) (abs_nonneg (W i ω)))
        have hmul := mul_le_mul_of_nonneg_right hdω (sq_nonneg (faceDot u (Z i ω)))
        have hpair := mul_le_mul_of_nonneg_left hyw (mul_nonneg hT (sq_nonneg (faceDot u (Z i ω))))
        nlinarith
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  exact conditionalMatrixAverage_relative_pair_domination (mΩ := mΩ) μ H hH _ _ _
    hBi hYi hWi hT hdom (fun _ => M) hbudgetY hbudgetW

def conditionalTranslatedRestorationCoefficient {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {p n r k ℓ : ℕ} (s : FaceSmoother p) (μ : Measure Ω) (H : MeasurableSpace Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) (v : Fin n → Ω → Vector p)
    (α : Fin k → Face p) (β : Fin ℓ → Face p) : Ω → Matrix (Fin r) (Fin r) ℝ :=
  conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
    (fun i ω => c i ω * restorationTranslationCoefficient s α β (v i ω))

theorem conditionalTranslatedRestorationCoefficient_zero_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p n r k ℓ : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (H : MeasurableSpace Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (α : Fin k → Face p) (β : Fin ℓ → Face p) :
    conditionalTranslatedRestorationCoefficient (mΩ := mΩ) s μ H Z c (fun _ _ => 0) α β =
      if ℓ = 0 then conditionalRestorationCoefficient (mΩ := mΩ) μ H Z c else 0 := by
  cases ℓ with
  | zero => simp [conditionalTranslatedRestorationCoefficient, restorationTranslationCoefficient_zero]
  | succ ℓ =>
    funext ω j l
    simp [conditionalTranslatedRestorationCoefficient, restorationTranslationCoefficient_zero,
      conditionalRestorationCoefficient, conditionalMatrixAverage, restorationRankOneSum]
    change (μ[(0 : Ω → ℝ)|H]) ω = 0
    simp only [condExp_zero, Pi.zero_apply]

/-- The relative signed M1 bound is kept signed through conditional
averaging, and only level zero survives under the required zero shift. -/
theorem conditional_restoration_coefficient_relative_signed_zero_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p n r k ℓ : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (_hH : H ≤ mΩ) (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (hi : ∀ i j l, Integrable (fun ω => c i ω * (Z i ω j * Z i ω l)) μ)
    {M : ℝ}
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z c ω) u| ≤ M * vectorNormSq u)
    (α : Fin k → Face p) (β : Fin ℓ → Face p) :
    (∀ j l, Integrable (fun ω => restorationRankOneSum Z c ω j l) μ) ∧
    (∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalTranslatedRestorationCoefficient (mΩ := mΩ) s μ H Z c
        (fun _ _ => 0) α β ω) u| ≤ (if ℓ = 0 then M else 0) * vectorNormSq u) := by
  refine ⟨fun j l => integrable_finset_sum _ (fun i _ => hi i j l), ?_⟩
  rw [conditionalTranslatedRestorationCoefficient_zero_shift (mΩ := mΩ)]
  split_ifs with hℓ
  · exact hbudget
  · exact ae_of_all _ (fun ω u => by simp [matrixQuadratic])

theorem continuous_restorationTranslationCoefficient {p k ℓ : ℕ} (s : FaceSmoother p)
    (α : Fin k → Face p) (β : Fin ℓ → Face p) :
    Continuous (restorationTranslationCoefficient s α β) := by
  unfold restorationTranslationCoefficient translationIncrement
  apply Continuous.mul
  · exact Real.continuous_exp.comp
      ((continuous_finset_sum _ (fun i _ => FaceSmoother.continuous_normalDot (α i))).div_const _)
  · exact continuous_finset_prod _ (fun i _ =>
      (Real.continuous_exp.comp ((FaceSmoother.continuous_normalDot (β i)).div_const _)).sub continuous_const)

theorem restorationTranslationEnvelope_nonneg {p : ℕ} (s : FaceSmoother p)
    {R : ℝ} (hR : 0 ≤ R) (k ℓ : ℕ) :
    0 ≤ Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ := by
  have hη : 0 ≤ Real.exp (R / s.bandwidth) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  positivity

/-- The exact translated coefficient at each binomial-series level obeys
the baseline conditional operator budget. Substituting `b=δ^s` gives the
manuscript's baseline factor without bounding the repeated `Z_i`. -/
theorem conditional_translated_restoration_coefficient_baseline
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p n r k ℓ : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) (v : Fin n → Ω → Vector p)
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (hc : ∀ i, AEStronglyMeasurable (m := mΩ) (c i) μ)
    (hv : ∀ i, AEStronglyMeasurable (m := mΩ) (v i) μ)
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcbound : ∀ i, ∀ᵐ ω ∂μ, |c i ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (α : Fin k → Face p) (β : Fin ℓ → Face p) :
    ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalTranslatedRestorationCoefficient (mΩ := mΩ) s μ H Z c v α β ω) u| ≤
        (b * Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ) * vectorNormSq u := by
  let E := Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ
  have hE : 0 ≤ E := restorationTranslationEnvelope_nonneg s hR k ℓ
  have hcm (i : Fin n) : AEStronglyMeasurable (m := mΩ)
      (fun ω => c i ω * restorationTranslationCoefficient s α β (v i ω)) μ :=
    (hc i).mul ((continuous_restorationTranslationCoefficient s α β).comp_aestronglyMeasurable (hv i))
  have hcb (i : Fin n) : ∀ᵐ ω ∂μ,
      |c i ω * restorationTranslationCoefficient s α β (v i ω)| ≤ b * E := by
    filter_upwards [hcbound i, hvb i] with ω hcω hvω
    rw [abs_mul]
    exact mul_le_mul hcω (abs_restorationTranslationCoefficient_le s α β hR hvω) (abs_nonneg _) hb
  have he := conditional_restoration_coefficient_baseline (mΩ := mΩ) μ H hH Z _ hZ hcm
    (mul_nonneg hb hE) hcb hbudget
  filter_upwards [he] with ω hω
  intro u
  simpa only [conditionalTranslatedRestorationCoefficient, E, mul_assoc] using hω u

/-- The translated M2 coefficient uses both relative face-square budgets
and retains shifts that depend on the summand or its paired copy. -/
theorem conditional_translated_restoration_coefficient_relative_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p n r k ℓ : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (Z : Fin n → Ω → Vector r) (Y W : Fin n → Ω → ℝ) (v : Fin n → Ω → Vector p)
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (hY : ∀ i, AEStronglyMeasurable (m := mΩ) (Y i) μ)
    (hW : ∀ i, AEStronglyMeasurable (m := mΩ) (W i) μ)
    (hv : ∀ i, AEStronglyMeasurable (m := mΩ) (v i) μ)
    {δ R M : ℝ} (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, |W i ω| ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudgetY : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun i z => (Y i z) ^ 2) ω) u ≤
        M * vectorNormSq u)
    (hbudgetW : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun i z => (W i z) ^ 2) ω) u ≤
        M * vectorNormSq u)
    (α : Fin k → Face p) (β : Fin ℓ → Face p) :
    ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalTranslatedRestorationCoefficient (mΩ := mΩ) s μ H Z
        (fun i z => Y i z * W i z) v α β ω) u| ≤
        (M * Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ) * vectorNormSq u := by
  let E := Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ
  have hE : 0 ≤ E := restorationTranslationEnvelope_nonneg s hR k ℓ
  have hd (i : Fin n) : AEStronglyMeasurable (m := mΩ)
      (fun ω => restorationTranslationCoefficient s α β (v i ω)) μ :=
    (continuous_restorationTranslationCoefficient s α β).comp_aestronglyMeasurable (hv i)
  have hdb (i : Fin n) : ∀ᵐ ω ∂μ, |restorationTranslationCoefficient s α β (v i ω)| ≤ E :=
    (hvb i).mono (fun ω hω => abs_restorationTranslationCoefficient_le s α β hR hω)
  have he := conditional_restoration_coefficient_relative_pair (mΩ := mΩ) μ H hH Z Y W
    (fun i ω => restorationTranslationCoefficient s α β (v i ω)) hZ hY hW hd hδ hE hYb hWb hdb hbudgetY hbudgetW
  filter_upwards [he] with ω hω
  intro u
  simpa only [conditionalTranslatedRestorationCoefficient, E, mul_assoc, mul_left_comm, mul_comm] using hω u

end

end RectangleCLT.Companion.SplitV4
