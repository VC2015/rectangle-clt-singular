import RectangleCLT.TruncationMoments
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Discarded moments and covariance loss

The estimates use the fourth moment and the discarded probability as
separate inputs.  In particular the fourth moment is never replaced by a
fourth power of the exponential tail scale.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Integral Cauchy--Schwarz in squared form, proved from nonnegative
squares.  The three integrability assumptions are exactly those used in
the expansion. -/
theorem integral_product_sq_le {f g : Ω → ℝ}
    (hf : Integrable (fun ω => f ω ^ 2) μ)
    (hg : Integrable (fun ω => g ω ^ 2) μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤
      (∫ ω, f ω ^ 2 ∂μ) * (∫ ω, g ω ^ 2 ∂μ) := by
  have hquad (t : ℝ) :
      0 ≤ (∫ ω, g ω ^ 2 ∂μ) * (t * t) +
        (-2 * ∫ ω, f ω * g ω ∂μ) * t + ∫ ω, f ω ^ 2 ∂μ := by
    have heq : (∫ ω, (f ω - t * g ω) ^ 2 ∂μ) =
        (∫ ω, g ω ^ 2 ∂μ) * (t * t) +
          (-2 * ∫ ω, f ω * g ω ∂μ) * t + ∫ ω, f ω ^ 2 ∂μ := by
      calc
        _ = ∫ ω, (t * t) * g ω ^ 2 + (-2 * t) * (f ω * g ω) + f ω ^ 2 ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun ω => by ring
        _ = _ := by
          rw [integral_add
            (f := fun ω => (t * t) * g ω ^ 2 + (-2 * t) * (f ω * g ω))
            (g := fun ω => f ω ^ 2)
            ((hg.const_mul (t * t)).add (hfg.const_mul (-2 * t))) hf,
            integral_add (f := fun ω => (t * t) * g ω ^ 2)
              (g := fun ω => (-2 * t) * (f ω * g ω))
              (hg.const_mul (t * t)) (hfg.const_mul (-2 * t))]
          simp only [integral_const_mul]
          ring
    rw [← heq]
    exact integral_nonneg fun ω => sq_nonneg _
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  nlinarith

/-- The same inequality summed over observations, so the distribution may
vary with the observation index. -/
theorem sum_integral_product_sq_le {n : ℕ} {f g : Fin n → Ω → ℝ}
    (hf : ∀ i, Integrable (fun ω => f i ω ^ 2) μ)
    (hg : ∀ i, Integrable (fun ω => g i ω ^ 2) μ)
    (hfg : ∀ i, Integrable (fun ω => f i ω * g i ω) μ) :
    (∑ i, ∫ ω, f i ω * g i ω ∂μ) ^ 2 ≤
      (∑ i, ∫ ω, f i ω ^ 2 ∂μ) * (∑ i, ∫ ω, g i ω ^ 2 ∂μ) := by
  have hquad (t : ℝ) :
      0 ≤ (∑ i, ∫ ω, g i ω ^ 2 ∂μ) * (t * t) +
        (-2 * ∑ i, ∫ ω, f i ω * g i ω ∂μ) * t + ∑ i, ∫ ω, f i ω ^ 2 ∂μ := by
    have hnonneg : 0 ≤ ∑ i, ∫ ω, (f i ω - t * g i ω) ^ 2 ∂μ :=
      Finset.sum_nonneg fun i _ => integral_nonneg fun ω => sq_nonneg _
    have heq (i : Fin n) : (∫ ω, (f i ω - t * g i ω) ^ 2 ∂μ) =
        (t * t) * (∫ ω, g i ω ^ 2 ∂μ) +
          (-2 * t) * (∫ ω, f i ω * g i ω ∂μ) + ∫ ω, f i ω ^ 2 ∂μ := by
      calc
        _ = ∫ ω, (t * t) * g i ω ^ 2 + (-2 * t) * (f i ω * g i ω) + f i ω ^ 2 ∂μ := by
          apply integral_congr_ae
          exact ae_of_all _ fun ω => by ring
        _ = _ := by
          rw [integral_add
            (f := fun ω => (t * t) * g i ω ^ 2 + (-2 * t) * (f i ω * g i ω))
            (g := fun ω => f i ω ^ 2)
            (((hg i).const_mul (t * t)).add ((hfg i).const_mul (-2 * t))) (hf i),
            integral_add (f := fun ω => (t * t) * g i ω ^ 2)
              (g := fun ω => (-2 * t) * (f i ω * g i ω))
              ((hg i).const_mul (t * t)) ((hfg i).const_mul (-2 * t))]
          simp only [integral_const_mul]
    simp_rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum] at hnonneg
    nlinarith only [hnonneg]
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  nlinarith

/-- Cauchy--Schwarz for the sum of discarded expectations, with a different
discard event for each observation. -/
theorem sum_indicator_integral_sq_le [IsFiniteMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {A : Fin n → Set Ω}
    (hA : ∀ i, MeasurableSet (A i))
    (hX : ∀ i, Integrable (X i) μ)
    (hX2 : ∀ i, Integrable (fun ω => X i ω ^ 2) μ) :
    (∑ i, ∫ ω, (A i).indicator (X i) ω ∂μ) ^ 2 ≤
      (∑ i, ∫ ω, X i ω ^ 2 ∂μ) * (∑ i, μ.real (A i)) := by
  let g : Fin n → Ω → ℝ := fun i => (A i).indicator (fun _ => 1)
  have hgi (i : Fin n) : Integrable (fun ω => g i ω ^ 2) μ := by
    have heq : (fun ω => g i ω ^ 2) = g i := by
      funext ω
      by_cases hω : ω ∈ A i <;> simp [g, hω]
    rw [heq]
    exact (integrable_const (1 : ℝ)).indicator (hA i)
  have hfg (i : Fin n) : (fun ω => X i ω * g i ω) = (A i).indicator (X i) := by
    funext ω
    by_cases hω : ω ∈ A i <;> simp [g, hω]
  have hfgi (i : Fin n) : Integrable (fun ω => X i ω * g i ω) μ := by
    rw [hfg]
    exact (hX i).indicator (hA i)
  have hgint (i : Fin n) : (∫ ω, g i ω ^ 2 ∂μ) = μ.real (A i) := by
    have heq : (fun ω => g i ω ^ 2) = (A i).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : ω ∈ A i <;> simp [g, hω]
    rw [heq, integral_indicator (hA i)]
    simp
  simpa only [hfg, hgint] using sum_integral_product_sq_le hX2 hgi hfgi

/-- The averaged fourth-moment hypothesis controls the averaged discarded
second moments by `B4*sqrt(q)`, preserving the paper's fourth-moment units. -/
theorem discarded_second_sum_le [IsFiniteMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {A : Fin n → Set Ω} {B4 q : ℝ}
    (hA : ∀ i, MeasurableSet (A i))
    (hX2 : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hX4 : ∀ i, Integrable (fun ω => X i ω ^ 4) μ)
    (hB : 0 ≤ B4) (hq : 0 ≤ q)
    (hfour : (∑ i, ∫ ω, X i ω ^ 4 ∂μ) ≤ n * B4 ^ 2)
    (hprob : ∀ i, μ.real (A i) ≤ q) :
    (∑ i, ∫ ω, (A i).indicator (fun x => X i x ^ 2) ω ∂μ) ≤
      n * B4 * Real.sqrt q := by
  have hX22 (i : Fin n) : Integrable (fun ω => (X i ω ^ 2) ^ 2) μ := by
    simpa only [← pow_mul] using hX4 i
  have hc := sum_indicator_integral_sq_le hA hX2 hX22
  simp only [← pow_mul, Nat.reduceMul] at hc
  have hp : (∑ i, μ.real (A i)) ≤ n * q := by
    calc
      _ ≤ ∑ _i : Fin n, q := Finset.sum_le_sum fun i _ => hprob i
      _ = n * q := by simp
  have hp0 : 0 ≤ ∑ i, μ.real (A i) := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  have hf0 : 0 ≤ (n : ℝ) * B4 ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hbound : (∑ i, ∫ ω, (A i).indicator (fun x => X i x ^ 2) ω ∂μ) ^ 2 ≤
      (n * B4 * Real.sqrt q) ^ 2 := by
    calc
      _ ≤ (∑ i, ∫ ω, X i ω ^ 4 ∂μ) * (∑ i, μ.real (A i)) := hc
      _ ≤ (n * B4 ^ 2) * (n * q) := mul_le_mul hfour hp hp0 hf0
      _ = (n * B4 * Real.sqrt q) ^ 2 := by rw [mul_pow, Real.sq_sqrt hq]; ring
  have hleft : 0 ≤ ∑ i, ∫ ω, (A i).indicator (fun x => X i x ^ 2) ω ∂μ := by
    apply Finset.sum_nonneg
    intro i _
    apply integral_nonneg
    intro ω
    by_cases hω : ω ∈ A i <;> simp [hω, sq_nonneg]
  exact (sq_le_sq₀ hleft (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB)
    (Real.sqrt_nonneg q))).mp hbound

/-- Summed discarded means under the actual summed second-moment
normalization. -/
theorem discarded_mean_sum_abs_le [IsFiniteMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {A : Fin n → Set Ω} {q : ℝ}
    (hA : ∀ i, MeasurableSet (A i))
    (hX : ∀ i, Integrable (X i) μ)
    (hX2 : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hq : 0 ≤ q) (hsecond : (∑ i, ∫ ω, X i ω ^ 2 ∂μ) ≤ n)
    (hprob : ∀ i, μ.real (A i) ≤ q) :
    |∑ i, ∫ ω, (A i).indicator (X i) ω ∂μ| ≤ n * Real.sqrt q := by
  have hc := sum_indicator_integral_sq_le hA hX hX2
  have hp : (∑ i, μ.real (A i)) ≤ n * q := by
    calc
      _ ≤ ∑ _i : Fin n, q := Finset.sum_le_sum fun i _ => hprob i
      _ = n * q := by simp
  have hp0 : 0 ≤ ∑ i, μ.real (A i) := Finset.sum_nonneg fun _ _ => measureReal_nonneg
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg q))).mp
  rw [sq_abs]
  calc
    _ ≤ (∑ i, ∫ ω, X i ω ^ 2 ∂μ) * (∑ i, μ.real (A i)) := hc
    _ ≤ (n : ℝ) * (n * q) := mul_le_mul hsecond hp hp0 (Nat.cast_nonneg _)
    _ = ((n : ℝ) * Real.sqrt q) ^ 2 := by rw [mul_pow, Real.sq_sqrt hq]; ring

/-- Discarded pair moments are bounded by the mean of the two discarded
coordinate second moments. -/
theorem indicator_pair_integral_abs_le_second_mean
    {f g : Ω → ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ)
    (hg2 : Integrable (fun ω => g ω ^ 2) μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ) :
    |∫ ω, A.indicator (fun x => f x * g x) ω ∂μ| ≤
      ((∫ ω, A.indicator (fun x => f x ^ 2) ω ∂μ) +
        (∫ ω, A.indicator (fun x => g x ^ 2) ω ∂μ)) / 2 := by
  have hi := (hf2.indicator hA).add (hg2.indicator hA)
  have hbound : (∫ ω, |A.indicator (fun x => f x * g x) ω| ∂μ) ≤
      ∫ ω, (A.indicator (fun x => f x ^ 2) ω +
        A.indicator (fun x => g x ^ 2) ω) / 2 ∂μ := by
    apply integral_mono ((hfg.indicator hA).abs) (hi.div_const 2)
    intro ω
    change |A.indicator (fun x => f x * g x) ω| ≤
      (A.indicator (fun x => f x ^ 2) ω + A.indicator (fun x => g x ^ 2) ω) / 2
    by_cases hω : ω ∈ A
    · simp only [Set.indicator_of_mem hω, abs_mul]
      nlinarith [sq_nonneg (|f ω| - |g ω|), sq_abs (f ω), sq_abs (g ω)]
    · simp [hω]
  rw [integral_div, integral_add (hf2.indicator hA) (hg2.indicator hA)] at hbound
  exact abs_integral_le_integral_abs.trans hbound

/-- Squared discarded second moment is controlled by the fourth moment
times the probability of the discarded event. -/
theorem discarded_second_sq_le_fourth_mul_probability [IsFiniteMeasure μ]
    {X : Ω → ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hX4 : Integrable (fun ω => X ω ^ 4) μ) :
    (∫ ω, A.indicator (fun x => X x ^ 2) ω ∂μ) ^ 2 ≤
      (∫ ω, X ω ^ 4 ∂μ) * μ.real A := by
  let g : Ω → ℝ := A.indicator (fun _ => 1)
  have hg : Integrable (fun ω => g ω ^ 2) μ := by
    have heq : (fun ω => g ω ^ 2) = g := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [g, hω]
    rw [heq]
    exact (integrable_const (1 : ℝ)).indicator hA
  have hfg : Integrable (fun ω => X ω ^ 2 * g ω) μ := by
    have heq : (fun ω => X ω ^ 2 * g ω) =
        A.indicator (fun ω => X ω ^ 2) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [g, hω]
    rw [heq]
    exact hX2.indicator hA
  have hf : Integrable (fun ω => (X ω ^ 2) ^ 2) μ := by
    simpa only [← pow_mul] using hX4
  have h := integral_product_sq_le hf hg hfg
  have hprod : (fun ω => X ω ^ 2 * g ω) =
      A.indicator (fun ω => X ω ^ 2) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [g, hω]
  have hgint : (∫ ω, g ω ^ 2 ∂μ) = μ.real A := by
    have heq : (fun ω => g ω ^ 2) = A.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [g, hω]
    rw [heq, integral_indicator hA]
    simp
  simpa only [hprod, hgint, ← pow_mul, Nat.reduceMul] using h

/-- Squared discarded mean is controlled by the discarded second moment
times its event probability. -/
theorem discarded_mean_sq_le_second_mul_probability [IsFiniteMeasure μ]
    {X : Ω → ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hX : Integrable X μ) (hX2 : Integrable (fun ω => X ω ^ 2) μ) :
    (∫ ω, A.indicator X ω ∂μ) ^ 2 ≤
      (∫ ω, A.indicator (fun x => X x ^ 2) ω ∂μ) * μ.real A := by
  let f : Ω → ℝ := A.indicator X
  let g : Ω → ℝ := A.indicator (fun _ => 1)
  have hf2 : (fun ω => f ω ^ 2) = A.indicator (fun ω => X ω ^ 2) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [f, hω]
  have hg2 : (fun ω => g ω ^ 2) = g := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [g, hω]
  have hfg : (fun ω => f ω * g ω) = A.indicator X := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [f, g, hω]
  have hfi : Integrable (fun ω => f ω ^ 2) μ := by
    rw [hf2]
    exact hX2.indicator hA
  have hgi : Integrable (fun ω => g ω ^ 2) μ := by
    rw [hg2]
    exact (integrable_const (1 : ℝ)).indicator hA
  have hfgi : Integrable (fun ω => f ω * g ω) μ := by
    rw [hfg]
    exact hX.indicator hA
  have h := integral_product_sq_le hfi hgi hfgi
  rw [hfg, hf2, hg2] at h
  simpa only [g, integral_indicator hA, integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ] using h

end

end RectangleCLT
