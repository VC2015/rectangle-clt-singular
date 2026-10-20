import RectangleCLTCompanion.RestorationTraceSeries
import RectangleCLTCompanion.RestorationSummability

/-! Translated-base restoration from the explicit actual averaged selector
matrix estimate.  That estimate remains an explicit premise of this
intermediate theorem; every coefficient, experiment, and series below is
concrete and all its interchanges have been proved. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p r : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

theorem measurable_selectorGaussianScore
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) {q : ℕ}
    (α : Fin q → Face p) (j l : Fin r) :
    Measurable (fun ω => selectorGaussianScore s A V α ω j l) := by
  have hA : Measurable (fun ag : Ω × Vector r => A.mulVec ag.2) := by
    apply measurable_pi_lambda
    intro k
    change Measurable (fun ag : Ω × Vector r => ∑ i, A k i * ag.2 i)
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
      ((measurable_pi_apply i).comp measurable_snd))
  have hU := hA.add (hV.comp measurable_fst)
  have hw := measurable_selectorTupleWeight_comp s α _ hU
  have hg : Measurable (fun ag : Ω × Vector r =>
      (ag.2 j * ag.2 l - if j = l then 1 else 0) *
        selectorTupleWeight s α (A.mulVec ag.2 + V ag.1)) :=
    ((((measurable_pi_apply j).comp measurable_snd).mul
      ((measurable_pi_apply l).comp measurable_snd)).sub measurable_const).mul hw
  exact hg.stronglyMeasurable.integral_prod_right'.measurable

private theorem integral_abs_le_of_integrable_series
    (ν : Measure Ω) (F : ℕ → Ω → ℝ) (f : Ω → ℝ) (G : ℕ → ℝ) {M : ℝ}
    (hFi : ∀ ℓ, Integrable (F ℓ) ν)
    (hf : ∀ ω, HasSum (fun ℓ => F ℓ ω) (f ω))
    (hG : HasSum G M)
    (hFG : ∀ ℓ, (∫ ω, ‖F ℓ ω‖ ∂ν) ≤ G ℓ) :
    Integrable f ν ∧ |∫ ω, f ω ∂ν| ≤ M := by
  have hsum : Summable (fun ℓ => ∫ ω, ‖F ℓ ω‖ ∂ν) :=
    Summable.of_nonneg_of_le (fun ℓ => integral_nonneg (fun _ => norm_nonneg _)) hFG hG.summable
  have hs := hasSum_integral_of_summable_integral_norm hFi hsum
  have heq : (∫ ω, ∑' ℓ, F ℓ ω ∂ν) = ∫ ω, f ω ∂ν := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => (hf ω).tsum_eq)
  rw [heq] at hs
  exact ⟨integrable_of_hasSum_integral_norm ν F f hFi hf hsum,
    hs.norm_le_of_bounded hG (fun ℓ =>
      (norm_integral_le_integral_norm _).trans (hFG ℓ))⟩

/-- The common-base selector restoration bound, before the finite derivative
partition coefficients and the two Gaussian IBPs are restored.  The left
side is the actual translated fresh-array/Gaussian experiment. -/
theorem restorationTranslatedExpectation_integrable_and_bound
    (s : FaceSmoother p) (ν : Measure Ω) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) {n k : ℕ}
    (Z : Ω → Fin n → Ξ → Vector r)
    (c : Fin n → (Fin k → Face p) → Ω → Ξ → ℝ)
    (v : Fin n → Ω → Ξ → Vector p) {b K R C T : ℝ}
    (hmatrix : AveragedSelectorMatrixEstimate s ν A V C T)
    (hk : 1 ≤ k) (hV : Measurable V)
    (hZm : ∀ ω i, Measurable (Z ω i))
    (hZ : ∀ ω i j l, Integrable (fun a => Z ω i a j * Z ω i a l) μ)
    (hc : ∀ i α ω, Measurable (fun a => c i α ω a))
    (hv : ∀ i ω, Measurable (v i ω))
    (hb : ∀ i α ω a, |c i α ω a| ≤ b)
    (hb0 : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hvb : ∀ i ω a, ‖v i ω a‖ ≤ R)
    (hbudget : ∀ ω u, ∑ i, ∫ a, (faceDot u (Z ω i a)) ^ 2 ∂μ ≤
      K * vectorNormSq u)
    (hBm : ∀ (ℓ : ℕ) (α : Fin k → Face p) (β : Fin ℓ → Face p) (j l : Fin r),
      Measurable (fun ω => translatedRestorationCoefficient s μ Z c v α β ω j l))
    (hC : 1 ≤ C) (_hT : 0 ≤ T)
    (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    Integrable (fun ω => fixedRestorationTranslatedExpectation s μ A (V ω) (Z ω)
      (fun i α a => c i α ω a) (fun i => v i ω)) ν ∧
    |∫ ω, fixedRestorationTranslatedExpectation s μ A (V ω) (Z ω)
      (fun i α a => c i α ω a) (fun i => v i ω) ∂ν| ≤
        (b * K * Real.exp ((k : ℝ) * R / s.bandwidth) * C ^ (k + 1) * T) /
          (1 - C * (Real.exp (R / s.bandwidth) - 1)) ^ (k + 1) := by
  let η := Real.exp (R / s.bandwidth) - 1
  let E := Real.exp ((k : ℝ) * R / s.bandwidth)
  let P := b * K * E * C ^ (k + 1) * T
  let F : ℕ → Ω → ℝ := fun ℓ ω =>
    fixedRestorationTraceOrder s μ A (V ω) (Z ω)
      (fun i α a => c i α ω a) (fun i => v i ω) ℓ
  let H : ℕ → Ω → ℝ := fun ℓ ω =>
    ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
      |Matrix.trace (translatedRestorationCoefficient s μ Z c v α β ω *
        selectorGaussianScore s A V (Fin.append α β) ω)|
  have hη : 0 ≤ η :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hη1 : η < 1 :=
    (le_mul_of_one_le_left hη hC).trans_lt hsmall
  have hradius : R / s.bandwidth < Real.log 2 := by
    apply (Real.exp_lt_exp).mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    dsimp only [η] at hη1
    linarith
  have hHi (ℓ : ℕ) : Integrable (H ℓ) ν := by
    let B : (Fin (k + ℓ) → Face p) → Ω → Matrix (Fin r) (Fin r) ℝ :=
      fun γ => translatedRestorationCoefficient s μ Z c v
        (fun i => γ (Fin.castAdd ℓ i)) (fun i => γ (Fin.natAdd k i))
    have hs := hmatrix (k + ℓ) (by omega) (b * E * η ^ ℓ * K)
      (by positivity) B (fun γ j l => hBm ℓ _ _ j l)
      (fun γ ω u => translatedRestorationCoefficient_quadratic_le s μ Z c v
        hZ (fun i α ω => (hc i α ω).aestronglyMeasurable) hv hb hb0 hR hvb hbudget _ _ ω u)
    apply hs.1.congr
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp only [H]
      rw [sum_faceTuples_append]
      apply Finset.sum_congr rfl
      intro γ _
      simp only [B, Fin.append_castAdd_natAdd])
  have hSm (ℓ : ℕ) : Measurable (fun ω =>
      ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
        Matrix.trace (translatedRestorationCoefficient s μ Z c v α β ω *
          selectorGaussianScore s A V (Fin.append α β) ω)) := by
    apply Finset.measurable_sum
    intro α _
    apply Finset.measurable_sum
    intro β _
    unfold Matrix.trace
    apply Finset.measurable_sum
    intro j _
    change Measurable (fun ω => ∑ l,
      translatedRestorationCoefficient s μ Z c v α β ω j l *
        selectorGaussianScore s A V (Fin.append α β) ω l j)
    exact Finset.measurable_sum _ (fun l _ => (hBm ℓ α β j l).mul
      (measurable_selectorGaussianScore s A V hV _ l j))
  have hnorm (ℓ : ℕ) (ω : Ω) :
      ‖F ℓ ω‖ ≤ ((k + ℓ).choose ℓ : ℝ) * H ℓ ω := by
    dsimp only [F, fixedRestorationTraceOrder, H]
    rw [Real.norm_eq_abs, abs_mul]
    have ha : |(-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ)| =
        ((k + ℓ).choose ℓ : ℝ) := by simp [abs_mul, abs_pow]
    rw [ha]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro α _
    exact Finset.abs_sum_le_sum_abs _ _
  have hFi (ℓ : ℕ) : Integrable (F ℓ) ν := by
    apply ((hHi ℓ).const_mul ((k + ℓ).choose ℓ : ℝ)).mono'
    · exact ((hSm ℓ).const_mul _).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hnorm ℓ)
  have hFG (ℓ : ℕ) : (∫ ω, ‖F ℓ ω‖ ∂ν) ≤
      P * (((k + ℓ).choose ℓ : ℝ) * (C * η) ^ ℓ) := by
    calc
      _ ≤ ∫ ω, ((k + ℓ).choose ℓ : ℝ) * H ℓ ω ∂ν :=
        integral_mono_ae (hFi ℓ).norm ((hHi ℓ).const_mul _)
          (Filter.Eventually.of_forall (hnorm ℓ))
      _ = ((k + ℓ).choose ℓ : ℝ) * ∫ ω, H ℓ ω ∂ν := integral_const_mul _ _
      _ ≤ ((k + ℓ).choose ℓ : ℝ) *
          ((b * E * η ^ ℓ * K) * C ^ (k + ℓ + 1) * T) :=
        mul_le_mul_of_nonneg_left
          (averaged_translatedRestorationCoefficient_order_le s ν μ A V Z c v hmatrix hk
            hZ (fun i α ω => (hc i α ω).aestronglyMeasurable) hv hb hb0 hK hR hvb
            hbudget (hBm ℓ)) (Nat.cast_nonneg _)
      _ = _ := by
        dsimp only [P]
        rw [show k + ℓ + 1 = (k + 1) + ℓ by omega, pow_add, mul_pow]
        ring
  have hG : HasSum (fun ℓ : ℕ => P *
      (((k + ℓ).choose ℓ : ℝ) * (C * η) ^ ℓ))
      (P / (1 - C * η) ^ (k + 1)) := by
    convert (hasSum_restoration_matrix_majorant k hC0 hη hsmall).mul_left P using 1
    ring
  exact integral_abs_le_of_integrable_series ν F _ _ hFi
    (fun ω => hasSum_fixedRestorationTraceOrder s μ A (V ω) (Z ω)
      (fun i α a => c i α ω a) (fun i => v i ω)
      (hZm ω) (hZ ω) (fun i α => hc i α ω) (fun i => hv i ω)
      (fun i α a => hb i α ω a) hb0 hR (fun i a => hvb i ω a) hradius)
    hG hFG

theorem abs_integral_fixedRestorationTranslatedExpectation_le
    (s : FaceSmoother p) (ν : Measure Ω) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) {n k : ℕ}
    (Z : Ω → Fin n → Ξ → Vector r)
    (c : Fin n → (Fin k → Face p) → Ω → Ξ → ℝ)
    (v : Fin n → Ω → Ξ → Vector p) {b K R C T : ℝ}
    (hmatrix : AveragedSelectorMatrixEstimate s ν A V C T)
    (hk : 1 ≤ k) (hV : Measurable V)
    (hZm : ∀ ω i, Measurable (Z ω i))
    (hZ : ∀ ω i j l, Integrable (fun a => Z ω i a j * Z ω i a l) μ)
    (hc : ∀ i α ω, Measurable (fun a => c i α ω a))
    (hv : ∀ i ω, Measurable (v i ω))
    (hb : ∀ i α ω a, |c i α ω a| ≤ b)
    (hb0 : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hvb : ∀ i ω a, ‖v i ω a‖ ≤ R)
    (hbudget : ∀ ω u, ∑ i, ∫ a, (faceDot u (Z ω i a)) ^ 2 ∂μ ≤
      K * vectorNormSq u)
    (hBm : ∀ (ℓ : ℕ) (α : Fin k → Face p) (β : Fin ℓ → Face p) (j l : Fin r),
      Measurable (fun ω => translatedRestorationCoefficient s μ Z c v α β ω j l))
    (hC : 1 ≤ C) (_hT : 0 ≤ T)
    (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    |∫ ω, fixedRestorationTranslatedExpectation s μ A (V ω) (Z ω)
      (fun i α a => c i α ω a) (fun i => v i ω) ∂ν| ≤
        (b * K * Real.exp ((k : ℝ) * R / s.bandwidth) * C ^ (k + 1) * T) /
          (1 - C * (Real.exp (R / s.bandwidth) - 1)) ^ (k + 1) := by
  exact (restorationTranslatedExpectation_integrable_and_bound s ν μ A V Z c v
    hmatrix hk hV hZm hZ hc hv hb hb0 hK hR hvb hbudget hBm hC _hT hsmall).2

end
end RectangleCLT.Companion
