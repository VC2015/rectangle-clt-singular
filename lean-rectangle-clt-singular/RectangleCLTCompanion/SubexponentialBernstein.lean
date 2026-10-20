import RectangleCLTCompanion.SubexponentialClipping

/-! A direct Bernstein-type estimate for clipped sub-exponential residuals.
The proof uses the exponential remainder bound and Chernoff's inequality;
it does not assume a separate concentration theorem. -/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

private theorem exp_le_one_add_add_sq (z : ℝ) :
    Real.exp z ≤ 1 + z + z ^ 2 * Real.exp |z| := by
  by_cases hz : |z| ≤ 1
  · have hr := (le_abs_self (Real.exp z - 1 - z)).trans
      (Real.abs_exp_sub_one_sub_id_le hz)
    have he : 1 ≤ Real.exp |z| := Real.one_le_exp (abs_nonneg z)
    have hs := mul_le_mul_of_nonneg_left he (sq_nonneg z)
    nlinarith
  · have hz' : 1 ≤ |z| := (lt_of_not_ge hz).le
    have hs : 1 ≤ z ^ 2 := by nlinarith [sq_abs z]
    by_cases hpos : 0 ≤ z
    · have he := mul_le_mul_of_nonneg_right hs (Real.exp_nonneg z)
      rw [abs_of_nonneg hpos]
      nlinarith
    · have hneg : z ≤ 0 := (lt_of_not_ge hpos).le
      have he : Real.exp z ≤ 1 := Real.exp_le_one_iff.mpr hneg
      have hs' : -z ≤ z ^ 2 := by rw [abs_of_nonpos hneg] at hz'; nlinarith
      have hem := mul_le_mul_of_nonneg_left
        (Real.one_le_exp (abs_nonneg z)) (sq_nonneg z)
      nlinarith

def centeredClipResidual {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (K u : ℝ) : Ω → ℝ :=
  fun ω => clipResidual (K * u) (X ω) - ∫ a, clipResidual (K * u) (X a) ∂μ

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {X : Ω → ℝ} {K u t : ℝ}

theorem ExponentialMomentBound.integrable_exp_residual
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) (ht : |t| ≤ 1 / (2 * K)) :
    Integrable (fun ω => Real.exp (t * clipResidual (K * u) (X ω))) μ := by
  have hm : Measurable (fun ω => Real.exp (t * clipResidual (K * u) (X ω))) :=
    (((clipResidual_continuous _).measurable.comp h.measurable).const_mul t).exp
  refine h.integrable_exp.mono hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs, Real.abs_exp]
  apply Real.exp_le_exp.mpr
  have hr := abs_clipResidual_le (mul_nonneg h.scale_pos.le hu) (X ω)
  have ht' : |t| ≤ 1 / K := ht.trans (by
    apply one_div_le_one_div_of_le h.scale_pos
    linarith [h.scale_pos])
  calc
    t * clipResidual (K * u) (X ω) ≤ |t * clipResidual (K * u) (X ω)| := le_abs_self _
    _ = |t| * |clipResidual (K * u) (X ω)| := abs_mul _ _
    _ ≤ (1 / K) * |X ω| :=
      mul_le_mul ht' hr (abs_nonneg _) (by positivity)
    _ = |X ω| / K := by ring

theorem ExponentialMomentBound.integrable_residual_sq_exp
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) (ht : |t| ≤ 1 / (2 * K)) :
    Integrable (fun ω => clipResidual (K * u) (X ω) ^ 2 *
      Real.exp (|t * clipResidual (K * u) (X ω)|)) μ := by
  have hm : Measurable (fun ω => clipResidual (K * u) (X ω) ^ 2 *
      Real.exp (|t * clipResidual (K * u) (X ω)|)) := by
    have hr := (clipResidual_continuous (K * u)).measurable.comp h.measurable
    exact (hr.pow_const 2).mul ((hr.const_mul t).abs.exp)
  refine (h.integrable_exp.const_mul (8 * K ^ 2 * Real.exp (-u))).mono
    hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ clipResidual (K * u) (X ω) ^ 2 *
      Real.exp (|t * clipResidual (K * u) (X ω)|) by positivity),
    abs_of_nonneg (show 0 ≤ 8 * K ^ 2 * Real.exp (-u) * Real.exp (|X ω| / K) by positivity)]
  exact clipResidual_sq_exp_le h.scale_pos hu ht _

theorem ExponentialMomentBound.integral_residual_sq_exp_le
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) (ht : |t| ≤ 1 / (2 * K)) :
    (∫ ω, clipResidual (K * u) (X ω) ^ 2 *
      Real.exp (|t * clipResidual (K * u) (X ω)|) ∂μ) ≤
      16 * K ^ 2 * Real.exp (-u) := by
  calc
    _ ≤ ∫ ω, 8 * K ^ 2 * Real.exp (-u) * Real.exp (|X ω| / K) ∂μ :=
      integral_mono (h.integrable_residual_sq_exp hu ht) (h.integrable_exp.const_mul _)
        (fun ω => clipResidual_sq_exp_le h.scale_pos hu ht _)
    _ = (8 * K ^ 2 * Real.exp (-u)) * (∫ ω, Real.exp (|X ω| / K) ∂μ) :=
      integral_const_mul _ _
    _ ≤ (8 * K ^ 2 * Real.exp (-u)) * 2 :=
      mul_le_mul_of_nonneg_left h.integral_exp_le (by positivity)
    _ = _ := by ring

theorem ExponentialMomentBound.integrable_exp_centered_residual
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) (ht : |t| ≤ 1 / (2 * K)) :
    Integrable (fun ω => Real.exp (t * centeredClipResidual μ X K u ω)) μ := by
  have heq : (fun ω => Real.exp (t * centeredClipResidual μ X K u ω)) =
      (fun ω => Real.exp (-(t * ∫ a, clipResidual (K * u) (X a) ∂μ)) *
        Real.exp (t * clipResidual (K * u) (X ω))) := by
    funext ω
    simp only [centeredClipResidual, mul_sub, Real.exp_sub, Real.exp_neg]
    ring
  rw [heq]
  exact (h.integrable_exp_residual hu ht).const_mul _

/-- A small-variance Laplace bound for the genuinely centered residual. -/
theorem ExponentialMomentBound.mgf_centered_residual_le
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) (ht : |t| ≤ 1 / (2 * K)) :
    mgf (centeredClipResidual μ X K u) μ t ≤
      Real.exp (16 * K ^ 2 * Real.exp (-u) * t ^ 2) := by
  let R : Ω → ℝ := fun ω => clipResidual (K * u) (X ω)
  let m : ℝ := ∫ a, R a ∂μ
  have hR : Integrable R μ := h.integrable_residual hu
  have hE : Integrable (fun ω => Real.exp (t * R ω)) μ :=
    h.integrable_exp_residual hu ht
  have hB : Integrable (fun ω => R ω ^ 2 * Real.exp (|t * R ω|)) μ :=
    h.integrable_residual_sq_exp hu ht
  have hpoint (ω : Ω) : Real.exp (t * R ω) ≤
      1 + t * R ω + t ^ 2 * (R ω ^ 2 * Real.exp (|t * R ω|)) := by
    convert exp_le_one_add_add_sq (t * R ω) using 1 <;> ring
  have hint := integral_mono hE
    (((integrable_const 1).add (hR.const_mul t)).add (hB.const_mul (t ^ 2))) hpoint
  have hid : (∫ ω, 1 + t * R ω + t ^ 2 * (R ω ^ 2 * Real.exp (|t * R ω|)) ∂μ) =
      1 + t * m + t ^ 2 * (∫ ω, R ω ^ 2 * Real.exp (|t * R ω|) ∂μ) := by
    rw [integral_add ((integrable_const 1).add (hR.const_mul t)) (hB.const_mul _),
      integral_add (integrable_const 1) (hR.const_mul t)]
    simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul, integral_const_mul]
    rfl
  rw [hid] at hint
  have hbound : mgf R μ t ≤ 1 + t * m + 16 * K ^ 2 * Real.exp (-u) * t ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (h.integral_residual_sq_exp_le hu ht) (sq_nonneg t)
    change (∫ ω, Real.exp (t * R ω) ∂μ) ≤ _
    nlinarith
  have heq : mgf (centeredClipResidual μ X K u) μ t = Real.exp (-(t * m)) * mgf R μ t := by
    unfold mgf
    rw [← integral_const_mul]
    congr 1
    funext ω
    change Real.exp (t * (R ω - m)) = Real.exp (-(t * m)) * Real.exp (t * R ω)
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  calc
    _ ≤ Real.exp (-(t * m)) *
        (1 + (t * m + 16 * K ^ 2 * Real.exp (-u) * t ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      linarith
    _ ≤ Real.exp (-(t * m)) * Real.exp (t * m + 16 * K ^ 2 * Real.exp (-u) * t ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Optimized Chernoff bound for a Laplace estimate available on a bounded
interval. The larger constants keep the optimization elementary. -/
theorem bernstein_upper_tail_of_mgf {Y : Ω → ℝ} {a c s : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hs : 0 ≤ s)
    (hint : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / c →
      Integrable (fun ω => Real.exp (t * Y ω)) μ)
    (hmgf : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / c → mgf Y μ t ≤ Real.exp (a * t ^ 2)) :
    μ.real {ω | 2 * Real.sqrt a * Real.sqrt s + 2 * c * s ≤ Y ω} ≤ Real.exp (-s) := by
  let v := Real.sqrt a
  let q := Real.sqrt s
  let d := v + c * q
  let t := q / d
  have hv : 0 < v := Real.sqrt_pos.mpr ha
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hd : 0 < d := add_pos_of_pos_of_nonneg hv (mul_nonneg hc.le hq)
  have ht : 0 ≤ t := div_nonneg hq hd.le
  have htc : t ≤ 1 / c := by
    apply (div_le_div_iff₀ hd hc).mpr
    dsimp only [d]
    nlinarith [hv.le]
  have htv : t * v ≤ q := by
    dsimp only [t]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).mpr
    dsimp only [d]
    nlinarith [mul_nonneg hc.le hq]
  have hsq : a * t ^ 2 ≤ s := by
    have hv2 : v ^ 2 = a := Real.sq_sqrt ha.le
    have hq2 : q ^ 2 = s := Real.sq_sqrt hs
    have htv0 : 0 ≤ t * v := mul_nonneg ht hv.le
    calc
      _ = (t * v) ^ 2 := by rw [← hv2]; ring
      _ ≤ q ^ 2 := (sq_le_sq₀ htv0 hq).mpr htv
      _ = _ := hq2
  have htr : t * (2 * v * q + 2 * c * s) = 2 * s := by
    have hq2 : q ^ 2 = s := Real.sq_sqrt hs
    dsimp only [t, d]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hd.ne').mpr
    rw [← hq2]
    ring
  have hh := measure_ge_le_exp_mul_mgf
    (X := Y) (t := t) (2 * v * q + 2 * c * s) ht (hint t ht htc)
  apply hh.trans
  calc
    _ ≤ Real.exp (-t * (2 * v * q + 2 * c * s)) * Real.exp (a * t ^ 2) :=
      mul_le_mul_of_nonneg_left (hmgf t ht htc) (Real.exp_nonneg _)
    _ = Real.exp (-(2 * s) + a * t ^ 2) := by rw [← Real.exp_add]; congr 1; nlinarith [htr]
    _ ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)

theorem ExponentialMomentBound.measurable_centered_residual
    (h : ExponentialMomentBound μ X K) : Measurable (centeredClipResidual μ X K u) :=
  ((clipResidual_continuous _).measurable.comp h.measurable).sub_const _

/-- The Laplace bound tensorizes over the actual independent residuals. -/
theorem residual_sum_mgf_le {n : ℕ} (X : Fin n → Ω → ℝ) {K u t : ℝ}
    (hX : ∀ i, ExponentialMomentBound μ (X i) K)
    (hind : iIndepFun X μ) (hu : 0 ≤ u) (ht : |t| ≤ 1 / (2 * K)) :
    mgf (fun ω => ∑ i, centeredClipResidual μ (X i) K u ω) μ t ≤
      Real.exp ((n : ℝ) * 16 * K ^ 2 * Real.exp (-u) * t ^ 2) := by
  let Y := fun i => centeredClipResidual μ (X i) K u
  have hmeas : ∀ i, Measurable (Y i) := fun i => (hX i).measurable_centered_residual
  have hi : iIndepFun Y μ := by
    exact hind.comp (fun i x => clipResidual (K * u) x - ∫ a, clipResidual (K * u) (X i a) ∂μ)
      (fun i => (clipResidual_continuous _).measurable.sub_const _)
  have heq : (fun ω => ∑ i, centeredClipResidual μ (X i) K u ω) =
      ∑ i ∈ (Finset.univ : Finset (Fin n)), Y i := by ext ω; simp [Y]
  rw [heq, hi.mgf_sum hmeas Finset.univ]
  calc
    _ ≤ ∏ _i : Fin n, Real.exp (16 * K ^ 2 * Real.exp (-u) * t ^ 2) := by
      apply Finset.prod_le_prod (fun _ _ => mgf_nonneg)
      intro i _
      exact (hX i).mgf_centered_residual_le hu ht
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; congr 1; ring

theorem residual_sum_integrable_exp {n : ℕ} (X : Fin n → Ω → ℝ) {K u t : ℝ}
    (hX : ∀ i, ExponentialMomentBound μ (X i) K)
    (hind : iIndepFun X μ) (hu : 0 ≤ u) (ht : |t| ≤ 1 / (2 * K)) :
    Integrable (fun ω => Real.exp (t * ∑ i, centeredClipResidual μ (X i) K u ω)) μ := by
  let Y := fun i => centeredClipResidual μ (X i) K u
  have hmeas : ∀ i, Measurable (Y i) := fun i => (hX i).measurable_centered_residual
  have hi : iIndepFun Y μ := by
    exact hind.comp (fun i x => clipResidual (K * u) x - ∫ a, clipResidual (K * u) (X i a) ∂μ)
      (fun i => (clipResidual_continuous _).measurable.sub_const _)
  have hh := hi.integrable_exp_mul_sum hmeas (s := Finset.univ)
    (fun i _ => (hX i).integrable_exp_centered_residual hu ht)
  simpa only [Finset.sum_apply] using hh

/-- Actual one-sided concentration of the unnormalized sum. -/
theorem residual_sum_upper_tail {n : ℕ} (hn : 1 ≤ n) (X : Fin n → Ω → ℝ)
    {K u s : ℝ} (hK : 0 < K) (hX : ∀ i, ExponentialMomentBound μ (X i) K)
    (hind : iIndepFun X μ) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    μ.real {ω | 2 * Real.sqrt ((n : ℝ) * 16 * K ^ 2 * Real.exp (-u)) * Real.sqrt s +
      4 * K * s ≤ ∑ i, centeredClipResidual μ (X i) K u ω} ≤ Real.exp (-s) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  apply bernstein_upper_tail_of_mgf (a := (n : ℝ) * 16 * K ^ 2 * Real.exp (-u))
    (c := 2 * K) (by positivity) (by positivity) hs
  · intro t ht htc
    exact residual_sum_integrable_exp X hX hind hu (by simpa [abs_of_nonneg ht] using htc)
  · intro t ht htc
    exact residual_sum_mgf_le X hX hind hu (by simpa [abs_of_nonneg ht] using htc)

/-- Two-sided form of the bounded-parameter Laplace estimate. -/
theorem bernstein_abs_tail_of_mgf {Y : Ω → ℝ} {a c s : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hs : 0 ≤ s)
    (hint : ∀ t : ℝ, |t| ≤ 1 / c → Integrable (fun ω => Real.exp (t * Y ω)) μ)
    (hmgf : ∀ t : ℝ, |t| ≤ 1 / c → mgf Y μ t ≤ Real.exp (a * t ^ 2)) :
    μ.real {ω | 2 * Real.sqrt a * Real.sqrt s + 2 * c * s ≤ |Y ω|} ≤
      2 * Real.exp (-s) := by
  let r := 2 * Real.sqrt a * Real.sqrt s + 2 * c * s
  have hup : μ.real {ω | r ≤ Y ω} ≤ Real.exp (-s) :=
    bernstein_upper_tail_of_mgf ha hc hs
      (fun t ht htc => hint t (by simpa [abs_of_nonneg ht] using htc))
      (fun t ht htc => hmgf t (by simpa [abs_of_nonneg ht] using htc))
  have hlo : μ.real {ω | r ≤ -Y ω} ≤ Real.exp (-s) := by
    apply bernstein_upper_tail_of_mgf (Y := fun ω => -Y ω) ha hc hs
    · intro t ht htc
      have hi := hint (-t) (by simpa [abs_neg, abs_of_nonneg ht] using htc)
      simpa only [mul_neg, neg_mul] using hi
    · intro t ht htc
      have hi := hmgf (-t) (by simpa [abs_neg, abs_of_nonneg ht] using htc)
      simpa only [mgf, mul_neg, neg_mul, neg_sq] using hi
  have hsub : {ω | r ≤ |Y ω|} ⊆ {ω | r ≤ Y ω} ∪ {ω | r ≤ -Y ω} := by
    intro ω hω
    by_cases hy : 0 ≤ Y ω
    · exact Or.inl (by simpa [abs_of_nonneg hy] using hω)
    · exact Or.inr (by simpa [abs_of_nonpos (le_of_lt (lt_of_not_ge hy))] using hω)
  calc
    _ ≤ μ.real ({ω | r ≤ Y ω} ∪ {ω | r ≤ -Y ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | r ≤ Y ω} + μ.real {ω | r ≤ -Y ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-s) + Real.exp (-s) := add_le_add hup hlo
    _ = _ := by ring

/-- Actual two-sided concentration of the unnormalized residual sum. -/
theorem residual_sum_abs_tail {n : ℕ} (hn : 1 ≤ n) (X : Fin n → Ω → ℝ)
    {K u s : ℝ} (hK : 0 < K) (hX : ∀ i, ExponentialMomentBound μ (X i) K)
    (hind : iIndepFun X μ) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    μ.real {ω | 2 * Real.sqrt ((n : ℝ) * 16 * K ^ 2 * Real.exp (-u)) * Real.sqrt s +
      4 * K * s ≤ |∑ i, centeredClipResidual μ (X i) K u ω|} ≤ 2 * Real.exp (-s) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  apply bernstein_abs_tail_of_mgf (a := (n : ℝ) * 16 * K ^ 2 * Real.exp (-u))
    (c := 2 * K) (by positivity) (by positivity) hs
  · intro t ht
    exact residual_sum_integrable_exp X hX hind hu ht
  · intro t ht
    exact residual_sum_mgf_le X hX hind hu ht

/-- Coordinate union bound. Only independence across observations is used;
the coordinates of each observation may be dependent. -/
theorem residual_array_tail {n p : ℕ} (hn : 1 ≤ n)
    (X : Fin n → Ω → Fin p → ℝ) {K u s : ℝ} (hK : 0 < K)
    (hX : ∀ i j, ExponentialMomentBound μ (fun ω => X i ω j) K)
    (hind : iIndepFun X μ) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    μ.real {ω | ∃ j : Fin p,
      2 * Real.sqrt ((n : ℝ) * 16 * K ^ 2 * Real.exp (-u)) * Real.sqrt s + 4 * K * s ≤
        |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} ≤
      2 * (p : ℝ) * Real.exp (-s) := by
  let r := 2 * Real.sqrt ((n : ℝ) * 16 * K ^ 2 * Real.exp (-u)) * Real.sqrt s + 4 * K * s
  have hcoord (j : Fin p) : iIndepFun (fun i ω => X i ω j) μ :=
    hind.comp (fun _ x => x j) (fun _ => measurable_pi_apply j)
  have htail (j : Fin p) :
      μ.real {ω | r ≤ |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} ≤
        2 * Real.exp (-s) :=
    residual_sum_abs_tail hn (fun i ω => X i ω j) hK (fun i => hX i j) (hcoord j) hu hs
  have heq : {ω | ∃ j : Fin p, r ≤ |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} =
      ⋃ j : Fin p, {ω | r ≤ |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} := by
    ext ω
    simp
  rw [heq]
  calc
    _ ≤ ∑ j : Fin p, μ.real {ω | r ≤ |∑ i, centeredClipResidual μ (fun a => X i a j) K u ω|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin p, 2 * Real.exp (-s) := Finset.sum_le_sum (fun j _ => htail j)
    _ = _ := by simp; ring

end
end RectangleCLT.Companion
