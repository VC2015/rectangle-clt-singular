import RectangleCLT.Statement
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Sub-exponential tails before truncation

The tail scale is separate from the fourth-moment scale.  These lemmas
apply to different distributions for every observation and coordinate.
`ExponentialMomentBound` records the exponential-moment convention at
the specified scale, including integrability of the exponential.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The usual exponential-moment bound at scale `K`. -/
structure ExponentialMomentBound (μ : Measure Ω) (X : Ω → ℝ) (K : ℝ) : Prop where
  scale_pos : 0 < K
  integrable_exp : Integrable (fun ω => Real.exp (|X ω| / K)) μ
  integral_exp_le_two : (∫ ω, Real.exp (|X ω| / K) ∂μ) ≤ 2

/-- The extended `ψ₁` Luxemburg norm.  Its value is infinity when no
admissible exponential scale exists; this avoids the empty-real-infimum
pitfall.  Admissibility is precisely `E exp (|X|/t) ≤ 2`. -/
def psiOneNorm (μ : Measure Ω) (X : Ω → ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ r : ℝ, ExponentialMomentBound μ X r ∧ t = ENNReal.ofReal r}

/-- Enlarging the exponential scale weakens the moment condition. -/
theorem ExponentialMomentBound.mono {X : Ω → ℝ} {K L : ℝ}
    (h : ExponentialMomentBound μ X K) (hX : Measurable X) (hKL : K ≤ L) :
    ExponentialMomentBound μ X L := by
  have hL : 0 < L := h.scale_pos.trans_le hKL
  have hle : ∀ ω, Real.exp (|X ω| / L) ≤ Real.exp (|X ω| / K) := by
    intro ω
    exact Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_left (abs_nonneg _) h.scale_pos hKL)
  have hi : Integrable (fun ω => Real.exp (|X ω| / L)) μ := by
    apply h.integrable_exp.mono' ((hX.abs.div_const L).exp.aestronglyMeasurable)
    exact ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hle ω
  exact ⟨hL, hi, (integral_mono hi h.integrable_exp hle).trans h.integral_exp_le_two⟩

/-- A norm bound supplies an admissible scale at `2K`.  Passing to this
slightly larger scale needs only the infimum property, so no unjustified
attainment of the Luxemburg infimum is used. -/
theorem exponentialMomentBound_two_mul_of_psiOneNorm_le
    {X : Ω → ℝ} {K : ℝ} (hX : Measurable X) (hK : 0 < K)
    (hψ : psiOneNorm μ X ≤ ENNReal.ofReal K) :
    ExponentialMomentBound μ X (2 * K) := by
  have hK2 : ENNReal.ofReal K < ENNReal.ofReal (2 * K) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hinf : psiOneNorm μ X < ENNReal.ofReal (2 * K) := hψ.trans_lt hK2
  obtain ⟨t, ⟨r, hr, rfl⟩, hrt⟩ := sInf_lt_iff.mp hinf
  exact hr.mono hX ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hrt).le

/-- Exponential integrability supplies the integrability needed for every
natural coordinate moment. -/
theorem ExponentialMomentBound.integrable_pow
    {X : Ω → ℝ} {K : ℝ} (h : ExponentialMomentBound μ X K)
    (hX : Measurable X) (m : ℕ) : Integrable (fun ω => X ω ^ m) μ := by
  have hfac : 0 < (m.factorial : ℝ) := by positivity
  have hKpow : 0 ≤ K ^ m := pow_nonneg h.scale_pos.le _
  apply (h.integrable_exp.const_mul (K ^ m * m.factorial)).mono'
    (hX.pow_const m).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    have he := Real.pow_div_factorial_le_exp
      (div_nonneg (abs_nonneg (X ω)) h.scale_pos.le) m
    have he' : (|X ω| / K) ^ m ≤
        (m.factorial : ℝ) * Real.exp (|X ω| / K) := by
      exact (div_le_iff₀ hfac).mp he |>.trans_eq (mul_comm _ _)
    have hid : |X ω| ^ m = K ^ m * (|X ω| / K) ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp [ne_of_gt h.scale_pos]
    rw [Real.norm_eq_abs, abs_pow, hid]
    exact (mul_le_mul_of_nonneg_left he' hKpow).trans_eq (by ring)

/-- The scalar tail bound follows from the actual exponential moment. -/
theorem ExponentialMomentBound.tail [IsFiniteMeasure μ]
    {X : Ω → ℝ} {K : ℝ} (h : ExponentialMomentBound μ X K) (u : ℝ) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-u / K) := by
  have hint : Integrable (fun ω => Real.exp (K⁻¹ * |X ω|)) μ := by
    simpa only [div_eq_mul_inv, mul_comm] using h.integrable_exp
  have htail := measure_ge_le_exp_mul_mgf (μ := μ)
    (X := fun ω => |X ω|) u (inv_nonneg.mpr h.scale_pos.le) hint
  have hmgf : mgf (fun ω => |X ω|) μ K⁻¹ ≤ 2 := by
    simpa only [mgf, div_eq_mul_inv, mul_comm] using h.integral_exp_le_two
  calc
    μ.real {ω | u ≤ |X ω|} ≤
        Real.exp (-K⁻¹ * u) * mgf (fun ω => |X ω|) μ K⁻¹ := htail
    _ ≤ Real.exp (-K⁻¹ * u) * 2 :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = 2 * Real.exp (-u / K) := by
      rw [show -K⁻¹ * u = -u / K by ring, mul_comm]

/-- A whole-vector truncation discards at most the sum of coordinate tails. -/
theorem vector_subexponential_tail [IsFiniteMeasure μ]
    {p : ℕ} {Y : Ω → Vector p} {K : ℝ}
    (h : ∀ j, ExponentialMomentBound μ (fun ω => Y ω j) K) (u : ℝ) :
    μ.real {ω | ∃ j, u ≤ |Y ω j|} ≤ (2 * p : ℝ) * Real.exp (-u / K) := by
  have hset : {ω | ∃ j, u ≤ |Y ω j|} = ⋃ j, {ω | u ≤ |Y ω j|} := by
    ext ω
    simp
  rw [hset]
  calc
    μ.real (⋃ j, {ω | u ≤ |Y ω j|}) ≤
        ∑ j : Fin p, μ.real {ω | u ≤ |Y ω j|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin p, 2 * Real.exp (-u / K) :=
      Finset.sum_le_sum fun j _ => (h j).tail u
    _ = (2 * p : ℝ) * Real.exp (-u / K) := by simp; ring

/-- The probability that any observation is discarded.  Independence is
not needed for this finite union estimate. -/
theorem observations_subexponential_tail [IsFiniteMeasure μ]
    {p n : ℕ} {Y : Fin n → Ω → Vector p} {K : ℝ}
    (h : ∀ i j, ExponentialMomentBound μ (fun ω => Y i ω j) K) (u : ℝ) :
    μ.real {ω | ∃ i j, u ≤ |Y i ω j|} ≤
      (2 * n * p : ℝ) * Real.exp (-u / K) := by
  have hset : {ω | ∃ i j, u ≤ |Y i ω j|} =
      ⋃ i, {ω | ∃ j, u ≤ |Y i ω j|} := by
    ext ω
    simp
  rw [hset]
  calc
    μ.real (⋃ i, {ω | ∃ j, u ≤ |Y i ω j|}) ≤
        ∑ i : Fin n, μ.real {ω | ∃ j, u ≤ |Y i ω j|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, (2 * p : ℝ) * Real.exp (-u / K) :=
      Finset.sum_le_sum fun i _ => vector_subexponential_tail (h i) u
    _ = (2 * n * p : ℝ) * Real.exp (-u / K) := by simp; ring

/-- The finite-product norm is the coordinate maximum, so the same bound
applies to the whole-observation discard event. -/
theorem observations_norm_subexponential_tail [IsFiniteMeasure μ]
    {p n : ℕ} {Y : Fin n → Ω → Vector p} {K u : ℝ} (hu : 0 ≤ u)
    (h : ∀ i j, ExponentialMomentBound μ (fun ω => Y i ω j) K) :
    μ.real {ω | ∃ i, u < ‖Y i ω‖} ≤
      (2 * n * p : ℝ) * Real.exp (-u / K) := by
  apply (measureReal_mono (μ := μ) (show
    {ω | ∃ i, u < ‖Y i ω‖} ⊆ {ω | ∃ i j, u ≤ |Y i ω j|} from ?_)).trans
      (observations_subexponential_tail h u)
  intro ω hω
  obtain ⟨i, hi⟩ := hω
  by_contra hnot
  push_neg at hnot
  have hcoord : ∀ j, ‖Y i ω j‖ ≤ u := fun j => by
    simpa only [Real.norm_eq_abs] using (hnot i j).le
  exact hi.not_ge ((pi_norm_le_iff_of_nonneg hu).mpr hcoord)

end

end RectangleCLT
