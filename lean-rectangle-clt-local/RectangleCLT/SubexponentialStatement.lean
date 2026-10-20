import RectangleCLT.LocalStatement
import RectangleCLT.SubexponentialTail

/-!
# Probability data and scales for the sub-exponential corollaries

The fourth-moment parameter `B4` and the exponential-tail parameter `K`
are independent inputs.  The fourth moments are averaged over the actual
observation laws, without any identical-distribution requirement.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

/-- The observation normalization in both sub-exponential corollaries. -/
def sampleNormalizedObservations {Ω : Type*} {p n : ℕ}
    (Y : Fin n → Ω → Vector p) : Fin n → Ω → Vector p :=
  fun i ω j => Y i ω j / Real.sqrt (n : ℝ)

/-- The truncation logarithm `H=log(enp)`. -/
def truncationLog (n p : ℕ) : ℝ := Real.log (Real.exp 1 * (n : ℝ) * (p : ℝ))

/-- The three-term sub-exponential rate, in the units used by the paper.
The covariance argument is the fixed original proxy. -/
def subexponentialRate {p : ℕ} (n : ℕ) (B4 K : ℝ)
    (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  B4 * dimensionLog p * Real.sqrt (dimensionLog p) /
      (pairGap Q * a3 Q * Real.sqrt (n : ℝ)) +
    B4 * dimensionLog p /
      (Real.rpow (pairGap Q) (5 / 6 : ℝ) *
        Real.rpow (a3 Q * a4 Q) (1 / 3 : ℝ) * Real.sqrt (n : ℝ)) +
    K * truncationLog n p * Real.sqrt (dimensionLog p) /
      (pairGap Q * Real.sqrt (n : ℝ))

/-- The substantive data of the standardized sub-exponential corollary.
There is no normal-approximation or truncation-output assumption here. -/
structure SubexponentialHypotheses {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (Y : Fin n → Ω → Vector p) (B4 K : ℝ) : Prop where
  dimension_pos : 1 ≤ p
  sample_size_pos : 1 ≤ n
  measurable : ∀ i, Measurable (Y i)
  independent : iIndepFun Y μ
  centered : ∀ i j, (∫ ω, Y i ω j ∂μ) = 0
  unit_diagonal : ∀ j, covariance μ (sumVector (sampleNormalizedObservations Y)) j j = 1
  fourth_scale_ge_one : 1 ≤ B4
  tail_scale_ge_one : 1 ≤ K
  fourth_moment_average : ∀ j, (∑ i, ∫ ω, |Y i ω j| ^ 4 ∂μ) / n ≤ B4 ^ 2
  psi_one_norm : ∀ i j, psiOneNorm μ (fun ω => Y i ω j) ≤ ENNReal.ofReal K

namespace SubexponentialHypotheses

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
  {Y : Fin n → Ω → Vector p} {B4 K : ℝ}

/-- Every actual coordinate has an admissible exponential scale at `2K`. -/
theorem exponential_moment (h : SubexponentialHypotheses μ Y B4 K)
    (i : Fin n) (j : Fin p) :
    ExponentialMomentBound μ (fun ω => Y i ω j) (2 * K) :=
  exponentialMomentBound_two_mul_of_psiOneNorm_le
    ((measurable_pi_apply j).comp (h.measurable i))
    (lt_of_lt_of_le (by norm_num) h.tail_scale_ge_one) (h.psi_one_norm i j)

/-- Moment integrability is derived from the tail assumption. -/
theorem integrable_coordinate_pow (h : SubexponentialHypotheses μ Y B4 K)
    (i : Fin n) (j : Fin p) (m : ℕ) :
    Integrable (fun ω => Y i ω j ^ m) μ :=
  (h.exponential_moment i j).integrable_pow
    ((measurable_pi_apply j).comp (h.measurable i)) m

/-- The paper's average fourth-moment condition in summed form. -/
theorem fourth_moment_sum (h : SubexponentialHypotheses μ Y B4 K)
    (j : Fin p) : (∑ i, ∫ ω, Y i ω j ^ 4 ∂μ) ≤ n * B4 ^ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h.sample_size_pos)
  have hfour := (div_le_iff₀ hn).mp (h.fourth_moment_average j)
  have heq (i : Fin n) : (fun ω => |Y i ω j| ^ 4) = (fun ω => Y i ω j ^ 4) := by
    funext ω
    exact (show Even 4 from by decide).pow_abs _
  simp_rw [heq] at hfour
  nlinarith only [hfour]

end SubexponentialHypotheses

end

end RectangleCLT
