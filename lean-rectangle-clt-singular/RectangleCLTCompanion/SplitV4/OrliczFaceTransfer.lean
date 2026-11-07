import RectangleCLTCompanion.SplitV4.GaussianFaceTransfer
import RectangleCLTCompanion.SubexponentialMain
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Sub-exponential polyhedral transfer

The genuine infimum-based Orlicz hypothesis gives exponential moments at
twice its scale. Finite Jensen then transfers those moments under the face
map without assuming any coordinate independence. Covariance congruence is
proved for the actual unbounded square-integrable normalized sum.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

/-- Finite Jensen with a leftover weight at zero. -/
theorem exp_projection_le_weighted_exp {p : ℕ} (a x : Vector p)
    (J H : ℝ) (hJ : 0 < J) (hH : 0 < H) (ha : (∑ j, |a j|) ≤ J) :
    Real.exp (|dotProduct a x| / (J * H)) ≤
      (1 - ∑ j, |a j| / J) + ∑ j, (|a j| / J) * Real.exp (|x j| / H) := by
  let w : Fin p → ℝ := fun j => |a j| / J
  have hw : ∀ j, 0 ≤ w j := fun j => div_nonneg (abs_nonneg _) hJ.le
  have hmass : (∑ j, w j) ≤ 1 := by
    calc
      (∑ j, w j) = (∑ j, |a j|) / J := by
        simp only [w, div_eq_mul_inv, Finset.sum_mul]
      _ ≤ 1 := (div_le_one hJ).mpr ha
  have hjensen := convexOn_exp.map_add_sum_le
    (t := Finset.univ) (w := w) (p := fun j => |x j| / H)
    (v := 1 - ∑ j, w j) (q := (0 : ℝ))
    (fun j _ => hw j) (by ring) (fun _ _ => Set.mem_univ _)
    (sub_nonneg.mpr hmass) (Set.mem_univ _)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hjensen
  have harg : |dotProduct a x| / (J * H) ≤ ∑ j, w j * (|x j| / H) := by
    have habs : |dotProduct a x| ≤ ∑ j, |a j| * |x j| := by
      simpa only [abs_mul] using
        Finset.abs_sum_le_sum_abs (fun j : Fin p => a j * x j) Finset.univ
    calc
      _ ≤ (∑ j, |a j| * |x j|) / (J * H) :=
        div_le_div_of_nonneg_right habs (mul_pos hJ hH).le
      _ = ∑ j, w j * (|x j| / H) := by
        simp only [w, div_eq_mul_inv, mul_inv_rev, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  exact (Real.exp_le_exp.mpr harg).trans hjensen

/-- Actual coordinate exponential moments survive a row-l1 bounded map.
Both genuine integrability and the expectation bound are retained. -/
theorem projected_exponential_moments
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {H : ℝ}
    (h : SubexponentialIndependentHypotheses μ X H)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 1 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (i : Fin n) (α : Fin m) :
    Integrable (fun ω => Real.exp (|M.mulVec (X i ω) α| / (J * H))) μ ∧
      (∫ ω, Real.exp (|M.mulVec (X i ω) α| / (J * H)) ∂μ) ≤ 2 := by
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hHp : 0 < H := zero_lt_one.trans_le h.one_le_scale
  let w : Fin p → ℝ := fun j => |M α j| / J
  let v : ℝ := 1 - ∑ j, w j
  let F : Ω → ℝ := fun ω => v + ∑ j, w j * Real.exp (|X i ω j| / H)
  have hw : ∀ j, 0 ≤ w j := fun j => div_nonneg (abs_nonneg _) hJp.le
  have hmass : (∑ j, w j) ≤ 1 := by
    calc
      (∑ j, w j) = (∑ j, |M α j|) / J := by
        simp only [w, div_eq_mul_inv, Finset.sum_mul]
      _ ≤ 1 := (div_le_one hJp).mpr (hM α)
  have hF : Integrable F μ :=
    (integrable_const v).add
      (integrable_finset_sum Finset.univ (fun j _ => (h.integrable_exp i j).const_mul (w j)))
  have hpoint (ω : Ω) : Real.exp (|M.mulVec (X i ω) α| / (J * H)) ≤ F ω :=
    exp_projection_le_weighted_exp (M α) (X i ω) J H hJp hHp (hM α)
  have hm : Measurable (fun ω => Real.exp (|M.mulVec (X i ω) α| / (J * H))) :=
    (((measurable_pi_apply α).comp
      ((measurable_rectangular_mulVec M).comp (h.measurable i))).abs.div_const _).exp
  have hi : Integrable (fun ω => Real.exp (|M.mulVec (X i ω) α| / (J * H))) μ :=
    hF.mono' hm.aestronglyMeasurable (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint ω)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, F ω ∂μ := integral_mono hi hF hpoint
    _ = v + ∑ j, w j * ∫ ω, Real.exp (|X i ω j| / H) ∂μ := by
      rw [integral_add (integrable_const v)
        (integrable_finset_sum Finset.univ (fun j _ => (h.integrable_exp i j).const_mul (w j)))]
      rw [integral_finset_sum Finset.univ (fun j _ => (h.integrable_exp i j).const_mul (w j))]
      simp only [integral_const, measureReal_univ_eq_one, one_smul, integral_const_mul]
    _ ≤ v + ∑ j, w j * 2 := add_le_add_left
      (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h.exponential_moment i j) (hw j)) v
    _ = 1 + ∑ j, w j := by rw [← Finset.sum_mul]; dsimp [v]; ring
    _ ≤ 2 := by linarith

theorem subexponentialIndependent_projected
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {H : ℝ}
    (h : SubexponentialIndependentHypotheses μ X H)
    (M : Matrix (Fin m) (Fin p) ℝ) (J : ℝ) (hJ : 1 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) :
    SubexponentialIndependentHypotheses μ (fun i ω => M.mulVec (X i ω)) (J * H) := by
  have hmeas := measurable_rectangular_mulVec M
  refine ⟨fun i => hmeas.comp (h.measurable i),
    h.independent.comp (fun _ => M.mulVec) (fun _ => hmeas), ?_,
    fun i α => (projected_exponential_moments h M J hJ hM i α).1,
    fun i α => (projected_exponential_moments h M J hJ hM i α).2,
    one_le_mul_of_one_le_of_one_le hJ h.one_le_scale⟩
  intro i α
  unfold Matrix.mulVec dotProduct
  rw [integral_finset_sum Finset.univ (fun j _ =>
    ((h.coordinate_exponentialMomentBound i j).integrable).const_mul _)]
  simp only [integral_const_mul, h.centered, mul_zero, Finset.sum_const_zero]

/-- Exact covariance congruence for an actual centered square-integrable
random vector. This lemma does not assume that the vector is bounded. -/
theorem covariance_mulVec_of_centered_memLp
    {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (M : Matrix (Fin m) (Fin p) ℝ)
    (hLp : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hc : ∀ j, (∫ ω, W ω j ∂μ) = 0) :
    covariance μ (fun ω => M.mulVec (W ω)) = M * covariance μ W * M.transpose := by
  have hm (α : Fin m) : (∫ ω, M.mulVec (W ω) α ∂μ) = 0 := by
    unfold Matrix.mulVec dotProduct
    rw [integral_finset_sum Finset.univ (fun j _ =>
      ((hLp j).integrable (by norm_num)).const_mul _)]
    simp only [integral_const_mul, hc, mul_zero, Finset.sum_const_zero]
  have hp (α β : Fin m) :
      (∫ ω, M.mulVec (W ω) α * M.mulVec (W ω) β ∂μ) =
        ∑ j, ∑ k, M α j * (∫ ω, W ω j * W ω k ∂μ) * M β k := by
    have he (ω : Ω) : M.mulVec (W ω) α * M.mulVec (W ω) β =
        ∑ j, ∑ k, M α j * (W ω j * W ω k) * M β k := by
      simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    have hint (j k : Fin p) :
        Integrable (fun ω => M α j * (W ω j * W ω k) * M β k) μ :=
      (((hLp j).integrable_mul (hLp k)).const_mul (M α j)).mul_const (M β k)
    rw [integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ => hint j k))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum Finset.univ (fun k _ => hint j k)]
    simp only [integral_mul_const, integral_const_mul]
  ext α β
  simp only [covariance, hm, hc, mul_zero, sub_zero, hp,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem normalizedObservationSum_mulVec
    {Ω : Type*} {p m n : ℕ} (M : Matrix (Fin m) (Fin p) ℝ)
    (X : Fin n → Ω → Vector p) :
    normalizedObservationSum (fun i ω => M.mulVec (X i ω)) =
      fun ω => M.mulVec (normalizedObservationSum X ω) := by
  funext ω
  simp only [normalizedObservationSum, sumVector_mulVec, Matrix.mulVec_smul]

theorem subexponential_projected_covariance
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {H : ℝ}
    (h : SubexponentialIndependentHypotheses μ X H)
    (M : Matrix (Fin m) (Fin p) ℝ) :
    covariance μ (normalizedObservationSum (fun i ω => M.mulVec (X i ω))) =
      M * covariance μ (normalizedObservationSum X) * M.transpose := by
  rw [normalizedObservationSum_mulVec]
  exact covariance_mulVec_of_centered_memLp μ _ M
    (normalizedObservationSum_coordinate_memLp_two h)
    (normalizedObservationSum_coordinate_centered h)

/-- The genuine Orlicz polyhedral transfer, for the actual supremum over
thresholds and the original Gaussian law. All rate quantities are recomputed
at `J*K`; the universal constant absorbs the Orlicz-to-exponential factor two. -/
theorem orliczPolyhedralCLT
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : 1 ≤ m) (hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) (K : ℝ)
    (h : Psi1IndependentHypotheses μ X K)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 1 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J * σ α)
    (hvariance : ∀ α, dotProduct (ν α)
      ((covariance μ (normalizedObservationSum X)).mulVec (ν α)) = (σ α) ^ 2) :
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤
      (2 * subexponentialUniversalConstant) *
        min 1 (unrestrictedRate (subexponentialScale n (J * K)) (dimensionLog m)) := by
  let M := standardizedFaceMap ν σ
  have hM : ∀ α, (∑ j, |M α j|) ≤ J := standardizedFaceMap_row_l1_le ν σ J hσ hν
  let Y : Fin n → Ω → Vector m := fun i ω => M.mulVec (X i ω)
  have he := h.exponentialHypotheses
  have hY : SubexponentialIndependentHypotheses μ Y (J * (2 * K)) :=
    subexponentialIndependent_projected he M J hJ hM
  have hcov : covariance μ (normalizedObservationSum Y) =
      M * covariance μ (normalizedObservationSum X) * M.transpose :=
    subexponential_projected_covariance he M
  have hunit : ∀ α, covariance μ (normalizedObservationSum Y) α α = 1 := by
    intro α
    rw [hcov]
    exact standardizedFaceMap_covariance_unit_diagonal ν σ _ hσ hvariance α
  obtain ⟨C, hC⟩ := gaussian_factor_exists_of_subexponential hY
  have hgram : C * C.transpose = M * (A * A.transpose) * M.transpose := by
    simpa only [hA] using hC.trans hcov
  have hd := polyhedralDistance_le_projected_rectangleDistance
    μ (normalizedObservationSum X) A C ν σ hσ hgram
  have hsum : normalizedObservationSum Y =
      fun ω => M.mulVec (normalizedObservationSum X ω) := normalizedObservationSum_mulVec M X
  change polyhedralDistance μ (normalizedObservationSum X) A ν ≤
    rectangleDistance μ (fun ω => M.mulVec (normalizedObservationSum X ω)) C at hd
  rw [← hsum] at hd
  apply hd.trans
  apply rectangleDistance_le
  intro R
  have hh := subexponentialCLT μ m n hm hn Y (J * (2 * K)) C hY hunit hC R
  rw [show J * (2 * K) = 2 * (J * K) by ring, subexponentialScale_mul] at hh
  have hscale := min_one_unrestrictedRate_mul_le (by norm_num : (1 : ℝ) ≤ 2)
    (subexponentialScale_pos hn (one_le_mul_of_one_le_of_one_le hJ h.one_le_scale))
    (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hm))
  have hCpos := zero_le_one.trans one_le_subexponentialUniversalConstant
  exact (hh.trans (mul_le_mul_of_nonneg_left hscale hCpos)).trans_eq (by
    dsimp only [dimensionLog]
    ring)

end

end RectangleCLT.Companion.SplitV4
