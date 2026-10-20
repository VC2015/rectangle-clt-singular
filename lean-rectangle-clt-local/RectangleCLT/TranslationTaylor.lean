import RectangleCLT.SmootherConvolution
import Mathlib.Analysis.Calculus.Taylor

/-! Actual derivatives and Taylor expansions along translations of the
rational rectangle smoother. All derivative tensors below are the iterated
ordinary derivatives already identified by checked derivative witnesses. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

/-- Coordinate derivative witnesses for a differentiable finite-product
function determine its derivative along every affine line. -/
theorem hasDerivAt_line_of_coordinate_derivatives {p : ℕ}
    (G : (Fin p → ℝ) → ℝ) (D : (Fin p → ℝ) → Fin p → ℝ)
    (hG : Differentiable ℝ G)
    (hD : ∀ x j, HasDerivAt
      (fun t => G (FaceSmoother.line x (FaceSmoother.coordinateDirection j) t))
      (D x j) 0)
    (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => G (FaceSmoother.line x y r))
      (∑ j, D (FaceSmoother.line x y t) j * y j) t := by
  have hline (a b : Fin p → ℝ) (r : ℝ) :
      HasDerivAt (FaceSmoother.line a b) b r := by
    change HasDerivAt (fun r => a + r • b) b r
    simpa only [one_smul] using ((hasDerivAt_id r).smul_const b).const_add a
  have hcoord (a : Fin p → ℝ) (j : Fin p) :
      (fderiv ℝ G a) (FaceSmoother.coordinateDirection j) = D a j := by
    have hd := (hG (FaceSmoother.line a (FaceSmoother.coordinateDirection j) 0)).hasFDerivAt.comp_hasDerivAt 0
      (hline a (FaceSmoother.coordinateDirection j) 0)
    simpa only [FaceSmoother.line_zero] using hd.unique (hD a j)
  have hy : y = ∑ j, y j • FaceSmoother.coordinateDirection j := by
    funext k
    simp [FaceSmoother.coordinateDirection, Finset.sum_apply, eq_comm]
  have hsum : (fderiv ℝ G (FaceSmoother.line x y t)) y =
      ∑ j, D (FaceSmoother.line x y t) j * y j := by
    calc
      _ = (fderiv ℝ G (FaceSmoother.line x y t))
          (∑ j, y j • FaceSmoother.coordinateDirection j) := congrArg _ hy
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, hcoord, mul_comm]
  simpa only [hsum] using (hG _).hasFDerivAt.comp_hasDerivAt t (hline x y t)


/-- On a uniquely differentiable set, global smoothness identifies the actual
within and unrestricted iterated scalar derivatives. -/
theorem iteratedDerivWithin_eq_of_contDiff {f : ℝ → ℝ} {n : ℕ}
    {S : Set ℝ} {x : ℝ} (hS : UniqueDiffOn ℝ S)
    (hf : ContDiff ℝ n f) (hx : x ∈ S) :
    iteratedDerivWithin n f S x = iteratedDeriv n f x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedDeriv_eq_iteratedFDeriv,
    iteratedFDerivWithin_eq_iteratedFDeriv hS hf.contDiffAt hx]

/-- The ordinary degree-three Taylor theorem on the unit interval, with an
actual fourth iterated derivative as its Lagrange remainder. -/
theorem taylor3_mean_remainder {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      f 1 - (f 0 + iteratedDeriv 1 f 0 + iteratedDeriv 2 f 0 / 2 +
        iteratedDeriv 3 f 0 / 6) = iteratedDeriv 4 f t / 24 := by
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have heq (n : ℕ) (hn : n ≤ 4) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin n f (Set.Icc (0 : ℝ) 1) x = iteratedDeriv n f x :=
    iteratedDerivWithin_eq_of_contDiff huniq (hf.of_le (by exact_mod_cast hn)) hx
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 3 f (Set.Icc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) := by
    apply ((hf.differentiable_iteratedDeriv 3 (by exact_mod_cast (show (3 : ℕ) < 4 by decide))).differentiableOn).congr
    intro t ht
    exact heq 3 (by omega) t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange
    (n := 3) (by norm_num : (0 : ℝ) < 1) (hf.of_le (by exact_mod_cast (show (3 : ℕ) ≤ 4 by decide))).contDiffOn hdiff
  refine ⟨t, ht, ?_⟩
  have htaylor : taylorWithinEval f 3 (Set.Icc (0 : ℝ) 1) 0 1 =
      f 0 + iteratedDeriv 1 f 0 + iteratedDeriv 2 f 0 / 2 +
        iteratedDeriv 3 f 0 / 6 := by
    simp only [taylor_within_apply]
    norm_num [Finset.sum_range_succ, taylorCoeffWithin, heq, iteratedDeriv_zero, Nat.factorial]
    ring
  rw [htaylor, heq 4 (by omega) t ⟨ht.1.le, ht.2.le⟩] at hrem
  simpa only [sub_zero, one_pow, mul_one, show (Nat.factorial 4 : ℝ) = 24 by norm_num [Nat.factorial], iteratedDeriv_one] using hrem


theorem taylor2_mean_remainder {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      f 1 - (f 0 + iteratedDeriv 1 f 0 + iteratedDeriv 2 f 0 / 2) =
        iteratedDeriv 3 f t / 6 := by
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have heq (n : ℕ) (hn : n ≤ 3) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin n f (Set.Icc (0 : ℝ) 1) x = iteratedDeriv n f x :=
    iteratedDerivWithin_eq_of_contDiff huniq (hf.of_le (by exact_mod_cast hn)) hx
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 2 f (Set.Icc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) := by
    apply ((hf.differentiable_iteratedDeriv 2 (by exact_mod_cast
      (show (2 : ℕ) < 3 by decide))).differentiableOn).congr
    intro t ht
    exact heq 2 (by omega) t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange
    (n := 2) (by norm_num : (0 : ℝ) < 1)
    (hf.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))).contDiffOn hdiff
  refine ⟨t, ht, ?_⟩
  have htaylor : taylorWithinEval f 2 (Set.Icc (0 : ℝ) 1) 0 1 =
      f 0 + iteratedDeriv 1 f 0 + iteratedDeriv 2 f 0 / 2 := by
    simp only [taylor_within_apply]
    norm_num [Finset.sum_range_succ, taylorCoeffWithin, heq, iteratedDeriv_zero, Nat.factorial]
    ring
  rw [htaylor, heq 3 (by omega) t ⟨ht.1.le, ht.2.le⟩] at hrem
  simpa only [sub_zero, one_pow, mul_one, show (Nat.factorial 3 : ℝ) = 6 by norm_num [Nat.factorial], iteratedDeriv_one] using hrem

theorem taylor0_mean_remainder {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      f 1 - (f 0) = iteratedDeriv 1 f t := by
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have heq (k : ℕ) (hk : k ≤ 1) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) x = iteratedDeriv k f x :=
    iteratedDerivWithin_eq_of_contDiff huniq (hf.of_le (by exact_mod_cast hk)) hx
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 0 f (Set.Icc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) := by
    apply ((hf.differentiable_iteratedDeriv 0 (by exact_mod_cast (show (0 : ℕ) < 1 by decide))).differentiableOn).congr
    intro t ht
    exact heq 0 (by omega) t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange
    (n := 0) (by norm_num : (0 : ℝ) < 1)
    (hf.of_le (by exact_mod_cast (show (0 : ℕ) ≤ 1 by decide))).contDiffOn hdiff
  refine ⟨t, ht, ?_⟩
  have htaylor : taylorWithinEval f 0 (Set.Icc (0 : ℝ) 1) 0 1 = f 0 := by
    simp only [taylor_within_apply]
    norm_num [Finset.sum_range_succ, taylorCoeffWithin, heq, iteratedDeriv_zero, Nat.factorial]
  rw [htaylor, heq 1 (by omega) t ⟨ht.1.le, ht.2.le⟩] at hrem
  simpa only [sub_zero, one_pow, mul_one, Nat.factorial, Nat.cast_one, Nat.cast_mul, div_one, iteratedDeriv_one] using hrem

theorem taylor1_mean_remainder {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      f 1 - (f 0 + iteratedDeriv 1 f 0) = iteratedDeriv 2 f t / 2 := by
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have heq (k : ℕ) (hk : k ≤ 2) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) x = iteratedDeriv k f x :=
    iteratedDerivWithin_eq_of_contDiff huniq (hf.of_le (by exact_mod_cast hk)) hx
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 1 f (Set.Icc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) := by
    apply ((hf.differentiable_iteratedDeriv 1 (by exact_mod_cast (show (1 : ℕ) < 2 by decide))).differentiableOn).congr
    intro t ht
    exact heq 1 (by omega) t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange
    (n := 1) (by norm_num : (0 : ℝ) < 1)
    (hf.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by decide))).contDiffOn hdiff
  refine ⟨t, ht, ?_⟩
  have htaylor : taylorWithinEval f 1 (Set.Icc (0 : ℝ) 1) 0 1 = f 0 + iteratedDeriv 1 f 0 := by
    simp only [taylor_within_apply]
    norm_num [Finset.sum_range_succ, taylorCoeffWithin, heq, iteratedDeriv_zero, Nat.factorial]
  rw [htaylor, heq 2 (by omega) t ⟨ht.1.le, ht.2.le⟩] at hrem
  simpa only [sub_zero, one_pow, mul_one, Nat.factorial, Nat.cast_one, Nat.cast_mul, div_one, iteratedDeriv_one] using hrem

theorem taylor0_of_derivative_chain (f0 f1 : ℝ → ℝ)
    (h0 : ∀ t, HasDerivAt f0 (f1 t) t)
    : ∃ t ∈ Set.Ioo (0 : ℝ) 1, f0 1 - (f0 0) = f1 t / 1 := by
  have hd (m : ℕ) (hm : m ≤ 0) : Differentiable ℝ (iteratedDeriv m f0) := by
    interval_cases m
    · simpa only [iteratedDeriv_zero] using (fun t => (h0 t).differentiableAt)
  have hf : ContDiff ℝ 0 f0 := contDiff_nat_iff_iteratedDeriv.mpr
    ⟨fun m hm => (hd m hm).continuous, fun m hm => hd m hm.le⟩
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have heq (m : ℕ) (hm : m ≤ 0) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin m f0 (Set.Icc (0 : ℝ) 1) u = iteratedDeriv m f0 u :=
    iteratedDerivWithin_eq_of_contDiff huniq (hf.of_le (by exact_mod_cast hm)) hu
  have ewithin (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin 0 f0 (Set.Icc (0 : ℝ) 1) u = f0 u := by
    rw [heq 0 (by omega) u hu, iteratedDeriv_zero]
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 0 f0 (Set.Icc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) := by
    apply DifferentiableOn.congr (Differentiable.differentiableOn
      (show Differentiable ℝ f0 from fun t => (h0 t).differentiableAt))
    intro t ht
    exact ewithin t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange
    (n := 0) (by norm_num : (0 : ℝ) < 1) hf.contDiffOn hdiff
  refine ⟨t, ht, ?_⟩
  have elast : iteratedDerivWithin 1 f0 (Set.Icc (0 : ℝ) 1) t = f1 t := by
    rw [show 1 = 0 + 1 by rfl, iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun u hu => ewithin u hu) (ewithin t ⟨ht.1.le, ht.2.le⟩)]
    exact (h0 t).hasDerivWithinAt.derivWithin (huniq t ⟨ht.1.le, ht.2.le⟩)
  have htaylor : taylorWithinEval f0 0 (Set.Icc (0 : ℝ) 1) 0 1 = f0 0 := by
    simp only [taylor_within_apply]
    norm_num [Finset.sum_range_succ, taylorCoeffWithin, heq, iteratedDeriv_zero, Nat.factorial]
  rw [htaylor, elast] at hrem
  simpa only [sub_zero, one_pow, mul_one, show (Nat.factorial 1 : ℝ) = 1 by norm_num [Nat.factorial]] using hrem

theorem taylor1_of_derivative_chain (f0 f1 f2 : ℝ → ℝ)
    (h0 : ∀ t, HasDerivAt f0 (f1 t) t)
    (h1 : ∀ t, HasDerivAt f1 (f2 t) t)
    : ∃ t ∈ Set.Ioo (0 : ℝ) 1, f0 1 - (f0 0 + f1 0) = f2 t / 2 := by
  have e1 : iteratedDeriv 1 f0 = f1 := by
    rw [iteratedDeriv_one]
    funext t
    exact (h0 t).deriv
  have hd (m : ℕ) (hm : m ≤ 1) : Differentiable ℝ (iteratedDeriv m f0) := by
    interval_cases m
    · simpa only [iteratedDeriv_zero] using (fun t => (h0 t).differentiableAt)
    · simpa only [e1] using (fun t => (h1 t).differentiableAt)
  have hf : ContDiff ℝ 1 f0 := contDiff_nat_iff_iteratedDeriv.mpr
    ⟨fun m hm => (hd m hm).continuous, fun m hm => hd m hm.le⟩
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have heq (m : ℕ) (hm : m ≤ 1) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin m f0 (Set.Icc (0 : ℝ) 1) u = iteratedDeriv m f0 u :=
    iteratedDerivWithin_eq_of_contDiff huniq (hf.of_le (by exact_mod_cast hm)) hu
  have ewithin (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin 1 f0 (Set.Icc (0 : ℝ) 1) u = f1 u := by
    rw [heq 1 (by omega) u hu, e1]
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 1 f0 (Set.Icc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) := by
    apply DifferentiableOn.congr (Differentiable.differentiableOn
      (show Differentiable ℝ f1 from fun t => (h1 t).differentiableAt))
    intro t ht
    exact ewithin t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange
    (n := 1) (by norm_num : (0 : ℝ) < 1) hf.contDiffOn hdiff
  refine ⟨t, ht, ?_⟩
  have elast : iteratedDerivWithin 2 f0 (Set.Icc (0 : ℝ) 1) t = f2 t := by
    rw [show 2 = 1 + 1 by rfl, iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun u hu => ewithin u hu) (ewithin t ⟨ht.1.le, ht.2.le⟩)]
    exact (h1 t).hasDerivWithinAt.derivWithin (huniq t ⟨ht.1.le, ht.2.le⟩)
  have htaylor : taylorWithinEval f0 1 (Set.Icc (0 : ℝ) 1) 0 1 = f0 0 + f1 0 := by
    simp only [taylor_within_apply]
    norm_num [Finset.sum_range_succ, taylorCoeffWithin, heq, iteratedDeriv_zero, Nat.factorial, e1]
  rw [htaylor, elast] at hrem
  simpa only [sub_zero, one_pow, mul_one, show (Nat.factorial 2 : ℝ) = 2 by norm_num [Nat.factorial]] using hrem

theorem taylor2_of_derivative_chain (f0 f1 f2 f3 : ℝ → ℝ)
    (h0 : ∀ t, HasDerivAt f0 (f1 t) t)
    (h1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (h2 : ∀ t, HasDerivAt f2 (f3 t) t)
    : ∃ t ∈ Set.Ioo (0 : ℝ) 1, f0 1 - (f0 0 + f1 0 + f2 0 / 2) = f3 t / 6 := by
  have e1 : iteratedDeriv 1 f0 = f1 := by
    rw [iteratedDeriv_one]
    funext t
    exact (h0 t).deriv
  have e2 : iteratedDeriv 2 f0 = f2 := by
    rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, e1]
    funext t
    exact (h1 t).deriv
  have hd (m : ℕ) (hm : m ≤ 2) : Differentiable ℝ (iteratedDeriv m f0) := by
    interval_cases m
    · simpa only [iteratedDeriv_zero] using (fun t => (h0 t).differentiableAt)
    · simpa only [e1] using (fun t => (h1 t).differentiableAt)
    · simpa only [e2] using (fun t => (h2 t).differentiableAt)
  have hf : ContDiff ℝ 2 f0 := contDiff_nat_iff_iteratedDeriv.mpr
    ⟨fun m hm => (hd m hm).continuous, fun m hm => hd m hm.le⟩
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have heq (m : ℕ) (hm : m ≤ 2) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin m f0 (Set.Icc (0 : ℝ) 1) u = iteratedDeriv m f0 u :=
    iteratedDerivWithin_eq_of_contDiff huniq (hf.of_le (by exact_mod_cast hm)) hu
  have ewithin (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin 2 f0 (Set.Icc (0 : ℝ) 1) u = f2 u := by
    rw [heq 2 (by omega) u hu, e2]
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 2 f0 (Set.Icc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) := by
    apply DifferentiableOn.congr (Differentiable.differentiableOn
      (show Differentiable ℝ f2 from fun t => (h2 t).differentiableAt))
    intro t ht
    exact ewithin t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange
    (n := 2) (by norm_num : (0 : ℝ) < 1) hf.contDiffOn hdiff
  refine ⟨t, ht, ?_⟩
  have elast : iteratedDerivWithin 3 f0 (Set.Icc (0 : ℝ) 1) t = f3 t := by
    rw [show 3 = 2 + 1 by rfl, iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun u hu => ewithin u hu) (ewithin t ⟨ht.1.le, ht.2.le⟩)]
    exact (h2 t).hasDerivWithinAt.derivWithin (huniq t ⟨ht.1.le, ht.2.le⟩)
  have htaylor : taylorWithinEval f0 2 (Set.Icc (0 : ℝ) 1) 0 1 = f0 0 + f1 0 + f2 0 / 2 := by
    simp only [taylor_within_apply]
    norm_num [Finset.sum_range_succ, taylorCoeffWithin, heq, iteratedDeriv_zero, Nat.factorial, e1, e2]
    ring
  rw [htaylor, elast] at hrem
  simpa only [sub_zero, one_pow, mul_one, show (Nat.factorial 3 : ℝ) = 6 by norm_num [Nat.factorial]] using hrem

theorem taylor3_of_derivative_chain (f0 f1 f2 f3 f4 : ℝ → ℝ)
    (h0 : ∀ t, HasDerivAt f0 (f1 t) t)
    (h1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (h2 : ∀ t, HasDerivAt f2 (f3 t) t)
    (h3 : ∀ t, HasDerivAt f3 (f4 t) t)
    : ∃ t ∈ Set.Ioo (0 : ℝ) 1, f0 1 - (f0 0 + f1 0 + f2 0 / 2 + f3 0 / 6) = f4 t / 24 := by
  have e1 : iteratedDeriv 1 f0 = f1 := by
    rw [iteratedDeriv_one]
    funext t
    exact (h0 t).deriv
  have e2 : iteratedDeriv 2 f0 = f2 := by
    rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, e1]
    funext t
    exact (h1 t).deriv
  have e3 : iteratedDeriv 3 f0 = f3 := by
    rw [show 3 = 2 + 1 by rfl, iteratedDeriv_succ, e2]
    funext t
    exact (h2 t).deriv
  have hd (m : ℕ) (hm : m ≤ 3) : Differentiable ℝ (iteratedDeriv m f0) := by
    interval_cases m
    · simpa only [iteratedDeriv_zero] using (fun t => (h0 t).differentiableAt)
    · simpa only [e1] using (fun t => (h1 t).differentiableAt)
    · simpa only [e2] using (fun t => (h2 t).differentiableAt)
    · simpa only [e3] using (fun t => (h3 t).differentiableAt)
  have hf : ContDiff ℝ 3 f0 := contDiff_nat_iff_iteratedDeriv.mpr
    ⟨fun m hm => (hd m hm).continuous, fun m hm => hd m hm.le⟩
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have heq (m : ℕ) (hm : m ≤ 3) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin m f0 (Set.Icc (0 : ℝ) 1) u = iteratedDeriv m f0 u :=
    iteratedDerivWithin_eq_of_contDiff huniq (hf.of_le (by exact_mod_cast hm)) hu
  have ewithin (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin 3 f0 (Set.Icc (0 : ℝ) 1) u = f3 u := by
    rw [heq 3 (by omega) u hu, e3]
  have hdiff : DifferentiableOn ℝ
      (iteratedDerivWithin 3 f0 (Set.Icc (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) := by
    apply DifferentiableOn.congr (Differentiable.differentiableOn
      (show Differentiable ℝ f3 from fun t => (h3 t).differentiableAt))
    intro t ht
    exact ewithin t ⟨ht.1.le, ht.2.le⟩
  obtain ⟨t, ht, hrem⟩ := taylor_mean_remainder_lagrange
    (n := 3) (by norm_num : (0 : ℝ) < 1) hf.contDiffOn hdiff
  refine ⟨t, ht, ?_⟩
  have elast : iteratedDerivWithin 4 f0 (Set.Icc (0 : ℝ) 1) t = f4 t := by
    rw [show 4 = 3 + 1 by rfl, iteratedDerivWithin_succ]
    rw [derivWithin_congr (fun u hu => ewithin u hu) (ewithin t ⟨ht.1.le, ht.2.le⟩)]
    exact (h3 t).hasDerivWithinAt.derivWithin (huniq t ⟨ht.1.le, ht.2.le⟩)
  have htaylor : taylorWithinEval f0 3 (Set.Icc (0 : ℝ) 1) 0 1 = f0 0 + f1 0 + f2 0 / 2 + f3 0 / 6 := by
    simp only [taylor_within_apply]
    norm_num [Finset.sum_range_succ, taylorCoeffWithin, heq, iteratedDeriv_zero, Nat.factorial, e1, e2, e3]
    ring
  rw [htaylor, elast] at hrem
  simpa only [sub_zero, one_pow, mul_one, show (Nat.factorial 4 : ℝ) = 24 by norm_num [Nat.factorial]] using hrem

/-- Integrating a genuine finite weighted remainder preserves its coordinate
weights, rather than replacing them by a maximum norm moment. -/
theorem abs_integral_sub_le_finite_sum {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι] (μ : Measure Ω)
    (A B : Ω → ℝ) (H : ι → Ω → ℝ) (w : ι → ℝ)
    (hA : Integrable A μ) (hB : Integrable B μ)
    (hH : ∀ i, Integrable (H i) μ)
    (hpoint : ∀ z, |A z - B z| ≤ ∑ i, H i z * w i) :
    |(∫ z, A z ∂μ) - ∫ z, B z ∂μ| ≤ ∑ i, (∫ z, H i z ∂μ) * w i := by
  rw [← integral_sub hA hB, ← Real.norm_eq_abs]
  have hi : Integrable (fun z => ∑ i, H i z * w i) μ :=
    integrable_finset_sum Finset.univ (fun i _ => (hH i).mul_const (w i))
  calc
    _ ≤ ∫ z, ‖A z - B z‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ∑ i, H i z * w i ∂μ := integral_mono_ae
      ((hA.sub hB).norm) hi (ae_of_all μ (fun z => by
        simpa only [Real.norm_eq_abs] using hpoint z))
    _ = _ := by
      rw [integral_finset_sum Finset.univ (fun i _ => (hH i).mul_const (w i))]
      simp only [integral_mul_const]


/-- Dominated differentiation along an arbitrary translation, for concrete
bounded derivative kernels against a probability shift law. -/
theorem hasDerivAt_shiftIntegral_line_translation {p : ℕ}
    (ν : Measure (Fin p → ℝ)) [IsProbabilityMeasure ν]
    (G D : (Fin p → ℝ) → ℝ) (y : Fin p → ℝ) (C : ℝ)
    (hG : Continuous G) (hD : Continuous D)
    (hiG : ∀ x, Integrable (fun z => G (x + z)) ν)
    (hb : ∀ x, ‖D x‖ ≤ C)
    (hd : ∀ x t, HasDerivAt (fun r => G (FaceSmoother.line x y r))
      (D (FaceSmoother.line x y t)) t)
    (x : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => shiftIntegral ν G (FaceSmoother.line x y r))
      (shiftIntegral ν D (FaceSmoother.line x y t)) t := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (bound := fun _ => C) (ε := 1)
    (F := fun r z => G (FaceSmoother.line x y r + z))
    (F' := fun r z => D (FaceSmoother.line x y r + z))
    (x₀ := t) (by norm_num)
    (Filter.Eventually.of_forall (fun r =>
      (hG.comp (continuous_const.add continuous_id)).aestronglyMeasurable))
    (hiG (FaceSmoother.line x y t))
    ((hD.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (ae_of_all ν (fun z r _ => hb _)) (integrable_const C)
    (ae_of_all ν (fun z r _ => by
      simpa only [FaceSmoother.line_add_shift] using hd (x + z) r))
  exact h.2


theorem abs_finite_weighted_sum_le {ι : Type*} [Fintype ι]
    (g w C : ι → ℝ) (hb : ∀ i, |g i| ≤ C i) :
    |∑ i, g i * w i| ≤ ∑ i, C i * |w i| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hb i) (abs_nonneg _)

theorem shiftIntegral_finite_weighted_sum {p : ℕ} {ι : Type*} [Fintype ι]
    (ν : Measure (Fin p → ℝ)) (G : ι → (Fin p → ℝ) → ℝ) (w : ι → ℝ)
    (x : Fin p → ℝ) (hi : ∀ i, Integrable (fun z => G i (x + z)) ν) :
    shiftIntegral ν (fun q => ∑ i, G i q * w i) x =
      ∑ i, shiftIntegral ν (G i) x * w i := by
  unfold shiftIntegral
  rw [integral_finset_sum Finset.univ (fun i _ => (hi i).mul_const (w i))]
  simp only [integral_mul_const]

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem contDiff_normalDot_translation (f : Face p) :
    ContDiff ℝ ⊤ (normalDot f) := by
  change ContDiff ℝ ⊤ (fun x : Fin p → ℝ => if f.2 then x f.1 else -x f.1)
  cases hf : f.2
  · simpa only [hf, Bool.false_eq_true, ↓reduceIte] using (contDiff_apply ℝ ℝ f.1).neg
  · simpa only [hf, ↓reduceIte] using (contDiff_apply ℝ ℝ f.1)

theorem contDiff_weight_translation (f : Face p) :
    ContDiff ℝ ⊤ (fun x => (s.weights x).weight f) := by
  by_cases hf : f ∈ s.faces
  · simpa only [weights, hf, ↓reduceIte, faceScore] using
      (((contDiff_normalDot_translation f).sub contDiff_const).div_const s.bandwidth).exp
  · simpa only [weights, hf, ↓reduceIte] using
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : Fin p → ℝ => (0 : ℝ)))

theorem contDiff_T_translation :
    ContDiff ℝ ⊤ (fun x => (s.weights x).T) := by
  unfold FaceWeights.T
  exact ContDiff.sum (fun f _ => s.contDiff_weight_translation f)

theorem contDiff_F_translation : ContDiff ℝ ⊤ s.F :=
  contDiff_const.div (contDiff_const.add s.contDiff_T_translation)
    (fun x => ne_of_gt (s.weights x).denominator_pos)

theorem contDiff_pi_translation (f : Face p) :
    ContDiff ℝ ⊤ (fun x => (s.weights x).pi f) :=
  (s.contDiff_weight_translation f).div (contDiff_const.add s.contDiff_T_translation)
    (fun x => ne_of_gt (s.weights x).denominator_pos)

theorem contDiff_v_translation (j : Fin p) :
    ContDiff ℝ ⊤ (fun x => (s.weights x).v j) :=
  (s.contDiff_pi_translation (j, true)).sub (s.contDiff_pi_translation (j, false))

theorem contDiff_coordinateMass_translation (j : Fin p) :
    ContDiff ℝ ⊤ (fun x => (s.weights x).coordinateMass j) :=
  (s.contDiff_pi_translation (j, true)).add (s.contDiff_pi_translation (j, false))

theorem contDiff_diagonalMass_translation (j k : Fin p) :
    ContDiff ℝ ⊤ (fun x => (s.weights x).diagonalMass j k) := by
  unfold FaceWeights.diagonalMass
  split_ifs
  · exact s.contDiff_coordinateMass_translation j
  · exact contDiff_const

theorem contDiff_firstDerivative_translation (j : Fin p) :
    ContDiff ℝ ⊤ (fun x => s.coordinateDerivativeF x j) := by
  simp_rw [s.coordinateDerivativeF_eq]
  exact ((s.contDiff_F_translation.div_const _).neg).mul (s.contDiff_v_translation j)

theorem contDiff_secondDerivative_translation (j k : Fin p) :
    ContDiff ℝ ⊤ (fun x => s.mixedSecondDerivativeF x j k) := by
  simp_rw [s.mixedSecondDerivativeF_eq]
  exact (s.contDiff_F_translation.div_const _).mul
    ((((contDiff_const.mul (s.contDiff_v_translation j)).mul
      (s.contDiff_v_translation k))).sub (s.contDiff_diagonalMass_translation j k))

theorem contDiff_thirdDiagonalMass_translation (j k l : Fin p) :
    ContDiff ℝ ⊤ (fun x => (s.weights x).thirdDiagonalMass j k l) := by
  unfold FaceWeights.thirdDiagonalMass
  split_ifs
  · exact s.contDiff_v_translation j
  · exact contDiff_const

theorem contDiff_thirdDerivative_translation (j k l : Fin p) :
    ContDiff ℝ ⊤ (fun x => s.mixedThirdDerivativeF x j k l) := by
  simp_rw [s.mixedThirdDerivativeF_eq]
  unfold FaceWeights.thirdFactor
  exact (s.contDiff_F_translation.div_const _).mul
    (((((contDiff_const.mul (s.contDiff_v_translation j)).mul
      (s.contDiff_v_translation k)).mul (s.contDiff_v_translation l)).add
      (contDiff_const.mul (((s.contDiff_diagonalMass_translation j k).mul
        (s.contDiff_v_translation l)).add ((s.contDiff_diagonalMass_translation j l).mul
        (s.contDiff_v_translation k)) |>.add ((s.contDiff_diagonalMass_translation k l).mul
        (s.contDiff_v_translation j))))).sub (s.contDiff_thirdDiagonalMass_translation j k l))

theorem hasDerivAt_secondDerivative_line_sum
    (x y : Fin p → ℝ) (j k : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.mixedSecondDerivativeF (line x y r) j k)
      (∑ l, s.mixedThirdDerivativeF (line x y t) j k l * y l) t :=
  hasDerivAt_line_of_coordinate_derivatives _ _
    ((s.contDiff_secondDerivative_translation j k).differentiable (by simp))
    (fun a l => by simpa only [line_zero] using
      s.hasDerivAt_secondDerivative_coordinate a j k l 0) x y t

theorem hasDerivAt_thirdDerivative_line_sum
    (x y : Fin p → ℝ) (j k l : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.mixedThirdDerivativeF (line x y r) j k l)
      (∑ m, s.mixedFourthDerivativeF (line x y t) j k l m * y m) t :=
  hasDerivAt_line_of_coordinate_derivatives _ _
    ((s.contDiff_thirdDerivative_translation j k l).differentiable (by simp))
    (fun a m => by simpa only [line_zero] using
      s.hasDerivAt_thirdDerivative_coordinate a j k l m 0) x y t


theorem hasDerivAt_F_line_sum_translation (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.F (line x y r))
      (∑ j, s.coordinateDerivativeF (line x y t) j * y j) t :=
  hasDerivAt_line_of_coordinate_derivatives _ _
    (s.contDiff_F_translation.differentiable (by simp))
    (fun a j => by simpa only [line_zero] using s.hasDerivAt_F_coordinate_normalized a j 0)
    x y t

theorem hasDerivAt_firstDerivative_line_sum_translation
    (x y : Fin p → ℝ) (j : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.coordinateDerivativeF (line x y r) j)
      (∑ k, s.mixedSecondDerivativeF (line x y t) j k * y k) t :=
  hasDerivAt_line_of_coordinate_derivatives _ _
    ((s.contDiff_firstDerivative_translation j).differentiable (by simp))
    (fun a k => by simpa only [line_zero] using s.hasDerivAt_firstDerivative_coordinate a j k 0)
    x y t

noncomputable def translationD1 (x y : Fin p → ℝ) : ℝ :=
  ∑ j, s.coordinateDerivativeF x j * y j

noncomputable def translationD2 (x y : Fin p → ℝ) : ℝ :=
  ∑ j, ∑ k, s.mixedSecondDerivativeF x j k * y j * y k

noncomputable def translationD3 (x y : Fin p → ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, s.mixedThirdDerivativeF x j k l * y j * y k * y l

noncomputable def translationD4 (x y : Fin p → ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, ∑ m, s.mixedFourthDerivativeF x j k l m * y j * y k * y l * y m

theorem hasDerivAt_translationD1 (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.translationD1 (line x y r) y)
      (s.translationD2 (line x y t) y) t := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    (s.hasDerivAt_firstDerivative_line_sum_translation x y j t).mul_const (y j))
  convert hd using 1
  unfold translationD2
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem hasDerivAt_translationD2 (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.translationD2 (line x y r) y)
      (s.translationD3 (line x y t) y) t := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    HasDerivAt.sum (u := Finset.univ) (fun k _ =>
      ((s.hasDerivAt_secondDerivative_line_sum x y j k t).mul_const (y j)).mul_const (y k)))
  convert hd using 1
  unfold translationD3
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem hasDerivAt_translationD3 (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.translationD3 (line x y r) y)
      (s.translationD4 (line x y t) y) t := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    HasDerivAt.sum (u := Finset.univ) (fun k _ =>
      HasDerivAt.sum (u := Finset.univ) (fun l _ =>
        (((s.hasDerivAt_thirdDerivative_line_sum x y j k l t).mul_const (y j)).mul_const
          (y k)).mul_const (y l))))
  convert hd using 1
  unfold translationD4
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem iteratedDeriv_F_line_one (x y : Fin p → ℝ) :
    iteratedDeriv 1 (fun r => s.F (line x y r)) =
      fun r => s.translationD1 (line x y r) y := by
  funext t
  rw [iteratedDeriv_one]
  exact (s.hasDerivAt_F_line_sum_translation x y t).deriv

theorem iteratedDeriv_F_line_two (x y : Fin p → ℝ) :
    iteratedDeriv 2 (fun r => s.F (line x y r)) =
      fun r => s.translationD2 (line x y r) y := by
  rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, s.iteratedDeriv_F_line_one]
  funext t
  exact (s.hasDerivAt_translationD1 x y t).deriv

theorem iteratedDeriv_F_line_three (x y : Fin p → ℝ) :
    iteratedDeriv 3 (fun r => s.F (line x y r)) =
      fun r => s.translationD3 (line x y r) y := by
  rw [show 3 = 2 + 1 by rfl, iteratedDeriv_succ, s.iteratedDeriv_F_line_two]
  funext t
  exact (s.hasDerivAt_translationD2 x y t).deriv

theorem iteratedDeriv_F_line_four (x y : Fin p → ℝ) :
    iteratedDeriv 4 (fun r => s.F (line x y r)) =
      fun r => s.translationD4 (line x y r) y := by
  rw [show 4 = 3 + 1 by rfl, iteratedDeriv_succ, s.iteratedDeriv_F_line_three]
  funext t
  exact (s.hasDerivAt_translationD3 x y t).deriv


@[simp] theorem line_one_translation (x y : Fin p → ℝ) : line x y 1 = x + y := by
  funext j
  simp [line]

/-- The cubic translation polynomial uses the actual mixed coordinate
derivatives, contracted with the translation vector. -/
noncomputable def translationTaylor3 (x y : Fin p → ℝ) : ℝ :=
  s.F x + s.translationD1 x y + s.translationD2 x y / 2 + s.translationD3 x y / 6

/-- A true Taylor expansion along an arbitrary vector, with an actual fourth
derivative at an interior point of the line segment. -/
theorem exists_translationTaylor3_remainder (x y : Fin p → ℝ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      s.F (x + y) - s.translationTaylor3 x y = s.translationD4 (line x y t) y / 24 := by
  have hline : ContDiff ℝ 4 (line x y) := by
    apply contDiff_pi.mpr
    intro j
    exact contDiff_const.add (contDiff_id.mul contDiff_const)
  have hf : ContDiff ℝ 4 (fun r => s.F (line x y r)) :=
    (s.contDiff_F_translation.of_le (by simp)).comp hline
  obtain ⟨t, ht, hrem⟩ := taylor3_mean_remainder hf
  refine ⟨t, ht, ?_⟩
  simpa only [s.iteratedDeriv_F_line_one, s.iteratedDeriv_F_line_two,
    s.iteratedDeriv_F_line_three, s.iteratedDeriv_F_line_four,
    line_zero, line_one_translation, translationTaylor3] using hrem

theorem abs_translationD4_le_norm (x y : Fin p → ℝ) :
    |s.translationD4 x y| ≤
      (∑ j, ∑ k, ∑ l, ∑ m, |s.mixedFourthDerivativeF x j k l m|) * ‖y‖ ^ 4 := by
  have hcoord (j : Fin p) : |y j| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm y j
  have hpoint (j k l m : Fin p) :
      |s.mixedFourthDerivativeF x j k l m * y j * y k * y l * y m| ≤
        |s.mixedFourthDerivativeF x j k l m| * ‖y‖ ^ 4 := by
    rw [show ‖y‖ ^ 4 = ‖y‖ * ‖y‖ * ‖y‖ * ‖y‖ by ring]
    simp only [abs_mul]
    rw [show |s.mixedFourthDerivativeF x j k l m| * (‖y‖ * ‖y‖ * ‖y‖ * ‖y‖) =
      |s.mixedFourthDerivativeF x j k l m| * ‖y‖ * ‖y‖ * ‖y‖ * ‖y‖ by ring]
    gcongr <;> exact hcoord _
  unfold translationD4
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m,
        |s.mixedFourthDerivativeF x j k l m * y j * y k * y l * y m| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m,
        |s.mixedFourthDerivativeF x j k l m| * ‖y‖ ^ 4 := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact Finset.sum_le_sum fun m _ => hpoint j k l m
    _ = _ := by simp only [← Finset.sum_mul]

/-- A dimension-free global cubic Taylor remainder for the actual smoother. -/
theorem abs_translationTaylor3_remainder_le (x y : Fin p → ℝ) :
    |s.F (x + y) - s.translationTaylor3 x y| ≤
      75 * ‖y‖ ^ 4 / (24 * s.bandwidth ^ 4) := by
  obtain ⟨t, ht, hrem⟩ := s.exists_translationTaylor3_remainder x y
  rw [hrem, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  have hbound := s.abs_translationD4_le_norm (line x y t) y
  have hsum := s.sum_abs_mixedFourthDerivativeF_le_variance (line x y t)
  have hvar := s.variance_le_one (line x y t)
  have hn : 75 * s.F (line x y t) * (1 - s.F (line x y t)) ≤ 75 := by
    nlinarith only [hvar]
  have hs : (∑ j, ∑ k, ∑ l, ∑ m,
      |s.mixedFourthDerivativeF (line x y t) j k l m|) ≤ 75 / s.bandwidth ^ 4 :=
    hsum.trans (div_le_div_of_nonneg_right hn (pow_nonneg s.bandwidth_pos.le 4))
  calc
    _ ≤ ((75 / s.bandwidth ^ 4) * ‖y‖ ^ 4) / 24 :=
      div_le_div_of_nonneg_right (hbound.trans
        (mul_le_mul_of_nonneg_right hs (pow_nonneg (norm_nonneg y) 4))) (by norm_num)
    _ = _ := by ring



/-- A coordinatewise fourth-derivative envelope gives the corresponding
weighted tensor contraction bound. -/
theorem abs_translationD4_le_tensor (x y : Fin p → ℝ)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ j k l m, |s.mixedFourthDerivativeF x j k l m| ≤ H j k l m) :
    |s.translationD4 x y| ≤
      ∑ j, ∑ k, ∑ l, ∑ m, H j k l m * |y j * y k * y l * y m| := by
  have hpoint (j k l m : Fin p) :
      |s.mixedFourthDerivativeF x j k l m * y j * y k * y l * y m| ≤
        H j k l m * |y j * y k * y l * y m| := by
    calc
      _ = |s.mixedFourthDerivativeF x j k l m| * |y j * y k * y l * y m| := by
        simp only [abs_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hH j k l m) (abs_nonneg _)
  unfold translationD4
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m,
        |s.mixedFourthDerivativeF x j k l m * y j * y k * y l * y m| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact Finset.sum_le_sum fun m _ => hpoint j k l m

/-- The cubic remainder preserves the weighted fourth-moment tensor. The
envelope concerns actual derivatives on the translated segment. -/
theorem abs_translationTaylor3_remainder_le_tensor (x y : Fin p → ℝ) {r : ℝ}
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hy : ‖y‖ ≤ r)
    (hH : ∀ z : Fin p → ℝ, ‖z‖ ≤ r → ∀ j k l m,
      |s.mixedFourthDerivativeF (x + z) j k l m| ≤ H j k l m) :
    |s.F (x + y) - s.translationTaylor3 x y| ≤
      (∑ j, ∑ k, ∑ l, ∑ m, H j k l m * |y j * y k * y l * y m|) / 24 := by
  obtain ⟨t, ht, hrem⟩ := s.exists_translationTaylor3_remainder x y
  have hz : ‖t • y‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have ht1 : t * ‖y‖ ≤ ‖y‖ := by nlinarith [norm_nonneg y, ht.2]
    exact ht1.trans hy
  have heq : line x y t = x + t • y := rfl
  have hb := s.abs_translationD4_le_tensor (line x y t) y H
    (by rw [heq]; exact hH (t • y) hz)
  rw [hrem, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  exact div_le_div_of_nonneg_right hb (by norm_num)


noncomputable def translationGradientTaylor2 (x y : Fin p → ℝ) (a : ℝ) : ℝ :=
  s.translationD1 x y + a * s.translationD2 x y + a ^ 2 * s.translationD3 x y / 2

/-- Taylor expansion of the actual directional gradient at a scaled shift.
The direction contracted into the gradient is kept separate from its scale. -/
theorem exists_translationGradientTaylor2_remainder (x y : Fin p → ℝ) (a : ℝ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      s.translationD1 (x + a • y) y - s.translationGradientTaylor2 x y a =
        a ^ 3 * s.translationD4 (line x y (a * t)) y / 6 := by
  let f : ℝ → ℝ := fun t => s.translationD1 (line x y (a * t)) y
  have hline : ContDiff ℝ ⊤ (fun t => line x y (a * t)) := by
    apply contDiff_pi.mpr
    intro j
    exact contDiff_const.add ((contDiff_const.mul contDiff_id).mul contDiff_const)
  have hf : ContDiff ℝ 3 f := by
    unfold f translationD1
    exact (ContDiff.sum (fun j _ =>
      ((s.contDiff_firstDerivative_translation j).comp hline).mul contDiff_const)).of_le (by simp)
  have hd0 (t : ℝ) : HasDerivAt f
      (a * s.translationD2 (line x y (a * t)) y) t := by
    have hd := (s.hasDerivAt_translationD1 x y (a * t)).comp t
      ((hasDerivAt_id t).const_mul a)
    convert hd using 1
    ring
  have hd1 (t : ℝ) : HasDerivAt
      (fun r => a * s.translationD2 (line x y (a * r)) y)
      (a ^ 2 * s.translationD3 (line x y (a * t)) y) t := by
    have hd := ((s.hasDerivAt_translationD2 x y (a * t)).comp t
      ((hasDerivAt_id t).const_mul a)).const_mul a
    convert hd using 1
    ring
  have hd2 (t : ℝ) : HasDerivAt
      (fun r => a ^ 2 * s.translationD3 (line x y (a * r)) y)
      (a ^ 3 * s.translationD4 (line x y (a * t)) y) t := by
    have hd := ((s.hasDerivAt_translationD3 x y (a * t)).comp t
      ((hasDerivAt_id t).const_mul a)).const_mul (a ^ 2)
    convert hd using 1
    ring
  have h1 : iteratedDeriv 1 f = fun t => a * s.translationD2 (line x y (a * t)) y := by
    funext t
    rw [iteratedDeriv_one]
    exact (hd0 t).deriv
  have h2 : iteratedDeriv 2 f = fun t => a ^ 2 * s.translationD3 (line x y (a * t)) y := by
    rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, h1]
    funext t
    exact (hd1 t).deriv
  have h3 : iteratedDeriv 3 f = fun t => a ^ 3 * s.translationD4 (line x y (a * t)) y := by
    rw [show 3 = 2 + 1 by rfl, iteratedDeriv_succ, h2]
    funext t
    exact (hd2 t).deriv
  obtain ⟨t, ht, hrem⟩ := taylor2_mean_remainder hf
  refine ⟨t, ht, ?_⟩
  have hscale : line x y a = x + a • y := rfl
  simpa only [h1, h2, h3, f, mul_one, mul_zero, line_zero, hscale,
    translationGradientTaylor2] using hrem

/-- The directional-gradient remainder retains the fourth coordinate tensor
and the exact cubic dependence on the shift scale. -/
theorem abs_translationGradientTaylor2_remainder_le_tensor
    (x y : Fin p → ℝ) (a : ℝ) {r : ℝ}
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hy : |a| * ‖y‖ ≤ r)
    (hH : ∀ z : Fin p → ℝ, ‖z‖ ≤ r → ∀ j k l m,
      |s.mixedFourthDerivativeF (x + z) j k l m| ≤ H j k l m) :
    |s.translationD1 (x + a • y) y - s.translationGradientTaylor2 x y a| ≤
      |a| ^ 3 / 6 *
        (∑ j, ∑ k, ∑ l, ∑ m, H j k l m * |y j * y k * y l * y m|) := by
  obtain ⟨t, ht, hrem⟩ := s.exists_translationGradientTaylor2_remainder x y a
  have hz : ‖(a * t) • y‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos ht.1]
    have hh : |a| * t * ‖y‖ ≤ |a| * ‖y‖ := by
      nlinarith [mul_nonneg (abs_nonneg a) (norm_nonneg y), ht.2]
    exact hh.trans hy
  have heq : line x y (a * t) = x + (a * t) • y := rfl
  have hb := s.abs_translationD4_le_tensor (line x y (a * t)) y H
    (by rw [heq]; exact hH ((a * t) • y) hz)
  rw [hrem, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  calc
    _ ≤ (|a| ^ 3 * (∑ j, ∑ k, ∑ l, ∑ m,
        H j k l m * |y j * y k * y l * y m|)) / 6 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg a) 3))
        (by norm_num)
    _ = _ := by ring

theorem continuous_translationD1 (y : Fin p → ℝ) :
    Continuous (fun x => s.translationD1 x y) := by
  unfold translationD1
  apply continuous_finset_sum
  intro j _
  exact (s.continuous_firstDerivative j).mul continuous_const

theorem norm_translationD1_le_constant (x y : Fin p → ℝ) :
    ‖s.translationD1 x y‖ ≤ ∑ j, (1 / s.bandwidth ^ 1) * |y j| := by
  have hp (j : Fin p) : |s.coordinateDerivativeF x j * y j| ≤
      (1 / s.bandwidth ^ 1) * |y j| := by
    calc
      _ = |s.coordinateDerivativeF x j| * |y j| := by simp only [abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [pow_one] using s.norm_firstDerivative_le x j) (abs_nonneg _)
  rw [Real.norm_eq_abs]
  unfold translationD1
  calc
    _ ≤ ∑ j, |s.coordinateDerivativeF x j * y j| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      exact Finset.sum_le_sum fun j _ => hp j

theorem continuous_translationD2 (y : Fin p → ℝ) :
    Continuous (fun x => s.translationD2 x y) := by
  unfold translationD2
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  exact ((s.continuous_secondDerivative j k).mul continuous_const).mul continuous_const

theorem norm_translationD2_le_constant (x y : Fin p → ℝ) :
    ‖s.translationD2 x y‖ ≤ ∑ j, ∑ k, (3 / s.bandwidth ^ 2) * |y j * y k| := by
  have hp (j k : Fin p) : |s.mixedSecondDerivativeF x j k * y j * y k| ≤
      (3 / s.bandwidth ^ 2) * |y j * y k| := by
    calc
      _ = |s.mixedSecondDerivativeF x j k| * |y j * y k| := by simp only [abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (s.norm_secondDerivative_le x j k) (abs_nonneg _)
  rw [Real.norm_eq_abs]
  unfold translationD2
  calc
    _ ≤ ∑ j, ∑ k, |s.mixedSecondDerivativeF x j k * y j * y k| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum fun k _ => hp j k

theorem continuous_translationD3 (y : Fin p → ℝ) :
    Continuous (fun x => s.translationD3 x y) := by
  unfold translationD3
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  apply continuous_finset_sum
  intro l _
  exact (((s.continuous_thirdDerivative j k l).mul continuous_const).mul continuous_const).mul continuous_const

theorem norm_translationD3_le_constant (x y : Fin p → ℝ) :
    ‖s.translationD3 x y‖ ≤ ∑ j, ∑ k, ∑ l, (13 / s.bandwidth ^ 3) * |y j * y k * y l| := by
  have hp (j k l : Fin p) : |s.mixedThirdDerivativeF x j k l * y j * y k * y l| ≤
      (13 / s.bandwidth ^ 3) * |y j * y k * y l| := by
    calc
      _ = |s.mixedThirdDerivativeF x j k l| * |y j * y k * y l| := by simp only [abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (s.norm_thirdDerivative_le x j k l) (abs_nonneg _)
  rw [Real.norm_eq_abs]
  unfold translationD3
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, |s.mixedThirdDerivativeF x j k l * y j * y k * y l| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact Finset.sum_le_sum fun l _ => hp j k l

theorem continuous_translationD4 (y : Fin p → ℝ) :
    Continuous (fun x => s.translationD4 x y) := by
  unfold translationD4
  apply continuous_finset_sum
  intro j _
  apply continuous_finset_sum
  intro k _
  apply continuous_finset_sum
  intro l _
  apply continuous_finset_sum
  intro m _
  exact ((((s.continuous_fourthDerivative j k l m).mul continuous_const).mul continuous_const).mul continuous_const).mul continuous_const

theorem norm_translationD4_le_constant (x y : Fin p → ℝ) :
    ‖s.translationD4 x y‖ ≤ ∑ j, ∑ k, ∑ l, ∑ m, (75 / s.bandwidth ^ 4) * |y j * y k * y l * y m| := by
  have hp (j k l m : Fin p) : |s.mixedFourthDerivativeF x j k l m * y j * y k * y l * y m| ≤
      (75 / s.bandwidth ^ 4) * |y j * y k * y l * y m| := by
    calc
      _ = |s.mixedFourthDerivativeF x j k l m| * |y j * y k * y l * y m| := by simp only [abs_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (s.norm_fourthDerivative_le x j k l m) (abs_nonneg _)
  rw [Real.norm_eq_abs]
  unfold translationD4
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m, |s.mixedFourthDerivativeF x j k l m * y j * y k * y l * y m| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact Finset.sum_le_sum fun m _ => hp j k l m

variable (ν : Measure (Fin p → ℝ)) [IsProbabilityMeasure ν]

noncomputable def convolutionTranslationD1 (x y : Fin p → ℝ) : ℝ :=
  ∑ j, s.convolutionFirstDerivative ν x j * y j

theorem integrable_translationD1_shift (x y : Fin p → ℝ) :
    Integrable (fun z => s.translationD1 (x + z) y) ν := by
  unfold translationD1
  apply integrable_finset_sum
  intro j _
  exact (s.integrable_firstDerivative_shift ν x j).mul_const (y j)

theorem integral_translationD1_shift (x y : Fin p → ℝ) :
    (∫ z, s.translationD1 (x + z) y ∂ν) = s.convolutionTranslationD1 ν x y := by
  unfold translationD1 convolutionTranslationD1
  simp_rw [s.convolutionFirstDerivative_eq_integral]
  have hi (j : Fin p) : Integrable (fun z => s.coordinateDerivativeF (x + z) j * y j) ν :=
    (s.integrable_firstDerivative_shift ν x j).mul_const (y j)
  rw [integral_finset_sum Finset.univ (fun j _ => hi j)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [integral_mul_const]

noncomputable def convolutionTranslationD2 (x y : Fin p → ℝ) : ℝ :=
  ∑ j, ∑ k, s.convolutionSecondDerivative ν x j k * y j * y k

theorem integrable_translationD2_shift (x y : Fin p → ℝ) :
    Integrable (fun z => s.translationD2 (x + z) y) ν := by
  unfold translationD2
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  exact ((s.integrable_secondDerivative_shift ν x j k).mul_const (y j)).mul_const (y k)

theorem integral_translationD2_shift (x y : Fin p → ℝ) :
    (∫ z, s.translationD2 (x + z) y ∂ν) = s.convolutionTranslationD2 ν x y := by
  unfold translationD2 convolutionTranslationD2
  simp_rw [s.convolutionSecondDerivative_eq_integral]
  have hi (j k : Fin p) : Integrable (fun z => s.mixedSecondDerivativeF (x + z) j k * y j * y k) ν :=
    ((s.integrable_secondDerivative_shift ν x j k).mul_const (y j)).mul_const (y k)
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ (fun k _ => hi j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => hi j k)]
  apply Finset.sum_congr rfl
  intro k _
  simp only [integral_mul_const]

noncomputable def convolutionTranslationD3 (x y : Fin p → ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, s.convolutionThirdDerivative ν x j k l * y j * y k * y l

theorem integrable_translationD3_shift (x y : Fin p → ℝ) :
    Integrable (fun z => s.translationD3 (x + z) y) ν := by
  unfold translationD3
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  apply integrable_finset_sum
  intro l _
  exact (((s.integrable_thirdDerivative_shift ν x j k l).mul_const (y j)).mul_const (y k)).mul_const (y l)

theorem integral_translationD3_shift (x y : Fin p → ℝ) :
    (∫ z, s.translationD3 (x + z) y ∂ν) = s.convolutionTranslationD3 ν x y := by
  unfold translationD3 convolutionTranslationD3
  simp_rw [s.convolutionThirdDerivative_eq_integral]
  have hi (j k l : Fin p) : Integrable (fun z => s.mixedThirdDerivativeF (x + z) j k l * y j * y k * y l) ν :=
    (((s.integrable_thirdDerivative_shift ν x j k l).mul_const (y j)).mul_const (y k)).mul_const (y l)
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ (fun l _ => hi j k l)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ (fun l _ => hi j k l))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finset_sum Finset.univ (fun l _ => hi j k l)]
  apply Finset.sum_congr rfl
  intro l _
  simp only [integral_mul_const]

noncomputable def convolutionTranslationD4 (x y : Fin p → ℝ) : ℝ :=
  ∑ j, ∑ k, ∑ l, ∑ m, s.convolutionFourthDerivative ν x j k l m * y j * y k * y l * y m

theorem integrable_translationD4_shift (x y : Fin p → ℝ) :
    Integrable (fun z => s.translationD4 (x + z) y) ν := by
  unfold translationD4
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  apply integrable_finset_sum
  intro l _
  apply integrable_finset_sum
  intro m _
  exact ((((s.integrable_fourthDerivative_shift ν x j k l m).mul_const (y j)).mul_const (y k)).mul_const (y l)).mul_const (y m)

theorem integral_translationD4_shift (x y : Fin p → ℝ) :
    (∫ z, s.translationD4 (x + z) y ∂ν) = s.convolutionTranslationD4 ν x y := by
  unfold translationD4 convolutionTranslationD4
  simp_rw [s.convolutionFourthDerivative_eq_integral]
  have hi (j k l m : Fin p) : Integrable
      (fun z => s.mixedFourthDerivativeF (x + z) j k l m * y j * y k * y l * y m) ν :=
    ((((s.integrable_fourthDerivative_shift ν x j k l m).mul_const (y j)).mul_const (y k)).mul_const (y l)).mul_const (y m)
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ (fun l _ => integrable_finset_sum Finset.univ (fun m _ => hi j k l m))))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ (fun l _ => integrable_finset_sum Finset.univ (fun m _ => hi j k l m)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finset_sum Finset.univ (fun l _ => integrable_finset_sum Finset.univ (fun m _ => hi j k l m))]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_finset_sum Finset.univ (fun m _ => hi j k l m)]
  apply Finset.sum_congr rfl
  intro m _
  simp only [integral_mul_const]

noncomputable def convolutionTaylor3 (x y : Fin p → ℝ) : ℝ :=
  s.convolution ν x + s.convolutionTranslationD1 ν x y +
    s.convolutionTranslationD2 ν x y / 2 + s.convolutionTranslationD3 ν x y / 6

theorem integrable_translationTaylor3_shift (x y : Fin p → ℝ) :
    Integrable (fun z => s.translationTaylor3 (x + z) y) ν :=
  (((s.integrable_F_shift ν x).add (s.integrable_translationD1_shift ν x y)).add
    ((s.integrable_translationD2_shift ν x y).div_const 2)).add
      ((s.integrable_translationD3_shift ν x y).div_const 6)

theorem integral_translationTaylor3_shift (x y : Fin p → ℝ) :
    (∫ z, s.translationTaylor3 (x + z) y ∂ν) = s.convolutionTaylor3 ν x y := by
  have h1 := integral_add (s.integrable_F_shift ν x) (s.integrable_translationD1_shift ν x y)
  have h2 := integral_add ((s.integrable_F_shift ν x).add
    (s.integrable_translationD1_shift ν x y))
    ((s.integrable_translationD2_shift ν x y).div_const 2)
  have h3 := integral_add (((s.integrable_F_shift ν x).add
    (s.integrable_translationD1_shift ν x y)).add
      ((s.integrable_translationD2_shift ν x y).div_const 2))
    ((s.integrable_translationD3_shift ν x y).div_const 6)
  change (∫ z, (((fun z => s.F (x + z)) + (fun z => s.translationD1 (x + z) y)) +
    (fun z => s.translationD2 (x + z) y / 2)) z + s.translationD3 (x + z) y / 6 ∂ν) = _
  simp only [Pi.add_apply] at h1 h2 h3 ⊢
  rw [h3, h2, h1]
  simp only [integral_div, s.integral_translationD1_shift,
    s.integral_translationD2_shift, s.integral_translationD3_shift,
    convolutionTaylor3, convolution, shiftIntegral]

/-- Cubic Taylor expansion of the actual probability convolution, using its
actual first, second, and third mixed derivative tensors. -/
theorem abs_convolutionTaylor3_remainder_le (x y : Fin p → ℝ) :
    |s.convolution ν (x + y) - s.convolutionTaylor3 ν x y| ≤
      75 * ‖y‖ ^ 4 / (24 * s.bandwidth ^ 4) := by
  have hi := integral_sub (s.integrable_F_shift ν (x + y))
    (s.integrable_translationTaylor3_shift ν x y)
  rw [s.integral_translationTaylor3_shift] at hi
  have hb : ∀ z, ‖s.F (x + y + z) - s.translationTaylor3 (x + z) y‖ ≤
      75 * ‖y‖ ^ 4 / (24 * s.bandwidth ^ 4) := by
    intro z
    have heq : x + y + z = (x + z) + y := by abel
    rw [heq, Real.norm_eq_abs]
    exact s.abs_translationTaylor3_remainder_le (x + z) y
  have hh := norm_integral_le_of_norm_le_const (μ := ν) (ae_of_all ν hb)
  simpa only [hi, convolution, shiftIntegral, Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using hh

/-- Tensor-preserving cubic remainder for the actual convolution. Each entry
of the dominating tensor is integrated separately. -/
theorem abs_convolutionTaylor3_remainder_le_tensor (x y : Fin p → ℝ) {r : ℝ}
    (H : (Fin p → ℝ) → Fin p → Fin p → Fin p → Fin p → ℝ)
    (hy : ‖y‖ ≤ r)
    (hiH : ∀ j k l m, Integrable (fun z => H z j k l m) ν)
    (hH : ∀ z u : Fin p → ℝ, ‖u‖ ≤ r → ∀ j k l m,
      |s.mixedFourthDerivativeF (x + z + u) j k l m| ≤ H z j k l m) :
    |s.convolution ν (x + y) - s.convolutionTaylor3 ν x y| ≤
      (∑ j, ∑ k, ∑ l, ∑ m,
        (∫ z, H z j k l m ∂ν) * |y j * y k * y l * y m|) / 24 := by
  let coeff : Fin p × Fin p × Fin p × Fin p → ℝ := fun i =>
    |y i.1 * y i.2.1 * y i.2.2.1 * y i.2.2.2| / 24
  let env : (Fin p × Fin p × Fin p × Fin p) → (Fin p → ℝ) → ℝ :=
    fun i z => H z i.1 i.2.1 i.2.2.1 i.2.2.2
  have hb (z : Fin p → ℝ) :
      |s.F (x + y + z) - s.translationTaylor3 (x + z) y| ≤ ∑ i, env i z * coeff i := by
    have heq : x + y + z = x + z + y := by abel
    rw [heq]
    have hh := s.abs_translationTaylor3_remainder_le_tensor (x + z) y (H z) hy (hH z)
    simpa only [env, coeff, Fintype.sum_prod_type, ← Finset.sum_div, ← mul_div_assoc] using hh
  have hh := abs_integral_sub_le_finite_sum ν
    (fun z => s.F (x + y + z)) (fun z => s.translationTaylor3 (x + z) y)
    env coeff (s.integrable_F_shift ν (x + y)) (s.integrable_translationTaylor3_shift ν x y)
    (fun i => hiH i.1 i.2.1 i.2.2.1 i.2.2.2) hb
  simpa only [s.integral_translationTaylor3_shift, convolution, shiftIntegral,
    env, coeff, Fintype.sum_prod_type, ← Finset.sum_div, ← mul_div_assoc] using hh

noncomputable def convolutionGradientTaylor2 (x y : Fin p → ℝ) (a : ℝ) : ℝ :=
  s.convolutionTranslationD1 ν x y + a * s.convolutionTranslationD2 ν x y +
    a ^ 2 * s.convolutionTranslationD3 ν x y / 2

theorem integrable_translationGradientTaylor2_shift (x y : Fin p → ℝ) (a : ℝ) :
    Integrable (fun z => s.translationGradientTaylor2 (x + z) y a) ν :=
  ((s.integrable_translationD1_shift ν x y).add
    ((s.integrable_translationD2_shift ν x y).const_mul a)).add
    (((s.integrable_translationD3_shift ν x y).const_mul (a ^ 2)).div_const 2)

theorem integral_translationGradientTaylor2_shift (x y : Fin p → ℝ) (a : ℝ) :
    (∫ z, s.translationGradientTaylor2 (x + z) y a ∂ν) =
      s.convolutionGradientTaylor2 ν x y a := by
  have h1 := integral_add (s.integrable_translationD1_shift ν x y)
    ((s.integrable_translationD2_shift ν x y).const_mul a)
  have h2 := integral_add ((s.integrable_translationD1_shift ν x y).add
    ((s.integrable_translationD2_shift ν x y).const_mul a))
    (((s.integrable_translationD3_shift ν x y).const_mul (a ^ 2)).div_const 2)
  simp only [Pi.add_apply] at h1 h2
  unfold translationGradientTaylor2 convolutionGradientTaylor2
  rw [h2, h1]
  simp only [integral_const_mul, integral_div, s.integral_translationD1_shift,
    s.integral_translationD2_shift, s.integral_translationD3_shift]

/-- The convolution directional-gradient remainder keeps every fourth
coordinate product and the exact cubic shift scale. -/
theorem abs_convolutionGradientTaylor2_remainder_le_tensor
    (x y : Fin p → ℝ) (a : ℝ) {r : ℝ}
    (H : (Fin p → ℝ) → Fin p → Fin p → Fin p → Fin p → ℝ)
    (hy : |a| * ‖y‖ ≤ r)
    (hiH : ∀ j k l m, Integrable (fun z => H z j k l m) ν)
    (hH : ∀ z u : Fin p → ℝ, ‖u‖ ≤ r → ∀ j k l m,
      |s.mixedFourthDerivativeF (x + z + u) j k l m| ≤ H z j k l m) :
    |s.convolutionTranslationD1 ν (x + a • y) y -
      s.convolutionGradientTaylor2 ν x y a| ≤
      |a| ^ 3 / 6 * (∑ j, ∑ k, ∑ l, ∑ m,
        (∫ z, H z j k l m ∂ν) * |y j * y k * y l * y m|) := by
  let coeff : Fin p × Fin p × Fin p × Fin p → ℝ := fun i =>
    |a| ^ 3 / 6 * |y i.1 * y i.2.1 * y i.2.2.1 * y i.2.2.2|
  let env : (Fin p × Fin p × Fin p × Fin p) → (Fin p → ℝ) → ℝ :=
    fun i z => H z i.1 i.2.1 i.2.2.1 i.2.2.2
  have hswap (b c : ℝ) : b * (|a| ^ 3 / 6 * c) = |a| ^ 3 / 6 * (b * c) := by ring
  have hb (z : Fin p → ℝ) :
      |s.translationD1 (x + a • y + z) y - s.translationGradientTaylor2 (x + z) y a| ≤
        ∑ i, env i z * coeff i := by
    have heq : x + a • y + z = x + z + a • y := by abel
    rw [heq]
    have hh := s.abs_translationGradientTaylor2_remainder_le_tensor (x + z) y a
      (H z) hy (hH z)
    simpa only [env, coeff, Fintype.sum_prod_type, hswap, ← Finset.mul_sum] using hh
  have hh := abs_integral_sub_le_finite_sum ν
    (fun z => s.translationD1 (x + a • y + z) y)
    (fun z => s.translationGradientTaylor2 (x + z) y a) env coeff
    (s.integrable_translationD1_shift ν (x + a • y) y)
    (s.integrable_translationGradientTaylor2_shift ν x y a)
    (fun i => hiH i.1 i.2.1 i.2.2.1 i.2.2.2) hb
  simpa only [s.integral_translationGradientTaylor2_shift, s.integral_translationD1_shift,
    env, coeff, Fintype.sum_prod_type, hswap, ← Finset.mul_sum] using hh
theorem hasDerivAt_convolutionTranslationD0_line (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.convolution ν (line x y r))
      (s.convolutionTranslationD1 ν (line x y t) y) t := by
  have hd := hasDerivAt_shiftIntegral_line_translation ν s.F (fun q => s.translationD1 q y) y
    (∑ j, (1 / s.bandwidth ^ 1) * |y j|)
    s.continuous_F (s.continuous_translationD1 y)
    (s.integrable_F_shift ν) (fun q => s.norm_translationD1_le_constant q y)
    (fun q r => s.hasDerivAt_F_line_sum_translation q y r) x t
  simpa only [shiftIntegral, convolution, s.integral_translationD1_shift] using hd

theorem hasDerivAt_convolutionTranslationD1_line (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.convolutionTranslationD1 ν (line x y r) y)
      (s.convolutionTranslationD2 ν (line x y t) y) t := by
  have hd := hasDerivAt_shiftIntegral_line_translation ν (fun q => s.translationD1 q y) (fun q => s.translationD2 q y) y
    (∑ j, ∑ k, (3 / s.bandwidth ^ 2) * |y j * y k|)
    (s.continuous_translationD1 y) (s.continuous_translationD2 y)
    (fun q => s.integrable_translationD1_shift ν q y) (fun q => s.norm_translationD2_le_constant q y)
    (fun q r => s.hasDerivAt_translationD1 q y r) x t
  simpa only [shiftIntegral, s.integral_translationD1_shift, s.integral_translationD2_shift] using hd

theorem hasDerivAt_convolutionTranslationD2_line (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.convolutionTranslationD2 ν (line x y r) y)
      (s.convolutionTranslationD3 ν (line x y t) y) t := by
  have hd := hasDerivAt_shiftIntegral_line_translation ν (fun q => s.translationD2 q y) (fun q => s.translationD3 q y) y
    (∑ j, ∑ k, ∑ l, (13 / s.bandwidth ^ 3) * |y j * y k * y l|)
    (s.continuous_translationD2 y) (s.continuous_translationD3 y)
    (fun q => s.integrable_translationD2_shift ν q y) (fun q => s.norm_translationD3_le_constant q y)
    (fun q r => s.hasDerivAt_translationD2 q y r) x t
  simpa only [shiftIntegral, s.integral_translationD2_shift, s.integral_translationD3_shift] using hd

theorem hasDerivAt_convolutionTranslationD3_line (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.convolutionTranslationD3 ν (line x y r) y)
      (s.convolutionTranslationD4 ν (line x y t) y) t := by
  have hd := hasDerivAt_shiftIntegral_line_translation ν (fun q => s.translationD3 q y) (fun q => s.translationD4 q y) y
    (∑ j, ∑ k, ∑ l, ∑ m, (75 / s.bandwidth ^ 4) * |y j * y k * y l * y m|)
    (s.continuous_translationD3 y) (s.continuous_translationD4 y)
    (fun q => s.integrable_translationD3_shift ν q y) (fun q => s.norm_translationD4_le_constant q y)
    (fun q r => s.hasDerivAt_translationD3 q y r) x t
  simpa only [shiftIntegral, s.integral_translationD3_shift, s.integral_translationD4_shift] using hd

omit [IsProbabilityMeasure ν] in
theorem abs_convolutionTranslationD4_le_tensor (x y : Fin p → ℝ)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ j k l m, |s.convolutionFourthDerivative ν x j k l m| ≤ H j k l m) :
    |s.convolutionTranslationD4 ν x y| ≤
      ∑ j, ∑ k, ∑ l, ∑ m, H j k l m * |y j * y k * y l * y m| := by
  have hpoint (j k l m : Fin p) :
      |s.convolutionFourthDerivative ν x j k l m * y j * y k * y l * y m| ≤
        H j k l m * |y j * y k * y l * y m| := by
    calc
      _ = |s.convolutionFourthDerivative ν x j k l m| * |y j * y k * y l * y m| := by
        simp only [abs_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hH j k l m) (abs_nonneg _)
  unfold convolutionTranslationD4
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m,
        |s.convolutionFourthDerivative ν x j k l m * y j * y k * y l * y m| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro k _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro l _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      exact Finset.sum_le_sum fun m _ => hpoint j k l m


/-- A direct Taylor expansion of the actual convolution. Its remainder uses
the fourth derivative of the convolution, preserving Gaussian cancellation. -/
theorem exists_convolutionTaylor3_remainder_direct (x y : Fin p → ℝ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      s.convolution ν (x + y) - s.convolutionTaylor3 ν x y =
        s.convolutionTranslationD4 ν (line x y t) y / 24 := by
  have hh := taylor3_of_derivative_chain
    (fun t => s.convolution ν (line x y t))
    (fun t => s.convolutionTranslationD1 ν (line x y t) y)
    (fun t => s.convolutionTranslationD2 ν (line x y t) y)
    (fun t => s.convolutionTranslationD3 ν (line x y t) y)
    (fun t => s.convolutionTranslationD4 ν (line x y t) y)
    (s.hasDerivAt_convolutionTranslationD0_line ν x y)
    (s.hasDerivAt_convolutionTranslationD1_line ν x y)
    (s.hasDerivAt_convolutionTranslationD2_line ν x y)
    (s.hasDerivAt_convolutionTranslationD3_line ν x y)
  simpa only [line_one_translation, line_zero, convolutionTaylor3] using hh

/-- The direct convolution remainder only assumes a local envelope for its
actual fourth mixed derivatives, rather than absolute derivatives before
Gaussian convolution. -/
theorem abs_convolutionTaylor3_remainder_le_tensor_direct
    (x y : Fin p → ℝ) {r : ℝ}
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hy : ‖y‖ ≤ r)
    (hH : ∀ z : Fin p → ℝ, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |s.convolution ν (x + y) - s.convolutionTaylor3 ν x y| ≤
      (∑ j, ∑ k, ∑ l, ∑ m, H j k l m * |y j * y k * y l * y m|) / 24 := by
  obtain ⟨t, ht, hrem⟩ := s.exists_convolutionTaylor3_remainder_direct ν x y
  have hz : ‖t • y‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have ht1 : t * ‖y‖ ≤ ‖y‖ := by nlinarith [norm_nonneg y, ht.2]
    exact ht1.trans hy
  have heq : line x y t = x + t • y := rfl
  have hb := s.abs_convolutionTranslationD4_le_tensor ν (line x y t) y H
    (by rw [heq]; exact hH (t • y) hz)
  rw [hrem, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  exact div_le_div_of_nonneg_right hb (by norm_num)

theorem exists_convolutionGradientTaylor2_remainder_direct
    (x y : Fin p → ℝ) (a : ℝ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      s.convolutionTranslationD1 ν (x + a • y) y -
        s.convolutionGradientTaylor2 ν x y a =
          a ^ 3 * s.convolutionTranslationD4 ν (line x y (a * t)) y / 6 := by
  let f : ℝ → ℝ := fun t => s.convolutionTranslationD1 ν (line x y (a * t)) y
  have hd0 (t : ℝ) : HasDerivAt f
      (a * s.convolutionTranslationD2 ν (line x y (a * t)) y) t := by
    have hd := (s.hasDerivAt_convolutionTranslationD1_line ν x y (a * t)).comp t
      ((hasDerivAt_id t).const_mul a)
    convert hd using 1
    ring
  have hd1 (t : ℝ) : HasDerivAt
      (fun r => a * s.convolutionTranslationD2 ν (line x y (a * r)) y)
      (a ^ 2 * s.convolutionTranslationD3 ν (line x y (a * t)) y) t := by
    have hd := ((s.hasDerivAt_convolutionTranslationD2_line ν x y (a * t)).comp t
      ((hasDerivAt_id t).const_mul a)).const_mul a
    convert hd using 1
    ring
  have hd2 (t : ℝ) : HasDerivAt
      (fun r => a ^ 2 * s.convolutionTranslationD3 ν (line x y (a * r)) y)
      (a ^ 3 * s.convolutionTranslationD4 ν (line x y (a * t)) y) t := by
    have hd := ((s.hasDerivAt_convolutionTranslationD3_line ν x y (a * t)).comp t
      ((hasDerivAt_id t).const_mul a)).const_mul (a ^ 2)
    convert hd using 1
    ring

  have hh := taylor2_of_derivative_chain f
    (fun t => a * s.convolutionTranslationD2 ν (line x y (a * t)) y)
    (fun t => a ^ 2 * s.convolutionTranslationD3 ν (line x y (a * t)) y)
    (fun t => a ^ 3 * s.convolutionTranslationD4 ν (line x y (a * t)) y) hd0 hd1 hd2
  have hscale : line x y a = x + a • y := rfl
  simpa only [f, mul_one, mul_zero, line_zero, hscale, convolutionGradientTaylor2] using hh

theorem abs_convolutionGradientTaylor2_remainder_le_tensor_direct
    (x y : Fin p → ℝ) (a : ℝ) {r : ℝ}
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hy : |a| * ‖y‖ ≤ r)
    (hH : ∀ z : Fin p → ℝ, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |s.convolutionTranslationD1 ν (x + a • y) y - s.convolutionGradientTaylor2 ν x y a| ≤
      |a| ^ 3 / 6 *
        (∑ j, ∑ k, ∑ l, ∑ m, H j k l m * |y j * y k * y l * y m|) := by
  obtain ⟨t, ht, hrem⟩ := s.exists_convolutionGradientTaylor2_remainder_direct ν x y a
  have hz : ‖(a * t) • y‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos ht.1]
    have hh : |a| * t * ‖y‖ ≤ |a| * ‖y‖ := by
      nlinarith [mul_nonneg (abs_nonneg a) (norm_nonneg y), ht.2]
    exact hh.trans hy
  have heq : line x y (a * t) = x + (a * t) • y := rfl
  have hb := s.abs_convolutionTranslationD4_le_tensor ν (line x y (a * t)) y H
    (by rw [heq]; exact hH ((a * t) • y) hz)
  rw [hrem, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  calc
    _ ≤ (|a| ^ 3 * (∑ j, ∑ k, ∑ l, ∑ m,
        H j k l m * |y j * y k * y l * y m|)) / 6 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (pow_nonneg (abs_nonneg a) 3))
        (by norm_num)
    _ = _ := by ring

theorem hasDerivAt_convolutionSecondDerivative_line_sum_translation
    (x y : Fin p → ℝ) (j k : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.convolutionSecondDerivative ν (line x y r) j k)
      (∑ l, s.convolutionThirdDerivative ν (line x y t) j k l * y l) t := by
  have hc : Continuous (fun q => ∑ l, s.mixedThirdDerivativeF q j k l * y l) :=
    continuous_finset_sum _ (fun l _ => (s.continuous_thirdDerivative j k l).mul continuous_const)
  have hb (q : Fin p → ℝ) :
      ‖∑ l, s.mixedThirdDerivativeF q j k l * y l‖ ≤ ∑ l, (13 / s.bandwidth ^ 3) * |y l| := by
    exact abs_finite_weighted_sum_le _ _ _ (fun l => s.norm_thirdDerivative_le q j k l)
  have hd := hasDerivAt_shiftIntegral_line_translation ν
    (fun q => s.mixedSecondDerivativeF q j k) (fun q => ∑ l, s.mixedThirdDerivativeF q j k l * y l)
    y (∑ l, (13 / s.bandwidth ^ 3) * |y l|)
    (s.continuous_secondDerivative j k) hc
    (fun q => s.integrable_secondDerivative_shift ν q j k) hb
    (fun q r => s.hasDerivAt_secondDerivative_line_sum q y j k r) x t
  have heq := shiftIntegral_finite_weighted_sum ν
    (fun l q => s.mixedThirdDerivativeF q j k l) y (line x y t)
    (fun l => s.integrable_thirdDerivative_shift ν (line x y t) j k l)
  simp only [shiftIntegral, ← s.convolutionThirdDerivative_eq_integral] at heq
  simp_rw [s.convolutionSecondDerivative_eq_integral]
  simpa only [shiftIntegral, heq] using hd

theorem hasDerivAt_convolutionThirdDerivative_line_sum_translation
    (x y : Fin p → ℝ) (j k l : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.convolutionThirdDerivative ν (line x y r) j k l)
      (∑ m, s.convolutionFourthDerivative ν (line x y t) j k l m * y m) t := by
  have hc : Continuous (fun q => ∑ m, s.mixedFourthDerivativeF q j k l m * y m) :=
    continuous_finset_sum _ (fun m _ => (s.continuous_fourthDerivative j k l m).mul continuous_const)
  have hb (q : Fin p → ℝ) :
      ‖∑ m, s.mixedFourthDerivativeF q j k l m * y m‖ ≤ ∑ m, (75 / s.bandwidth ^ 4) * |y m| := by
    exact abs_finite_weighted_sum_le _ _ _ (fun m => s.norm_fourthDerivative_le q j k l m)
  have hd := hasDerivAt_shiftIntegral_line_translation ν
    (fun q => s.mixedThirdDerivativeF q j k l) (fun q => ∑ m, s.mixedFourthDerivativeF q j k l m * y m)
    y (∑ m, (75 / s.bandwidth ^ 4) * |y m|)
    (s.continuous_thirdDerivative j k l) hc
    (fun q => s.integrable_thirdDerivative_shift ν q j k l) hb
    (fun q r => s.hasDerivAt_thirdDerivative_line_sum q y j k l r) x t
  have heq := shiftIntegral_finite_weighted_sum ν
    (fun m q => s.mixedFourthDerivativeF q j k l m) y (line x y t)
    (fun m => s.integrable_fourthDerivative_shift ν (line x y t) j k l m)
  simp only [shiftIntegral, ← s.convolutionFourthDerivative_eq_integral] at heq
  simp_rw [s.convolutionThirdDerivative_eq_integral]
  simpa only [shiftIntegral, heq] using hd


/-- First-order translation of an actual convolution Hessian entry. -/
theorem exists_convolutionSecondDerivative_remainder (x y : Fin p → ℝ) (j k : Fin p) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      s.convolutionSecondDerivative ν (x + y) j k -
        (s.convolutionSecondDerivative ν x j k +
          ∑ l, s.convolutionThirdDerivative ν x j k l * y l) =
        (∑ l, ∑ m, s.convolutionFourthDerivative ν (line x y t) j k l m * y l * y m) / 2 := by
  have hd1 (t : ℝ) : HasDerivAt
      (fun r => ∑ l, s.convolutionThirdDerivative ν (line x y r) j k l * y l)
      (∑ l, ∑ m, s.convolutionFourthDerivative ν (line x y t) j k l m * y l * y m) t := by
    have hd := HasDerivAt.sum (u := Finset.univ) (fun l _ =>
      (s.hasDerivAt_convolutionThirdDerivative_line_sum_translation ν x y j k l t).mul_const (y l))
    convert hd using 1
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hh := taylor1_of_derivative_chain
    (fun t => s.convolutionSecondDerivative ν (line x y t) j k)
    (fun t => ∑ l, s.convolutionThirdDerivative ν (line x y t) j k l * y l)
    (fun t => ∑ l, ∑ m, s.convolutionFourthDerivative ν (line x y t) j k l m * y l * y m)
    (s.hasDerivAt_convolutionSecondDerivative_line_sum_translation ν x y j k) hd1
  simpa only [line_one_translation, line_zero] using hh

/-- Zeroth-order translation of an actual convolution third derivative. -/
theorem exists_convolutionThirdDerivative_remainder
    (x y : Fin p → ℝ) (j k l : Fin p) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      s.convolutionThirdDerivative ν (x + y) j k l -
        s.convolutionThirdDerivative ν x j k l =
        ∑ m, s.convolutionFourthDerivative ν (line x y t) j k l m * y m := by
  have hh := taylor0_of_derivative_chain
    (fun t => s.convolutionThirdDerivative ν (line x y t) j k l)
    (fun t => ∑ m, s.convolutionFourthDerivative ν (line x y t) j k l m * y m)
    (s.hasDerivAt_convolutionThirdDerivative_line_sum_translation ν x y j k l)
  simpa only [line_one_translation, line_zero, div_one] using hh

/-- Tensor-preserving first-order Hessian remainder at a common center. -/
theorem abs_convolutionSecondDerivative_remainder_le_tensor
    (x y : Fin p → ℝ) (j k : Fin p) {r : ℝ}
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hy : ‖y‖ ≤ r)
    (hH : ∀ z : Fin p → ℝ, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |s.convolutionSecondDerivative ν (x + y) j k -
      (s.convolutionSecondDerivative ν x j k +
        ∑ l, s.convolutionThirdDerivative ν x j k l * y l)| ≤
      (∑ l, ∑ m, H j k l m * |y l * y m|) / 2 := by
  obtain ⟨t, ht, hrem⟩ := s.exists_convolutionSecondDerivative_remainder ν x y j k
  have hz : ‖t • y‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have ht1 : t * ‖y‖ ≤ ‖y‖ := by nlinarith [norm_nonneg y, ht.2]
    exact ht1.trans hy
  have heq : line x y t = x + t • y := rfl
  have hb := abs_finite_weighted_sum_le
    (fun i : Fin p × Fin p => s.convolutionFourthDerivative ν (line x y t) j k i.1 i.2)
    (fun i : Fin p × Fin p => y i.1 * y i.2)
    (fun i : Fin p × Fin p => H j k i.1 i.2)
    (fun i => by rw [heq]; exact hH (t • y) hz j k i.1 i.2)
  have hb' : |∑ l, ∑ m, s.convolutionFourthDerivative ν (line x y t) j k l m * y l * y m| ≤
      ∑ l, ∑ m, H j k l m * |y l * y m| := by
    simpa only [Fintype.sum_prod_type, mul_assoc] using hb
  rw [hrem, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right hb' (by norm_num)

/-- Tensor-preserving third-derivative increment at a common center. -/
theorem abs_convolutionThirdDerivative_remainder_le_tensor
    (x y : Fin p → ℝ) (j k l : Fin p) {r : ℝ}
    (H : Fin p → Fin p → Fin p → Fin p → ℝ) (hy : ‖y‖ ≤ r)
    (hH : ∀ z : Fin p → ℝ, ‖z‖ ≤ r → ∀ j k l m,
      |s.convolutionFourthDerivative ν (x + z) j k l m| ≤ H j k l m) :
    |s.convolutionThirdDerivative ν (x + y) j k l -
      s.convolutionThirdDerivative ν x j k l| ≤
      ∑ m, H j k l m * |y m| := by
  obtain ⟨t, ht, hrem⟩ := s.exists_convolutionThirdDerivative_remainder ν x y j k l
  have hz : ‖t • y‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    have ht1 : t * ‖y‖ ≤ ‖y‖ := by nlinarith [norm_nonneg y, ht.2]
    exact ht1.trans hy
  have heq : line x y t = x + t • y := rfl
  rw [hrem]
  exact abs_finite_weighted_sum_le _ _ _
    (fun m => by rw [heq]; exact hH (t • y) hz j k l m)

end FaceSmoother
end RectangleCLT
