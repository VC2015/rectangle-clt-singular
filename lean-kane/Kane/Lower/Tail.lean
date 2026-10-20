import Kane.Lower.PaleyZygmund
import Kane.Lower.Threshold
import Kane.Lower.Exponential

/-! Genuine halfspace tail witnesses obtained by exponential Paley--Zygmund. -/

open scoped BigOperators

namespace Kane.Lower

theorem avg_exp_signedSum_sq (n : ℕ) (t : ℝ) :
    avg (fun x : Cube n => Real.exp (t * signedSum (fun _ => true) x) ^ 2) =
      Real.cosh (2 * t) ^ n := by
  have hpoint (x : Cube n) :
      Real.exp (t * signedSum (fun _ => true) x) ^ 2 =
        Real.exp ((2 * t) * signedSum (fun _ => true) x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  exact avg_exp_signedSum _ _

/-- The exponentially tilted cube sum has a quantitatively nonempty upper tail. -/
theorem exponential_paley (n : ℕ) (t η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    Real.exp (-2 * (n : ℝ) * t ^ 2) * (1 - η) ^ 2 ≤
      avg (fun x : Cube n =>
        if η * Real.cosh t ^ n ≤ Real.exp (t * signedSum (fun _ => true) x)
        then (1 : ℝ) else 0) := by
  have hmean : 0 < avg (fun x : Cube n => Real.exp (t * signedSum (fun _ => true) x)) := by
    rw [avg_exp_signedSum]
    positivity
  have hsecond : 0 < avg (fun x : Cube n => Real.exp (t * signedSum (fun _ => true) x) ^ 2) := by
    rw [avg_exp_signedSum_sq]
    positivity
  have hp := paley_zygmund
    (fun x : Cube n => Real.exp (t * signedSum (fun _ => true) x))
    (fun x => (Real.exp_pos _).le) hmean hsecond η hη hη1
  rw [avg_exp_signedSum, avg_exp_signedSum_sq] at hp
  have hM : 1 ≤ Real.cosh t ^ n := by
    have hh := one_add_n_half_sq_le_cosh_pow n t
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (sq_nonneg t)]
  have hBpos : 0 < Real.cosh (2 * t) ^ n := by positivity
  have hB : Real.cosh (2 * t) ^ n ≤ Real.exp (2 * (n : ℝ) * t ^ 2) := by
    have hh := avg_exp_signedSum_le (n := n) (fun _ => true) (2 * t)
    rw [avg_exp_signedSum] at hh
    convert hh using 1
    congr 1
    ring
  have hnum : (1 - η) ^ 2 ≤ (1 - η) ^ 2 * (Real.cosh t ^ n) ^ 2 := by
    have hsq : 1 ≤ (Real.cosh t ^ n) ^ 2 := by nlinarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq (sq_nonneg (1 - η))
  calc
    _ = (1 - η) ^ 2 / Real.exp (2 * (n : ℝ) * t ^ 2) := by
      rw [show -2 * (n : ℝ) * t ^ 2 = -(2 * (n : ℝ) * t ^ 2) by ring, Real.exp_neg]
      ring
    _ ≤ (1 - η) ^ 2 / (Real.cosh (2 * t) ^ n) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hBpos hB
    _ ≤ (1 - η) ^ 2 * (Real.cosh t ^ n) ^ 2 / (Real.cosh (2 * t) ^ n) :=
      div_le_div_of_nonneg_right hnum hBpos.le
    _ ≤ _ := hp

/-- Exponentiating the uniform halfspace threshold gives the Paley event exactly. -/
theorem uniformHalfspace_exponential_mass_ge (n : ℕ) (t η : ℝ)
    (ht : 0 < t) (hη : 0 < η) (hη1 : η ≤ 1) :
    Real.exp (-2 * (n : ℝ) * t ^ 2) * (1 - η) ^ 2 ≤
      avg (fun x => boolVal ((uniformHalfspace n
        (Real.log (η * Real.cosh t ^ n) / t)).indicator x)) := by
  have hp := exponential_paley n t η hη.le hη1
  calc
    _ ≤ _ := hp
    _ = _ := by
      apply avg_congr
      intro x
      have harg : 0 < η * Real.cosh t ^ n := by positivity
      have hevent : Real.log (η * Real.cosh t ^ n) / t ≤ signedSum (fun _ => true) x ↔
          η * Real.cosh t ^ n ≤ Real.exp (t * signedSum (fun _ => true) x) := by
        rw [div_le_iff₀ ht, mul_comm (signedSum (fun _ => true) x) t]
        exact Real.log_le_iff_le_exp harg
      simp [uniformHalfspace_indicator, boolVal, hevent]

theorem half_tilt_threshold (n : ℕ) (t : ℝ) :
    Real.log ((1 / 2 : ℝ) * Real.cosh t ^ n) / t = tiltThreshold n t := by
  unfold tiltThreshold
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (by positivity), Real.log_pow]
  have hh : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hh]
  ring

/-- Large logarithms admit a real uniform halfspace with mass at least `exp(-L)`
and a threshold bounded below by a universal multiple of `sqrt(n L)`. -/
theorem large_halfspace_witness {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 64 ≤ L) (hLn : L ≤ (n : ℝ)) :
    ∃ a : ℝ, Real.sqrt ((n : ℝ) * L) / 64 ≤ a ∧
      Real.exp (-L) ≤ avg (fun x => boolVal ((uniformHalfspace n a).indicator x)) := by
  refine ⟨tiltThreshold n (largeTilt n L), largeTilt_threshold_lower hn hL hLn, ?_⟩
  have hp := uniformHalfspace_exponential_mass_ge n (largeTilt n L) (1 / 2)
    (largeTilt_pos hn (by linarith)) (by norm_num) (by norm_num)
  rw [half_tilt_threshold] at hp
  have hp' : Real.exp (-2 * (n : ℝ) * (largeTilt n L) ^ 2) / 4 ≤
      avg (fun x => boolVal ((uniformHalfspace n (tiltThreshold n (largeTilt n L))).indicator x)) := by
    convert hp using 1
    norm_num
    ring
  exact (largeTilt_probability_lower hn hL).trans hp'

/-- A fixed-mass halfspace supplies the positive `sqrt n` lower bound needed
when `log k` is bounded. -/
theorem small_halfspace_witness {n : ℕ} (hn : 0 < n) :
    ∃ a : ℝ, Real.log (9 / 8 : ℝ) * Real.sqrt (n : ℝ) ≤ a ∧
      Real.exp (-2) / 16 ≤
        avg (fun x => boolVal ((uniformHalfspace n a).indicator x)) := by
  refine ⟨Real.log ((3 / 4 : ℝ) * Real.cosh (smallTilt n) ^ n) / smallTilt n,
    smallTilt_threshold_lower hn, ?_⟩
  have hp := uniformHalfspace_exponential_mass_ge n (smallTilt n) (3 / 4)
    (smallTilt_pos hn) (by norm_num) (by norm_num)
  have hp' : Real.exp (-2 * (n : ℝ) * (smallTilt n) ^ 2) / 16 ≤
      avg (fun x => boolVal ((uniformHalfspace n
        (Real.log ((3 / 4 : ℝ) * Real.cosh (smallTilt n) ^ n) / smallTilt n)).indicator x)) := by
    convert hp using 1
    norm_num
    ring
  rw [smallTilt_probability_eq hn] at hp'
  exact hp'

end Kane.Lower
