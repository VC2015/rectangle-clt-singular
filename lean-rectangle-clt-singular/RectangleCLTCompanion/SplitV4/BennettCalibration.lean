import RectangleCLTCompanion.SplitV4.BennettOptimization

/-! Exact deterministic calibration identities in the large-parameter
Bennett regime. The premises are scalar definitions of the bandwidth and
scales, rather than probabilistic estimates. -/

namespace RectangleCLT.Companion.SplitV4
noncomputable section

private theorem rpow_three_halves_eq {L : ℝ} (hL : 0 < L) :
    L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
  calc
    _ = L ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by congr 1; norm_num
    _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := Real.rpow_add hL _ _
    _ = _ := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

private theorem rpow_five_halves_eq {L : ℝ} (hL : 0 < L) :
    L ^ (5 / 2 : ℝ) = L * L ^ (3 / 2 : ℝ) := by
  calc
    _ = L ^ ((1 : ℝ) + (3 / 2 : ℝ)) := by congr 1; norm_num
    _ = _ := by rw [Real.rpow_add hL, Real.rpow_one]

/-- The exact four costs after the large-K bandwidth substitution.
All logarithmic powers are real powers of a strictly positive scalar.
No bound or asymptotic equivalence is used in place of an identity. -/
theorem bennett_large_calibration_identities
    {q d L A U V K ell r t u : ℝ}
    (hq : 0 < q) (hL : 0 < L) (hell : 0 < ell) (hK : 0 < K)
    (hr : 0 < r) (ht : 0 < t)
    (hU : U ^ 2 = d * L ^ (5 / 2 : ℝ))
    (hKV : V ^ 2 = K * U ^ 2)
    (hV : V = A * L ^ (3 / 2 - 1 / q : ℝ))
    (hrV : r * ell ^ (1 - 1 / q : ℝ) = V)
    (htR : t * L ^ (3 / 2 : ℝ) = r) (hu : u = ell * t) :
    u = A * (ell / L) ^ (1 / q : ℝ) ∧
      d * L / t = r * ell ^ (2 * (1 - 1 / q) : ℝ) / K ∧
      d ^ 2 * Real.sqrt L / t ^ 3 = r * ell ^ (4 * (1 - 1 / q) : ℝ) / K ^ 2 ∧
      Real.sqrt L * d * (A / t) ^ (q / 2 : ℝ) / t =
        r * ell ^ (2 * (1 - 1 / q) + (q - 1) / 2 : ℝ) / K := by
  let b := 1 - 1 / q
  have hL3 := rpow_three_halves_eq hL
  have hL5 := rpow_five_halves_eq hL
  have hell2 : ell ^ (2 * b) = (ell ^ b) ^ 2 := by
    rw [show (2 : ℝ) * b = b * 2 by ring, Real.rpow_mul hell.le, Real.rpow_two]
  have hell4 : ell ^ (4 * b) = (ell ^ (2 * b)) ^ 2 := by
    rw [show (4 : ℝ) * b = (2 * b) * 2 by ring, Real.rpow_mul hell.le, Real.rpow_two]
  have hr2 : r ^ 2 * ell ^ (2 * b) = V ^ 2 := by
    rw [hell2, ← mul_pow, hrV]
  have hfirstBase : d * L / t = U ^ 2 / r := by
    apply (div_eq_div_iff ht.ne' hr.ne').mpr
    rw [← htR, hU, hL5]
    ring
  have hfirst : d * L / t = r * ell ^ (2 * b) / K := by
    rw [hfirstBase]
    apply (div_eq_div_iff hr.ne' hK.ne').mpr
    calc
      _ = K * U ^ 2 := by ring
      _ = V ^ 2 := hKV.symm
      _ = _ := by rw [← hr2]; ring
  have hLsquare : Real.sqrt L * L ^ (3 / 2 : ℝ) = L ^ 2 := by
    rw [hL3]
    calc
      _ = L * (Real.sqrt L) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hL.le]; ring
  have hsecondBase : d ^ 2 * Real.sqrt L / t ^ 3 = (d * L / t) ^ 2 / r := by
    rw [div_pow, div_div]
    apply (div_eq_div_iff (pow_ne_zero 3 ht.ne') (mul_ne_zero (pow_ne_zero 2 ht.ne') hr.ne')).mpr
    rw [← htR]
    calc
      _ = d ^ 2 * t ^ 3 * (Real.sqrt L * L ^ (3 / 2 : ℝ)) := by ring
      _ = _ := by rw [hLsquare]; ring
  have hsecond : d ^ 2 * Real.sqrt L / t ^ 3 = r * ell ^ (4 * b) / K ^ 2 := by
    rw [hsecondBase, hfirst, hell4]
    field_simp [hK.ne', hr.ne']
    ring
  have hLsplit : L ^ (3 / 2 : ℝ) = L ^ (3 / 2 - 1 / q : ℝ) * L ^ (1 / q : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hden : L ^ (3 / 2 - 1 / q : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hL _).ne'
  have hProd : t * L ^ (1 / q : ℝ) * ell ^ b = A := by
    apply mul_left_cancel₀ hden
    calc
      _ = (t * L ^ (3 / 2 : ℝ)) * ell ^ b := by rw [hLsplit]; ring
      _ = V := by rw [htR, hrV]
      _ = L ^ (3 / 2 - 1 / q : ℝ) * A := by rw [hV]; ring
  have hAt : A / t = L ^ (1 / q : ℝ) * ell ^ b := by
    apply (div_eq_iff ht.ne').mpr
    rw [← hProd]
    ring
  have hellsum : ell ^ b * ell ^ (1 / q : ℝ) = ell := by
    rw [← Real.rpow_add hell]
    change ell ^ ((1 - 1 / q) + 1 / q : ℝ) = ell
    rw [show ((1 - 1 / q) + 1 / q : ℝ) = 1 by ring, Real.rpow_one]
  have hu' : u = A * (ell / L) ^ (1 / q : ℝ) := by
    have hLi : L ^ (1 / q : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hL _).ne'
    symm
    calc
      _ = (t * L ^ (1 / q : ℝ) * ell ^ b) *
          (ell ^ (1 / q : ℝ) / L ^ (1 / q : ℝ)) := by rw [hProd, Real.div_rpow hell.le hL.le]
      _ = t * (ell ^ b * ell ^ (1 / q : ℝ)) := by field_simp [hLi]; ring
      _ = t * ell := by rw [hellsum]
      _ = u := by rw [hu]; ring
  have hApow : (A / t) ^ (q / 2 : ℝ) = Real.sqrt L * ell ^ ((q - 1) / 2 : ℝ) := by
    rw [hAt, Real.mul_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hell.le _),
      ← Real.rpow_mul hL.le, ← Real.rpow_mul hell.le]
    have he₁ : (1 / q) * (q / 2) = (1 / 2 : ℝ) := by field_simp [hq.ne']
    have he₂ : b * (q / 2) = (q - 1) / 2 := by dsimp only [b]; field_simp [hq.ne']
    rw [he₁, he₂, ← Real.sqrt_eq_rpow]
  refine ⟨hu', hfirst, hsecond, ?_⟩
  calc
    _ = (d * L / t) * ell ^ ((q - 1) / 2 : ℝ) := by
      rw [hApow]
      calc
        _ = d * ((Real.sqrt L) ^ 2) / t * ell ^ ((q - 1) / 2 : ℝ) := by ring
        _ = _ := by rw [Real.sq_sqrt hL.le]
    _ = r * (ell ^ (2 * b) * ell ^ ((q - 1) / 2 : ℝ)) / K := by rw [hfirst]; ring
    _ = _ := by rw [← Real.rpow_add hell]

/-- The two terms in the Bennett expected-maximum bound and its logarithm
have exactly the required large-regime scales. -/
theorem bennett_large_tail_identities
    {q d L A U V K ell r t u : ℝ}
    (hq : 0 < q) (hL : 0 < L) (hell : 0 < ell) (hK : 0 < K)
    (hr : 0 < r) (ht : 0 < t)
    (hU : U ^ 2 = d * L ^ (5 / 2 : ℝ))
    (hKV : V ^ 2 = K * U ^ 2)
    (hV : V = A * L ^ (3 / 2 - 1 / q : ℝ))
    (hrV : r * ell ^ (1 - 1 / q : ℝ) = V)
    (htR : t * L ^ (3 / 2 : ℝ) = r) (hu : u = ell * t) :
    Real.sqrt L * u * L = r * ell ∧
      Real.sqrt L * A ^ q / u ^ (q - 1 : ℝ) = r ∧
      u ^ 2 * L / (d * (A / t) ^ (q / 2 : ℝ)) =
        K * ell ^ (2 / q - (q - 1) / 2 : ℝ) := by
  have hc := bennett_large_calibration_identities hq hL hell hK hr ht hU hKV hV hrV htR hu
  have hu' := hc.1
  have hfirst := hc.2.1
  have hMixed := hc.2.2.2
  let b := 1 - 1 / q
  let e := (q - 1) / 2
  have hL3 := rpow_three_halves_eq hL
  have hu0 : 0 < u := by rw [hu]; exact mul_pos hell ht
  have hApos : 0 < A := by
    have hh : 0 < A * (ell / L) ^ (1 / q : ℝ) := by rw [← hu']; exact hu0
    exact pos_of_mul_pos_left hh (Real.rpow_pos_of_pos (div_pos hell hL) _).le
  have hdne : d ≠ 0 := by
    intro hd
    have hh : 0 < r * ell ^ (2 * (1 - 1 / q) : ℝ) / K := by positivity
    rw [← hfirst, hd, zero_mul, zero_div] at hh
    exact (lt_irrefl 0) hh
  have huq : u ^ q = A ^ q * ell / L := by
    rw [hu', Real.mul_rpow hApos.le (Real.rpow_nonneg (div_pos hell hL).le _),
      ← Real.rpow_mul (div_pos hell hL).le]
    have he : (1 / q) * q = (1 : ℝ) := by field_simp [hq.ne']
    rw [he, Real.rpow_one]
    ring
  have hM₁ : Real.sqrt L * u * L = r * ell := by
    rw [hu, ← htR, hL3]
    ring
  have htail : A ^ q / u ^ (q - 1 : ℝ) = u * L / ell := by
    rw [Real.rpow_sub hu0, Real.rpow_one, huq]
    field_simp [hL.ne', hell.ne', hu0.ne', (Real.rpow_pos_of_pos hApos q).ne'] <;> ring
  have hM₂ : Real.sqrt L * A ^ q / u ^ (q - 1 : ℝ) = r := by
    calc
      _ = Real.sqrt L * (A ^ q / u ^ (q - 1 : ℝ)) := by ring
      _ = (Real.sqrt L * u * L) / ell := by rw [htail]; ring
      _ = r := by rw [hM₁]; field_simp [hell.ne']
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hAp : 0 < (A / t) ^ (q / 2 : ℝ) := Real.rpow_pos_of_pos (div_pos hApos ht) _
  have hellp : 0 < ell ^ (2 * b + e) := Real.rpow_pos_of_pos hell _
  have hbudget : d * (A / t) ^ (q / 2 : ℝ) * K = t ^ 2 * L * ell ^ (2 * b + e) := by
    apply mul_left_cancel₀ hroot.ne'
    calc
      _ = (Real.sqrt L * d * (A / t) ^ (q / 2 : ℝ) / t) * (t * K) := by
        field_simp [ht.ne'] <;> ring
      _ = (r * ell ^ (2 * b + e) / K) * (t * K) := by rw [hMixed]
      _ = r * ell ^ (2 * b + e) * t := by field_simp [hK.ne'] <;> ring
      _ = Real.sqrt L * (t ^ 2 * L * ell ^ (2 * b + e)) := by
        rw [← htR, hL3]
        ring
  have hratio : u ^ 2 * L / (d * (A / t) ^ (q / 2 : ℝ)) =
      K * ell ^ 2 / ell ^ (2 * b + e) := by
    apply (div_eq_div_iff (mul_ne_zero hdne hAp.ne') hellp.ne').mpr
    rw [hu]
    calc
      _ = ell ^ 2 * (t ^ 2 * L * ell ^ (2 * b + e)) := by ring
      _ = _ := by rw [← hbudget]; ring
  refine ⟨hM₁, hM₂, ?_⟩
  rw [hratio]
  calc
    _ = K * (ell ^ (2 : ℝ) / ell ^ (2 * b + e)) := by rw [Real.rpow_two]; ring
    _ = K * ell ^ ((2 : ℝ) - (2 * b + e)) := by rw [← Real.rpow_sub hell]
    _ = _ := by congr 1; congr 1; dsimp only [b, e]; ring

end
end RectangleCLT.Companion.SplitV4
