import RectangleCLTCompanion.SplitV4.SmootherC4
import RectangleCLTCompanion.FourthIdentityTaylor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Canonical C4 Taylor identities for an arbitrary actual smooth test.
The tensors are iterated Fréchet derivatives, rather than supplied Taylor
remainders or probabilistic comparison premises. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem hasDerivAt_iteratedFDeriv_segment {p k : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (hk : k < 4) (x v : Vector p)
    (w : Fin k → Vector p) (a r : ℝ) :
    HasDerivAt (fun t => iteratedFDeriv ℝ k F (x+(a*t) • v) w)
      (a*iteratedFDeriv ℝ (k+1) F (x+(a*r) • v) (Fin.cons v w)) r := by
  let y := x+(a*r) • v
  have hd := ((hF.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast hk)) y).hasFDerivAt
  have he := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Vector p) ℝ w).hasFDerivAt.comp y hd
  have hl : HasDerivAt (fun t : ℝ => x+(a*t) • v) (a • v) r := by
    simpa only [mul_one] using (((hasDerivAt_id r).const_mul a).smul_const v).const_add x
  have hh := he.comp_hasDerivAt r hl
  simpa only [y, ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply,
    map_smul, smul_eq_mul, iteratedFDeriv_succ_apply_left,
    Fin.cons_zero, Fin.tail_cons] using hh

def canonicalDiagonal {p : ℕ} (F : Vector p → ℝ) (k : ℕ) (x v : Vector p) : ℝ :=
  iteratedFDeriv ℝ k F x (fun _ => v)

theorem hasDerivAt_canonicalDiagonal_segment {p k : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (hk : k < 4) (x v : Vector p) (a r : ℝ) :
    HasDerivAt (fun t => canonicalDiagonal F k (x+(a*t) • v) v)
      (a*canonicalDiagonal F (k+1) (x+(a*r) • v) v) r := by
  have he : Fin.cons v (fun _ : Fin k => v) = (fun _ : Fin (k+1) => v) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simpa only [canonicalDiagonal, he] using
    hasDerivAt_iteratedFDeriv_segment hF hk x v (fun _ => v) a r

theorem canonical_value_taylor_four {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x v : Vector p) (a : ℝ) :
    F (x+a • v) - (F x+a*canonicalDiagonal F 1 x v+
      a^2/2*canonicalDiagonal F 2 x v+a^3/6*canonicalDiagonal F 3 x v) =
      ∫ r in (0 : ℝ)..1, a^4/6*(1-r)^3*canonicalDiagonal F 4 (x+(a*r) • v) v := by
  have hcont : Continuous (fun r => canonicalDiagonal F 4 (x+r • v) v) :=
    ((hF.continuous_iteratedFDeriv (m := 4) (by norm_num)).comp
      (show Continuous (fun r : ℝ => x+r • v) from
        continuous_const.add (continuous_id.smul continuous_const))).eval continuous_const
  have hh := RectangleCLT.Companion.integral_taylor_four
    (fun r => canonicalDiagonal F 0 (x+r • v) v)
    (fun r => canonicalDiagonal F 1 (x+r • v) v)
    (fun r => canonicalDiagonal F 2 (x+r • v) v)
    (fun r => canonicalDiagonal F 3 (x+r • v) v)
    (fun r => canonicalDiagonal F 4 (x+r • v) v)
    (fun r => by simpa only [one_mul] using hasDerivAt_canonicalDiagonal_segment hF (k := 0) (by decide) x v 1 r)
    (fun r => by simpa only [one_mul] using hasDerivAt_canonicalDiagonal_segment hF (k := 1) (by decide) x v 1 r)
    (fun r => by simpa only [one_mul] using hasDerivAt_canonicalDiagonal_segment hF (k := 2) (by decide) x v 1 r)
    (fun r => by simpa only [one_mul] using hasDerivAt_canonicalDiagonal_segment hF (k := 3) (by decide) x v 1 r)
    hcont a
  simpa only [canonicalDiagonal, iteratedFDeriv_zero_apply, zero_smul, add_zero] using hh

theorem canonical_gradient_taylor_three {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x v : Vector p) (a : ℝ) :
    canonicalDiagonal F 1 (x+a • v) v - (canonicalDiagonal F 1 x v+
      a*canonicalDiagonal F 2 x v+a^2/2*canonicalDiagonal F 3 x v) =
      ∫ r in (0 : ℝ)..1, a^3/2*(1-r)^2*canonicalDiagonal F 4 (x+(a*r) • v) v := by
  have hcont : Continuous (fun r => canonicalDiagonal F 4 (x+r • v) v) :=
    ((hF.continuous_iteratedFDeriv (m := 4) (by norm_num)).comp
      (show Continuous (fun r : ℝ => x+r • v) from
        continuous_const.add (continuous_id.smul continuous_const))).eval continuous_const
  have hh := RectangleCLT.Companion.integral_taylor_three
    (fun r => canonicalDiagonal F 1 (x+r • v) v)
    (fun r => canonicalDiagonal F 2 (x+r • v) v)
    (fun r => canonicalDiagonal F 3 (x+r • v) v)
    (fun r => canonicalDiagonal F 4 (x+r • v) v)
    (fun r => by simpa only [one_mul] using hasDerivAt_canonicalDiagonal_segment hF (k := 1) (by decide) x v 1 r)
    (fun r => by simpa only [one_mul] using hasDerivAt_canonicalDiagonal_segment hF (k := 2) (by decide) x v 1 r)
    (fun r => by simpa only [one_mul] using hasDerivAt_canonicalDiagonal_segment hF (k := 3) (by decide) x v 1 r)
    hcont a
  simpa only [zero_smul, add_zero] using hh

theorem canonical_hessian_taylor_two {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x u v : Vector p) (a : ℝ) :
    iteratedFDeriv ℝ 2 F (x+a • v) (fun _ => u) -
      (iteratedFDeriv ℝ 2 F x (fun _ => u)+
        a*iteratedFDeriv ℝ 3 F x (Fin.cons v (fun _ => u))) =
      ∫ r in (0 : ℝ)..1, a^2*(1-r)*
        iteratedFDeriv ℝ 4 F (x+(a*r) • v) (Fin.cons v (Fin.cons v (fun _ => u))) := by
  have hc : Continuous (fun r => iteratedFDeriv ℝ 4 F (x+r • v)
      (Fin.cons v (Fin.cons v (fun _ : Fin 2 => u)))) :=
    ((hF.continuous_iteratedFDeriv (m := 4) (by norm_num)).comp
      (show Continuous (fun r : ℝ => x+r • v) from
        continuous_const.add (continuous_id.smul continuous_const))).eval continuous_const
  have hh := RectangleCLT.Companion.integral_taylor_two
    (fun r => iteratedFDeriv ℝ 2 F (x+r • v) (fun _ => u))
    (fun r => iteratedFDeriv ℝ 3 F (x+r • v) (Fin.cons v (fun _ => u)))
    (fun r => iteratedFDeriv ℝ 4 F (x+r • v) (Fin.cons v (Fin.cons v (fun _ => u))))
    (fun r => by simpa only [one_mul] using hasDerivAt_iteratedFDeriv_segment hF (k := 2) (by decide) x v (fun _ => u) 1 r)
    (fun r => by simpa only [one_mul] using hasDerivAt_iteratedFDeriv_segment hF (k := 3) (by decide) x v (Fin.cons v (fun _ => u)) 1 r)
    hc a
  simpa only [zero_smul, add_zero] using hh

theorem canonical_third_taylor_one {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x u v : Vector p) (a : ℝ) :
    iteratedFDeriv ℝ 3 F (x+a • v) (fun _ => u)-iteratedFDeriv ℝ 3 F x (fun _ => u) =
      ∫ r in (0 : ℝ)..1, a*iteratedFDeriv ℝ 4 F (x+(a*r) • v) (Fin.cons v (fun _ => u)) := by
  have hc : Continuous (fun r => iteratedFDeriv ℝ 4 F (x+r • v) (Fin.cons v (fun _ : Fin 3 => u))) :=
    ((hF.continuous_iteratedFDeriv (m := 4) (by norm_num)).comp
      (show Continuous (fun r : ℝ => x+r • v) from
        continuous_const.add (continuous_id.smul continuous_const))).eval continuous_const
  have hh := RectangleCLT.Companion.integral_taylor_one
    (fun r => iteratedFDeriv ℝ 3 F (x+r • v) (fun _ => u))
    (fun r => iteratedFDeriv ℝ 4 F (x+r • v) (Fin.cons v (fun _ => u)))
    (fun r => by simpa only [one_mul] using hasDerivAt_iteratedFDeriv_segment hF (k := 3) (by decide) x v (fun _ => u) 1 r)
    hc a
  simpa only [zero_smul, add_zero] using hh

end
end RectangleCLT.Companion.SplitV4
