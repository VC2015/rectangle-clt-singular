import RectangleCLT.GaussianThirdMajorant
import RectangleCLT.SmootherStability

/-! Stability of the concrete positive Gaussian soft-face moments. These
pointwise comparisons provide uniform majorants on the Taylor remainder cube. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem softFaceWeight_shift_le (S : Finset (Face p)) (x : Vector p)
    {z : Vector p} {r : ℝ} (hz : ‖z‖ ≤ r) :
    s.softFaceWeight S (x + z) ≤
      Real.exp ((1 + 2 * (S.card : ℝ)) * r / s.bandwidth) * s.softFaceWeight S x := by
  have hprod : (∏ f ∈ S, (s.weights (x + z)).pi f) ≤
      ∏ f ∈ S, Real.exp (2 * r / s.bandwidth) * (s.weights x).pi f := by
    exact Finset.prod_le_prod (fun f _ => (s.weights (x + z)).pi_nonneg f)
      (fun f _ => s.pi_shift_le x hz f)
  have hexp : Real.exp (r / s.bandwidth) *
      Real.exp (2 * r / s.bandwidth) ^ S.card =
        Real.exp ((1 + 2 * (S.card : ℝ)) * r / s.bandwidth) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (Real.exp (r / s.bandwidth) * s.F x) *
        ∏ f ∈ S, Real.exp (2 * r / s.bandwidth) * (s.weights x).pi f :=
      mul_le_mul (s.F_shift_le x hz) hprod
        (Finset.prod_nonneg fun f _ => (s.weights (x + z)).pi_nonneg f)
        (mul_nonneg (Real.exp_nonneg _) (s.weights x).F_pos.le)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      unfold softFaceWeight
      rw [← hexp]
      ring

theorem gaussianSoftFaceMoment_shift_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (S : Finset (Face p)) (k : ℕ) {z : Vector p} {r : ℝ} (hz : ‖z‖ ≤ r) :
    s.gaussianSoftFaceMoment A (x + z) S k ≤
      Real.exp ((1 + 2 * (S.card : ℝ)) * r / s.bandwidth) *
        s.gaussianSoftFaceMoment A x S k := by
  unfold gaussianSoftFaceMoment
  rw [← integral_const_mul]
  apply integral_mono
    (s.integrable_gaussianSoftFaceMoment hp A (x + z) S k)
    ((s.integrable_gaussianSoftFaceMoment hp A x S k).const_mul _)
  intro w
  have hpoly : 0 ≤ (1 + fourFaceProjectionRadius A w) ^ k :=
    pow_nonneg (by linarith [fourFaceProjectionRadius_nonneg A w]) k
  have hb := mul_le_mul_of_nonneg_left (s.softFaceWeight_shift_le S (A.mulVec w + x) hz) hpoly
  simpa only [add_assoc, mul_left_comm] using hb

theorem softFaceWeight_shift_le_exp_nine (S : Finset (Face p)) (hS : S.card ≤ 4)
    (x : Vector p) {z : Vector p} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r ≤ s.bandwidth) :
    s.softFaceWeight S (x + z) ≤ Real.exp 9 * s.softFaceWeight S x := by
  apply (s.softFaceWeight_shift_le S x hz).trans
  apply mul_le_mul_of_nonneg_right _ (s.softFaceWeight_nonneg S x)
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ s.bandwidth_pos).mpr
  have hcard : (S.card : ℝ) ≤ 4 := by exact_mod_cast hS
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  nlinarith

theorem gaussianSoftFaceMoment_shift_le_exp_nine (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (S : Finset (Face p)) (hS : S.card ≤ 4) (k : ℕ)
    {z : Vector p} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r ≤ s.bandwidth) :
    s.gaussianSoftFaceMoment A (x + z) S k ≤
      Real.exp 9 * s.gaussianSoftFaceMoment A x S k := by
  apply (s.gaussianSoftFaceMoment_shift_le hp A x S k hz).trans
  apply mul_le_mul_of_nonneg_right _ (s.gaussianSoftFaceMoment_nonneg A x S k)
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ s.bandwidth_pos).mpr
  have hcard : (S.card : ℝ) ≤ 4 := by exact_mod_cast hS
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  nlinarith

end
end RectangleCLT.FaceSmoother
