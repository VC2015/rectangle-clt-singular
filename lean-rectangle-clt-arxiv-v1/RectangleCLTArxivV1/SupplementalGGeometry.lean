import RectangleCLTArxivV1.SeededIntrinsic
import RectangleCLTCompanion.RestorationHessian

/-! The actual angular coefficient in Supplemental G's Hessian
decomposition. These finite-dimensional identities do not assume a
concentration or remainder estimate. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def capPairCoefficient {r : ℕ} (u v z w : Vector r) : ℝ :=
  dotProduct u z * dotProduct v w + dotProduct v z * dotProduct u w -
    dotProduct u v * (dotProduct u z * dotProduct u w + dotProduct v z * dotProduct v w)

def capSign (ρ : ℝ) : ℝ := if 0 ≤ ρ then 1 else -1

def capAngularDirection {r : ℕ} (u v : Vector r) : Vector r :=
  (1 / Real.sqrt (2*(1-|dotProduct u v|))) • (u-capSign (dotProduct u v) • v)

theorem vectorNormSq_eq_dot_self {r : ℕ} (u : Vector r) :
    vectorNormSq u = dotProduct u u := by simp [vectorNormSq, dotProduct, pow_two]

theorem dot_self_sub_smul {r : ℕ} (u v : Vector r) (s : ℝ) :
    dotProduct (u-s • v) (u-s • v) =
      dotProduct u u - 2*s*dotProduct u v + s^2*dotProduct v v := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, dotProduct_comm v u]
  simp only [smul_eq_mul]
  ring

theorem abs_dotProduct_unit_le_one {r : ℕ} (u v : Vector r)
    (hu : vectorNormSq u = 1) (hv : vectorNormSq v = 1) :
    |dotProduct u v| ≤ 1 := by
  rw [vectorNormSq_eq_dot_self] at hu hv
  have hp := vectorNormSq_nonneg (u-v)
  have hn := vectorNormSq_nonneg (u-(-1:ℝ) • v)
  rw [vectorNormSq_eq_dot_self, ← one_smul ℝ v, dot_self_sub_smul, hu, hv] at hp
  rw [vectorNormSq_eq_dot_self, dot_self_sub_smul, hu, hv] at hn
  rw [abs_le]
  constructor <;> norm_num at hp hn ⊢ <;> linarith

theorem capPairCoefficient_symmetric {r : ℕ} (u v z w : Vector r) :
    capPairCoefficient v u z w = capPairCoefficient u v z w := by
  unfold capPairCoefficient
  rw [dotProduct_comm v u]
  ring

theorem capPairCoefficient_equal {r : ℕ} (u z w : Vector r)
    (hu : vectorNormSq u = 1) : capPairCoefficient u u z w = 0 := by
  rw [vectorNormSq_eq_dot_self] at hu
  simp only [capPairCoefficient, hu, one_mul]
  ring

theorem capPairCoefficient_opposite {r : ℕ} (u z w : Vector r)
    (hu : vectorNormSq u = 1) : capPairCoefficient u (-u) z w = 0 := by
  rw [vectorNormSq_eq_dot_self] at hu
  simp only [capPairCoefficient, neg_dotProduct, dotProduct_neg, hu]
  ring

theorem capAngularDirection_projection {r : ℕ} (u v z : Vector r) :
    dotProduct (capAngularDirection u v) z =
      (dotProduct u z-capSign (dotProduct u v)*dotProduct v z) /
        Real.sqrt (2*(1-|dotProduct u v|)) := by
  simp only [capAngularDirection, smul_dotProduct, sub_dotProduct, smul_eq_mul]
  ring

theorem capAngularDirection_unit {r : ℕ} (u v : Vector r)
    (hu : vectorNormSq u = 1) (hv : vectorNormSq v = 1)
    (hnonparallel : |dotProduct u v| < 1) :
    vectorNormSq (capAngularDirection u v) = 1 := by
  have hc : 0 < 2*(1-|dotProduct u v|) := by linarith
  have hs := Real.sq_sqrt hc.le
  have hs0 := (Real.sqrt_pos.mpr hc).ne'
  rw [vectorNormSq_eq_dot_self] at hu hv ⊢
  simp only [capAngularDirection, smul_dotProduct, dotProduct_smul, smul_eq_mul, dot_self_sub_smul, hu, hv]
  by_cases hp : 0 ≤ dotProduct u v
  · simp only [capSign, if_pos hp, abs_of_nonneg hp]
    rw [abs_of_nonneg hp] at hs hs0
    field_simp only [hs0]
    nlinarith only [hs]
  · have hn := le_of_lt (lt_of_not_ge hp)
    simp only [capSign, if_neg hp, abs_of_nonpos hn]
    rw [abs_of_nonpos hn] at hs hs0
    field_simp only [hs0]
    nlinarith only [hs]

/-- The angle cancellation identity, with the exact normalized difference
direction of the printed Supplemental G proof. -/
theorem capPairCoefficient_angular_identity {r : ℕ} (u v z w : Vector r)
    (hnonparallel : |dotProduct u v| < 1) :
    capPairCoefficient u v z w =
      capSign (dotProduct u v)*(1-|dotProduct u v|)*
        (dotProduct u z*dotProduct u w + dotProduct v z*dotProduct v w -
          2*dotProduct (capAngularDirection u v) z*dotProduct (capAngularDirection u v) w) := by
  rw [capAngularDirection_projection, capAngularDirection_projection]
  have hc : 0 < 2*(1-|dotProduct u v|) := by linarith
  have hs := Real.sq_sqrt hc.le
  have hs0 := (Real.sqrt_pos.mpr hc).ne'
  unfold capPairCoefficient
  by_cases hp : 0 ≤ dotProduct u v
  · simp only [capSign, if_pos hp, abs_of_nonneg hp]
    rw [abs_of_nonneg hp] at hs hs0
    field_simp only [hs0]
    ring_nf at hs ⊢
    rw [hs]
    ring
  · have hn := le_of_lt (lt_of_not_ge hp)
    simp only [capSign, if_neg hp, abs_of_nonpos hn]
    rw [abs_of_nonpos hn] at hs hs0
    field_simp only [hs0]
    ring_nf at hs ⊢
    rw [hs]
    ring

/-- The original face envelope bounds the actual pair coefficient by
four times the squared envelope. -/
theorem capPairCoefficient_abs_le {r : ℕ} (u v z w : Vector r) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρ : |dotProduct u v| ≤ 1)
    (huz : |dotProduct u z| ≤ δ) (hvz : |dotProduct v z| ≤ δ)
    (huw : |dotProduct u w| ≤ δ) (hvw : |dotProduct v w| ≤ δ) :
    |capPairCoefficient u v z w| ≤ 4*δ^2 := by
  have h₁ := mul_le_mul huz hvw (abs_nonneg _) hδ
  have h₂ := mul_le_mul hvz huw (abs_nonneg _) hδ
  have h₃ := mul_le_mul huz huw (abs_nonneg _) hδ
  have h₄ := mul_le_mul hvz hvw (abs_nonneg _) hδ
  have hsum : |dotProduct u z*dotProduct u w + dotProduct v z*dotProduct v w| ≤ 2*δ^2 := by
    calc
      _ ≤ |dotProduct u z| *|dotProduct u w| + |dotProduct v z| *|dotProduct v w| := by
        simpa only [abs_mul] using abs_add (dotProduct u z*dotProduct u w) (dotProduct v z*dotProduct v w)
      _ ≤ _ := by nlinarith only [h₃,h₄]
  have hlast := mul_le_mul hρ hsum (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  unfold capPairCoefficient
  calc
    _ ≤ |dotProduct u z*dotProduct v w + dotProduct v z*dotProduct u w| +
        |dotProduct u v*(dotProduct u z*dotProduct u w+dotProduct v z*dotProduct v w)| := abs_sub _ _
    _ ≤ (|dotProduct u z| *|dotProduct v w|+|dotProduct v z| *|dotProduct u w|) + 2*δ^2 := by
      exact add_le_add (by simpa only [abs_mul] using abs_add (dotProduct u z*dotProduct v w) (dotProduct v z*dotProduct u w))
        (by simpa only [abs_mul,one_mul] using hlast)
    _ ≤ _ := by nlinarith only [h₁,h₂]

theorem cap_angle_loss_cancels {ρ : ℝ} (hρ : |ρ| < 1) :
    (1-|ρ|)/Real.sqrt (1-ρ^2) ≤ Real.sqrt (1-ρ^2) := by
  have hsq : 0 < 1-ρ^2 := by nlinarith [sq_abs ρ, abs_nonneg ρ]
  have hs := Real.sq_sqrt hsq.le
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hsq)).mpr
  nlinarith [sq_abs ρ, mul_nonneg (abs_nonneg ρ) (sub_nonneg.mpr hρ.le)]

end
end RectangleCLTArxivV1
