import RectangleCLTArxivV1.SupplementalHWeightedMass
import RectangleCLT.GaussianProjectionMaximum

/-! Actual Gaussian moments of the signed-face projection maximum. No
independence of the face projections or rank condition is imposed. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def supplementalHProjectionRadius {p r : ℕ} (U : Face p → Vector r) (g : Vector r) : ℝ :=
  1+‖linearProjectionFamily U g‖

theorem supplementalHProjectionRadius_ge_one {p r : ℕ} (U : Face p → Vector r) (g : Vector r) :
    1 ≤ supplementalHProjectionRadius U g := le_add_of_nonneg_right (norm_nonneg _)

theorem measurable_supplementalHProjectionRadius {p r : ℕ} (U : Face p → Vector r) :
    Measurable (supplementalHProjectionRadius U) :=
  measurable_const.add (measurable_linearProjectionFamily U).norm

theorem abs_faceDot_le_supplementalHProjectionRadius {p r : ℕ}
    (U : Face p → Vector r) (f : Face p) (g : Vector r) :
    |faceDot (U f) g| ≤ supplementalHProjectionRadius U g := by
  have hh := norm_le_pi_norm (linearProjectionFamily U g) f
  have hm : |faceDot (U f) g| ≤ ‖linearProjectionFamily U g‖ := by
    simpa only [Real.norm_eq_abs,linearProjectionFamily,faceDot] using hh
  exact hm.trans (le_add_of_nonneg_left zero_le_one)

private theorem supplementalH_face_card_exp {p : ℕ} (hp : 1 ≤ p) :
    2*(Fintype.card (Face p):ℝ) ≤ Real.exp (8*dimensionLog p) := by
  have hp1 : 1 ≤ (p:ℝ) := by exact_mod_cast hp
  have hp0 : 0 < (p:ℝ) := by linarith
  have hcard : 2*(Fintype.card (Face p):ℝ)=4*(p:ℝ) := by
    simp [Face,Fintype.card_prod]
    ring
  have hexp1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hexp8 : (256:ℝ) ≤ Real.exp 8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hexp1 8
    norm_num at hh
    simpa only [←Real.exp_nat_mul,show (8:ℝ)*1=8 by norm_num] using hh
  have hp8 : (p:ℝ) ≤ (p:ℝ)^8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hp1 (show 1≤8 by decide)
  have heq : Real.exp (8*dimensionLog p)=Real.exp 8*(p:ℝ)^8 := by
    rw [dimensionLog,Real.log_mul (Real.exp_ne_zero _) hp0.ne',Real.log_exp]
    rw [mul_add,mul_one,Real.exp_add]
    congr 1
    rw [show (8:ℝ)*Real.log (p:ℝ)=(8:ℕ)*Real.log (p:ℝ) by norm_num,
      Real.exp_nat_mul,Real.exp_log hp0]
  rw [hcard,heq]
  exact (show 4*(p:ℝ) ≤ 256*(p:ℝ)^8 by nlinarith).trans
    (mul_le_mul_of_nonneg_right hexp8 (pow_nonneg hp0.le 8))

/-- The first and third cases give the two cubic mass/projection budgets. -/
theorem supplementalHProjectionRadius_moment_le {p r : ℕ} (hp : 1 ≤ p)
    (U : Face p → Vector r) (hU : ∀ f, vectorNormSq (U f)=1) (q : ℕ) :
    Integrable (fun g => (supplementalHProjectionRadius U g)^q) (standardGaussian r) ∧
      (∫ g, (supplementalHProjectionRadius U g)^q ∂standardGaussian r) ≤
        (Real.sqrt (dimensionLog p))^q*Real.exp (8+((q+1:ℝ))^2/2) := by
  letI : Nonempty (Face p) := ⟨(⟨0,by omega⟩,true)⟩
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hi := projectionMaximum_weighted_moment_le (d := 1) U
    (fun f => by simpa only [vectorNormSq] using (hU f).le)
    (fun g => ‖linearProjectionFamily U g‖) (measurable_linearProjectionFamily U).norm
    (fun g => norm_nonneg _) hL (supplementalH_face_card_exp hp)
    (fun g => by simp) (le_refl (Real.sqrt (dimensionLog p))) q
  have hdom (g : Vector r) : (supplementalHProjectionRadius U g)^q ≤
      Real.exp (‖linearProjectionFamily U g‖/Real.sqrt (dimensionLog p))*
        (supplementalHProjectionRadius U g)^q := by
    have he : 1 ≤ Real.exp (‖linearProjectionFamily U g‖/Real.sqrt (dimensionLog p)) :=
      Real.one_le_exp (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    exact le_mul_of_one_le_left (pow_nonneg (by unfold supplementalHProjectionRadius; positivity) q) he
  have hplain : Integrable (fun g => (supplementalHProjectionRadius U g)^q) (standardGaussian r) := by
    apply hi.1.mono' ((measurable_supplementalHProjectionRadius U).pow_const q).aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg
        (zero_le_one.trans (supplementalHProjectionRadius_ge_one U g)) q)]
      exact hdom g)
  refine ⟨hplain,(integral_mono hplain hi.1 hdom).trans ?_⟩
  simpa only [supplementalHProjectionRadius,one_mul] using hi.2

end
end RectangleCLTArxivV1
