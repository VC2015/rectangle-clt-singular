import RectangleCLTCompanion.RestorationGaussianIBP

/-! Rectangular Gaussian-factor version of the second Stein identity.  The
ambient covariance can be singular: no inverse or determinant of the factor
matrix occurs. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p r : ℕ}

theorem restorationAffine_update (A : Matrix (Fin p) (Fin r) ℝ)
    (x : Vector p) (g : Vector r) (j : Fin r) (t : ℝ) :
    A.mulVec (Function.update g j t) + x =
      FaceSmoother.line (A.mulVec g + x) (fun l => A l j) (t - g j) := by
  classical
  have heq : Function.update g j t =
      g + (t - g j) • (Pi.single j (1 : ℝ) : Vector r) := by
    ext k
    by_cases hk : k = j
    · subst k; simp
    · simp [Function.update_of_ne hk, Pi.single_eq_of_ne hk]
  rw [heq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  ext l
  simp only [FaceSmoother.line, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.transpose_apply]
  ring

theorem hasDerivAt_restorationAffine_slice
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (F : Vector p → ℝ) (D : Vector p → Fin p → ℝ)
    (hF : ∀ a y, HasDerivAt (fun t => F (FaceSmoother.line a y t))
      (∑ l, D a l * y l) 0)
    (g : Vector r) (j : Fin r) :
    HasDerivAt (fun t => F (A.mulVec (Function.update g j t) + x))
      (∑ l, D (A.mulVec g + x) l * A l j) (g j) := by
  have hd0 : HasDerivAt
      (fun a => F (FaceSmoother.line (A.mulVec g + x) (fun l => A l j) a))
      (∑ l, D (A.mulVec g + x) l * A l j) (g j - g j) := by
    simpa only [sub_self] using hF (A.mulVec g + x) (fun l => A l j)
  have hd := hd0.comp (h := fun t : ℝ => t - g j) (g j)
    ((hasDerivAt_id (g j)).sub_const (g j))
  simpa only [Function.comp_apply, mul_one, restorationAffine_update] using hd

private theorem bounded_finite_sum_mul {ι X : Type*} [Fintype ι]
    (f : ι → X → ℝ) (a : ι → ℝ)
    (hf : ∀ i, ∃ C : ℝ, ∀ x, |f i x| ≤ C) :
    ∃ C : ℝ, ∀ x, |∑ i, f i x * a i| ≤ C := by
  choose C hC using hf
  refine ⟨∑ i, C i * |a i|, fun x => ?_⟩
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hC i x) (abs_nonneg _)

private theorem continuous_restorationAffine (A : Matrix (Fin p) (Fin r) ℝ)
    (x : Vector p) : Continuous (fun g => A.mulVec g + x) := by
  apply Continuous.add _ continuous_const
  apply continuous_pi
  intro l
  change Continuous (fun g : Vector r => ∑ j, A l j * g j)
  exact continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_apply j))

theorem restoration_matrixQuadratic_mulVec
    (A : Matrix (Fin p) (Fin r) ℝ) (B : Matrix (Fin p) (Fin p) ℝ) (z : Vector r) :
    matrixQuadratic B (A.mulVec z) =
      matrixQuadratic (A.transpose * (B * A)) z := by
  have hquad {q : ℕ} (C : Matrix (Fin q) (Fin q) ℝ) (u : Vector q) :
      matrixQuadratic C u = dotProduct u (C.mulVec u) := by
    simp only [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hquad, hquad, ← Matrix.mulVec_mulVec z A.transpose (B * A),
    ← Matrix.mulVec_mulVec z B A, Matrix.mulVec_transpose]
  rw [dotProduct_comm (A.mulVec z), Matrix.dotProduct_mulVec, dotProduct_comm]

/-- Actual second Gaussian integration by parts for an arbitrary bounded
twice differentiable observed-space jet, pulled back through a rectangular
factor.  All hypotheses concern ordinary derivatives and bounded functions;
the Gaussian identity is proved, not supplied as an analytic premise. -/
theorem restorationAffine_second_stein
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (F : Vector p → ℝ) (D : Vector p → Fin p → ℝ)
    (DD : Vector p → Fin p → Fin p → ℝ)
    (hF : ∀ a y, HasDerivAt (fun t => F (FaceSmoother.line a y t))
      (∑ l, D a l * y l) 0)
    (hD : ∀ a y l, HasDerivAt (fun t => D (FaceSmoother.line a y t) l)
      (∑ m, DD a l m * y m) 0)
    (hFm : Measurable F) (hDm : ∀ l, Measurable (fun a => D a l))
    (hDDm : ∀ l m, Measurable (fun a => DD a l m))
    (hFb : ∃ C : ℝ, ∀ a, |F a| ≤ C)
    (hDb : ∀ l, ∃ C : ℝ, ∀ a, |D a l| ≤ C)
    (hDDb : ∀ l m, ∃ C : ℝ, ∀ a, |DD a l m| ≤ C)
    (z : Vector r) :
    (∫ g, repeatedDirectionScore g z * F (A.mulVec g + x) ∂standardGaussian r) =
      ∫ g, matrixQuadratic (DD (A.mulVec g + x)) (A.mulVec z) ∂standardGaussian r := by
  let f : Vector r → ℝ := fun g => F (A.mulVec g + x)
  let d : Fin r → Vector r → ℝ := fun j g => ∑ l, D (A.mulVec g + x) l * A l j
  let dd : Fin r → Fin r → Vector r → ℝ :=
    fun j k g => ∑ l, (∑ m, DD (A.mulVec g + x) l m * A m k) * A l j
  have hf (j : Fin r) (g : Vector r) :
      HasDerivAt (fun t => f (Function.update g j t)) (d j g) (g j) :=
    hasDerivAt_restorationAffine_slice A x F D hF g j
  have hd (j k : Fin r) (g : Vector r) :
      HasDerivAt (fun t => d j (Function.update g k t)) (dd j k g) (g k) := by
    exact HasDerivAt.sum (fun l _ =>
      (hasDerivAt_restorationAffine_slice A x (fun a => D a l)
        (fun a m => DD a l m) (fun a y => hD a y l) g k).mul_const (A l j))
  have hm := (continuous_restorationAffine A x).measurable
  have hdm (j : Fin r) : Measurable (d j) :=
    Finset.measurable_sum _ (fun l _ => (hDm l |>.comp hm).mul_const _)
  have hddm (j k : Fin r) : Measurable (dd j k) :=
    Finset.measurable_sum _ (fun l _ =>
      (Finset.measurable_sum _ (fun m _ => (hDDm l m |>.comp hm).mul_const _)).mul_const _)
  have hdb (j : Fin r) : ∃ C : ℝ, ∀ g, |d j g| ≤ C := by
    apply bounded_finite_sum_mul _ (fun l => A l j)
    intro l
    obtain ⟨C, hC⟩ := hDb l
    exact ⟨C, fun g => hC (A.mulVec g + x)⟩
  have hddb (j k : Fin r) : ∃ C : ℝ, ∀ g, |dd j k g| ≤ C := by
    apply bounded_finite_sum_mul _ (fun l => A l j)
    intro l
    apply bounded_finite_sum_mul _ (fun m => A m k)
    intro m
    obtain ⟨C, hC⟩ := hDDb l m
    exact ⟨C, fun g => hC (A.mulVec g + x)⟩
  have hfb : ∃ C : ℝ, ∀ g, |f g| ≤ C := by
    obtain ⟨C, hC⟩ := hFb
    exact ⟨C, fun g => hC (A.mulVec g + x)⟩
  have hs := standardGaussian_second_directional_stein_bounded f d dd hf hd
    (hFm.comp hm) hdm hddm hfb hdb hddb z
  convert hs using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun g => by
    dsimp only [dd]
    rw [restoration_matrixQuadratic_mulVec]
    congr 1
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    ring)

end
end RectangleCLT.Companion
