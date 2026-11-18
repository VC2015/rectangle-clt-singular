import RectangleCLTArxivV1.HFourthCubicRestoration

/-! Exact extraction of the signed cubic matrix at a common Gaussian base.
No nuclear estimate is used in these identities. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem hFourth_sum_singleton_tuples {p : ℕ} (F : (Fin 1 → Face p) → ℝ) :
    (∑ α, F α)=∑ f : Face p, F ![f] := by
  rw [sum_face_tuples_cons]
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro f _
  congr 1

theorem hFourth_trace_rankOneSum_mul {Ω : Type*} {n r : ℕ}
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) (ω : Ω)
    (M : Matrix (Fin r) (Fin r) ℝ) :
    Matrix.trace (restorationRankOneSum Z c ω*M)=∑ i, c i ω*matrixQuadratic M (Z i ω) := by
  have he : restorationRankOneSum Z c ω=∑ i, c i ω • rankOne (Z i ω) := by
    ext j k
    simp [restorationRankOneSum,rankOne,Matrix.sum_apply]
  rw [he,Matrix.sum_mul,Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_mul,Matrix.trace_smul,Matrix.trace_mul_comm,trace_mul_rankOne,smul_eq_mul]

theorem hFourth_trace_cubicScore_eq_integral {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (U : Face p → Vector r) (V : Ω → Vector p) (α : Fin (K+1) → Face p) (ω : Ω)
    (B : Matrix (Fin r) (Fin r) ℝ) :
    Matrix.trace (B*hFourthCubicGaussianScore s A U V α ω)=
      ∫ g, Matrix.trace (B*capThirdHermiteMatrix (U (α 0)) g)*
        selectorTupleWeight s α (A.mulVec g+V ω) ∂standardGaussian r := by
  have hi (j k : Fin r) :=
    (hFourthCubicGaussianScore_integrable_entry s A U V α ω k j).const_mul (B j k)
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,hFourthCubicGaussianScore]
  simp_rw [← integral_const_mul]
  have he (j : Fin r) :
      (∑ k, ∫ g, B j k*(capThirdHermiteMatrix (U (α 0)) g k j*
        selectorTupleWeight s α (A.mulVec g+V ω)) ∂standardGaussian r)=
      ∫ g, ∑ k, B j k*(capThirdHermiteMatrix (U (α 0)) g k j*
        selectorTupleWeight s α (A.mulVec g+V ω)) ∂standardGaussian r :=
    (integral_finset_sum _ (fun k _ => hi j k)).symm
  simp_rw [he]
  rw [← integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hi j k))]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    dsimp only
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring)

theorem hFourth_integrable_fixed_cubicScore_weight {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (u Z : Vector r) (x : Vector p) (α : Fin K → Face p) :
    Integrable (fun g => capThirdHermiteScore u Z g*
      selectorTupleWeight s α (A.mulVec g+x)) (standardGaussian r) := by
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      (capThirdHermiteMatrix_integrable u j k).const_mul (Z j*Z k)))
  have hs : Integrable (fun g => capThirdHermiteScore u Z g) (standardGaussian r) := by
    convert hi using 1
    funext g
    rw [capThirdHermiteScore_eq_matrixQuadratic]
    simp only [matrixQuadratic]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hw : Measurable (fun g : Vector r => selectorTupleWeight s α (A.mulVec g+x)) :=
    measurable_selectorTupleWeight_comp s α _
      ((continuous_const.matrix_mulVec continuous_id).measurable.add_const x)
  simpa only [mul_comm] using hs.bdd_mul' hw.aestronglyMeasurable
    (ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (selectorTupleWeight_nonneg s α _)]
      exact selectorTupleWeight_le_one s α _))

/-- Deterministic Gaussian coefficient extraction at a fixed base and
fixed array. This is the identity used before conditional averaging. -/
theorem hFourth_fixed_cubic_restoration_order {p r n : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (x : Vector p) (Z : Fin n → Vector r) (c : Fin n → Face p → ℝ)
    (v : Fin n → Vector p) (ℓ : ℕ) :
    (∫ g, ∑ i, ∑ f : Face p,
      (c i f*capThirdHermiteScore (U f) (Z i) g)*
        restorationSeriesTerm s ![f] (A.mulVec g+x) (v i) ℓ ∂standardGaussian r)=
      (-1:ℝ)^ℓ*((1+ℓ).choose ℓ:ℝ)*
        ∑ γ : Fin (ℓ+1) → Face p,
          Matrix.trace (restorationRankOneSum (fun i (_ : Unit) => Z i)
            (fun i _ => c i (γ 0)*restorationTranslationCoefficient s ![γ 0] (Fin.tail γ) (v i)) ()*
              hFourthCubicGaussianScore s A U (fun _ : Unit => x) γ ()) := by
  classical
  let a := (-1:ℝ)^ℓ*((1+ℓ).choose ℓ:ℝ)
  let F := fun (i : Fin n) (f : Face p) (β : Fin ℓ → Face p) (g : Vector r) =>
    (c i f*restorationTranslationCoefficient s ![f] β (v i))*
      capThirdHermiteScore (U f) (Z i) g*
        selectorTupleWeight s (Fin.cons f β) (A.mulVec g+x)
  have hi (i : Fin n) (f : Face p) (β : Fin ℓ → Face p) :
      Integrable (F i f β) (standardGaussian r) := by
    simpa only [F,mul_assoc] using (hFourth_integrable_fixed_cubicScore_weight s A (U f) (Z i) x (Fin.cons f β)).const_mul
      (c i f*restorationTranslationCoefficient s ![f] β (v i))
  have hp (i : Fin n) (f : Face p) (g : Vector r) :
      (c i f*capThirdHermiteScore (U f) (Z i) g)*restorationSeriesTerm s ![f] (A.mulVec g+x) (v i) ℓ=
        a*∑ β : Fin ℓ → Face p, F i f β g := by
    unfold restorationSeriesTerm
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    simp [F,selectorTupleWeight,Fin.prod_univ_succ]
    dsimp only [a]
    ring
  have he (f : Face p) (β : Fin ℓ → Face p) :
      Matrix.trace (restorationRankOneSum (fun i (_ : Unit) => Z i)
        (fun i _ => c i f*restorationTranslationCoefficient s ![f] β (v i)) ()*
          hFourthCubicGaussianScore s A U (fun _ : Unit => x) (Fin.cons f β) ())=
        ∫ g, ∑ i, F i f β g ∂standardGaussian r := by
    rw [hFourth_trace_cubicScore_eq_integral]
    simp only [hFourth_trace_rankOneSum_mul,← capThirdHermiteScore_eq_matrixQuadratic,
      Fin.cons_zero,Finset.sum_mul]
    rfl
  simp_rw [hp]
  simp_rw [← Finset.mul_sum]
  rw [integral_const_mul]
  unfold a
  congr 1
  rw [sum_face_tuples_cons]
  simp only [Fin.cons_zero,Fin.tail_cons]
  simp_rw [he]
  have hswap (g : Vector r) : (∑ i, ∑ f, ∑ β, F i f β g)=∑ f, ∑ β, ∑ i, F i f β g := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun f _ => Finset.sum_comm)
  simp_rw [hswap]
  rw [integral_finset_sum _ (fun f _ => integrable_finset_sum _ (fun β _ =>
    integrable_finset_sum _ (fun i _ => hi i f β)))]
  exact Finset.sum_congr rfl (fun f _ => integral_finset_sum _ (fun β _ =>
    integrable_finset_sum _ (fun i _ => hi i f β)))

end
end RectangleCLTArxivV1
