import RectangleCLTCompanion.SplitV4.SymmetricFamilyCount
import RectangleCLTCompanion.SplitV4.RectangularGaussianLaw

/-! The actual independent Gaussian pair counterpart of the masked common family. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def familyGaussianFactor (P : SymmetricFamilyParameters) (m : ℕ) :
    Matrix (Fin (m * m)) (Fin m ⊕ Fin m) ℝ :=
  fun r => additiveGridFactor m P.scale (Real.sqrt P.variance) (finProdFinEquiv.symm r)

theorem familyGaussianFactor_mulVec (P : SymmetricFamilyParameters) {m : ℕ}
    (z : (Fin m ⊕ Fin m) → ℝ) (r : Fin (m * m)) :
    (familyGaussianFactor P m).mulVec z r = P.scale * z (Sum.inl (finProdFinEquiv.symm r).1) +
      Real.sqrt P.variance * z (Sum.inr (finProdFinEquiv.symm r).2) :=
  additiveGridFactor_mulVec P.scale (Real.sqrt P.variance) z (finProdFinEquiv.symm r)

theorem familyGaussianFactor_gram (P : SymmetricFamilyParameters) (m : ℕ) :
    familyGaussianFactor P m * (familyGaussianFactor P m).transpose = familyCovariance m P.variance := by
  ext r r'
  change (additiveGridFactor m P.scale (Real.sqrt P.variance) *
    (additiveGridFactor m P.scale (Real.sqrt P.variance)).transpose)
      (finProdFinEquiv.symm r) (finProdFinEquiv.symm r') = _
  rw [additiveGridFactor_gram, P.scale_sq, Real.sq_sqrt P.variance_pos.le]
  rfl

def familyGaussianPairLaw (m : ℕ) : Measure (Vector m × Vector m) := (standardGaussian m).prod (standardGaussian m)
instance familyGaussianPairLaw_probability (m : ℕ) : IsProbabilityMeasure (familyGaussianPairLaw m) := by
  unfold familyGaussianPairLaw
  infer_instance

def familyGaussianPairMap (P : SymmetricFamilyParameters) {m : ℕ} (z : Vector m × Vector m) : Vector (m * m) :=
  fun r => P.scale * z.1 (finProdFinEquiv.symm r).1 + Real.sqrt P.variance * z.2 (finProdFinEquiv.symm r).2

theorem measurable_familyGaussianPairMap (P : SymmetricFamilyParameters) (m : ℕ) :
    Measurable (familyGaussianPairMap P : Vector m × Vector m → Vector (m * m)) := by
  apply measurable_pi_lambda
  intro r
  exact (measurable_const.mul ((measurable_pi_apply _).comp measurable_fst)).add
    (measurable_const.mul ((measurable_pi_apply _).comp measurable_snd))

theorem familyGaussianPairMap_law (P : SymmetricFamilyParameters) (m : ℕ) :
    (familyGaussianPairLaw m).map (familyGaussianPairMap P) = rectangularGaussianLaw (familyGaussianFactor P m) := by
  have hp := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin m ⊕ Fin m => gaussianReal 0 1)
  unfold rectangularGaussianLaw finiteStandardGaussian
  rw [← hp.map_eq, Measure.map_map (measurable_rectangularMulVec _) hp.measurable]
  apply Measure.map_congr
  exact ae_of_all _ (fun z => by
    funext r
    rw [Function.comp_apply, familyGaussianFactor_mulVec]
    rfl)

theorem familyCovariance_factor_exists (P : SymmetricFamilyParameters) (m : ℕ) :
    ∃ A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ, A * A.transpose = familyCovariance m P.variance := by
  have hL2 (r : Fin (m * m)) : MemLp (fun z : FamilySeed m => familyObservation P z r) 2 (familySeedLaw P m) :=
    memLp_family_finite _ _ 2
  obtain ⟨A, hA⟩ := gaussian_factor_exists_of_coordinate_memLp_two (familyObservation P) hL2 (integral_familyObservation P)
  have hcov : covariance (familySeedLaw P m) (familyObservation P) = familyCovariance m P.variance := by
    ext r r'
    simp only [covariance, integral_familyObservation, mul_zero, sub_zero]
    exact integral_familyObservation_product P r r'
  exact ⟨A, hA.trans hcov⟩

theorem familyGaussianPairMap_eq_gaussianLaw (P : SymmetricFamilyParameters) {m : ℕ}
    (A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ) (hA : A * A.transpose = familyCovariance m P.variance) :
    (familyGaussianPairLaw m).map (familyGaussianPairMap P) = gaussianLaw A := by
  rw [familyGaussianPairMap_law]
  exact rectangularGaussianLaw_eq_gaussianLaw _ A ((familyGaussianFactor_gram P m).trans hA.symm)

theorem familyGaussianPairMap_maximum (P : SymmetricFamilyParameters) {m : ℕ} [NeZero m]
    (z : Vector m × Vector m) :
    finiteMaximum (fun ju : Fin m × Fin m => familyGaussianPairMap P z (finProdFinEquiv ju)) =
      P.scale * finiteMaximum z.1 + Real.sqrt P.variance * finiteMaximum z.2 := by
  simp only [familyGaussianPairMap, Equiv.symm_apply_apply]
  exact finiteMaximum_separable z.1 z.2 P.scale_pos.le (Real.sqrt_nonneg _)

theorem familyGaussian_maxima_independent (m : ℕ) [NeZero m] :
    IndepFun (fun z : Vector m × Vector m => finiteMaximum z.1)
      (fun z => finiteMaximum z.2) (familyGaussianPairLaw m) := by
  have hi : IndepFun Prod.fst Prod.snd ((standardGaussian m).prod (standardGaussian m)) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable measurable_snd.aemeasurable).mpr
    simp only [show (fun z : Vector m × Vector m => (z.1, z.2)) = id from rfl,
      Measure.map_id, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul]
  exact hi.comp (measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j))
    (measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j))

end
end RectangleCLT.Companion.SplitV4
