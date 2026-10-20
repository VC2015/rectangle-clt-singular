import RectangleCLT.GaussianTriple
import RectangleCLT.GaussianNormalMap
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection

/-! Concrete affine Gaussian sections.  The section law is the pushforward of
an actual product standard Gaussian under orthogonal projection onto a unit
normal's affine hyperplane.  Its signed second moment is proved from the
coordinate moments, including when the ambient dimension is zero. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal InnerProductSpace

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

/-- Orthogonal residual, written in coordinates so that the Euclidean norm
is never confused with the maximum norm of the native product. -/
def gaussianSectionResidual {r : ℕ} (u z : Vector r) : Vector r :=
  z - faceDot u z • u

/-- An actual point on the affine hyperplane with unit normal `u` and
signed distance `a`. -/
def gaussianSectionPoint {r : ℕ} (u : Vector r) (a : ℝ) (z : Vector r) : Vector r :=
  a • u + gaussianSectionResidual u z

theorem measurable_gaussianSectionResidual {r : ℕ} (u : Vector r) :
    Measurable (gaussianSectionResidual u) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply j).sub
    ((Finset.measurable_sum _ (fun k _ => measurable_const.mul (measurable_pi_apply k))).mul
      measurable_const)

theorem measurable_gaussianSectionPoint {r : ℕ} (u : Vector r) (a : ℝ) :
    Measurable (gaussianSectionPoint u a) := by
  exact measurable_const.add (measurable_gaussianSectionResidual u)

def gaussianSectionLaw {r : ℕ} (u : Vector r) (a : ℝ) : Measure (Vector r) :=
  (standardGaussian r).map (gaussianSectionPoint u a)

instance gaussianSectionLaw_probability {r : ℕ} (u : Vector r) (a : ℝ) :
    IsProbabilityMeasure (gaussianSectionLaw u a) := by
  unfold gaussianSectionLaw
  exact isProbabilityMeasure_map (measurable_gaussianSectionPoint u a).aemeasurable

theorem gaussianSectionPoint_eq {r : ℕ} (u : Vector r) (a : ℝ) (z : Vector r) :
    gaussianSectionPoint u a z = z + (a - faceDot u z) • u := by
  ext j
  simp only [gaussianSectionPoint, gaussianSectionResidual, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem faceDot_add_smul_self {r : ℕ} (u z : Vector r) (t : ℝ) :
    faceDot u (z + t • u) = faceDot u z + t * vectorNormSq u := by
  simp only [faceDot, vectorNormSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gaussianSectionPoint_on_hyperplane {r : ℕ} (u : Vector r) (a : ℝ)
    (hu : vectorNormSq u = 1) (z : Vector r) :
    faceDot u (gaussianSectionPoint u a z) = a := by
  rw [gaussianSectionPoint_eq, faceDot_add_smul_self, hu]
  ring

/-- This algebraic identity is independent of probability. -/
theorem vectorNormSq_gaussianSectionResidual {r : ℕ} (u z : Vector r)
    (hu : vectorNormSq u = 1) :
    vectorNormSq (gaussianSectionResidual u z) = vectorNormSq z - faceDot u z ^ 2 := by
  unfold vectorNormSq gaussianSectionResidual
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sq, mul_pow]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmiddle : (∑ j, 2 * z j * (faceDot u z * u j)) = 2 * faceDot u z * faceDot u z := by
    calc
      _ = ∑ j, (2 * faceDot u z) * (u j * z j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hlast : (∑ j, faceDot u z ^ 2 * u j ^ 2) = faceDot u z ^ 2 := by
    rw [← Finset.mul_sum]
    change faceDot u z ^ 2 * vectorNormSq u = faceDot u z ^ 2
    rw [hu, mul_one]
  rw [hmiddle, hlast]
  ring

theorem vectorNormSq_gaussianSectionPoint {r : ℕ} (u : Vector r) (a : ℝ)
    (hu : vectorNormSq u = 1) (z : Vector r) :
    vectorNormSq (gaussianSectionPoint u a z) =
      vectorNormSq z - faceDot u z ^ 2 + a ^ 2 := by
  have hp : gaussianSectionPoint u a z = z + (a - faceDot u z) • u := by
    ext j
    simp only [gaussianSectionPoint, gaussianSectionResidual, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hp]
  unfold vectorNormSq
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sq, mul_pow]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hmiddle : (∑ j, 2 * z j * ((a - faceDot u z) * u j)) =
      2 * (a - faceDot u z) * faceDot u z := by
    unfold faceDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hlast : (∑ j, (a - faceDot u z) ^ 2 * u j ^ 2) = (a - faceDot u z) ^ 2 := by
    rw [← Finset.mul_sum]
    change (a - faceDot u z) ^ 2 * vectorNormSq u = (a - faceDot u z) ^ 2
    rw [hu, mul_one]
  rw [hmiddle, hlast]
  ring

theorem standardGaussian_integrable_vectorNormSq (r : ℕ) :
    Integrable (fun z : Vector r => vectorNormSq z) (standardGaussian r) :=
  integrable_finset_sum Finset.univ
    (fun j _ => standardGaussian_integrable_coordinate_pow r j 2)

theorem standardGaussian_integral_vectorNormSq (r : ℕ) :
    (∫ z : Vector r, vectorNormSq z ∂standardGaussian r) = r := by
  unfold vectorNormSq
  rw [integral_finset_sum Finset.univ
    (fun j _ => standardGaussian_integrable_coordinate_pow r j 2)]
  simp only [standardGaussian_integral_coordinate_sq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem standardGaussian_integrable_faceDot_sq {r : ℕ} (u : Vector r) :
    Integrable (fun z => faceDot u z ^ 2) (standardGaussian r) := by
  simpa only [sq] using standardGaussian_integrable_faceDot_product u u

theorem standardGaussian_integral_faceDot_sq {r : ℕ} (u : Vector r) :
    (∫ z, faceDot u z ^ 2 ∂standardGaussian r) = vectorNormSq u := by
  classical
  have hexpand (z : Vector r) : faceDot u z ^ 2 =
      ∑ j, ∑ k, (u j * u k) * (z j * z k) := by
    unfold faceDot
    rw [sq, Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hi (j k : Fin r) : Integrable
      (fun z : Vector r => (u j * u k) * (z j * z k)) (standardGaussian r) :=
    (standardGaussian_integrable_coordinate_product r j k).const_mul _
  simp_rw [hexpand]
  rw [integral_finset_sum Finset.univ
    (fun j _ => integrable_finset_sum Finset.univ (fun k _ => hi j k))]
  simp_rw [integral_finset_sum Finset.univ (fun k _ => hi _ k), integral_const_mul,
    standardGaussian_integral_coordinate_product]
  simp [vectorNormSq, sq]

theorem standardGaussian_integrable_sectionResidual_normSq {r : ℕ} (u : Vector r)
    (hu : vectorNormSq u = 1) :
    Integrable (fun z => vectorNormSq (gaussianSectionResidual u z)) (standardGaussian r) := by
  simp_rw [vectorNormSq_gaussianSectionResidual u _ hu]
  exact (standardGaussian_integrable_vectorNormSq r).sub
    (standardGaussian_integrable_faceDot_sq u)

/-- The exact dimension drop of an orthogonal Gaussian residual. -/
theorem standardGaussian_integral_sectionResidual_normSq {r : ℕ} (u : Vector r)
    (hu : vectorNormSq u = 1) :
    (∫ z, vectorNormSq (gaussianSectionResidual u z) ∂standardGaussian r) = (r : ℝ) - 1 := by
  simp_rw [vectorNormSq_gaussianSectionResidual u _ hu]
  rw [integral_sub (standardGaussian_integrable_vectorNormSq r)
    (standardGaussian_integrable_faceDot_sq u), standardGaussian_integral_vectorNormSq,
    standardGaussian_integral_faceDot_sq, hu]

theorem standardGaussian_integrable_sectionPoint_normSq {r : ℕ} (u : Vector r) (a : ℝ)
    (hu : vectorNormSq u = 1) :
    Integrable (fun z => vectorNormSq (gaussianSectionPoint u a z)) (standardGaussian r) := by
  simp_rw [vectorNormSq_gaussianSectionPoint u a hu]
  exact ((standardGaussian_integrable_vectorNormSq r).sub
    (standardGaussian_integrable_faceDot_sq u)).add (integrable_const _)

/-- The signed Gaussian score on an actual affine hyperplane section has
mean `a²−1`. The ambient dimension cancels exactly. -/
theorem standardGaussian_integral_section_score {r : ℕ} (u : Vector r) (a : ℝ)
    (hu : vectorNormSq u = 1) :
    (∫ z, (vectorNormSq (gaussianSectionPoint u a z) - (r : ℝ))
      ∂standardGaussian r) = a ^ 2 - 1 := by
  have hpoint : (∫ z, vectorNormSq (gaussianSectionPoint u a z)
      ∂standardGaussian r) = (r : ℝ) - 1 + a ^ 2 := by
    simp_rw [vectorNormSq_gaussianSectionPoint u a hu]
    calc
      _ = (∫ z, vectorNormSq z - faceDot u z ^ 2 ∂standardGaussian r) + a ^ 2 := by
        simpa only [Pi.sub_apply, integral_const, measureReal_univ_eq_one, one_smul] using
          integral_add ((standardGaussian_integrable_vectorNormSq r).sub
            (standardGaussian_integrable_faceDot_sq u)) (integrable_const (a ^ 2))
      _ = _ := by
        rw [integral_sub (standardGaussian_integrable_vectorNormSq r)
          (standardGaussian_integrable_faceDot_sq u), standardGaussian_integral_vectorNormSq,
          standardGaussian_integral_faceDot_sq, hu]

  rw [integral_sub (standardGaussian_integrable_sectionPoint_normSq u a hu)
    (integrable_const (r : ℝ)), hpoint]
  simp
  ring

/-- The affine section's genuine probability law, rather than a moment
assumption about a named Gaussian law. -/
theorem gaussianSectionLaw_integral_score {r : ℕ} (u : Vector r) (a : ℝ)
    (hu : vectorNormSq u = 1) :
    (∫ x, (vectorNormSq x - (r : ℝ)) ∂gaussianSectionLaw u a) = a ^ 2 - 1 := by
  unfold gaussianSectionLaw
  rw [integral_map (measurable_gaussianSectionPoint u a).aemeasurable]
  · exact standardGaussian_integral_section_score u a hu
  · exact ((Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).pow_const 2)).sub
      measurable_const).aestronglyMeasurable

/-- A volume-preserving transformation preserving the actual density
preserves the resulting measure. -/
theorem measurePreserving_withDensity_of_invariant
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (ρ : X → ℝ≥0∞)
    (hρ : Measurable ρ) (hinv : ∀ x, ρ (e x) = ρ x) :
    MeasurePreserving e (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨e.measurable, Measure.ext (fun s hs => ?_)⟩
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  calc
    _ = ∫⁻ x in e ⁻¹' s, ρ (e x) ∂μ := by simp_rw [hinv]
    _ = _ := he.setLIntegral_comp_preimage hs hρ

/-- A Euclidean isometry transported to the project's concrete product
coordinates. -/
def gaussianRotation {r : ℕ}
    (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) :
    Vector r ≃ᵐ Vector r :=
  (EuclideanSpace.measurableEquiv (Fin r)).symm.trans
    (e.toMeasurableEquiv.trans (EuclideanSpace.measurableEquiv (Fin r)))

theorem gaussianRotation_volume_preserving {r : ℕ}
    (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) :
    MeasurePreserving (gaussianRotation e) volume volume := by
  exact (EuclideanSpace.volume_preserving_measurableEquiv (Fin r)).comp
    (e.measurePreserving.comp (PiLp.volume_preserving_equiv_symm (Fin r)))

theorem vectorNormSq_eq_euclidean_norm_sq {r : ℕ} (x : Vector r) :
    vectorNormSq x = ‖(WithLp.equiv 2 (Vector r)).symm x‖ ^ 2 := by
  symm
  simpa [vectorNormSq, Real.norm_eq_abs, sq_abs] using
    PiLp.norm_sq_eq_of_L2 (fun _ : Fin r => ℝ) ((WithLp.equiv 2 (Vector r)).symm x)

theorem vectorNormSq_gaussianRotation {r : ℕ}
    (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (x : Vector r) :
    vectorNormSq (gaussianRotation e x) = vectorNormSq x := by
  rw [vectorNormSq_eq_euclidean_norm_sq, vectorNormSq_eq_euclidean_norm_sq]
  change ‖e ((WithLp.equiv 2 (Vector r)).symm x)‖ ^ 2 = _
  rw [e.norm_map]

/-- Orthogonal invariance of the actual finite product Gaussian, derived
from its concrete Lebesgue density and volume-preserving isometries. -/
theorem gaussianRotation_standardGaussian_preserving {r : ℕ}
    (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) :
    MeasurePreserving (gaussianRotation e) (standardGaussian r) (standardGaussian r) := by
  rw [standardGaussian_eq_withDensity]
  apply measurePreserving_withDensity_of_invariant _
    (gaussianRotation_volume_preserving e)
    (fun x => ENNReal.ofReal (standardGaussianDensity r x))
    (standardGaussianDensity_measurable r).ennreal_ofReal
  intro x
  congr 1
  simp only [standardGaussianDensity_eq_kernel, gaussianKernel,
    vectorNormSq_gaussianRotation]

theorem gaussianRotation_add {r : ℕ}
    (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (x y : Vector r) :
    gaussianRotation e (x + y) = gaussianRotation e x + gaussianRotation e y := by
  change (WithLp.equiv 2 (Vector r))
      (e ((WithLp.equiv 2 (Vector r)).symm (x + y))) = _
  rw [show (WithLp.equiv 2 (Vector r)).symm (x + y) =
    (WithLp.equiv 2 (Vector r)).symm x + (WithLp.equiv 2 (Vector r)).symm y from rfl,
    map_add]
  rfl

theorem gaussianRotation_smul {r : ℕ}
    (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (a : ℝ) (x : Vector r) : gaussianRotation e (a • x) = a • gaussianRotation e x := by
  change (WithLp.equiv 2 (Vector r))
      (e ((WithLp.equiv 2 (Vector r)).symm (a • x))) = _
  rw [show (WithLp.equiv 2 (Vector r)).symm (a • x) =
    a • (WithLp.equiv 2 (Vector r)).symm x from rfl, map_smul]
  rfl

theorem faceDot_eq_euclidean_inner {r : ℕ} (x y : Vector r) :
    faceDot x y = ⟪(WithLp.equiv 2 (Vector r)).symm x,
      (WithLp.equiv 2 (Vector r)).symm y⟫_ℝ := by
  simp only [PiLp.inner_apply, faceDot, RCLike.inner_apply', conj_trivial]
  rfl

theorem gaussianRotation_faceDot {r : ℕ}
    (e : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (x y : Vector r) :
    faceDot (gaussianRotation e x) (gaussianRotation e y) = faceDot x y := by
  rw [faceDot_eq_euclidean_inner, faceDot_eq_euclidean_inner]
  change ⟪e ((WithLp.equiv 2 (Vector r)).symm x),
    e ((WithLp.equiv 2 (Vector r)).symm y)⟫_ℝ = _
  exact e.inner_map_map _ _

/-- Genuine Fubini along the affine hyperplanes obtained from an arbitrary
orthogonal frame. No conditional Gaussian identity is assumed. -/
theorem standardGaussian_integral_rotated_sections {n : ℕ}
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) {f : Vector (n + 1) → ℝ}
    (hf : Integrable f (standardGaussian (n + 1))) :
    (∫ x, f x ∂standardGaussian (n + 1)) =
      ∫ y : Vector n, ∫ t : ℝ, f (gaussianRotation e (j.insertNth t y))
        ∂gaussianReal 0 1 ∂standardGaussian n := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  let T := split.symm.trans (gaussianRotation e)
  have hsplit : MeasurePreserving split (standardGaussian (n + 1))
      ((gaussianReal 0 1).prod (standardGaussian n)) :=
    measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) j
  have hT : MeasurePreserving T ((gaussianReal 0 1).prod (standardGaussian n))
      (standardGaussian (n + 1)) :=
    (gaussianRotation_standardGaussian_preserving e).comp (hsplit.symm split)
  have hfi : Integrable (fun z => f (T z))
      ((gaussianReal 0 1).prod (standardGaussian n)) :=
    (hT.integrable_comp_emb T.measurableEmbedding).mpr hf
  calc
    _ = ∫ z : ℝ × Vector n, f (T z)
        ∂(gaussianReal 0 1).prod (standardGaussian n) := (hT.integral_comp' f).symm
    _ = _ := by
      simpa [T, split, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using
        integral_prod_symm (fun z : ℝ × Vector n => f (T z)) hfi

/-- An explicit orthogonal map carrying a chosen coordinate unit normal to
any prescribed unit normal. A Householder reflection also handles equality. -/
def coordinateNormalRotation {r : ℕ} (j : Fin r) (u : Vector r) :
    EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r) :=
  (ℝ ∙ ((WithLp.equiv 2 (Vector r)).symm (Pi.single j 1) -
    (WithLp.equiv 2 (Vector r)).symm u))ᗮ.reflection

theorem coordinateNormalRotation_unit {r : ℕ} (j : Fin r) (u : Vector r)
    (hu : vectorNormSq u = 1) :
    gaussianRotation (coordinateNormalRotation j u) (Pi.single j 1) = u := by
  have hnormu : ‖(WithLp.equiv 2 (Vector r)).symm u‖ = 1 := by
    have hh := vectorNormSq_eq_euclidean_norm_sq u
    rw [hu] at hh
    nlinarith [norm_nonneg ((WithLp.equiv 2 (Vector r)).symm u)]
  have hnormj : ‖(WithLp.equiv 2 (Vector r)).symm (Pi.single j 1)‖ = 1 := by
    rw [← EuclideanSpace.single, EuclideanSpace.norm_single]
    norm_num
  have hh := Submodule.reflection_sub (hnormj.trans hnormu.symm)
  change (WithLp.equiv 2 (Vector r))
      (coordinateNormalRotation j u ((WithLp.equiv 2 (Vector r)).symm (Pi.single j 1))) = u
  rw [show coordinateNormalRotation j u ((WithLp.equiv 2 (Vector r)).symm (Pi.single j 1)) =
      (WithLp.equiv 2 (Vector r)).symm u from hh]
  rfl

/-- An actual orthogonal chart of the hyperplanes normal to `u`. -/
def normalSectionChart {n : ℕ} (j : Fin (n + 1)) (u : Vector (n + 1))
    (t : ℝ) (y : Vector n) : Vector (n + 1) :=
  gaussianRotation (coordinateNormalRotation j u) (j.insertNth t y)

theorem normalSectionChart_on_hyperplane {n : ℕ}
    (j : Fin (n + 1)) (u : Vector (n + 1)) (hu : vectorNormSq u = 1)
    (t : ℝ) (y : Vector n) : faceDot u (normalSectionChart j u t y) = t := by
  change faceDot u (gaussianRotation (coordinateNormalRotation j u) (j.insertNth t y)) = t
  calc
    _ = faceDot (gaussianRotation (coordinateNormalRotation j u) (Pi.single j 1))
        (gaussianRotation (coordinateNormalRotation j u) (j.insertNth t y)) := by
      rw [coordinateNormalRotation_unit j u hu]
    _ = faceDot (Pi.single j 1) (j.insertNth t y) := gaussianRotation_faceDot _ _ _
    _ = t := by simp [faceDot, Pi.single_apply, ite_mul]

theorem insertNth_eq_single_add_zero {n : ℕ} (j : Fin (n + 1)) (t : ℝ)
    (y : Vector n) : j.insertNth t y =
      t • (Pi.single j (1 : ℝ) : Vector (n + 1)) +
        (j.insertNth (0 : ℝ) y : Vector (n + 1)) := by
  ext k
  by_cases hk : k = j
  · subst k
    simp
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    simp

theorem normalSectionChart_eq_normal_add_base {n : ℕ}
    (j : Fin (n + 1)) (u : Vector (n + 1)) (hu : vectorNormSq u = 1)
    (t : ℝ) (y : Vector n) :
    normalSectionChart j u t y = t • u + normalSectionChart j u 0 y := by
  unfold normalSectionChart
  rw [insertNth_eq_single_add_zero j t y, gaussianRotation_add, gaussianRotation_smul,
    coordinateNormalRotation_unit j u hu]

theorem normalSectionChart_eq_sectionPoint {n : ℕ}
    (j : Fin (n + 1)) (u : Vector (n + 1)) (hu : vectorNormSq u = 1)
    (t : ℝ) (y : Vector n) :
    normalSectionChart j u t y = gaussianSectionPoint u t (normalSectionChart j u 0 y) := by
  rw [normalSectionChart_eq_normal_add_base j u hu]
  simp only [gaussianSectionPoint, gaussianSectionResidual,
    normalSectionChart_on_hyperplane j u hu 0 y, zero_smul, sub_zero]

theorem standardGaussian_integral_normal_sections {n : ℕ}
    (j : Fin (n + 1)) (u : Vector (n + 1)) {f : Vector (n + 1) → ℝ}
    (hf : Integrable f (standardGaussian (n + 1))) :
    (∫ x, f x ∂standardGaussian (n + 1)) =
      ∫ y : Vector n, ∫ t : ℝ, f (normalSectionChart j u t y)
        ∂gaussianReal 0 1 ∂standardGaussian n :=
  standardGaussian_integral_rotated_sections (coordinateNormalRotation j u) j hf

theorem vectorNormSq_normalSectionChart {n : ℕ}
    (j : Fin (n + 1)) (u : Vector (n + 1)) (t : ℝ) (y : Vector n) :
    vectorNormSq (normalSectionChart j u t y) = t ^ 2 + vectorNormSq y := by
  rw [normalSectionChart, vectorNormSq_gaussianRotation]
  unfold vectorNormSq
  rw [Fin.sum_univ_succAbove _ j]
  simp

/-- Exact signed section mass in actual codimension-one Gaussian
coordinates; the normal scalar density is not suppressed. -/
theorem normalSectionChart_integral_score {n : ℕ}
    (j : Fin (n + 1)) (u : Vector (n + 1)) (t : ℝ) :
    (∫ y : Vector n,
      (vectorNormSq (normalSectionChart j u t y) - ((n + 1 : ℕ) : ℝ))
      ∂standardGaussian n) = t ^ 2 - 1 := by
  simp_rw [vectorNormSq_normalSectionChart]
  have hadd := integral_add (integrable_const (t ^ 2))
    (standardGaussian_integrable_vectorNormSq n)
  have hi := integral_sub ((integrable_const (t ^ 2)).add
    (standardGaussian_integrable_vectorNormSq n)) (integrable_const ((n + 1 : ℕ) : ℝ))
  simp only [Pi.add_apply, integral_const, measureReal_univ_eq_one, one_smul,
    standardGaussian_integral_vectorNormSq] at hadd hi
  rw [hi, hadd]
  push_cast
  ring

theorem normalSectionChart_signed_mass {n : ℕ}
    (j : Fin (n + 1)) (u : Vector (n + 1)) (t : ℝ) :
    gaussianPDFReal 0 1 t *
      (∫ y : Vector n,
        (vectorNormSq (normalSectionChart j u t y) - ((n + 1 : ℕ) : ℝ))
        ∂standardGaussian n) = (t ^ 2 - 1) * gaussianPDFReal 0 1 t := by
  rw [normalSectionChart_integral_score]
  ring

end
end RectangleCLT.Companion.SignedSurface
