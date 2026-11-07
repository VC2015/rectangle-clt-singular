import RectangleCLTCompanion.SplitV4.GaussianThresholdPairData
import RectangleCLTCompanion.SplitV4.GaussianThresholdMixedDerivatives
import Mathlib.Tactic.LinearCombination

/-! Actual two-normal Gaussian coarea. Composing the genuine one-normal
product maps preserves the full Gaussian law and transports integrability,
including the unbounded radius weights used by adaptive pair tubes. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def gaussianPairSectionMap {r : ℕ} (e f : Vector r) (z : (ℝ × ℝ) × Vector r) : Vector r :=
  gaussianPairSectionPoint e f z.1.1 z.1.2 z.2

theorem measurable_gaussianPairSectionMap {r : ℕ} (e f : Vector r) :
    Measurable (gaussianPairSectionMap e f) := by
  have hin : Measurable (fun z : (ℝ × ℝ) × Vector r =>
      gaussianNormalSectionMap f (z.1.2, z.2)) :=
    (measurable_gaussianNormalSectionMap f).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact (measurable_gaussianNormalSectionMap e).comp
    ((measurable_fst.comp measurable_fst).prodMk hin)

/-- Two independent Gaussian normal coordinates and the actual residual
Gaussian reconstruct the ambient standard Gaussian law. Orthogonality is
only needed to identify these as the selected face coordinates. -/
theorem gaussianPairSectionMap_measurePreserving {n : ℕ}
    (e f : Vector (n + 1)) (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1) :
    MeasurePreserving (gaussianPairSectionMap e f)
      (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (standardGaussian (n + 1)))
      (standardGaussian (n + 1)) := by
  have hinner := (MeasurePreserving.id (gaussianReal 0 1)).prod
    (gaussianNormalSectionMap_measurePreserving f hf)
  have hout := (gaussianNormalSectionMap_measurePreserving e he).comp hinner
  have hall := hout.comp (measurePreserving_prodAssoc (gaussianReal 0 1)
    (gaussianReal 0 1) (standardGaussian (n + 1)))
  exact hall

theorem integrable_gaussianPairSectionMap_iff {n : ℕ}
    (e f : Vector (n + 1)) (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1)
    (F : Vector (n + 1) → ℝ) (hF : Measurable F) :
    Integrable (fun z : (ℝ × ℝ) × Vector (n + 1) => F (gaussianPairSectionMap e f z))
      (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (standardGaussian (n + 1))) ↔
      Integrable F (standardGaussian (n + 1)) :=
  (gaussianPairSectionMap_measurePreserving e f he hf).integrable_comp hF.aestronglyMeasurable

theorem integral_gaussianPairSectionMap {n : ℕ}
    (e f : Vector (n + 1)) (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1)
    (F : Vector (n + 1) → ℝ) (hF : Measurable F) :
    (∫ z : (ℝ × ℝ) × Vector (n + 1), F (gaussianPairSectionMap e f z)
      ∂(((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (standardGaussian (n + 1)))) =
      ∫ g, F g ∂standardGaussian (n + 1) := by
  have hh := integral_map
    (μ := ((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (standardGaussian (n + 1)))
    (measurable_gaussianPairSectionMap e f).aemeasurable hF.aestronglyMeasurable
  rw [(gaussianPairSectionMap_measurePreserving e f he hf).map_eq] at hh
  exact hh.symm

/-- Genuine Fubini/coarea for every actual integrable ambient test. -/
theorem standardGaussian_integral_pair_sections {n : ℕ}
    (e f : Vector (n + 1)) (he : vectorNormSq e = 1) (hf : vectorNormSq f = 1)
    (F : Vector (n + 1) → ℝ) (hF : Measurable F) (hi : Integrable F (standardGaussian (n + 1))) :
    (∫ g, F g ∂standardGaussian (n + 1)) =
      ∫ a : ℝ, ∫ c : ℝ, ∫ g, F (gaussianPairSectionPoint e f a c g)
        ∂standardGaussian (n + 1) ∂gaussianReal 0 1 ∂gaussianReal 0 1 := by
  have hip := (integrable_gaussianPairSectionMap_iff e f he hf F hF).mpr hi
  have hh := integral_prod (fun z : (ℝ × ℝ) × Vector (n + 1) => F (gaussianPairSectionMap e f z)) hip
  have hhi := integral_prod (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun z : ℝ × ℝ => ∫ g, F (gaussianPairSectionPoint e f z.1 z.2 g) ∂standardGaussian (n + 1))
    hip.integral_prod_left
  exact (integral_gaussianPairSectionMap e f he hf F hF).symm.trans (hh.trans hhi)

theorem gaussianPairSectionPoint_orthogonal_formula {r : ℕ}
    (e f : Vector r) (hef : faceDot e f = 0) (a c : ℝ) (g : Vector r) :
    gaussianPairSectionPoint e f a c g =
      a • e + c • f + g - faceDot e g • e - faceDot f g • f := by
  unfold gaussianPairSectionPoint SignedSurface.gaussianSectionPoint SignedSurface.gaussianSectionResidual
  rw [threshold_faceDot_add_right, threshold_faceDot_smul_right,
    threshold_faceDot_sub_right, threshold_faceDot_smul_right, hef]
  ext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem gaussianNormalProjection_orthogonal {r : ℕ}
    (u v : Vector r) (hu : vectorNormSq u = 1) :
    faceDot u (gaussianNormalProjection u v) = 0 := by
  have hself : faceDot u u = 1 := by simpa only [faceDot, vectorNormSq, pow_two] using hu
  rw [gaussianNormalProjection, threshold_faceDot_sub_right, threshold_faceDot_smul_right,
    hself, faceDot_comm u v]
  ring

theorem gaussianPair_faceDot_add_left {r : ℕ} (e f g : Vector r) :
    faceDot (e + f) g = faceDot e g + faceDot f g := by
  rw [faceDot_comm, threshold_faceDot_add_right, faceDot_comm g e, faceDot_comm g f]

/-- An orthonormal change of the two normal coordinates leaves the actual
two-section map unchanged, pointwise in the genuine residual Gaussian. -/
theorem gaussianPairSectionPoint_change_frame {r : ℕ}
    (e f u q : Vector r) (hef : faceDot e f = 0) (huq : faceDot u q = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (hu : u = a • e + b • f) (hq : q = b • e - a • f) (t s : ℝ) (g : Vector r) :
    gaussianPairSectionPoint u q t s g =
      gaussianPairSectionPoint e f (a * t + b * s) (b * t - a * s) g := by
  rw [gaussianPairSectionPoint_orthogonal_formula u q huq,
    gaussianPairSectionPoint_orthogonal_formula e f hef, hu, hq]
  simp only [gaussianPair_faceDot_add_left, threshold_faceDot_sub_left, threshold_faceDot_smul_left]
  ext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have he := congrArg (fun z : ℝ => z * (e k * faceDot e g)) hab
  have hf := congrArg (fun z : ℝ => z * (f k * faceDot f g)) hab
  linear_combination -he - hf

theorem gaussianPDF_product_eq_of_sum_squares (a b c d : ℝ)
    (hs : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2) :
    gaussianPDFReal 0 1 a * gaussianPDFReal 0 1 b =
      gaussianPDFReal 0 1 c * gaussianPDFReal 0 1 d := by
  have he : -a ^ 2 / 2 + -b ^ 2 / 2 = -c ^ 2 / 2 + -d ^ 2 / 2 := by linarith
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  calc
    _ = (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 * Real.exp (-a ^ 2 / 2 + -b ^ 2 / 2) := by
      rw [Real.exp_add]
      ring
    _ = _ := by rw [he]
    _ = _ := by rw [Real.exp_add]; ring

theorem gaussianPair_rotation_preserves_density (a b t s : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    gaussianPDFReal 0 1 t * gaussianPDFReal 0 1 s =
      gaussianPDFReal 0 1 (a * t + b * s) * gaussianPDFReal 0 1 (b * t - a * s) := by
  apply gaussianPDF_product_eq_of_sum_squares
  have he := congrArg (fun z : ℝ => z * (t ^ 2 + s ^ 2)) hab
  nlinarith

theorem gaussianFiniteSectionProbability_eq_strict {m r : ℕ}
    (s : Finset (Fin m)) (v : Fin m → Vector r) (b : Vector m) (u : Vector r) (t : ℝ)
    (hp : ∀ k ∈ s, gaussianNormalProjection u (v k) ≠ 0) :
    gaussianThresholdSectionProbability s v b u t =
      (standardGaussian r).real {g | ∀ k ∈ s,
        faceDot (v k) (SignedSurface.gaussianSectionPoint u t g) < b k} := by
  have hn := gaussianFiniteThresholdEvent_ae_no_boundary s
    (fun k => gaussianNormalProjection u (v k)) hp (fun k => b k - t * faceDot (v k) u)
  rw [gaussianThresholdSectionProbability_eq_section]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hn] with g hg
  apply propext
  constructor
  · intro h k hk
    have hne := hg k hk
    have hd := gaussianSectionPoint_faceDot u (v k) g t
    exact lt_of_le_of_ne (h k hk) (by intro he; apply hne; linarith)
  · intro h k hk
    exact (h k hk).le

end
end RectangleCLT.Companion.SplitV4
