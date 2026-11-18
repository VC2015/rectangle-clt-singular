import RectangleCLTArxivV1.SupplementalHFrameSections
import RectangleCLTCompanion.SplitV4.GaussianPairSections

/-! A true three-normal Gaussian section law. The product-law transport
needs unit normals; orthogonality identifies the actual normal coordinates. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

def gaussianTripleSectionPoint {r : ℕ} (e f h : Vector r) (a b c : ℝ) (g : Vector r) : Vector r :=
  gaussianPairSectionPoint e f a b (gaussianSectionPoint h c g)

def gaussianTripleSectionMap {r : ℕ} (e f h : Vector r)
    (z : ((ℝ × ℝ) × ℝ) × Vector r) : Vector r :=
  gaussianTripleSectionPoint e f h z.1.1.1 z.1.1.2 z.1.2 z.2

theorem measurable_gaussianTripleSectionMap {r : ℕ} (e f h : Vector r) :
    Measurable (gaussianTripleSectionMap e f h) := by
  have hin : Measurable (fun z : ((ℝ × ℝ) × ℝ) × Vector r =>
      gaussianNormalSectionMap h (z.1.2,z.2)) :=
    (measurable_gaussianNormalSectionMap h).comp (measurable_fst.snd.prodMk measurable_snd)
  exact (measurable_gaussianPairSectionMap e f).comp (measurable_fst.fst.prodMk hin)

/-- Three actual independent scalar normal coordinates and a residual
ambient Gaussian reconstruct the ambient standard Gaussian law. -/
theorem gaussianTripleSectionMap_measurePreserving {n : ℕ}
    (e f h : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hh : vectorNormSq h=1) :
    MeasurePreserving (gaussianTripleSectionMap e f h)
      ((((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (gaussianReal 0 1)).prod (standardGaussian (n+1)))
      (standardGaussian (n+1)) := by
  have hin := (MeasurePreserving.id ((gaussianReal 0 1).prod (gaussianReal 0 1))).prod
    (gaussianNormalSectionMap_measurePreserving h hh)
  have hout := (gaussianPairSectionMap_measurePreserving e f he hf).comp hin
  exact hout.comp (measurePreserving_prodAssoc ((gaussianReal 0 1).prod (gaussianReal 0 1))
    (gaussianReal 0 1) (standardGaussian (n+1)))

theorem integrable_gaussianTripleSectionMap_iff {n : ℕ}
    (e f h : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hh : vectorNormSq h=1)
    (F : Vector (n+1) → ℝ) (hF : Measurable F) :
    Integrable (fun z => F (gaussianTripleSectionMap e f h z))
      ((((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (gaussianReal 0 1)).prod (standardGaussian (n+1))) ↔
      Integrable F (standardGaussian (n+1)) :=
  (gaussianTripleSectionMap_measurePreserving e f h he hf hh).integrable_comp hF.aestronglyMeasurable

theorem integral_gaussianTripleSectionMap {n : ℕ}
    (e f h : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hh : vectorNormSq h=1)
    (F : Vector (n+1) → ℝ) (hF : Measurable F) :
    (∫ z,F (gaussianTripleSectionMap e f h z)
      ∂((((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (gaussianReal 0 1)).prod (standardGaussian (n+1))))=
      ∫ g,F g ∂standardGaussian (n+1) := by
  have ht := integral_map (μ := (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod (gaussianReal 0 1)).prod (standardGaussian (n+1)))
    (measurable_gaussianTripleSectionMap e f h).aemeasurable hF.aestronglyMeasurable
  rw [(gaussianTripleSectionMap_measurePreserving e f h he hf hh).map_eq] at ht
  exact ht.symm

theorem faceDot_gaussianSectionPoint_of_orthogonal {r : ℕ} (u v : Vector r)
    (huv : faceDot u v=0) (a : ℝ) (g : Vector r) :
    faceDot u (gaussianSectionPoint v a g)=faceDot u g := by
  rw [gaussianSectionPoint_eq,threshold_faceDot_add_right,threshold_faceDot_smul_right,huv,mul_zero,add_zero]

/-- Explicit affine normal-point plus residual formula for an ordinary
orthogonal triple. No Gaussian density identity is assumed. -/
theorem gaussianTripleSectionPoint_eq_affine {r : ℕ} (e f h : Vector r)
    (hef : faceDot e f=0) (heh : faceDot e h=0) (hfh : faceDot f h=0)
    (a b c : ℝ) (g : Vector r) :
    gaussianTripleSectionPoint e f h a b c g=
      (a • e+b • f+c • h)+g-
        (faceDot e g • e+faceDot f g • f+faceDot h g • h) := by
  unfold gaussianTripleSectionPoint gaussianPairSectionPoint
  rw [gaussianSectionPoint_eq,
    faceDot_gaussianSectionPoint_of_orthogonal e f hef,
    faceDot_gaussianSectionPoint_of_orthogonal e h heh,
    gaussianSectionPoint_eq,faceDot_gaussianSectionPoint_of_orthogonal f h hfh,
    gaussianSectionPoint_eq]
  module

theorem gaussianTripleSectionPoint_levels {r : ℕ} (e f h : Vector r)
    (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hh : vectorNormSq h=1)
    (hef : faceDot e f=0) (heh : faceDot e h=0) (hfh : faceDot f h=0)
    (a b c : ℝ) (g : Vector r) :
    faceDot e (gaussianTripleSectionPoint e f h a b c g)=a ∧
      faceDot f (gaussianTripleSectionPoint e f h a b c g)=b ∧
      faceDot h (gaussianTripleSectionPoint e f h a b c g)=c := by
  have hfe : faceDot f e=0 := by rw [faceDot_comm]; exact hef
  have hhe : faceDot h e=0 := by rw [faceDot_comm]; exact heh
  have hhf : faceDot h f=0 := by rw [faceDot_comm]; exact hfh
  unfold gaussianTripleSectionPoint gaussianPairSectionPoint
  constructor
  · exact gaussianSectionPoint_on_hyperplane e a he _
  · constructor
    · rw [faceDot_gaussianSectionPoint_of_orthogonal f e hfe]
      exact gaussianSectionPoint_on_hyperplane f b hf _
    · rw [faceDot_gaussianSectionPoint_of_orthogonal h e hhe,
        faceDot_gaussianSectionPoint_of_orthogonal h f hhf]
      exact gaussianSectionPoint_on_hyperplane h c hh g

end
end RectangleCLTArxivV1
