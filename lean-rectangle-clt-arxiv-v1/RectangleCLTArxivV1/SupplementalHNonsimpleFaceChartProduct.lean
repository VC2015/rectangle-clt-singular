import RectangleCLTArxivV1.SupplementalHSurfaceMeasure
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact product-Gaussian block coordinates for a proper tangent chart.
The Gaussian law and Lebesgue density are the concrete original measures;
no abstract projection-law identity is supplied as a premise. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def nonsimpleChartAppendEquiv (n q : ℕ) :
    (Vector n × Vector q) ≃ᵐ Vector (n+q) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin q => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+q) => ℝ) finSumFinEquiv)

theorem nonsimpleChartAppendEquiv_apply (n q : ℕ) (y : Vector n) (a : Vector q) :
    nonsimpleChartAppendEquiv n q (y,a)=Fin.append y a := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [nonsimpleChartAppendEquiv,MeasurableEquiv.trans_apply,Fin.append_left]
    rw [←finSumFinEquiv_apply_left j,MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  · simp only [nonsimpleChartAppendEquiv,MeasurableEquiv.trans_apply,Fin.append_right]
    rw [←finSumFinEquiv_apply_right j,MeasurableEquiv.piCongrLeft_apply_apply]
    rfl

theorem nonsimpleChartAppendEquiv_gaussian_preserving (n q : ℕ) :
    MeasurePreserving (nonsimpleChartAppendEquiv n q)
      ((standardGaussian n).prod (standardGaussian q)) (standardGaussian (n+q)) := by
  exact (measurePreserving_piCongrLeft
    (fun _ : Fin (n+q) => gaussianReal 0 1) finSumFinEquiv).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin q => gaussianReal 0 1))

def nonsimpleChartPrefix (n q : ℕ) (g : Vector (n+q)) : Vector n :=
  fun i => g (Fin.castAdd q i)

theorem nonsimpleChartPrefix_measurable (n q : ℕ) :
    Measurable (nonsimpleChartPrefix n q) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

theorem nonsimpleChartPrefix_append (n q : ℕ) (y : Vector n) (a : Vector q) :
    nonsimpleChartPrefix n q (Fin.append y a)=y := by
  ext i
  simp [nonsimpleChartPrefix]

/-- Actual product-Gaussian projection law, including an empty tangent
coordinate block when the affine face is a point. -/
theorem nonsimpleChartPrefix_gaussian_map (n q : ℕ) :
    (standardGaussian (n+q)).map (nonsimpleChartPrefix n q)=standardGaussian n := by
  have hA := nonsimpleChartAppendEquiv_gaussian_preserving n q
  calc
    _=(((standardGaussian n).prod (standardGaussian q)).map
        (nonsimpleChartAppendEquiv n q)).map (nonsimpleChartPrefix n q) :=
      congrArg (fun μ => μ.map (nonsimpleChartPrefix n q)) hA.map_eq.symm
    _=((standardGaussian n).prod (standardGaussian q)).map
        ((nonsimpleChartPrefix n q) ∘ (nonsimpleChartAppendEquiv n q)) := by
      rw [Measure.map_map (nonsimpleChartPrefix_measurable n q)
        (nonsimpleChartAppendEquiv n q).measurable]
    _=((standardGaussian n).prod (standardGaussian q)).map Prod.fst := by
      congr 1
      funext z
      rw [Function.comp_apply,nonsimpleChartAppendEquiv_apply,
        nonsimpleChartPrefix_append]
    _=standardGaussian n := by simp

theorem nonsimpleChartDensity_append (n q : ℕ) (y : Vector n) (a : Vector q) :
    standardGaussianDensity (n+q) (Fin.append y a)=
      standardGaussianDensity n y*standardGaussianDensity q a := by
  unfold standardGaussianDensity
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right]

theorem nonsimpleChartDensity_rotation {r : ℕ}
    (L : EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (x : Vector r) :
    standardGaussianDensity r (gaussianRotation L x)=standardGaussianDensity r x := by
  simp only [standardGaussianDensity_eq_kernel,gaussianKernel,vectorNormSq_gaussianRotation]

/-- A pointwise orthonormal-coordinate section identity gives the actual
Gaussian chart law. The sole compatibility premise is an equality of
concrete maps, not a Gaussian-law or surface-integration identity. -/
theorem nonsimpleChart_gaussian_map_of_rotated_prefix {n q : ℕ}
    (L : EuclideanSpace ℝ (Fin (n+q)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+q)))
    (S : Vector (n+q) → Vector (n+q)) (C : Vector n → Vector (n+q))
    (hS : Measurable S) (hC : Measurable C)
    (hcompat : ∀ g,S (gaussianRotation L g)=C (nonsimpleChartPrefix n q g)) :
    (standardGaussian (n+q)).map S=(standardGaussian n).map C := by
  have hR := (gaussianRotation_standardGaussian_preserving L).map_eq
  calc
    _=((standardGaussian (n+q)).map (gaussianRotation L)).map S :=
      congrArg (fun μ => μ.map S) hR.symm
    _=(standardGaussian (n+q)).map (S ∘ gaussianRotation L) := by
      rw [Measure.map_map hS (gaussianRotation L).measurable]
    _=(standardGaussian (n+q)).map (C ∘ nonsimpleChartPrefix n q) := by
      congr 1
      funext g
      exact hcompat g
    _=((standardGaussian (n+q)).map (nonsimpleChartPrefix n q)).map C := by
      rw [Measure.map_map hC (nonsimpleChartPrefix_measurable n q)]
    _=(standardGaussian n).map C := by rw [nonsimpleChartPrefix_gaussian_map]

end
end RectangleCLTArxivV1
