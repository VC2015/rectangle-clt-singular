import RectangleCLTCompanion.SplitV4.ContinuousPartials
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Symmetry of genuine continuous second coordinate derivatives, obtained
from the checked finite-dimensional Fréchet chain and Schwarz's theorem. -/

open Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem continuous_second_coordinate_derivatives_symmetric {m : ℕ}
    (f : (Fin m → ℝ) → ℝ) (d : (Fin m → ℝ) → Fin m → ℝ)
    (e : (Fin m → ℝ) → Fin m → Fin m → ℝ)
    (hd : ∀ b j c, HasDerivAt (fun t => f (Function.update b j t)) (d (Function.update b j c) j) c)
    (hc : ∀ j, Continuous (fun b => d b j))
    (he : ∀ b j l c, HasDerivAt (fun t => d (Function.update b l t) j) (e (Function.update b l c) j l) c)
    (hec : ∀ j l, Continuous (fun b => e b j l)) (b : Fin m → ℝ) (j l : Fin m) :
    e b j l = e b l j := by
  let p (k : Fin m) : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
  let df : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ := fun x => ∑ k, d x k • p k
  let ddf : (Fin m → ℝ) →L[ℝ] ((Fin m → ℝ) →L[ℝ] ℝ) :=
    ∑ k, (∑ i, e b k i • p i).smulRight (p k)
  have hdf (x : Fin m → ℝ) : HasFDerivAt f (df x) x :=
    hasFDerivAt_of_continuous_coordinate_derivatives f d hd hc x
  have hdk (k : Fin m) : HasFDerivAt (fun x => d x k) (∑ i, e b k i • p i) b :=
    hasFDerivAt_of_continuous_coordinate_derivatives (fun x => d x k) (fun x i => e x k i)
      (fun x i c => he x k i c) (fun i => hec k i) b
  have hddf : HasFDerivAt df ddf b := by
    exact HasFDerivAt.sum (fun k _ => (hdk k).smul_const (p k))
  have hs := second_derivative_symmetric_of_eventually
    (Filter.Eventually.of_forall hdf) hddf (Pi.single l (1 : ℝ)) (Pi.single j (1 : ℝ))
  simpa [ddf, p, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, Pi.single_apply, smul_eq_mul] using hs

end
end RectangleCLT.Companion.SplitV4
