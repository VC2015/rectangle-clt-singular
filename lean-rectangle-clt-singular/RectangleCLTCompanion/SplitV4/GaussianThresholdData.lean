import RectangleCLTCompanion.SignedSurfaceGaussianSection

/-! Actual hard Gaussian threshold functions used in Appendix B.5. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- The actual hard Gaussian distribution function of the normal projections. -/
def gaussianThresholdCDF {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : ℝ :=
  (standardGaussian r).real {g | ∀ j, faceDot (u j) g ≤ b j}

def gaussianThresholdFirst {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j : Fin m) : ℝ :=
  deriv (fun t => gaussianThresholdCDF u (Function.update b j t)) (b j)

/-- `j,l` means differentiate the `j`th first derivative in coordinate `l`. -/
def gaussianThresholdMixed {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (j l : Fin m) : ℝ :=
  deriv (fun t => gaussianThresholdFirst u (Function.update b l t) j) (b l)

/-- The actual radial Gaussian score on the hard threshold polyhedron. -/
def gaussianThresholdTrace {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : ℝ :=
  ∫ g, ({g | ∀ j, faceDot (u j) g ≤ b j}).indicator
    (fun g => vectorNormSq g - (r : ℝ)) g ∂standardGaussian r

/-- The common-threshold derivative is defined through genuine derivatives. -/
def gaussianThresholdDerivative {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : ℝ :=
  ∑ j, deriv (fun t => gaussianThresholdTrace u (Function.update b j t)) (b j)

end
end RectangleCLT.Companion.SplitV4
