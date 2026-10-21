import RectangleCLT.GeneralProxyBounded

/-! The full general covariance-proxy theorem, including an arbitrary
independent genuine Gaussian component, with both targets and the exact
minimum of all available moment and covariance alternatives. -/

universe u
namespace RectangleCLT

/-- Proposition 4 under its exact pair-gap-only proxy hypotheses. -/
theorem generalCovarianceProxyCLT : GeneralCovarianceProxyCLT.{u} generalProxyConstant :=
  generalCovarianceProxyCLT_of_bounded (zero_le_one.trans generalProxyConstant_ge_one)
    generalBoundedCovarianceProxyCLT.{0}

theorem generalCovarianceProxyCLTExists :
    ∃ C : ℝ, 1 ≤ C ∧ GeneralCovarianceProxyCLT.{u} C :=
  ⟨generalProxyConstant, generalProxyConstant_ge_one, generalCovarianceProxyCLT⟩

end RectangleCLT
