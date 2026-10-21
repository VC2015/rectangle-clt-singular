import RectangleCLT.GeneralGaussianComponent
import RectangleCLT.GeneralMain

/-! The unconditional general Gaussian-component extension. All moment
alternatives are inherited from the proved bounded general CLT through
the covariance-preserving finite-array limit. -/

universe u

namespace RectangleCLT

/-- The general bound of Lemma 11, with the actual Gaussian component
included in the covariance and excluded from the third and fourth moments.
Only a positive pair gap is required. -/
theorem generalGaussianRectangleCLT :
    GeneralGaussianRectangleCLT.{u} generalCLTConstant :=
  generalGaussianRectangleCLT_of_bounded
    (zero_le_one.trans generalCLTConstant_ge_one) generalRectangleCLT.{0}

theorem generalGaussianRectangleCLTExists : GeneralGaussianRectangleCLTExists.{u} :=
  ⟨generalCLTConstant, generalCLTConstant_ge_one, generalGaussianRectangleCLT⟩

end RectangleCLT
