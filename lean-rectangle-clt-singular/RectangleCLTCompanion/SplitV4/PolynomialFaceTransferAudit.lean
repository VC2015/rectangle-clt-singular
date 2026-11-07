import RectangleCLTCompanion.SplitV4.PolynomialFaceTransfer
import Lean.Util.CollectAxioms

/-! Strict audit of the polynomial branch of Corollary 3. -/

#print RectangleCLT.Companion.SplitV4.PolynomialIndependentHypotheses

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomial_projected_average_fourth

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialIndependent_projected

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT

#print axioms RectangleCLT.Companion.SplitV4.polynomial_projected_average_fourth
#print axioms RectangleCLT.Companion.SplitV4.one_le_polynomial_projection_bound
#print axioms RectangleCLT.Companion.SplitV4.polynomialIndependent_projected
#print axioms RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.PolynomialIndependentHypotheses.coordinate_memLp_two,
    ``RectangleCLT.Companion.SplitV4.PolynomialIndependentHypotheses.projected_centered,
    ``RectangleCLT.Companion.SplitV4.PolynomialIndependentHypotheses.projected_coordinate_memLp_two,
    ``RectangleCLT.Companion.SplitV4.polynomial_projected_covariance,
    ``RectangleCLT.Companion.SplitV4.polynomial_projected_average_second,
    ``RectangleCLT.Companion.SplitV4.polynomial_projected_average_second_le,
    ``RectangleCLT.Companion.SplitV4.one_le_polynomial_projection_bound,
    ``RectangleCLT.Companion.SplitV4.polynomial_projected_fourth_integrable,
    ``RectangleCLT.Companion.SplitV4.polynomial_projected_average_fourth,
    ``RectangleCLT.Companion.SplitV4.polynomial_projected_envelope_moment,
    ``RectangleCLT.Companion.SplitV4.polynomialIndependent_projected,
    ``RectangleCLT.Companion.SplitV4.polynomialPolyhedralCLT]
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in polynomial face-transfer closure"
  logInfo "Audited 12 polynomial face-transfer declarations, including the actual polyhedral supremum endpoint."
  logInfo "Fourth moments are averaged before applying coordinate budgets; no coordinate independence, rank condition, or logarithmic growth restriction is assumed."
