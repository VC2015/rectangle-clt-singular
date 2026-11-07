import RectangleCLTCompanion.SplitV4.GenericBernoulliAveraging
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.continuous_canonicalDiagonal_base

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.norm_canonicalDiagonal_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericBernoulliMoment_eq_integral_retained

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sum_mask_genericBernoulliMoment_commonPoint

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.continuous_canonicalDiagonal_base,
    ``RectangleCLT.Companion.SplitV4.norm_canonicalDiagonal_le,
    ``RectangleCLT.Companion.SplitV4.genericBernoulliMoment_eq_integral_retained,
    ``RectangleCLT.Companion.SplitV4.sum_mask_genericBernoulliMoment_commonPoint]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual generic Bernoulli common-point averaging"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited actual independent-copy and selector averaging for arbitrary C4 tests, derivative orders at most four, and genuine product integrability."
