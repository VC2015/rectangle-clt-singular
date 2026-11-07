import RectangleCLTCompanion.SplitV4.GenericC4CubicLaw
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericCubicContraction

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_canonicalMoment_comp

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.continuous_canonicalMoment

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.norm_canonicalMoment_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.continuous_genericCubicContraction

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.norm_genericCubicContraction_le

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_genericCubicContraction_comp

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.genericCommonCubic_eq_sum_mask_integral

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_genericCommonCubic_gaussian

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integrable_genericCubicContraction_seededLaw

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_genericCommonCubic_eq_seededLaw

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.genericCubicContraction,
    ``RectangleCLT.Companion.SplitV4.integrable_canonicalMoment_comp,
    ``RectangleCLT.Companion.SplitV4.continuous_canonicalMoment,
    ``RectangleCLT.Companion.SplitV4.norm_canonicalMoment_le,
    ``RectangleCLT.Companion.SplitV4.continuous_genericCubicContraction,
    ``RectangleCLT.Companion.SplitV4.norm_genericCubicContraction_le,
    ``RectangleCLT.Companion.SplitV4.integrable_genericCubicContraction_comp,
    ``RectangleCLT.Companion.SplitV4.genericCommonCubic_eq_sum_mask_integral,
    ``RectangleCLT.Companion.SplitV4.integrable_genericCommonCubic_gaussian,
    ``RectangleCLT.Companion.SplitV4.integrable_genericCubicContraction_seededLaw,
    ``RectangleCLT.Companion.SplitV4.integral_genericCommonCubic_eq_seededLaw]
  for name in names do
    let action : CollectAxioms.M Unit := CollectAxioms.collect name
    let (_, state) := (action.run env).run {}
    for ax in state.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in actual general-C4 common cubic law identification"
    logInfo m!"{name}: transitive axioms {state.axioms.toList}"
  logInfo "Audited genuine common-point cubic contraction, continuity and product integrability, and its expectation under the actual seeded interpolation probability law."
