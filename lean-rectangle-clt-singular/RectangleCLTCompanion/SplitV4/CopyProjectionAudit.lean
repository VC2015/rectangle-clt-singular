import RectangleCLTCompanion.SplitV4.CopyProjection
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.copyGaussianProjection_measurePreserving
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.integral_copyGaussianProjection

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.copyGaussianProjection_measurePreserving,
    ``RectangleCLT.Companion.SplitV4.integrable_copyGaussianProjection_iff,
    ``RectangleCLT.Companion.SplitV4.integral_copyGaussianProjection]
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in copy/Gaussian projection dependency closure"
  logInfo m!"Audited {names.size} copy/Gaussian projection theorem declarations."
