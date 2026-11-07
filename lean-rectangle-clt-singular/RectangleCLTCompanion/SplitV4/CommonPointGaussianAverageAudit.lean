import RectangleCLTCompanion.SplitV4.CommonPointGaussianAverage
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.gaussian_common_point_fourth_random_data

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := #[
    ``RectangleCLT.Companion.SplitV4.continuous_diagonalFourth_joint,
    ``RectangleCLT.Companion.SplitV4.sum_fourthLocalMajorant_le_constant,
    ``RectangleCLT.Companion.SplitV4.gaussian_common_point_fourth_random_data]
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in independent Gaussian common-point averaging"
  logInfo m!"Audited {names.size} independent Gaussian common-point averaging theorem declarations."
