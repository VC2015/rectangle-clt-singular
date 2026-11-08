import RectangleCLTCompanion.SplitV4.Printed.RademacherMaximumGlobal
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

#print RectangleCLT.Companion.SplitV4.Printed.rademacherGlobalError
#print RectangleCLT.Companion.SplitV4.Printed.rademacherGlobalSmallConstant
#print RectangleCLT.Companion.SplitV4.Printed.rademacherGlobalConstant
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacher_scalar_berryEsseen
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_damped_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherMaximum_low_error
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacher_mgf
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.familyRademacherUpperTail_subgaussian
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_rademacher_cutoff_conditions
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error
#print axioms RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString.startsWith
            "RectangleCLTCompanion.SplitV4.Printed.RademacherMaximum" then
          names := names.push n
  unless names.size > 0 do
    throwError "No printed global Rademacher maximum declarations found"
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed global Rademacher maximum closure"
  logInfo m!"Audited all {names.size} printed global Rademacher maximum theorem declarations; only the three permitted axioms."
  let forbidden := #[
    ``RectangleCLT.Companion.SplitV4.familyRademacher_log_tail,
    ``RectangleCLT.Companion.SplitV4.familyRademacherMaximum_pointwise_error,
    ``RectangleCLT.Companion.SplitV4.moderateScalarTail_bound,
    ``RectangleCLT.Companion.SplitV4.moderateScalarTail_small_threshold]
  let required := #[
    ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
    ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_identity,
    ``RectangleCLT.Companion.SplitV4.Printed.independent_copy_variance_integral]
  let mut visited : NameSet := {}
  let mut pending := #[``RectangleCLT.Companion.SplitV4.Printed.eventually_familyRademacherMaximum_global_error]
  let mut offset := 0
  while offset < pending.size do
    let n := pending[offset]!
    offset := offset + 1
    unless visited.contains n do
      visited := visited.insert n
      if forbidden.contains n then
        throwError "Global printed Rademacher comparison bypassed the printed F.1 route through {n}"
      if let some ci := env.checked.get.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? then
          pending := pending ++ v.getUsedConstants
  for n in required do
    unless visited.contains n do
      throwError "Global printed Rademacher comparison does not reach required printed F.1 input {n}"
  logInfo m!"Global Rademacher endpoint closure checked across {visited.size} constants: literal all-x F.1, Laplace IBP and copy variance reached; old F.1/small-x/log-tail endpoints absent."
