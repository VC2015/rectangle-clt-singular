import RectangleCLTCompanion.SplitV4.Main
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

/-!
Machine-readable direct dependencies of the kernel-checked declarations in
this checkpoint.  Each output line begins `SPLITV4_DEPENDENCY ` and contains
one JSON object.  The actual elaborated type is printed with `pp.all`; type
and proof-value dependencies are separate.  Proof expressions themselves
are never printed.  Every declaration also receives
an independent transitive axiom audit against the handoff's exact allowlist.

The direct edges are syntactic constant occurrences, not a claim that every
edge is analytically essential.  Reused historical endpoints are included
explicitly.  Expanded mathematical contracts are printed by `SplitV4/Audit`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let isTheorem := fun ci : ConstantInfo => match ci with
    | .thmInfo _ => true
    | _ => false
  let mut selected : NameSet := {}
  for n in #[
      ``RectangleCLT.Companion.unrestrictedCLT,
      ``RectangleCLT.Companion.unrestrictedCLTExists,
      ``RectangleCLT.Companion.subexponentialCLT_psi1,
      ``RectangleCLT.Companion.skewedTwoPointLowerScale,
      ``RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent,
      ``RectangleCLT.Companion.gaussian_factor_exists_of_subexponential,
      ``RectangleCLT.Companion.gaussian_mean_relative_to_one_face,
      ``RectangleCLT.Companion.rectangleError_le_smoother_gap_add_sharp_endpoint,
      ``RectangleCLT.thinning_covariance,
      ``RectangleCLT.thinning_third_moment,
      ``RectangleCLT.hasDerivAt_thinning_third_coefficient,
      ``RectangleCLT.Companion.SplitV4.C4Test.ofContDiff,
      ``RectangleCLT.Companion.SplitV4.smootherC4Test] do
    selected := selected.insert n
  for (n, ci) in env.constants.toList do
    if isTheorem ci then
      if let some idx := env.getModuleIdxFor? n then
        if env.header.moduleNames[idx.toNat]!.toString.startsWith
            "RectangleCLTCompanion.SplitV4." then
          selected := selected.insert n
  let names := (RBTree.toArray selected).qsort (fun a b => a.toString < b.toString)
  let encodeNames := fun ns : Array Name =>
    Json.arr ((ns.qsort (fun a b => a.toString < b.toString)).map
      (fun n => Json.str n.toString))
  for n in names do
    let some ci := env.checked.get.find? n
      | throwError "Declaration {n} is absent from the checked kernel environment"
    unless isTheorem ci || n == ``RectangleCLT.Companion.SplitV4.C4Test.ofContDiff ||
        n == ``RectangleCLT.Companion.SplitV4.smootherC4Test do
      throwError "Expected a theorem or explicitly audited C4 constructor at endpoint {n}"
    let some value := ci.value?
      | throwError "The checked theorem {n} has no proof value"
    let (_, axiomState) := ((CollectAxioms.collect n).run env).run {}
    for ax in axiomState.axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in dependency closure of {n}"
    let moduleName := match env.getModuleIdxFor? n with
      | some idx => env.header.moduleNames[idx.toNat]!.toString
      | none => ""
    let expandedType ← liftTermElabM do
      withOptions (fun opts => opts.setBool `pp.all true) do
        return (← Meta.ppExpr ci.type).pretty
    let record := Json.mkObj [
      ("declaration", Json.str n.toString),
      ("declaration_kind", Json.str (if isTheorem ci then "theorem" else "definition")),
      ("module", Json.str moduleName),
      ("expanded_lean_type", Json.str expandedType),
      ("type_used_constants", encodeNames ci.type.getUsedConstants),
      ("value_used_constants", encodeNames value.getUsedConstants),
      ("transitive_axioms", encodeNames axiomState.axioms)]
    liftIO <| IO.println ("SPLITV4_DEPENDENCY " ++ record.compress)
  logInfo m!"Emitted and axiom-audited {names.size} split-V4 checkpoint dependency records."
