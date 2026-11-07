import RectangleCLTCompanion.SplitV4.SparseMomentOptimal
import Lean.Util.CollectAxioms

/-! Strict transitive actual-law audit of the full sparse polynomial lower theorem. -/

#print RectangleCLT.Companion.SplitV4.sparseFamilyParameters
#print RectangleCLT.Companion.SplitV4.sparseMomentK
#print RectangleCLT.Companion.SplitV4.sparseMomentLowerRate
#print RectangleCLT.Companion.SplitV4.polynomialSparseParameter
#print RectangleCLT.Companion.SplitV4.polynomialSparseRate
#print RectangleCLT.Companion.SplitV4.sparseLowerKhat
#print RectangleCLT.Companion.SplitV4.sparseLowerLog
#print RectangleCLT.Companion.SplitV4.sparseLowerCount
#print RectangleCLT.Companion.SplitV4.sparseLowerTheta
#print RectangleCLT.Companion.SplitV4.sparseLowerPi
#print RectangleCLT.Companion.SplitV4.sparseLowerAmplitude
#print RectangleCLT.Companion.SplitV4.sparseMomentRateConversion
#print RectangleCLT.Companion.SplitV4.sparseMomentLowerCoefficient
#print RectangleCLT.Companion.SplitV4.sparseMomentUpperCoefficient
#print RectangleCLT.Companion.SplitV4.SparseMomentLowerConstruction

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseMomentOptimal

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseMomentLower

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseMoment_uniform_comparison

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.tendsto_sparseFamily_orthantError_div_rate

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparsePaperCalibration

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.sparseFamilyCalibration

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.eventually_sparseFamily_polynomialIndependent

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.polynomialWorstDistance_sparse_le

#print axioms RectangleCLT.Companion.SplitV4.sparseMomentOptimal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    "RectangleCLTCompanion.SplitV4.SparseFamily",
    "RectangleCLTCompanion.SplitV4.SparseFamilyMoments",
    "RectangleCLTCompanion.SplitV4.SparseFamilyCalibration",
    "RectangleCLTCompanion.SplitV4.SparseUniformBounds",
    "RectangleCLTCompanion.SplitV4.SparseMomentRates",
    "RectangleCLTCompanion.SplitV4.SparsePaperCalibration",
    "RectangleCLTCompanion.SplitV4.SparseMomentLower",
    "RectangleCLTCompanion.SplitV4.SparseMomentOptimal" ]
  let mut names : Array Name := #[]
  for (name, ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? name then
        if modules.contains env.header.moduleNames[idx.toNat]!.toString then
          names := names.push name
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_, state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in sparse polynomial lower declarations"
  logInfo m!"Audited {names.size} sparse polynomial lower theorem declarations, each transitively; only the permitted three axioms."
  logInfo "Full Theorem 8 is proved for the literal K/logK/R assumptions with q>2 and B_n>=2. Actual iid symmetric polynomial models, exact matching Gaussian covariance, actual orthant limit, eventual full-distance lower bound and matching unrestricted/centrally-symmetric suprema are conclusions. Both positive comparison coefficients are explicit functions of q alone."
