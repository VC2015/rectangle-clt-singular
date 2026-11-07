import RectangleCLTCompanion.SplitV4.Printed.SkewLowerMaintext
import Lean.Util.CollectAxioms

set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.twoPoint_normalized_tail_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_log_tail_normalized_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_exact_product_asymptotic_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_mean_value_prefactor_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_detecting_rectangle_liminf_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_ereal_liminf_from_F1
set_option pp.all true in
#check RectangleCLT.Companion.SplitV4.Printed.skew_maintext_sharpness_from_F1

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  let owned := #["SkewLowerModerate", "SkewLowerTail", "SkewLowerProduct", "SkewLowerMeanValue", "SkewLowerMaintext"]
  for (n,ci) in env.constants.toList do
    if ci.isThm then
      if let some idx := env.getModuleIdxFor? n then
        let mod := env.header.moduleNames[idx.toNat]!.toString
        if owned.any (fun suffix => mod == "RectangleCLTCompanion.SplitV4.Printed." ++ suffix) then
          names := names.push n
  let action : CollectAxioms.M Unit := names.forM CollectAxioms.collect
  let (_,state) := (action.run env).run {}
  for ax in state.axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      throwError "Unexpected axiom {ax} in printed Theorem 3"
  for n in state.visited.toList do
    let s := n.toString
    if s == "RectangleCLT.Companion.SplitV4.moderateScalarTail_bound" ||
        s == "RectangleCLT.Companion.lowerSkew_cramer_eventually" ||
        s == "RectangleCLT.Companion.lowerScaleRectangle_liminf" ||
        s == "RectangleCLT.Companion.lowerScaleRectangleDistance_liminf" ||
        s == "RectangleCLT.Companion.skewedTwoPointLowerScale" ||
        s == "RectangleCLT.Companion.lowerConstructionDistance_le" ||
        s == "RectangleCLT.Companion.lowerConstructionDistance_ratio_eventually_le" then
      throwError "Forbidden old tail/final-bound bypass {n} in printed Theorem 3"
  let checkRoute : Name → Array Name → CommandElabM Unit := fun target required => do
    let (_,deps) := ((CollectAxioms.collect target).run env).run {}
    for n in required do
      unless deps.visited.contains n do
        throwError "Printed Theorem 3 terminal {target} omits required route declaration {n}"
  checkRoute ``RectangleCLT.Companion.SplitV4.Printed.skew_full_distance_ereal_liminf_from_F1
    #[``RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail,
      ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
      ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison,
      ``RectangleCLT.Companion.SplitV4.Printed.skew_signed_product_normalized_from_F1]
  checkRoute ``RectangleCLT.Companion.SplitV4.Printed.skew_exact_product_asymptotic_from_F1
    #[``RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail,
      ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
      ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison]
  checkRoute ``RectangleCLT.Companion.SplitV4.Printed.skew_mean_value_prefactor_from_F1
    #[``RectangleCLT.Companion.SplitV4.Printed.product_power_mean_value,
      ``RectangleCLT.Companion.SplitV4.Printed.iid_normalized_moderate_tail,
      ``RectangleCLT.Companion.SplitV4.Printed.moderateScalarTail_bound_printed,
      ``RectangleCLT.Companion.SplitV4.Printed.strict_laplace_tail_comparison]
  logInfo m!"Audited {names.size} printed F1 law application, skew-tail, exact signed product and lower-distance declarations; no old Cramer/final-bound bypass and only the three permitted axioms."
