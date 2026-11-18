import RectangleCLTArxivV1
import Lean.Util.CollectAxioms
import Lean.Elab.Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option pp.all true
open Lean Elab Command in
run_cmd do
  let requested : Array String := #[
    "RectangleCLTArxivV1.gaussianEndpointSmoothing_intrinsic",
    "_private.RectangleCLTArxivV1.PairedGaussianEndpointSmoothing.0.RectangleCLTArxivV1.integrate_good_event_bound",
    "Kane.exp_avg_le_avg_exp",
    "Kane.avg_le_sqrt_of_exp_moment"]
  let env ← getEnv
  let allNames := env.constants.toList.foldl (fun acc (n, _) => acc.insert n.toString n)
    ({} : Std.HashMap String Name)
  let missing := requested.filter fun n => !(allNames.contains n)
  let mut present : Array Json := #[]
  for s in requested do
    if let some n := allNames[s]? then
      let mod := (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?
      present := present.push <| Json.mkObj [("name", toJson s),
        ("kernel_import_module", toJson (mod.map Name.toString))]
  IO.println <| (Json.mkObj [("requested", toJson requested), ("missing", toJson missing),
    ("present", Json.arr present)]).compress
