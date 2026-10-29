import DominantFiveBody.CoorbitalSourceCalculus
import DominantFiveBody.ProbeOriginalDerivatives
import Lean
set_option pp.fullNames true
set_option pp.width 120
open Lean Elab Command in
run_cmd do
  let names : List Name := [``DominantFiveBody.source_masses,``DominantFiveBody.source_angle_domain]
  let mut result : Array Json := #[]
  for name in names do
    let info ← getConstInfo name
    let pretty ← liftTermElabM do Meta.ppExpr info.type
    result := result.push (Json.mkObj [("lean_declaration",toJson name.toString),("lean_statement",toJson pretty.pretty)])
  liftIO <| IO.FS.writeFile "logs/source-audit-build/root-types-test.json" (Json.pretty (toJson result))
