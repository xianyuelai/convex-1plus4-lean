import DominantFiveBody.RegularTripleSourceFormulas
import DominantFiveBody.SlowRootSourceIdentities
import Lean
open scoped BigOperators ContDiff Topology
universe u_1 u_2 u_3 u_4
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.numericTypes true
open Lean Elab Command in
run_cmd do
  let names : List Name := [``DominantFiveBody.polar_distance_sq_cos,``DominantFiveBody.sqrt_cube_inverse_eq_negative_three_halves,``DominantFiveBody.regularTripleScalarH_source_formula,``DominantFiveBody.regularTripleScalarH_differentiableAt,``DominantFiveBody.regularTripleScalarH_fderiv_apply,``DominantFiveBody.regularTripleBoundaryM_source_formula,``DominantFiveBody.tripleAngularDifference_boundary_eq_LM,``DominantFiveBody.tripleAngularMean_boundary_source_H,``DominantFiveBody.tripleSlowPoint_source_formula,``DominantFiveBody.nestedSlowPoint_source_formula,``DominantFiveBody.nestedBoundaryScalarPositions_source_formula,``DominantFiveBody.nestedBoundaryScalarPositions_weighted_center,``DominantFiveBody.nestedSlowRootCandidate_contDiffAt,``DominantFiveBody.nestedSlowRootCandidate_contDiffOn,``DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness,``DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness]
  let mut result : Array Json := #[]
  for name in names do
    let info ← getConstInfo name
    let pretty ← liftTermElabM do Meta.ppExpr info.type
    result := result.push (Json.mkObj [("lean_declaration",toJson name.toString),("lean_statement",toJson pretty.pretty)])
  liftIO <| IO.FS.writeFile "docs/regular-triple-slow-source-types.json" (Json.pretty (toJson result))
#print axioms DominantFiveBody.polar_distance_sq_cos
#print axioms DominantFiveBody.sqrt_cube_inverse_eq_negative_three_halves
#print axioms DominantFiveBody.regularTripleScalarH_source_formula
#print axioms DominantFiveBody.regularTripleScalarH_differentiableAt
#print axioms DominantFiveBody.regularTripleScalarH_fderiv_apply
#print axioms DominantFiveBody.regularTripleBoundaryM_source_formula
#print axioms DominantFiveBody.tripleAngularDifference_boundary_eq_LM
#print axioms DominantFiveBody.tripleAngularMean_boundary_source_H
#print axioms DominantFiveBody.tripleSlowPoint_source_formula
#print axioms DominantFiveBody.nestedSlowPoint_source_formula
#print axioms DominantFiveBody.nestedBoundaryScalarPositions_source_formula
#print axioms DominantFiveBody.nestedBoundaryScalarPositions_weighted_center
#print axioms DominantFiveBody.nestedSlowRootCandidate_contDiffAt
#print axioms DominantFiveBody.nestedSlowRootCandidate_contDiffOn
#print axioms DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness
#print axioms DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness
