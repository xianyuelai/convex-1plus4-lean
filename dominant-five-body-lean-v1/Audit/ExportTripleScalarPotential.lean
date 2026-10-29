import DominantFiveBody.TripleScalarPotentialMinimizer
import Lean
open scoped BigOperators ContDiff Topology
universe u_1 u_2 u_3 u_4
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
open Lean Elab Command in
run_cmd do
  let names : List Name := [``DominantFiveBody.tripleScalarPotential_source_formula,``DominantFiveBody.tripleScalarChamber_isOpen,``DominantFiveBody.tripleScalarChamber_convex,``DominantFiveBody.tripleScalarPotential_ordered_formula,``DominantFiveBody.tripleScalarPotential_nonneg,``DominantFiveBody.tripleQuadraticPotential_strictJensen,``DominantFiveBody.inverse_positive_gap_convex,``DominantFiveBody.tripleScalarPotential_strictConvexOn,``DominantFiveBody.tripleScalarPotential_continuousAt,``DominantFiveBody.tripleScalarPotential_sublevel_coordinate_bounds,``DominantFiveBody.tripleScalarPotential_sublevel_gap_bounds,``DominantFiveBody.tripleScalarPotential_compact_sublevel,``DominantFiveBody.tripleScalarPotential_isProperMap,``DominantFiveBody.tripleScalarPotential_hasFDerivAt,``DominantFiveBody.tripleScalarPotential_fderiv_apply,``DominantFiveBody.tripleScalarPotential_divided_gradient,``DominantFiveBody.tripleScalarPotential_critical_iff_root,``DominantFiveBody.tripleScalarPotential_exists_minimizer,``DominantFiveBody.tripleScalarPotential_critical_isMinOn,``DominantFiveBody.tripleScalar_potential_root_existsUnique,``DominantFiveBody.tripleScalar_potential_root_existsUnique_centered]
  let mut result : Array Json := #[]
  for name in names do
    let info ← getConstInfo name
    let pretty ← liftTermElabM do Meta.ppExpr info.type
    result := result.push (Json.mkObj [("lean_declaration",toJson name.toString),("lean_statement",toJson pretty.pretty)])
  liftIO <| IO.FS.writeFile "docs/triple-scalar-potential-types.json" (Json.pretty (toJson result))
#print axioms DominantFiveBody.tripleScalarPotential_source_formula
#print axioms DominantFiveBody.tripleScalarChamber_isOpen
#print axioms DominantFiveBody.tripleScalarChamber_convex
#print axioms DominantFiveBody.tripleScalarPotential_ordered_formula
#print axioms DominantFiveBody.tripleScalarPotential_nonneg
#print axioms DominantFiveBody.tripleQuadraticPotential_strictJensen
#print axioms DominantFiveBody.inverse_positive_gap_convex
#print axioms DominantFiveBody.tripleScalarPotential_strictConvexOn
#print axioms DominantFiveBody.tripleScalarPotential_continuousAt
#print axioms DominantFiveBody.tripleScalarPotential_sublevel_coordinate_bounds
#print axioms DominantFiveBody.tripleScalarPotential_sublevel_gap_bounds
#print axioms DominantFiveBody.tripleScalarPotential_compact_sublevel
#print axioms DominantFiveBody.tripleScalarPotential_isProperMap
#print axioms DominantFiveBody.tripleScalarPotential_hasFDerivAt
#print axioms DominantFiveBody.tripleScalarPotential_fderiv_apply
#print axioms DominantFiveBody.tripleScalarPotential_divided_gradient
#print axioms DominantFiveBody.tripleScalarPotential_critical_iff_root
#print axioms DominantFiveBody.tripleScalarPotential_exists_minimizer
#print axioms DominantFiveBody.tripleScalarPotential_critical_isMinOn
#print axioms DominantFiveBody.tripleScalar_potential_root_existsUnique
#print axioms DominantFiveBody.tripleScalar_potential_root_existsUnique_centered
