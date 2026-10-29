import DominantFiveBody.NestedSourceDerivativeDetails
import DominantFiveBody.NestedSourceSignTable
import DominantFiveBody.NestedSourceCaptureDetails
import DominantFiveBody.SlowInternalTaylor
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
  let names : List Name := [``DominantFiveBody.nestedBoundaryKernel_unit_hasDerivAt,``DominantFiveBody.nestedBoundaryKernel_unit_second_hasDerivAt,``DominantFiveBody.nestedBoundaryKernel_original_derivatives,``DominantFiveBody.nestedChartExtendedRows_boundary_alpha_independent,``DominantFiveBody.nestedChartJacobian_boundary_alpha_independent,``DominantFiveBody.nestedSourceCasePermutation_source,``DominantFiveBody.nestedSourceCaseTable_source,``DominantFiveBody.nestedSourceCase_order_is_original,``DominantFiveBody.nestedSource_individual_inverse_limits,``DominantFiveBody.nestedSource_common_balls_without_alpha_limit,``DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound,``DominantFiveBody.affinePolarPoint_divided_identity,``DominantFiveBody.affinePolarPoint_cartesian_Osquare,``DominantFiveBody.tripleChartPoint_cartesian_Osquare,``DominantFiveBody.tripleChart_exteriorMass_Ocube,``DominantFiveBody.tripleChart_relativeAverage_cubic_identity,``DominantFiveBody.tripleChart_relativeAverage_Ocube,``DominantFiveBody.tripleChart_reaction_Ocube,``DominantFiveBody.nestedBoundaryDisplacement_to_triple,``DominantFiveBody.nestedChartPoint_cartesian_Osquare,``DominantFiveBody.nestedChart_reaction_Ocube,``DominantFiveBody.newtonTargetField_affinePolar_Osquare,``DominantFiveBody.backgroundProbeField_affinePolar_Osquare,``DominantFiveBody.tripleInternalCartesian_scaling,``DominantFiveBody.tripleInternalVectorQuotient_zero,``DominantFiveBody.tripleInternalVectorQuotient_contDiffAt,``DominantFiveBody.tripleInternalVectorQuotient_Olinear,``DominantFiveBody.tripleInternalCartesian_Osquare]
  let mut result : Array Json := #[]
  for name in names do
    let info ← getConstInfo name
    let pretty ← liftTermElabM do Meta.ppExpr info.type
    result := result.push (Json.mkObj [("lean_declaration",toJson name.toString),("lean_statement",toJson pretty.pretty)])
  liftIO <| IO.FS.writeFile "docs/nested-source-details-types.json" (Json.pretty (toJson result))
#print axioms DominantFiveBody.nestedBoundaryKernel_unit_hasDerivAt
#print axioms DominantFiveBody.nestedBoundaryKernel_unit_second_hasDerivAt
#print axioms DominantFiveBody.nestedBoundaryKernel_original_derivatives
#print axioms DominantFiveBody.nestedChartExtendedRows_boundary_alpha_independent
#print axioms DominantFiveBody.nestedChartJacobian_boundary_alpha_independent
#print axioms DominantFiveBody.nestedSourceCasePermutation_source
#print axioms DominantFiveBody.nestedSourceCaseTable_source
#print axioms DominantFiveBody.nestedSourceCase_order_is_original
#print axioms DominantFiveBody.nestedSource_individual_inverse_limits
#print axioms DominantFiveBody.nestedSource_common_balls_without_alpha_limit
#print axioms DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound
#print axioms DominantFiveBody.affinePolarPoint_divided_identity
#print axioms DominantFiveBody.affinePolarPoint_cartesian_Osquare
#print axioms DominantFiveBody.tripleChartPoint_cartesian_Osquare
#print axioms DominantFiveBody.tripleChart_exteriorMass_Ocube
#print axioms DominantFiveBody.tripleChart_relativeAverage_cubic_identity
#print axioms DominantFiveBody.tripleChart_relativeAverage_Ocube
#print axioms DominantFiveBody.tripleChart_reaction_Ocube
#print axioms DominantFiveBody.nestedBoundaryDisplacement_to_triple
#print axioms DominantFiveBody.nestedChartPoint_cartesian_Osquare
#print axioms DominantFiveBody.nestedChart_reaction_Ocube
#print axioms DominantFiveBody.newtonTargetField_affinePolar_Osquare
#print axioms DominantFiveBody.backgroundProbeField_affinePolar_Osquare
#print axioms DominantFiveBody.tripleInternalCartesian_scaling
#print axioms DominantFiveBody.tripleInternalVectorQuotient_zero
#print axioms DominantFiveBody.tripleInternalVectorQuotient_contDiffAt
#print axioms DominantFiveBody.tripleInternalVectorQuotient_Olinear
#print axioms DominantFiveBody.tripleInternalCartesian_Osquare
