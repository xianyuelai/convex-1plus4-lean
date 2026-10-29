import DominantFiveBody.Main
import DominantFiveBody.ChartFormulaCoverage
import DominantFiveBody.HadamardTargetDifference
import DominantFiveBody.JointAnalyticCharts
import DominantFiveBody.NestedBoundaryDeterminant
import DominantFiveBody.SmoothOrderedSliceConnection
import DominantFiveBody.BackgroundSlow
import DominantFiveBody.BackgroundSpectrum
import DominantFiveBody.ChartEpsilonBounds
import DominantFiveBody.ChartExplicitDefinitions
import DominantFiveBody.ChartFormulaCoverage
import DominantFiveBody.ChartScalarFields
import DominantFiveBody.ChartSourceSelections
import DominantFiveBody.CollisionNestedDirections
import DominantFiveBody.CollisionTripleNestedComplete
import DominantFiveBody.CollisionUpperNestedComplete
import DominantFiveBody.ConvexContinuation
import DominantFiveBody.DistinctChartSource
import DominantFiveBody.HadamardTargetDifference
import DominantFiveBody.JointAnalyticCharts
import DominantFiveBody.NestedActualCapture
import DominantFiveBody.NestedAngularMatrix
import DominantFiveBody.NestedAreaDerivative
import DominantFiveBody.NestedAreaPositivity
import DominantFiveBody.NestedAreas
import DominantFiveBody.NestedBoundary
import DominantFiveBody.NestedBoundaryDeterminant
import DominantFiveBody.NestedChart
import DominantFiveBody.NestedCollinearity
import DominantFiveBody.NestedContinuation
import DominantFiveBody.NestedConvexContinuation
import DominantFiveBody.NestedConvexity
import DominantFiveBody.NestedCoordinateDeterminant
import DominantFiveBody.NestedDirections
import DominantFiveBody.NestedInternal
import DominantFiveBody.NestedInternalAreaPositivity
import DominantFiveBody.NestedJacobian
import DominantFiveBody.NestedKernelFormulas
import DominantFiveBody.NestedRecovery
import DominantFiveBody.NestedRegularization
import DominantFiveBody.NestedSlowCoordinates
import DominantFiveBody.NestedSmooth
import DominantFiveBody.NestedSourceCaptureDetails
import DominantFiveBody.NestedSourceDerivativeDetails
import DominantFiveBody.NestedSourceRows
import DominantFiveBody.NestedSourceSignTable
import DominantFiveBody.NestedUniformAreas
import DominantFiveBody.NestedUnitBoundary
import DominantFiveBody.NestedZeroFaces
import DominantFiveBody.NoCollisionContinuation
import DominantFiveBody.NoCollisionSliceConnection
import DominantFiveBody.OrderedSliceNestedCases
import DominantFiveBody.OriginalDividedEdges
import DominantFiveBody.OriginalNestedIntegral
import DominantFiveBody.OriginalNestedKernels
import DominantFiveBody.PairActualCapture
import DominantFiveBody.PairAreas
import DominantFiveBody.PairBoundary
import DominantFiveBody.PairBoundaryInvertibility
import DominantFiveBody.PairChart
import DominantFiveBody.PairContinuation
import DominantFiveBody.PairInternal
import DominantFiveBody.PairJacobian
import DominantFiveBody.PairPhysicalContinuation
import DominantFiveBody.PairRadialFactor
import DominantFiveBody.PairRegularization
import DominantFiveBody.PairSmooth
import DominantFiveBody.RegularTripleSourceFormulas
import DominantFiveBody.RelativeAction
import DominantFiveBody.SeparatedBaseContinuation
import DominantFiveBody.SingleScaleKernel
import DominantFiveBody.SingleScaleWeightedSums
import DominantFiveBody.SlowInternalTaylor
import DominantFiveBody.SlowNewtonTaylor
import DominantFiveBody.SlowRootSourceIdentities
import DominantFiveBody.SlowTaylorOrders
import DominantFiveBody.SmoothOrderedSliceConnection
import DominantFiveBody.SourceFormulaExpansions
import DominantFiveBody.TripleActualCapture
import DominantFiveBody.TripleAreaDerivative
import DominantFiveBody.TripleAreaPositivity
import DominantFiveBody.TripleAreas
import DominantFiveBody.TripleBoundary
import DominantFiveBody.TripleChart
import DominantFiveBody.TripleCollinearity
import DominantFiveBody.TripleContinuation
import DominantFiveBody.TripleConvexContinuation
import DominantFiveBody.TripleConvexity
import DominantFiveBody.TripleDirections
import DominantFiveBody.TripleIntegratedJacobian
import DominantFiveBody.TripleInternal
import DominantFiveBody.TripleJacobian
import DominantFiveBody.TripleRecovery
import DominantFiveBody.TripleRegularization
import DominantFiveBody.TripleScalar
import DominantFiveBody.TripleScalarPotential
import DominantFiveBody.TripleScalarPotentialConvex
import DominantFiveBody.TripleScalarPotentialGradient
import DominantFiveBody.TripleScalarPotentialMinimizer
import DominantFiveBody.TripleScalarPotentialProper
import DominantFiveBody.TripleSlowBoundary
import DominantFiveBody.TripleSlowExterior
import DominantFiveBody.TripleSmooth
import DominantFiveBody.TripleUpperActualCapture
import DominantFiveBody.TripleZeroEndpoint
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.numericTypes true
set_option pp.maxSteps 10000000
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.affinePolarPoint_cartesian_Osquare"
#check @DominantFiveBody.affinePolarPoint_cartesian_Osquare
#print axioms DominantFiveBody.affinePolarPoint_cartesian_Osquare
#eval IO.println "COVERAGE_END DominantFiveBody.affinePolarPoint_cartesian_Osquare"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.affinePolarPoint_divided_identity"
#check @DominantFiveBody.affinePolarPoint_divided_identity
#print axioms DominantFiveBody.affinePolarPoint_divided_identity
#eval IO.println "COVERAGE_END DominantFiveBody.affinePolarPoint_divided_identity"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundAngularScale_contDiffAt"
#check @DominantFiveBody.backgroundAngularScale_contDiffAt
#print axioms DominantFiveBody.backgroundAngularScale_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundAngularScale_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundMatrix_characteristic_factor"
#check @DominantFiveBody.backgroundMatrix_characteristic_factor
#print axioms DominantFiveBody.backgroundMatrix_characteristic_factor
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundMatrix_characteristic_factor"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundMatrix_trace"
#check @DominantFiveBody.backgroundMatrix_trace
#print axioms DominantFiveBody.backgroundMatrix_trace
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundMatrix_trace"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundOperator_apply"
#check @DominantFiveBody.backgroundOperator_apply
#print axioms DominantFiveBody.backgroundOperator_apply
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundOperator_apply"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundOperator_coordinates"
#check @DominantFiveBody.backgroundOperator_coordinates
#print axioms DominantFiveBody.backgroundOperator_coordinates
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundOperator_coordinates"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundProbeField_affinePolar_Osquare"
#check @DominantFiveBody.backgroundProbeField_affinePolar_Osquare
#print axioms DominantFiveBody.backgroundProbeField_affinePolar_Osquare
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundProbeField_affinePolar_Osquare"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundProbeField_hasFDerivAt"
#check @DominantFiveBody.backgroundProbeField_hasFDerivAt
#print axioms DominantFiveBody.backgroundProbeField_hasFDerivAt
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundProbeField_hasFDerivAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundProbeField_source_formula"
#check @DominantFiveBody.backgroundProbeField_source_formula
#print axioms DominantFiveBody.backgroundProbeField_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundProbeField_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundProbeField_zero"
#check @DominantFiveBody.backgroundProbeField_zero
#print axioms DominantFiveBody.backgroundProbeField_zero
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundProbeField_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundScalarLift_vector_balance"
#check @DominantFiveBody.backgroundScalarLift_vector_balance
#print axioms DominantFiveBody.backgroundScalarLift_vector_balance
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundScalarLift_vector_balance"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlowDirection_contDiffAt"
#check @DominantFiveBody.backgroundSlowDirection_contDiffAt
#print axioms DominantFiveBody.backgroundSlowDirection_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlowDirection_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlowDirection_eigen"
#check @DominantFiveBody.backgroundSlowDirection_eigen
#print axioms DominantFiveBody.backgroundSlowDirection_eigen
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlowDirection_eigen"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlowK_contDiffAt"
#check @DominantFiveBody.backgroundSlowK_contDiffAt
#print axioms DominantFiveBody.backgroundSlowK_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlowK_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlowLambda_characteristic"
#check @DominantFiveBody.backgroundSlowLambda_characteristic
#print axioms DominantFiveBody.backgroundSlowLambda_characteristic
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlowLambda_characteristic"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlowLambda_eq"
#check @DominantFiveBody.backgroundSlowLambda_eq
#print axioms DominantFiveBody.backgroundSlowLambda_eq
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlowLambda_eq"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlowLambda_lt_fast"
#check @DominantFiveBody.backgroundSlowLambda_lt_fast
#print axioms DominantFiveBody.backgroundSlowLambda_lt_fast
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlowLambda_lt_fast"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlowLength_contDiffAt"
#check @DominantFiveBody.backgroundSlowLength_contDiffAt
#print axioms DominantFiveBody.backgroundSlowLength_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlowLength_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlow_formula_complete"
#check @DominantFiveBody.backgroundSlow_formula_complete
#print axioms DominantFiveBody.backgroundSlow_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlow_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlow_polar_displacement"
#check @DominantFiveBody.backgroundSlow_polar_displacement
#print axioms DominantFiveBody.backgroundSlow_polar_displacement
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlow_polar_displacement"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlow_scaling"
#check @DominantFiveBody.backgroundSlow_scaling
#print axioms DominantFiveBody.backgroundSlow_scaling
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlow_scaling"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSlow_zero_complete"
#check @DominantFiveBody.backgroundSlow_zero_complete
#print axioms DominantFiveBody.backgroundSlow_zero_complete
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSlow_zero_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.backgroundSpectrum_formula_complete"
#check @DominantFiveBody.backgroundSpectrum_formula_complete
#print axioms DominantFiveBody.backgroundSpectrum_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.backgroundSpectrum_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.circle_areas_complete"
#check @DominantFiveBody.circle_areas_complete
#print axioms DominantFiveBody.circle_areas_complete
#eval IO.println "COVERAGE_END DominantFiveBody.circle_areas_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.closedCoorbital_largest_mass_gauge"
#check @DominantFiveBody.closedCoorbital_largest_mass_gauge
#print axioms DominantFiveBody.closedCoorbital_largest_mass_gauge
#eval IO.println "COVERAGE_END DominantFiveBody.closedCoorbital_largest_mass_gauge"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.fixedAngleDeletedResidual_same_eq"
#check @DominantFiveBody.fixedAngleDeletedResidual_same_eq
#print axioms DominantFiveBody.fixedAngleDeletedResidual_same_eq
#eval IO.println "COVERAGE_END DominantFiveBody.fixedAngleDeletedResidual_same_eq"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.fixedAngle_zero_source_full_block"
#check @DominantFiveBody.fixedAngle_zero_source_full_block
#print axioms DominantFiveBody.fixedAngle_zero_source_full_block
#eval IO.println "COVERAGE_END DominantFiveBody.fixedAngle_zero_source_full_block"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.hadamard_target_difference"
#check @DominantFiveBody.hadamard_target_difference
#print axioms DominantFiveBody.hadamard_target_difference
#eval IO.println "COVERAGE_END DominantFiveBody.hadamard_target_difference"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.kappaPrime_h_source"
#check @DominantFiveBody.kappaPrime_h_source
#print axioms DominantFiveBody.kappaPrime_h_source
#eval IO.println "COVERAGE_END DominantFiveBody.kappaPrime_h_source"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedAngularBoundaryMatrix_source"
#check @DominantFiveBody.nestedAngularBoundaryMatrix_source
#print axioms DominantFiveBody.nestedAngularBoundaryMatrix_source
#eval IO.println "COVERAGE_END DominantFiveBody.nestedAngularBoundaryMatrix_source"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedAngularExterior_recovery"
#check @DominantFiveBody.nestedAngularExterior_recovery
#print axioms DominantFiveBody.nestedAngularExterior_recovery
#eval IO.println "COVERAGE_END DominantFiveBody.nestedAngularExterior_recovery"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedAngularInnerDifference_at_boundary"
#check @DominantFiveBody.nestedAngularInnerDifference_at_boundary
#print axioms DominantFiveBody.nestedAngularInnerDifference_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedAngularInnerDifference_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedAngularMean_at_boundary"
#check @DominantFiveBody.nestedAngularMean_at_boundary
#print axioms DominantFiveBody.nestedAngularMean_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedAngularMean_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedAngularOuterDifference_at_boundary"
#check @DominantFiveBody.nestedAngularOuterDifference_at_boundary
#print axioms DominantFiveBody.nestedAngularOuterDifference_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedAngularOuterDifference_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedAngularRows_source_complete"
#check @DominantFiveBody.nestedAngularRows_source_complete
#print axioms DominantFiveBody.nestedAngularRows_source_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedAngularRows_source_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedAreaAlongRoot_deriv_eq_partial"
#check @DominantFiveBody.nestedAreaAlongRoot_deriv_eq_partial
#print axioms DominantFiveBody.nestedAreaAlongRoot_deriv_eq_partial
#eval IO.println "COVERAGE_END DominantFiveBody.nestedAreaAlongRoot_deriv_eq_partial"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedAreaAlongZeroRoot_hasDerivAt"
#check @DominantFiveBody.nestedAreaAlongZeroRoot_hasDerivAt
#print axioms DominantFiveBody.nestedAreaAlongZeroRoot_hasDerivAt
#eval IO.println "COVERAGE_END DominantFiveBody.nestedAreaAlongZeroRoot_hasDerivAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBasePoint_formula_complete"
#check @DominantFiveBody.nestedBasePoint_formula_complete
#print axioms DominantFiveBody.nestedBasePoint_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBasePoint_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBasePoint_regular"
#check @DominantFiveBody.nestedBasePoint_regular
#print axioms DominantFiveBody.nestedBasePoint_regular
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBasePoint_regular"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBoundaryDerivativeMatrix_det"
#check @DominantFiveBody.nestedBoundaryDerivativeMatrix_det
#print axioms DominantFiveBody.nestedBoundaryDerivativeMatrix_det
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBoundaryDerivativeMatrix_det"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBoundaryDerivativeMatrix_triangular_diagonal"
#check @DominantFiveBody.nestedBoundaryDerivativeMatrix_triangular_diagonal
#print axioms DominantFiveBody.nestedBoundaryDerivativeMatrix_triangular_diagonal
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBoundaryDerivativeMatrix_triangular_diagonal"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBoundaryDisplacement_to_triple"
#check @DominantFiveBody.nestedBoundaryDisplacement_to_triple
#print axioms DominantFiveBody.nestedBoundaryDisplacement_to_triple
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBoundaryDisplacement_to_triple"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBoundaryKernel_fderiv_apply"
#check @DominantFiveBody.nestedBoundaryKernel_fderiv_apply
#print axioms DominantFiveBody.nestedBoundaryKernel_fderiv_apply
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBoundaryKernel_fderiv_apply"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBoundaryKernel_original_derivatives"
#check @DominantFiveBody.nestedBoundaryKernel_original_derivatives
#print axioms DominantFiveBody.nestedBoundaryKernel_original_derivatives
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBoundaryKernel_original_derivatives"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBoundaryKernels_source_complete"
#check @DominantFiveBody.nestedBoundaryKernels_source_complete
#print axioms DominantFiveBody.nestedBoundaryKernels_source_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBoundaryKernels_source_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBoundaryScalarPositions_source_formula"
#check @DominantFiveBody.nestedBoundaryScalarPositions_source_formula
#print axioms DominantFiveBody.nestedBoundaryScalarPositions_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBoundaryScalarPositions_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedBoundaryScalarPositions_weighted_center"
#check @DominantFiveBody.nestedBoundaryScalarPositions_weighted_center
#print axioms DominantFiveBody.nestedBoundaryScalarPositions_weighted_center
#eval IO.println "COVERAGE_END DominantFiveBody.nestedBoundaryScalarPositions_weighted_center"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartExtendedRows_base_root"
#check @DominantFiveBody.nestedChartExtendedRows_base_root
#print axioms DominantFiveBody.nestedChartExtendedRows_base_root
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartExtendedRows_base_root"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartExtendedRows_eq_physical"
#check @DominantFiveBody.nestedChartExtendedRows_eq_physical
#print axioms DominantFiveBody.nestedChartExtendedRows_eq_physical
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartExtendedRows_eq_physical"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartExtendedRows_joint_analyticAt"
#check @DominantFiveBody.nestedChartExtendedRows_joint_analyticAt
#print axioms DominantFiveBody.nestedChartExtendedRows_joint_analyticAt
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartExtendedRows_joint_analyticAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartExtendedRows_joint_contDiffAt"
#check @DominantFiveBody.nestedChartExtendedRows_joint_contDiffAt
#print axioms DominantFiveBody.nestedChartExtendedRows_joint_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartExtendedRows_joint_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartExtendedRows_zero_iff_normalized"
#check @DominantFiveBody.nestedChartExtendedRows_zero_iff_normalized
#print axioms DominantFiveBody.nestedChartExtendedRows_zero_iff_normalized
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartExtendedRows_zero_iff_normalized"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartJacobian_boundary_alpha_independent"
#check @DominantFiveBody.nestedChartJacobian_boundary_alpha_independent
#print axioms DominantFiveBody.nestedChartJacobian_boundary_alpha_independent
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartJacobian_boundary_alpha_independent"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartJacobian_boundary_isInvertible"
#check @DominantFiveBody.nestedChartJacobian_boundary_isInvertible
#print axioms DominantFiveBody.nestedChartJacobian_boundary_isInvertible
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartJacobian_boundary_isInvertible"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartJacobian_unit_radial"
#check @DominantFiveBody.nestedChartJacobian_unit_radial
#print axioms DominantFiveBody.nestedChartJacobian_unit_radial
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartJacobian_unit_radial"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartJacobian_unit_radial_difference"
#check @DominantFiveBody.nestedChartJacobian_unit_radial_difference
#print axioms DominantFiveBody.nestedChartJacobian_unit_radial_difference
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartJacobian_unit_radial_difference"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartPhysicalRows_zero_iff"
#check @DominantFiveBody.nestedChartPhysicalRows_zero_iff
#print axioms DominantFiveBody.nestedChartPhysicalRows_zero_iff
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartPhysicalRows_zero_iff"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChartPoint_cartesian_Osquare"
#check @DominantFiveBody.nestedChartPoint_cartesian_Osquare
#print axioms DominantFiveBody.nestedChartPoint_cartesian_Osquare
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChartPoint_cartesian_Osquare"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_all_ten_areas_uniform_product"
#check @DominantFiveBody.nestedChart_all_ten_areas_uniform_product
#print axioms DominantFiveBody.nestedChart_all_ten_areas_uniform_product
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_all_ten_areas_uniform_product"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_compact_boundary_continuation"
#check @DominantFiveBody.nestedChart_compact_boundary_continuation
#print axioms DominantFiveBody.nestedChart_compact_boundary_continuation
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_compact_boundary_continuation"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_convex_physical_continuation"
#check @DominantFiveBody.nestedChart_convex_physical_continuation
#print axioms DominantFiveBody.nestedChart_convex_physical_continuation
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_convex_physical_continuation"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_coordinates_complete"
#check @DominantFiveBody.nestedChart_coordinates_complete
#print axioms DominantFiveBody.nestedChart_coordinates_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_coordinates_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_radial_uniform_epsilon_bound"
#check @DominantFiveBody.nestedChart_radial_uniform_epsilon_bound
#print axioms DominantFiveBody.nestedChart_radial_uniform_epsilon_bound
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_radial_uniform_epsilon_bound"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_reaction_Ocube"
#check @DominantFiveBody.nestedChart_reaction_Ocube
#print axioms DominantFiveBody.nestedChart_reaction_Ocube
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_reaction_Ocube"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_zero_eps_all_scale_faces"
#check @DominantFiveBody.nestedChart_zero_eps_all_scale_faces
#print axioms DominantFiveBody.nestedChart_zero_eps_all_scale_faces
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_zero_eps_all_scale_faces"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_zero_face_area_zero_nonnegative_eta"
#check @DominantFiveBody.nestedChart_zero_face_area_zero_nonnegative_eta
#print axioms DominantFiveBody.nestedChart_zero_face_area_zero_nonnegative_eta
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_zero_face_area_zero_nonnegative_eta"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness"
#check @DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness
#print axioms DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedChart_zero_face_parallel_of_local_uniqueness"
#check @DominantFiveBody.nestedChart_zero_face_parallel_of_local_uniqueness
#print axioms DominantFiveBody.nestedChart_zero_face_parallel_of_local_uniqueness
#eval IO.println "COVERAGE_END DominantFiveBody.nestedChart_zero_face_parallel_of_local_uniqueness"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedCircle_coefficient_complete"
#check @DominantFiveBody.nestedCircle_coefficient_complete
#print axioms DominantFiveBody.nestedCircle_coefficient_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedCircle_coefficient_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedContinuationRoot_fixed_mass_endpoint"
#check @DominantFiveBody.nestedContinuationRoot_fixed_mass_endpoint
#print axioms DominantFiveBody.nestedContinuationRoot_fixed_mass_endpoint
#eval IO.println "COVERAGE_END DominantFiveBody.nestedContinuationRoot_fixed_mass_endpoint"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedEdge_signed_base_gap_pos"
#check @DominantFiveBody.nestedEdge_signed_base_gap_pos
#print axioms DominantFiveBody.nestedEdge_signed_base_gap_pos
#eval IO.println "COVERAGE_END DominantFiveBody.nestedEdge_signed_base_gap_pos"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedExternalAreaQuotient_exterior_boundary"
#check @DominantFiveBody.nestedExternalAreaQuotient_exterior_boundary
#print axioms DominantFiveBody.nestedExternalAreaQuotient_exterior_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedExternalAreaQuotient_exterior_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedExternalAreaQuotient_primary_boundary"
#check @DominantFiveBody.nestedExternalAreaQuotient_primary_boundary
#print axioms DominantFiveBody.nestedExternalAreaQuotient_primary_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedExternalAreaQuotient_primary_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedGaps_formula_complete"
#check @DominantFiveBody.nestedGaps_formula_complete
#print axioms DominantFiveBody.nestedGaps_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedGaps_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInnerDirection_identity"
#check @DominantFiveBody.nestedInnerDirection_identity
#print axioms DominantFiveBody.nestedInnerDirection_identity
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInnerDirection_identity"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInnerJOverT_joint_contDiffAt"
#check @DominantFiveBody.nestedInnerJOverT_joint_contDiffAt
#print axioms DominantFiveBody.nestedInnerJOverT_joint_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInnerJOverT_joint_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInnerJ_factor"
#check @DominantFiveBody.nestedInnerJ_factor
#print axioms DominantFiveBody.nestedInnerJ_factor
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInnerJ_factor"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInnerJ_formula_complete"
#check @DominantFiveBody.nestedInnerJ_formula_complete
#print axioms DominantFiveBody.nestedInnerJ_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInnerJ_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInnerM_at_boundary"
#check @DominantFiveBody.nestedInnerM_at_boundary
#print axioms DominantFiveBody.nestedInnerM_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInnerM_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInnerM_formula"
#check @DominantFiveBody.nestedInnerM_formula
#print axioms DominantFiveBody.nestedInnerM_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInnerM_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInnerN_source_formula"
#check @DominantFiveBody.nestedInnerN_source_formula
#print axioms DominantFiveBody.nestedInnerN_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInnerN_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInnerO_source_formula"
#check @DominantFiveBody.nestedInnerO_source_formula
#print axioms DominantFiveBody.nestedInnerO_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInnerO_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInnerWSq_formula"
#check @DominantFiveBody.nestedInnerWSq_formula
#print axioms DominantFiveBody.nestedInnerWSq_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInnerWSq_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInner_distance"
#check @DominantFiveBody.nestedInner_distance
#print axioms DominantFiveBody.nestedInner_distance
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInner_distance"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInternalAreaQuotient_zero_formula"
#check @DominantFiveBody.nestedInternalAreaQuotient_zero_formula
#print axioms DominantFiveBody.nestedInternalAreaQuotient_zero_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInternalAreaQuotient_zero_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInternalArea_factor_cubic_along_root"
#check @DominantFiveBody.nestedInternalArea_factor_cubic_along_root
#print axioms DominantFiveBody.nestedInternalArea_factor_cubic_along_root
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInternalArea_factor_cubic_along_root"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedInternalArea_factor_square"
#check @DominantFiveBody.nestedInternalArea_factor_square
#print axioms DominantFiveBody.nestedInternalArea_factor_square
#eval IO.println "COVERAGE_END DominantFiveBody.nestedInternalArea_factor_square"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedMacroArea_unit_boundary"
#check @DominantFiveBody.nestedMacroArea_unit_boundary
#print axioms DominantFiveBody.nestedMacroArea_unit_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedMacroArea_unit_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOriginalScalarPath_endpoints"
#check @DominantFiveBody.nestedOriginalScalarPath_endpoints
#print axioms DominantFiveBody.nestedOriginalScalarPath_endpoints
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOriginalScalarPath_endpoints"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOriginalScalarPath_positive_common_tube"
#check @DominantFiveBody.nestedOriginalScalarPath_positive_common_tube
#print axioms DominantFiveBody.nestedOriginalScalarPath_positive_common_tube
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOriginalScalarPath_positive_common_tube"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOuterDirection_identity"
#check @DominantFiveBody.nestedOuterDirection_identity
#print axioms DominantFiveBody.nestedOuterDirection_identity
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOuterDirection_identity"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOuterL_formula"
#check @DominantFiveBody.nestedOuterL_formula
#print axioms DominantFiveBody.nestedOuterL_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOuterL_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOuterL_original_integral"
#check @DominantFiveBody.nestedOuterL_original_integral
#print axioms DominantFiveBody.nestedOuterL_original_integral
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOuterL_original_integral"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOuterN_formula"
#check @DominantFiveBody.nestedOuterN_formula
#print axioms DominantFiveBody.nestedOuterN_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOuterN_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOuterN_original_integral"
#check @DominantFiveBody.nestedOuterN_original_integral
#print axioms DominantFiveBody.nestedOuterN_original_integral
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOuterN_original_integral"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOuterO_formula"
#check @DominantFiveBody.nestedOuterO_formula
#print axioms DominantFiveBody.nestedOuterO_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOuterO_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOuterWSq_formula"
#check @DominantFiveBody.nestedOuterWSq_formula
#print axioms DominantFiveBody.nestedOuterWSq_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOuterWSq_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedOuter_distance"
#check @DominantFiveBody.nestedOuter_distance
#print axioms DominantFiveBody.nestedOuter_distance
#eval IO.println "COVERAGE_END DominantFiveBody.nestedOuter_distance"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedRadialExterior_recovery"
#check @DominantFiveBody.nestedRadialExterior_recovery
#print axioms DominantFiveBody.nestedRadialExterior_recovery
#eval IO.println "COVERAGE_END DominantFiveBody.nestedRadialExterior_recovery"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedRadialInnerDifference_at_boundary"
#check @DominantFiveBody.nestedRadialInnerDifference_at_boundary
#print axioms DominantFiveBody.nestedRadialInnerDifference_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedRadialInnerDifference_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedRadialMean_at_boundary"
#check @DominantFiveBody.nestedRadialMean_at_boundary
#print axioms DominantFiveBody.nestedRadialMean_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedRadialMean_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedRadialOuterDifference_at_boundary"
#check @DominantFiveBody.nestedRadialOuterDifference_at_boundary
#print axioms DominantFiveBody.nestedRadialOuterDifference_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.nestedRadialOuterDifference_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedRadialRows_source_complete"
#check @DominantFiveBody.nestedRadialRows_source_complete
#print axioms DominantFiveBody.nestedRadialRows_source_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedRadialRows_source_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedRows_formula_complete"
#check @DominantFiveBody.nestedRows_formula_complete
#print axioms DominantFiveBody.nestedRows_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedRows_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedRows_recovery"
#check @DominantFiveBody.nestedRows_recovery
#print axioms DominantFiveBody.nestedRows_recovery
#eval IO.println "COVERAGE_END DominantFiveBody.nestedRows_recovery"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedScalarAngularKernel_formula"
#check @DominantFiveBody.nestedScalarAngularKernel_formula
#print axioms DominantFiveBody.nestedScalarAngularKernel_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedScalarAngularKernel_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedScalarAngularKernel_substitution"
#check @DominantFiveBody.nestedScalarAngularKernel_substitution
#print axioms DominantFiveBody.nestedScalarAngularKernel_substitution
#eval IO.println "COVERAGE_END DominantFiveBody.nestedScalarAngularKernel_substitution"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedScalarFields_at_actual_targets"
#check @DominantFiveBody.nestedScalarFields_at_actual_targets
#print axioms DominantFiveBody.nestedScalarFields_at_actual_targets
#eval IO.println "COVERAGE_END DominantFiveBody.nestedScalarFields_at_actual_targets"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedScalarH_source_formula"
#check @DominantFiveBody.nestedScalarH_source_formula
#print axioms DominantFiveBody.nestedScalarH_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedScalarH_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedScalarK_source_formula"
#check @DominantFiveBody.nestedScalarK_source_formula
#print axioms DominantFiveBody.nestedScalarK_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedScalarK_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedScalarPositions_formula_complete"
#check @DominantFiveBody.nestedScalarPositions_formula_complete
#print axioms DominantFiveBody.nestedScalarPositions_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.nestedScalarPositions_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedScalarRadialKernel_formula"
#check @DominantFiveBody.nestedScalarRadialKernel_formula
#print axioms DominantFiveBody.nestedScalarRadialKernel_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedScalarRadialKernel_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedScalarRadialKernel_substitution"
#check @DominantFiveBody.nestedScalarRadialKernel_substitution
#print axioms DominantFiveBody.nestedScalarRadialKernel_substitution
#eval IO.println "COVERAGE_END DominantFiveBody.nestedScalarRadialKernel_substitution"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSlowPoint_root"
#check @DominantFiveBody.nestedSlowPoint_root
#print axioms DominantFiveBody.nestedSlowPoint_root
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSlowPoint_root"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSlowPoint_source_formula"
#check @DominantFiveBody.nestedSlowPoint_source_formula
#print axioms DominantFiveBody.nestedSlowPoint_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSlowPoint_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSlowRootCandidate_contDiffAt"
#check @DominantFiveBody.nestedSlowRootCandidate_contDiffAt
#print axioms DominantFiveBody.nestedSlowRootCandidate_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSlowRootCandidate_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSlowRootCandidate_contDiffOn"
#check @DominantFiveBody.nestedSlowRootCandidate_contDiffOn
#print axioms DominantFiveBody.nestedSlowRootCandidate_contDiffOn
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSlowRootCandidate_contDiffOn"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSourceCasePermutation_source"
#check @DominantFiveBody.nestedSourceCasePermutation_source
#print axioms DominantFiveBody.nestedSourceCasePermutation_source
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSourceCasePermutation_source"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSourceCaseTable_source"
#check @DominantFiveBody.nestedSourceCaseTable_source
#print axioms DominantFiveBody.nestedSourceCaseTable_source
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSourceCaseTable_source"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSourceCase_order_is_original"
#check @DominantFiveBody.nestedSourceCase_order_is_original
#print axioms DominantFiveBody.nestedSourceCase_order_is_original
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSourceCase_order_is_original"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSource_common_balls_without_alpha_limit"
#check @DominantFiveBody.nestedSource_common_balls_without_alpha_limit
#print axioms DominantFiveBody.nestedSource_common_balls_without_alpha_limit
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSource_common_balls_without_alpha_limit"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSource_individual_inverse_limits"
#check @DominantFiveBody.nestedSource_individual_inverse_limits
#print axioms DominantFiveBody.nestedSource_individual_inverse_limits
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSource_individual_inverse_limits"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound"
#check @DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound
#print axioms DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound
#eval IO.println "COVERAGE_END DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedStrictConvex_of_positive_areas"
#check @DominantFiveBody.nestedStrictConvex_of_positive_areas
#print axioms DominantFiveBody.nestedStrictConvex_of_positive_areas
#eval IO.println "COVERAGE_END DominantFiveBody.nestedStrictConvex_of_positive_areas"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedToFixedSlice_full_abs_det"
#check @DominantFiveBody.nestedToFixedSlice_full_abs_det
#print axioms DominantFiveBody.nestedToFixedSlice_full_abs_det
#eval IO.println "COVERAGE_END DominantFiveBody.nestedToFixedSlice_full_abs_det"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedToFixedSlice_full_det"
#check @DominantFiveBody.nestedToFixedSlice_full_det
#print axioms DominantFiveBody.nestedToFixedSlice_full_det
#eval IO.println "COVERAGE_END DominantFiveBody.nestedToFixedSlice_full_det"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedToFixedSlice_full_matrix"
#check @DominantFiveBody.nestedToFixedSlice_full_matrix
#print axioms DominantFiveBody.nestedToFixedSlice_full_matrix
#eval IO.println "COVERAGE_END DominantFiveBody.nestedToFixedSlice_full_matrix"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nestedUnitPoint_scalar_root"
#check @DominantFiveBody.nestedUnitPoint_scalar_root
#print axioms DominantFiveBody.nestedUnitPoint_scalar_root
#eval IO.println "COVERAGE_END DominantFiveBody.nestedUnitPoint_scalar_root"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.nested_kernel_integral_shift"
#check @DominantFiveBody.nested_kernel_integral_shift
#print axioms DominantFiveBody.nested_kernel_integral_shift
#eval IO.println "COVERAGE_END DominantFiveBody.nested_kernel_integral_shift"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.newtonTargetField_affinePolar_Osquare"
#check @DominantFiveBody.newtonTargetField_affinePolar_Osquare
#print axioms DominantFiveBody.newtonTargetField_affinePolar_Osquare
#eval IO.println "COVERAGE_END DominantFiveBody.newtonTargetField_affinePolar_Osquare"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.noCollision_actual_sequence_capture_of_regular_limit"
#check @DominantFiveBody.noCollision_actual_sequence_capture_of_regular_limit
#print axioms DominantFiveBody.noCollision_actual_sequence_capture_of_regular_limit
#eval IO.println "COVERAGE_END DominantFiveBody.noCollision_actual_sequence_capture_of_regular_limit"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.noCollision_physical_local_continuation"
#check @DominantFiveBody.noCollision_physical_local_continuation
#print axioms DominantFiveBody.noCollision_physical_local_continuation
#eval IO.println "COVERAGE_END DominantFiveBody.noCollision_physical_local_continuation"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_complete_lower_triple_nested_directions"
#check @DominantFiveBody.normalized_complete_lower_triple_nested_directions
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_directions
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_complete_lower_triple_nested_directions"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_complete_lower_triple_nested_original_capture"
#check @DominantFiveBody.normalized_complete_lower_triple_nested_original_capture
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_original_capture
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_complete_lower_triple_nested_original_capture"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_complete_lower_triple_nested_radial_bound"
#check @DominantFiveBody.normalized_complete_lower_triple_nested_radial_bound
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_radial_bound
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_complete_lower_triple_nested_radial_bound"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_complete_lower_triple_nested_scale_complete"
#check @DominantFiveBody.normalized_complete_lower_triple_nested_scale_complete
#print axioms DominantFiveBody.normalized_complete_lower_triple_nested_scale_complete
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_complete_lower_triple_nested_scale_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_complete_lower_triple_regular_actual_capture"
#check @DominantFiveBody.normalized_complete_lower_triple_regular_actual_capture
#print axioms DominantFiveBody.normalized_complete_lower_triple_regular_actual_capture
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_complete_lower_triple_regular_actual_capture"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_complete_pair_actual_capture"
#check @DominantFiveBody.normalized_complete_pair_actual_capture
#print axioms DominantFiveBody.normalized_complete_pair_actual_capture
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_complete_pair_actual_capture"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_complete_pair_actual_chart_limits"
#check @DominantFiveBody.normalized_complete_pair_actual_chart_limits
#print axioms DominantFiveBody.normalized_complete_pair_actual_chart_limits
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_complete_pair_actual_chart_limits"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_complete_upper_triple_nested_scale_complete"
#check @DominantFiveBody.normalized_complete_upper_triple_nested_scale_complete
#print axioms DominantFiveBody.normalized_complete_upper_triple_nested_scale_complete
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_complete_upper_triple_nested_scale_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_complete_upper_triple_regular_actual_capture"
#check @DominantFiveBody.normalized_complete_upper_triple_regular_actual_capture
#print axioms DominantFiveBody.normalized_complete_upper_triple_regular_actual_capture
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_complete_upper_triple_regular_actual_capture"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.normalized_noCollision_ordered_capture"
#check @DominantFiveBody.normalized_noCollision_ordered_capture
#print axioms DominantFiveBody.normalized_noCollision_ordered_capture
#eval IO.println "COVERAGE_END DominantFiveBody.normalized_noCollision_ordered_capture"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.orderedSlice_lower_nested_triple_capture"
#check @DominantFiveBody.orderedSlice_lower_nested_triple_capture
#print axioms DominantFiveBody.orderedSlice_lower_nested_triple_capture
#eval IO.println "COVERAGE_END DominantFiveBody.orderedSlice_lower_nested_triple_capture"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.orderedSlice_smooth_connection_explicit"
#check @DominantFiveBody.orderedSlice_smooth_connection_explicit
#print axioms DominantFiveBody.orderedSlice_smooth_connection_explicit
#eval IO.println "COVERAGE_END DominantFiveBody.orderedSlice_smooth_connection_explicit"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.orientedArea_cyclic"
#check @DominantFiveBody.orientedArea_cyclic
#print axioms DominantFiveBody.orientedArea_cyclic
#eval IO.println "COVERAGE_END DominantFiveBody.orientedArea_cyclic"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairAngularDifference_at_boundary"
#check @DominantFiveBody.pairAngularDifference_at_boundary
#print axioms DominantFiveBody.pairAngularDifference_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.pairAngularDifference_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairAngularExterior_joint_contDiffAt"
#check @DominantFiveBody.pairAngularExterior_joint_contDiffAt
#print axioms DominantFiveBody.pairAngularExterior_joint_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.pairAngularExterior_joint_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairAngularMean_at_boundary"
#check @DominantFiveBody.pairAngularMean_at_boundary
#print axioms DominantFiveBody.pairAngularMean_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.pairAngularMean_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairAreaQuotient_joint_contDiff"
#check @DominantFiveBody.pairAreaQuotient_joint_contDiff
#print axioms DominantFiveBody.pairAreaQuotient_joint_contDiff
#eval IO.println "COVERAGE_END DominantFiveBody.pairAreaQuotient_joint_contDiff"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairArea_factor"
#check @DominantFiveBody.pairArea_factor
#print axioms DominantFiveBody.pairArea_factor
#eval IO.println "COVERAGE_END DominantFiveBody.pairArea_factor"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartExtendedRows_eq_physical"
#check @DominantFiveBody.pairChartExtendedRows_eq_physical
#print axioms DominantFiveBody.pairChartExtendedRows_eq_physical
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartExtendedRows_eq_physical"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartExtendedRows_joint_analyticAt"
#check @DominantFiveBody.pairChartExtendedRows_joint_analyticAt
#print axioms DominantFiveBody.pairChartExtendedRows_joint_analyticAt
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartExtendedRows_joint_analyticAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartExtendedRows_joint_contDiffAt"
#check @DominantFiveBody.pairChartExtendedRows_joint_contDiffAt
#print axioms DominantFiveBody.pairChartExtendedRows_joint_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartExtendedRows_joint_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartJacobian_boundary_isInvertible"
#check @DominantFiveBody.pairChartJacobian_boundary_isInvertible
#print axioms DominantFiveBody.pairChartJacobian_boundary_isInvertible
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartJacobian_boundary_isInvertible"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartJacobian_exterior_source_a0"
#check @DominantFiveBody.pairChartJacobian_exterior_source_a0
#print axioms DominantFiveBody.pairChartJacobian_exterior_source_a0
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartJacobian_exterior_source_a0"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartJacobian_unit_difference"
#check @DominantFiveBody.pairChartJacobian_unit_difference
#print axioms DominantFiveBody.pairChartJacobian_unit_difference
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartJacobian_unit_difference"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartJacobian_unit_exterior"
#check @DominantFiveBody.pairChartJacobian_unit_exterior
#print axioms DominantFiveBody.pairChartJacobian_unit_exterior
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartJacobian_unit_exterior"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartJacobian_unit_mean"
#check @DominantFiveBody.pairChartJacobian_unit_mean
#print axioms DominantFiveBody.pairChartJacobian_unit_mean
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartJacobian_unit_mean"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartJacobian_unit_radial"
#check @DominantFiveBody.pairChartJacobian_unit_radial
#print axioms DominantFiveBody.pairChartJacobian_unit_radial
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartJacobian_unit_radial"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartJacobian_unit_radial_difference"
#check @DominantFiveBody.pairChartJacobian_unit_radial_difference
#print axioms DominantFiveBody.pairChartJacobian_unit_radial_difference
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartJacobian_unit_radial_difference"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartPhysicalRows_zero_iff"
#check @DominantFiveBody.pairChartPhysicalRows_zero_iff
#print axioms DominantFiveBody.pairChartPhysicalRows_zero_iff
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartPhysicalRows_zero_iff"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartRows_half_interval_choice"
#check @DominantFiveBody.pairChartRows_half_interval_choice
#print axioms DominantFiveBody.pairChartRows_half_interval_choice
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartRows_half_interval_choice"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChartWSq_formula_complete"
#check @DominantFiveBody.pairChartWSq_formula_complete
#print axioms DominantFiveBody.pairChartWSq_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.pairChartWSq_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChart_boundary_radial"
#check @DominantFiveBody.pairChart_boundary_radial
#print axioms DominantFiveBody.pairChart_boundary_radial
#eval IO.println "COVERAGE_END DominantFiveBody.pairChart_boundary_radial"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChart_compact_boundary_continuation"
#check @DominantFiveBody.pairChart_compact_boundary_continuation
#print axioms DominantFiveBody.pairChart_compact_boundary_continuation
#eval IO.println "COVERAGE_END DominantFiveBody.pairChart_compact_boundary_continuation"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChart_compact_physical_continuation"
#check @DominantFiveBody.pairChart_compact_physical_continuation
#print axioms DominantFiveBody.pairChart_compact_physical_continuation
#eval IO.println "COVERAGE_END DominantFiveBody.pairChart_compact_physical_continuation"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChart_coordinates_complete"
#check @DominantFiveBody.pairChart_coordinates_complete
#print axioms DominantFiveBody.pairChart_coordinates_complete
#eval IO.println "COVERAGE_END DominantFiveBody.pairChart_coordinates_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChart_distance_sq"
#check @DominantFiveBody.pairChart_distance_sq
#print axioms DominantFiveBody.pairChart_distance_sq
#eval IO.println "COVERAGE_END DominantFiveBody.pairChart_distance_sq"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChart_omitted_mass_lower_fixed_anchor"
#check @DominantFiveBody.pairChart_omitted_mass_lower_fixed_anchor
#print axioms DominantFiveBody.pairChart_omitted_mass_lower_fixed_anchor
#eval IO.println "COVERAGE_END DominantFiveBody.pairChart_omitted_mass_lower_fixed_anchor"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairChart_zero_eps_all_scale_faces"
#check @DominantFiveBody.pairChart_zero_eps_all_scale_faces
#print axioms DominantFiveBody.pairChart_zero_eps_all_scale_faces
#eval IO.println "COVERAGE_END DominantFiveBody.pairChart_zero_eps_all_scale_faces"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairCoordinateMatrix_det"
#check @DominantFiveBody.pairCoordinateMatrix_det
#print axioms DominantFiveBody.pairCoordinateMatrix_det
#eval IO.println "COVERAGE_END DominantFiveBody.pairCoordinateMatrix_det"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairInternal_weighted_radial_source"
#check @DominantFiveBody.pairInternal_weighted_radial_source
#print axioms DominantFiveBody.pairInternal_weighted_radial_source
#eval IO.println "COVERAGE_END DominantFiveBody.pairInternal_weighted_radial_source"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairRadialDifference_at_boundary"
#check @DominantFiveBody.pairRadialDifference_at_boundary
#print axioms DominantFiveBody.pairRadialDifference_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.pairRadialDifference_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairRadialExterior_joint_contDiffAt"
#check @DominantFiveBody.pairRadialExterior_joint_contDiffAt
#print axioms DominantFiveBody.pairRadialExterior_joint_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.pairRadialExterior_joint_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairRadialMean_at_boundary"
#check @DominantFiveBody.pairRadialMean_at_boundary
#print axioms DominantFiveBody.pairRadialMean_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.pairRadialMean_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairRadial_root_compact_uniform_bound"
#check @DominantFiveBody.pairRadial_root_compact_uniform_bound
#print axioms DominantFiveBody.pairRadial_root_compact_uniform_bound
#eval IO.println "COVERAGE_END DominantFiveBody.pairRadial_root_compact_uniform_bound"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairRadial_root_exact_factor"
#check @DominantFiveBody.pairRadial_root_exact_factor
#print axioms DominantFiveBody.pairRadial_root_exact_factor
#eval IO.println "COVERAGE_END DominantFiveBody.pairRadial_root_exact_factor"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairRows_recovery"
#check @DominantFiveBody.pairRows_recovery
#print axioms DominantFiveBody.pairRows_recovery
#eval IO.println "COVERAGE_END DominantFiveBody.pairRows_recovery"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pairSourceA0_abs_lower"
#check @DominantFiveBody.pairSourceA0_abs_lower
#print axioms DominantFiveBody.pairSourceA0_abs_lower
#eval IO.println "COVERAGE_END DominantFiveBody.pairSourceA0_abs_lower"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.pair_areas_boundary_complete"
#check @DominantFiveBody.pair_areas_boundary_complete
#print axioms DominantFiveBody.pair_areas_boundary_complete
#eval IO.println "COVERAGE_END DominantFiveBody.pair_areas_boundary_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.polarDividedEdgeIntegral_factor"
#check @DominantFiveBody.polarDividedEdgeIntegral_factor
#print axioms DominantFiveBody.polarDividedEdgeIntegral_factor
#eval IO.println "COVERAGE_END DominantFiveBody.polarDividedEdgeIntegral_factor"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.polarDividedEdgeIntegral_zero"
#check @DominantFiveBody.polarDividedEdgeIntegral_zero
#print axioms DominantFiveBody.polarDividedEdgeIntegral_zero
#eval IO.println "COVERAGE_END DominantFiveBody.polarDividedEdgeIntegral_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.reducedAngularJacobian_zero_full_matrix"
#check @DominantFiveBody.reducedAngularJacobian_zero_full_matrix
#print axioms DominantFiveBody.reducedAngularJacobian_zero_full_matrix
#eval IO.println "COVERAGE_END DominantFiveBody.reducedAngularJacobian_zero_full_matrix"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.reducedJacobian_at_closed_separated_root_isInvertible"
#check @DominantFiveBody.reducedJacobian_at_closed_separated_root_isInvertible
#print axioms DominantFiveBody.reducedJacobian_at_closed_separated_root_isInvertible
#eval IO.println "COVERAGE_END DominantFiveBody.reducedJacobian_at_closed_separated_root_isInvertible"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.regularTripleBoundaryM_source_formula"
#check @DominantFiveBody.regularTripleBoundaryM_source_formula
#print axioms DominantFiveBody.regularTripleBoundaryM_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.regularTripleBoundaryM_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.regularTripleScalarH_source_formula"
#check @DominantFiveBody.regularTripleScalarH_source_formula
#print axioms DominantFiveBody.regularTripleScalarH_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.regularTripleScalarH_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.scalarSlow_positive_seed"
#check @DominantFiveBody.scalarSlow_positive_seed
#print axioms DominantFiveBody.scalarSlow_positive_seed
#eval IO.println "COVERAGE_END DominantFiveBody.scalarSlow_positive_seed"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.scalarSlow_source_equations"
#check @DominantFiveBody.scalarSlow_source_equations
#print axioms DominantFiveBody.scalarSlow_source_equations
#eval IO.println "COVERAGE_END DominantFiveBody.scalarSlow_source_equations"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScaleAngularTerm_contDiffAt"
#check @DominantFiveBody.singleScaleAngularTerm_contDiffAt
#print axioms DominantFiveBody.singleScaleAngularTerm_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.singleScaleAngularTerm_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScaleAngularTerm_eq_physical"
#check @DominantFiveBody.singleScaleAngularTerm_eq_physical
#print axioms DominantFiveBody.singleScaleAngularTerm_eq_physical
#eval IO.println "COVERAGE_END DominantFiveBody.singleScaleAngularTerm_eq_physical"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScaleChi_complete"
#check @DominantFiveBody.singleScaleChi_complete
#print axioms DominantFiveBody.singleScaleChi_complete
#eval IO.println "COVERAGE_END DominantFiveBody.singleScaleChi_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScaleRadialTerm_contDiffAt"
#check @DominantFiveBody.singleScaleRadialTerm_contDiffAt
#print axioms DominantFiveBody.singleScaleRadialTerm_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.singleScaleRadialTerm_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScaleRadialTerm_eq_physical"
#check @DominantFiveBody.singleScaleRadialTerm_eq_physical
#print axioms DominantFiveBody.singleScaleRadialTerm_eq_physical
#eval IO.println "COVERAGE_END DominantFiveBody.singleScaleRadialTerm_eq_physical"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScaleWSq_formula_complete"
#check @DominantFiveBody.singleScaleWSq_formula_complete
#print axioms DominantFiveBody.singleScaleWSq_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.singleScaleWSq_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScaleWeightedRadialPair_pair_sum"
#check @DominantFiveBody.singleScaleWeightedRadialPair_pair_sum
#print axioms DominantFiveBody.singleScaleWeightedRadialPair_pair_sum
#eval IO.println "COVERAGE_END DominantFiveBody.singleScaleWeightedRadialPair_pair_sum"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScale_distance"
#check @DominantFiveBody.singleScale_distance
#print axioms DominantFiveBody.singleScale_distance
#eval IO.println "COVERAGE_END DominantFiveBody.singleScale_distance"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScale_distance_sq"
#check @DominantFiveBody.singleScale_distance_sq
#print axioms DominantFiveBody.singleScale_distance_sq
#eval IO.println "COVERAGE_END DominantFiveBody.singleScale_distance_sq"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScale_internal_weighted_angular_sum"
#check @DominantFiveBody.singleScale_internal_weighted_angular_sum
#print axioms DominantFiveBody.singleScale_internal_weighted_angular_sum
#eval IO.println "COVERAGE_END DominantFiveBody.singleScale_internal_weighted_angular_sum"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScale_pair_weighted_radial_sum"
#check @DominantFiveBody.singleScale_pair_weighted_radial_sum
#print axioms DominantFiveBody.singleScale_pair_weighted_radial_sum
#eval IO.println "COVERAGE_END DominantFiveBody.singleScale_pair_weighted_radial_sum"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.singleScale_three_weighted_radial_sum"
#check @DominantFiveBody.singleScale_three_weighted_radial_sum
#print axioms DominantFiveBody.singleScale_three_weighted_radial_sum
#eval IO.println "COVERAGE_END DominantFiveBody.singleScale_three_weighted_radial_sum"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleAngularDifference_boundary_eq_LM"
#check @DominantFiveBody.tripleAngularDifference_boundary_eq_LM
#print axioms DominantFiveBody.tripleAngularDifference_boundary_eq_LM
#eval IO.println "COVERAGE_END DominantFiveBody.tripleAngularDifference_boundary_eq_LM"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleAngularDifference_unit_scalar"
#check @DominantFiveBody.tripleAngularDifference_unit_scalar
#print axioms DominantFiveBody.tripleAngularDifference_unit_scalar
#eval IO.println "COVERAGE_END DominantFiveBody.tripleAngularDifference_unit_scalar"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleAngularExteriorDifference_background"
#check @DominantFiveBody.tripleAngularExteriorDifference_background
#print axioms DominantFiveBody.tripleAngularExteriorDifference_background
#eval IO.println "COVERAGE_END DominantFiveBody.tripleAngularExteriorDifference_background"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleAngularExterior_joint_contDiffAt"
#check @DominantFiveBody.tripleAngularExterior_joint_contDiffAt
#print axioms DominantFiveBody.tripleAngularExterior_joint_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.tripleAngularExterior_joint_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleAngularMean_background_zero"
#check @DominantFiveBody.tripleAngularMean_background_zero
#print axioms DominantFiveBody.tripleAngularMean_background_zero
#eval IO.println "COVERAGE_END DominantFiveBody.tripleAngularMean_background_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleAngularMean_boundary_source_H"
#check @DominantFiveBody.tripleAngularMean_boundary_source_H
#print axioms DominantFiveBody.tripleAngularMean_boundary_source_H
#eval IO.println "COVERAGE_END DominantFiveBody.tripleAngularMean_boundary_source_H"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleAreaAlongRoot_deriv_eq_partial"
#check @DominantFiveBody.tripleAreaAlongRoot_deriv_eq_partial
#print axioms DominantFiveBody.tripleAreaAlongRoot_deriv_eq_partial
#eval IO.println "COVERAGE_END DominantFiveBody.tripleAreaAlongRoot_deriv_eq_partial"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleAreaAlongZeroRoot_hasDerivAt"
#check @DominantFiveBody.tripleAreaAlongZeroRoot_hasDerivAt
#print axioms DominantFiveBody.tripleAreaAlongZeroRoot_hasDerivAt
#eval IO.println "COVERAGE_END DominantFiveBody.tripleAreaAlongZeroRoot_hasDerivAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleBoundaryDisplacement_angular"
#check @DominantFiveBody.tripleBoundaryDisplacement_angular
#print axioms DominantFiveBody.tripleBoundaryDisplacement_angular
#eval IO.println "COVERAGE_END DominantFiveBody.tripleBoundaryDisplacement_angular"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleBoundaryDisplacement_radial"
#check @DominantFiveBody.tripleBoundaryDisplacement_radial
#print axioms DominantFiveBody.tripleBoundaryDisplacement_radial
#eval IO.println "COVERAGE_END DominantFiveBody.tripleBoundaryDisplacement_radial"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartExtendedRows_eq_physical"
#check @DominantFiveBody.tripleChartExtendedRows_eq_physical
#print axioms DominantFiveBody.tripleChartExtendedRows_eq_physical
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartExtendedRows_eq_physical"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartExtendedRows_joint_analyticAt"
#check @DominantFiveBody.tripleChartExtendedRows_joint_analyticAt
#print axioms DominantFiveBody.tripleChartExtendedRows_joint_analyticAt
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartExtendedRows_joint_analyticAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartExtendedRows_joint_contDiffAt"
#check @DominantFiveBody.tripleChartExtendedRows_joint_contDiffAt
#print axioms DominantFiveBody.tripleChartExtendedRows_joint_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartExtendedRows_joint_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartExtendedRows_unit_root"
#check @DominantFiveBody.tripleChartExtendedRows_unit_root
#print axioms DominantFiveBody.tripleChartExtendedRows_unit_root
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartExtendedRows_unit_root"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartExtendedRows_zero_iff_normalized"
#check @DominantFiveBody.tripleChartExtendedRows_zero_iff_normalized
#print axioms DominantFiveBody.tripleChartExtendedRows_zero_iff_normalized
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartExtendedRows_zero_iff_normalized"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartJacobian_unit_difference"
#check @DominantFiveBody.tripleChartJacobian_unit_difference
#print axioms DominantFiveBody.tripleChartJacobian_unit_difference
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartJacobian_unit_difference"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartJacobian_unit_mean"
#check @DominantFiveBody.tripleChartJacobian_unit_mean
#print axioms DominantFiveBody.tripleChartJacobian_unit_mean
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartJacobian_unit_mean"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartJacobian_unit_radial"
#check @DominantFiveBody.tripleChartJacobian_unit_radial
#print axioms DominantFiveBody.tripleChartJacobian_unit_radial
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartJacobian_unit_radial"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartJacobian_unit_radial_difference"
#check @DominantFiveBody.tripleChartJacobian_unit_radial_difference
#print axioms DominantFiveBody.tripleChartJacobian_unit_radial_difference
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartJacobian_unit_radial_difference"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChartPoint_cartesian_Osquare"
#check @DominantFiveBody.tripleChartPoint_cartesian_Osquare
#print axioms DominantFiveBody.tripleChartPoint_cartesian_Osquare
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChartPoint_cartesian_Osquare"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_boundary_continuation_of_scalar_root"
#check @DominantFiveBody.tripleChart_boundary_continuation_of_scalar_root
#print axioms DominantFiveBody.tripleChart_boundary_continuation_of_scalar_root
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_boundary_continuation_of_scalar_root"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_boundary_radial"
#check @DominantFiveBody.tripleChart_boundary_radial
#print axioms DominantFiveBody.tripleChart_boundary_radial
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_boundary_radial"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_convex_physical_continuation"
#check @DominantFiveBody.tripleChart_convex_physical_continuation
#print axioms DominantFiveBody.tripleChart_convex_physical_continuation
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_convex_physical_continuation"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_coordinates_complete"
#check @DominantFiveBody.tripleChart_coordinates_complete
#print axioms DominantFiveBody.tripleChart_coordinates_complete
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_coordinates_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_exteriorMass_Ocube"
#check @DominantFiveBody.tripleChart_exteriorMass_Ocube
#print axioms DominantFiveBody.tripleChart_exteriorMass_Ocube
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_exteriorMass_Ocube"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_internal_area_positive_neighborhood"
#check @DominantFiveBody.tripleChart_internal_area_positive_neighborhood
#print axioms DominantFiveBody.tripleChart_internal_area_positive_neighborhood
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_internal_area_positive_neighborhood"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_radial_uniform_epsilon_bound"
#check @DominantFiveBody.tripleChart_radial_uniform_epsilon_bound
#print axioms DominantFiveBody.tripleChart_radial_uniform_epsilon_bound
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_radial_uniform_epsilon_bound"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_reaction_Ocube"
#check @DominantFiveBody.tripleChart_reaction_Ocube
#print axioms DominantFiveBody.tripleChart_reaction_Ocube
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_reaction_Ocube"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_relativeAverage_Ocube"
#check @DominantFiveBody.tripleChart_relativeAverage_Ocube
#print axioms DominantFiveBody.tripleChart_relativeAverage_Ocube
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_relativeAverage_Ocube"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_relativeAverage_cubic_identity"
#check @DominantFiveBody.tripleChart_relativeAverage_cubic_identity
#print axioms DominantFiveBody.tripleChart_relativeAverage_cubic_identity
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_relativeAverage_cubic_identity"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_strictConvex_neighborhood"
#check @DominantFiveBody.tripleChart_strictConvex_neighborhood
#print axioms DominantFiveBody.tripleChart_strictConvex_neighborhood
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_strictConvex_neighborhood"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_zero_eps_all_scale_faces"
#check @DominantFiveBody.tripleChart_zero_eps_all_scale_faces
#print axioms DominantFiveBody.tripleChart_zero_eps_all_scale_faces
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_zero_eps_all_scale_faces"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_zero_face_area_zero_of_local_uniqueness"
#check @DominantFiveBody.tripleChart_zero_face_area_zero_of_local_uniqueness
#print axioms DominantFiveBody.tripleChart_zero_face_area_zero_of_local_uniqueness
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_zero_face_area_zero_of_local_uniqueness"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness"
#check @DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness
#print axioms DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleChart_zero_face_parallel_of_local_uniqueness"
#check @DominantFiveBody.tripleChart_zero_face_parallel_of_local_uniqueness
#print axioms DominantFiveBody.tripleChart_zero_face_parallel_of_local_uniqueness
#eval IO.println "COVERAGE_END DominantFiveBody.tripleChart_zero_face_parallel_of_local_uniqueness"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleCircleAreaCoefficient_zero"
#check @DominantFiveBody.tripleCircleAreaCoefficient_zero
#print axioms DominantFiveBody.tripleCircleAreaCoefficient_zero
#eval IO.println "COVERAGE_END DominantFiveBody.tripleCircleAreaCoefficient_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleCircleAreaCoefficient_zero_pos"
#check @DominantFiveBody.tripleCircleAreaCoefficient_zero_pos
#print axioms DominantFiveBody.tripleCircleAreaCoefficient_zero_pos
#eval IO.println "COVERAGE_END DominantFiveBody.tripleCircleAreaCoefficient_zero_pos"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleExteriorRadialRow_background_zero"
#check @DominantFiveBody.tripleExteriorRadialRow_background_zero
#print axioms DominantFiveBody.tripleExteriorRadialRow_background_zero
#eval IO.println "COVERAGE_END DominantFiveBody.tripleExteriorRadialRow_background_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleExternalAreaQuotient_exterior_boundary"
#check @DominantFiveBody.tripleExternalAreaQuotient_exterior_boundary
#print axioms DominantFiveBody.tripleExternalAreaQuotient_exterior_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.tripleExternalAreaQuotient_exterior_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleExternalAreaQuotient_primary_boundary"
#check @DominantFiveBody.tripleExternalAreaQuotient_primary_boundary
#print axioms DominantFiveBody.tripleExternalAreaQuotient_primary_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.tripleExternalAreaQuotient_primary_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleIntegratedJacobian_entries"
#check @DominantFiveBody.tripleIntegratedJacobian_entries
#print axioms DominantFiveBody.tripleIntegratedJacobian_entries
#eval IO.println "COVERAGE_END DominantFiveBody.tripleIntegratedJacobian_entries"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleIntegratedJacobian_lower_norm_bound"
#check @DominantFiveBody.tripleIntegratedJacobian_lower_norm_bound
#print axioms DominantFiveBody.tripleIntegratedJacobian_lower_norm_bound
#eval IO.println "COVERAGE_END DominantFiveBody.tripleIntegratedJacobian_lower_norm_bound"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalAngularReduced_vector_projection"
#check @DominantFiveBody.tripleInternalAngularReduced_vector_projection
#print axioms DominantFiveBody.tripleInternalAngularReduced_vector_projection
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalAngularReduced_vector_projection"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalAngular_eq_physical"
#check @DominantFiveBody.tripleInternalAngular_eq_physical
#print axioms DominantFiveBody.tripleInternalAngular_eq_physical
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalAngular_eq_physical"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalAngular_source_formula"
#check @DominantFiveBody.tripleInternalAngular_source_formula
#print axioms DominantFiveBody.tripleInternalAngular_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalAngular_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalArea_factor_cubic_along_root"
#check @DominantFiveBody.tripleInternalArea_factor_cubic_along_root
#print axioms DominantFiveBody.tripleInternalArea_factor_cubic_along_root
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalArea_factor_cubic_along_root"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalCartesian_Osquare"
#check @DominantFiveBody.tripleInternalCartesian_Osquare
#print axioms DominantFiveBody.tripleInternalCartesian_Osquare
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalCartesian_Osquare"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalCartesian_scaling"
#check @DominantFiveBody.tripleInternalCartesian_scaling
#print axioms DominantFiveBody.tripleInternalCartesian_scaling
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalCartesian_scaling"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalRadialReduced_vector_projection"
#check @DominantFiveBody.tripleInternalRadialReduced_vector_projection
#print axioms DominantFiveBody.tripleInternalRadialReduced_vector_projection
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalRadialReduced_vector_projection"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalRadial_eq_physical"
#check @DominantFiveBody.tripleInternalRadial_eq_physical
#print axioms DominantFiveBody.tripleInternalRadial_eq_physical
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalRadial_eq_physical"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalRadial_source_formula"
#check @DominantFiveBody.tripleInternalRadial_source_formula
#print axioms DominantFiveBody.tripleInternalRadial_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalRadial_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalVectorQuotient_Olinear"
#check @DominantFiveBody.tripleInternalVectorQuotient_Olinear
#print axioms DominantFiveBody.tripleInternalVectorQuotient_Olinear
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalVectorQuotient_Olinear"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalVectorQuotient_contDiffAt"
#check @DominantFiveBody.tripleInternalVectorQuotient_contDiffAt
#print axioms DominantFiveBody.tripleInternalVectorQuotient_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalVectorQuotient_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternalVectorQuotient_zero"
#check @DominantFiveBody.tripleInternalVectorQuotient_zero
#print axioms DominantFiveBody.tripleInternalVectorQuotient_zero
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternalVectorQuotient_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternal_weighted_angular_zero"
#check @DominantFiveBody.tripleInternal_weighted_angular_zero
#print axioms DominantFiveBody.tripleInternal_weighted_angular_zero
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternal_weighted_angular_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleInternal_weighted_radial_upper_sum"
#check @DominantFiveBody.tripleInternal_weighted_radial_upper_sum
#print axioms DominantFiveBody.tripleInternal_weighted_radial_upper_sum
#eval IO.println "COVERAGE_END DominantFiveBody.tripleInternal_weighted_radial_upper_sum"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleOrderedSegment_ordered"
#check @DominantFiveBody.tripleOrderedSegment_ordered
#print axioms DominantFiveBody.tripleOrderedSegment_ordered
#eval IO.println "COVERAGE_END DominantFiveBody.tripleOrderedSegment_ordered"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.triplePointDirection_identity"
#check @DominantFiveBody.triplePointDirection_identity
#print axioms DominantFiveBody.triplePointDirection_identity
#eval IO.println "COVERAGE_END DominantFiveBody.triplePointDirection_identity"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.triplePointDirection_joint_contDiff"
#check @DominantFiveBody.triplePointDirection_joint_contDiff
#print axioms DominantFiveBody.triplePointDirection_joint_contDiff
#eval IO.println "COVERAGE_END DominantFiveBody.triplePointDirection_joint_contDiff"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.triplePointDirection_original_integral_all_scales"
#check @DominantFiveBody.triplePointDirection_original_integral_all_scales
#print axioms DominantFiveBody.triplePointDirection_original_integral_all_scales
#eval IO.println "COVERAGE_END DominantFiveBody.triplePointDirection_original_integral_all_scales"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.triplePointDirection_source_at_zero"
#check @DominantFiveBody.triplePointDirection_source_at_zero
#print axioms DominantFiveBody.triplePointDirection_source_at_zero
#eval IO.println "COVERAGE_END DominantFiveBody.triplePointDirection_source_at_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleRadialDifference_at_boundary"
#check @DominantFiveBody.tripleRadialDifference_at_boundary
#print axioms DominantFiveBody.tripleRadialDifference_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.tripleRadialDifference_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleRadialExteriorDifference_background"
#check @DominantFiveBody.tripleRadialExteriorDifference_background
#print axioms DominantFiveBody.tripleRadialExteriorDifference_background
#eval IO.println "COVERAGE_END DominantFiveBody.tripleRadialExteriorDifference_background"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleRadialExterior_joint_contDiffAt"
#check @DominantFiveBody.tripleRadialExterior_joint_contDiffAt
#print axioms DominantFiveBody.tripleRadialExterior_joint_contDiffAt
#eval IO.println "COVERAGE_END DominantFiveBody.tripleRadialExterior_joint_contDiffAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleRadialMean_at_boundary"
#check @DominantFiveBody.tripleRadialMean_at_boundary
#print axioms DominantFiveBody.tripleRadialMean_at_boundary
#eval IO.println "COVERAGE_END DominantFiveBody.tripleRadialMean_at_boundary"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleRadialMean_background_zero"
#check @DominantFiveBody.tripleRadialMean_background_zero
#print axioms DominantFiveBody.tripleRadialMean_background_zero
#eval IO.println "COVERAGE_END DominantFiveBody.tripleRadialMean_background_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleReducedDifferential_matrix"
#check @DominantFiveBody.tripleReducedDifferential_matrix
#print axioms DominantFiveBody.tripleReducedDifferential_matrix
#eval IO.println "COVERAGE_END DominantFiveBody.tripleReducedDifferential_matrix"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleReducedJacobian_det_ne_zero"
#check @DominantFiveBody.tripleReducedJacobian_det_ne_zero
#print axioms DominantFiveBody.tripleReducedJacobian_det_ne_zero
#eval IO.println "COVERAGE_END DominantFiveBody.tripleReducedJacobian_det_ne_zero"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleReducedJacobian_formula_complete"
#check @DominantFiveBody.tripleReducedJacobian_formula_complete
#print axioms DominantFiveBody.tripleReducedJacobian_formula_complete
#eval IO.println "COVERAGE_END DominantFiveBody.tripleReducedJacobian_formula_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleRows_recovery"
#check @DominantFiveBody.tripleRows_recovery
#print axioms DominantFiveBody.tripleRows_recovery
#eval IO.println "COVERAGE_END DominantFiveBody.tripleRows_recovery"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleRows_zero_iff"
#check @DominantFiveBody.tripleRows_zero_iff
#print axioms DominantFiveBody.tripleRows_zero_iff
#eval IO.println "COVERAGE_END DominantFiveBody.tripleRows_zero_iff"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarJacobian_lower_norm_bound"
#check @DominantFiveBody.tripleScalarJacobian_lower_norm_bound
#print axioms DominantFiveBody.tripleScalarJacobian_lower_norm_bound
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarJacobian_lower_norm_bound"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarJacobian_strict_row_dominance"
#check @DominantFiveBody.tripleScalarJacobian_strict_row_dominance
#print axioms DominantFiveBody.tripleScalarJacobian_strict_row_dominance
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarJacobian_strict_row_dominance"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarPotential_critical_iff_root"
#check @DominantFiveBody.tripleScalarPotential_critical_iff_root
#print axioms DominantFiveBody.tripleScalarPotential_critical_iff_root
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarPotential_critical_iff_root"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarPotential_divided_gradient"
#check @DominantFiveBody.tripleScalarPotential_divided_gradient
#print axioms DominantFiveBody.tripleScalarPotential_divided_gradient
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarPotential_divided_gradient"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarPotential_exists_minimizer"
#check @DominantFiveBody.tripleScalarPotential_exists_minimizer
#print axioms DominantFiveBody.tripleScalarPotential_exists_minimizer
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarPotential_exists_minimizer"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarPotential_isProperMap"
#check @DominantFiveBody.tripleScalarPotential_isProperMap
#print axioms DominantFiveBody.tripleScalarPotential_isProperMap
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarPotential_isProperMap"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarPotential_source_formula"
#check @DominantFiveBody.tripleScalarPotential_source_formula
#print axioms DominantFiveBody.tripleScalarPotential_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarPotential_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarPotential_strictConvexOn"
#check @DominantFiveBody.tripleScalarPotential_strictConvexOn
#print axioms DominantFiveBody.tripleScalarPotential_strictConvexOn
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarPotential_strictConvexOn"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarResidual_hasFDerivAt"
#check @DominantFiveBody.tripleScalarResidual_hasFDerivAt
#print axioms DominantFiveBody.tripleScalarResidual_hasFDerivAt
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarResidual_hasFDerivAt"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalarResidual_ordered_segment_integral"
#check @DominantFiveBody.tripleScalarResidual_ordered_segment_integral
#print axioms DominantFiveBody.tripleScalarResidual_ordered_segment_integral
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalarResidual_ordered_segment_integral"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalar_J_entries_complete"
#check @DominantFiveBody.tripleScalar_J_entries_complete
#print axioms DominantFiveBody.tripleScalar_J_entries_complete
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalar_J_entries_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalar_centered_gap_root_recovery"
#check @DominantFiveBody.tripleScalar_centered_gap_root_recovery
#print axioms DominantFiveBody.tripleScalar_centered_gap_root_recovery
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalar_centered_gap_root_recovery"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalar_matrices_complete"
#check @DominantFiveBody.tripleScalar_matrices_complete
#print axioms DominantFiveBody.tripleScalar_matrices_complete
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalar_matrices_complete"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalar_potential_root_existsUnique_centered"
#check @DominantFiveBody.tripleScalar_potential_root_existsUnique_centered
#print axioms DominantFiveBody.tripleScalar_potential_root_existsUnique_centered
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalar_potential_root_existsUnique_centered"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalar_root_unique_by_integratedJacobian"
#check @DominantFiveBody.tripleScalar_root_unique_by_integratedJacobian
#print axioms DominantFiveBody.tripleScalar_root_unique_by_integratedJacobian
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalar_root_unique_by_integratedJacobian"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleScalar_root_weighted_center"
#check @DominantFiveBody.tripleScalar_root_weighted_center
#print axioms DominantFiveBody.tripleScalar_root_weighted_center
#eval IO.println "COVERAGE_END DominantFiveBody.tripleScalar_root_weighted_center"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleSlowPoint_root"
#check @DominantFiveBody.tripleSlowPoint_root
#print axioms DominantFiveBody.tripleSlowPoint_root
#eval IO.println "COVERAGE_END DominantFiveBody.tripleSlowPoint_root"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleSlowPoint_source_formula"
#check @DominantFiveBody.tripleSlowPoint_source_formula
#print axioms DominantFiveBody.tripleSlowPoint_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.tripleSlowPoint_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.tripleSlowPoint_vector_balance"
#check @DominantFiveBody.tripleSlowPoint_vector_balance
#print axioms DominantFiveBody.tripleSlowPoint_vector_balance
#eval IO.println "COVERAGE_END DominantFiveBody.tripleSlowPoint_vector_balance"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.twoSourcePolarAngular_fderiv_apply"
#check @DominantFiveBody.twoSourcePolarAngular_fderiv_apply
#print axioms DominantFiveBody.twoSourcePolarAngular_fderiv_apply
#eval IO.println "COVERAGE_END DominantFiveBody.twoSourcePolarAngular_fderiv_apply"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.twoSourcePolarAngular_source_formula"
#check @DominantFiveBody.twoSourcePolarAngular_source_formula
#print axioms DominantFiveBody.twoSourcePolarAngular_source_formula
#eval IO.println "COVERAGE_END DominantFiveBody.twoSourcePolarAngular_source_formula"
#eval IO.println "COVERAGE_BEGIN DominantFiveBody.weighted_angularResidual_zero"
#check @DominantFiveBody.weighted_angularResidual_zero
#print axioms DominantFiveBody.weighted_angularResidual_zero
#eval IO.println "COVERAGE_END DominantFiveBody.weighted_angularResidual_zero"
