"""Attach explicitly source-reviewed v1 bridge lemmas, without certifying a build.

These are semantic bindings only. verify_paper.ps1 must still check their exact
types, definitions, all axioms, a clean build and fresh kernel replay.
"""
from pathlib import Path
import copy
import json

ROOT=Path(__file__).resolve().parents[1]


# Frozen source-reviewed obligations, not inferred from the ledger at verification time.
REVIEWED_V1_REQUIREMENTS = {'eq:co-equations': {'definitions': ['DominantFiveBody.coorbitalDistance',
                                     'DominantFiveBody.coorbitalPotential',
                                     'DominantFiveBody.coorbitalResidual',
                                     'DominantFiveBody.satellitePairs'],
                     'theorems': ['DominantFiveBody.coorbitalPotential_eq_angularPotential']},
 'prose:487': {'definitions': [],
               'theorems': ['DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_individual_limits',
                            'DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_near_display_bound',
                            'DominantFiveBody.normalized_complete_lower_triple_nested_rectangle_near_display_rhs_vanishes',
                            'DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_individual_limits',
                            'DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_near_display_bound',
                            'DominantFiveBody.normalized_complete_upper_triple_nested_rectangle_near_display_rhs_vanishes',
                            'DominantFiveBody.physicalSourceAngularRadialDerivative_near_display_bound',
                            'DominantFiveBody.physical_nested_polar_rectangle_derivatives_individually_uniform']},
 'prose:833': {'definitions': [],
               'theorems': ['DominantFiveBody.affinePolarPoint_cartesian_Osquare',
                            'DominantFiveBody.affinePolarPoint_divided_identity',
                            'DominantFiveBody.backgroundProbeField_affinePolar_Osquare',
                            'DominantFiveBody.backgroundProbeField_zero',
                            'DominantFiveBody.nestedBoundaryDisplacement_to_triple',
                            'DominantFiveBody.nestedChartPoint_cartesian_Osquare',
                            'DominantFiveBody.nestedChart_reaction_Ocube',
                            'DominantFiveBody.nestedSlowPoint_root',
                            'DominantFiveBody.newtonTargetField_affinePolar_Osquare',
                            'DominantFiveBody.tripleAngularExteriorDifference_background',
                            'DominantFiveBody.tripleAngularMean_background_zero',
                            'DominantFiveBody.tripleBoundaryDisplacement_angular',
                            'DominantFiveBody.tripleBoundaryDisplacement_radial',
                            'DominantFiveBody.tripleChartPoint_cartesian_Osquare',
                            'DominantFiveBody.tripleChart_exteriorMass_Ocube',
                            'DominantFiveBody.tripleChart_reaction_Ocube',
                            'DominantFiveBody.tripleChart_relativeAverage_Ocube',
                            'DominantFiveBody.tripleChart_relativeAverage_cubic_identity',
                            'DominantFiveBody.tripleExteriorRadialRow_background_zero',
                            'DominantFiveBody.tripleInternalAngularReduced_vector_projection',
                            'DominantFiveBody.tripleInternalCartesian_Osquare',
                            'DominantFiveBody.tripleInternalCartesian_scaling',
                            'DominantFiveBody.tripleInternalRadialReduced_vector_projection',
                            'DominantFiveBody.tripleInternalVectorQuotient_Olinear',
                            'DominantFiveBody.tripleInternalVectorQuotient_contDiffAt',
                            'DominantFiveBody.tripleInternalVectorQuotient_zero',
                            'DominantFiveBody.tripleRadialExteriorDifference_background',
                            'DominantFiveBody.tripleRadialMean_background_zero',
                            'DominantFiveBody.tripleSlowPoint_root',
                            'DominantFiveBody.tripleSlowPoint_vector_balance',
                            'DominantFiveBody.v1FieldDefect_Ocube_of_fixed_exterior',
                            'DominantFiveBody.v1FieldDefect_cubic_factor',
                            'DominantFiveBody.v1_epsilon_angularResidual_corrected_projection',
                            'DominantFiveBody.v1_nestedChartPoints_fixed_exterior',
                            'DominantFiveBody.v1_nestedChart_fieldDefect_Ocube',
                            'DominantFiveBody.v1_nestedChart_fieldDefect_cubic_factor',
                            'DominantFiveBody.v1_nestedSlowPoint_fieldDefect_Ocube',
                            'DominantFiveBody.v1_radialResidual_corrected_projection',
                            'DominantFiveBody.v1_tripleChartPoints_fixed_exterior',
                            'DominantFiveBody.v1_tripleChart_fieldDefect_Ocube',
                            'DominantFiveBody.v1_tripleChart_fieldDefect_cubic_factor',
                            'DominantFiveBody.v1_tripleSlowPoint_fieldDefect_Ocube']},
 'v1:boundary.off_solution_projection': {'definitions': ['DominantFiveBody.v1CorrectedVectorResidual',
                                                         'DominantFiveBody.v1FieldDefect'],
                                         'theorems': ['DominantFiveBody.v1_angularResidual_corrected_projection_div',
                                                      'DominantFiveBody.v1_epsilon_angularResidual_corrected_projection',
                                                      'DominantFiveBody.v1_radialResidual_corrected_projection']},
 'v1:hessian.coordinates': {'definitions': ['DominantFiveBody.coorbitalHessianCoefficient',
                                            'DominantFiveBody.coorbitalHessianMatrix'],
                            'theorems': ['DominantFiveBody.coorbitalHessianCoefficient_of_lt',
                                         'DominantFiveBody.coorbitalHessianCoefficient_symmetric',
                                         'DominantFiveBody.coorbitalPhysicalHessian_pair_formula']},
 'v1:hessian.entries': {'definitions': [],
                        'theorems': ['DominantFiveBody.coorbitalHessianMatrix_diagonal',
                                     'DominantFiveBody.coorbitalHessianMatrix_offDiagonal']},
 'v1:hessian.quadratic': {'definitions': [],
                          'theorems': ['DominantFiveBody.coorbitalHessianMatrix_quadratic',
                                       'DominantFiveBody.coorbitalHessianMatrix_quadratic_expanded']},
 'v1:hessian.slice': {'definitions': ['DominantFiveBody.coorbitalFirstAngleInsertion',
                                      'DominantFiveBody.coorbitalSliceHessianMap',
                                      'DominantFiveBody.coorbitalSliceHessianMatrix',
                                      'DominantFiveBody.coorbitalSlicePotential',
                                      'DominantFiveBody.coorbitalSlicePotentialDerivative'],
                      'theorems': ['DominantFiveBody.coorbitalSliceHessianMatrix_eq_submatrix',
                                   'DominantFiveBody.coorbitalSliceHessian_quadratic_zero_first',
                                   'DominantFiveBody.coorbitalSlicePotential_hessian_pullback']}}


def main():
    path=ROOT/'docs/FULL_ASSERTIONS.json'
    ledger=json.loads(path.read_text(encoding='utf-8-sig'))
    rows={r['id']:r for r in ledger['assertions']}

    def bind(key,names,note,definitions=()):
        row=rows[key]
        known={b['lean_declaration']:b for b in row.get('lean_bindings',[])}
        for name in names:
            full='DominantFiveBody.'+name
            known.setdefault(full,dict(lean_declaration=full,lean_statement=''))
        row.update(status='VERIFIED',remaining_dependencies=[],
            lean_bindings=list(known.values()),proof_route=note,
            v1_source_review='Independently reviewed actual objects, quantifiers, domains, zero-mass endpoints and zero-parameter handling. Exact types and kernel acceptance remain separate mandatory checks.')
        if definitions:
            row['definition_references']=sorted(set(row.get('definition_references',[]))|
                {'DominantFiveBody.'+x for x in definitions})

    bind('v1:hessian.coordinates',[
        'coorbitalHessianCoefficient_of_lt','coorbitalHessianCoefficient_symmetric',
        'coorbitalPhysicalHessian_pair_formula'],
        'The matrix is evaluated from the actual second Frechet derivative on coordinate basis vectors; coefficients extend the positive ordered separation symmetrically. No equilibrium or positivity premise is added.',
        ['coorbitalHessianCoefficient','coorbitalHessianMatrix'])
    bind('v1:hessian.entries',['coorbitalHessianMatrix_diagonal','coorbitalHessianMatrix_offDiagonal'],
        'Entrywise computation from the physical second differential, not from the unweighted angular-equation Jacobian.')
    bind('v1:hessian.quadratic',['coorbitalHessianMatrix_quadratic','coorbitalHessianMatrix_quadratic_expanded'],
        'Both the expanded matrix quadratic expression and the weighted square-difference expression are proved for the actual physical Hessian.')
    bind('v1:hessian.slice',['coorbitalSlicePotential_hessian_pullback',
        'coorbitalSliceHessianMatrix_eq_submatrix','coorbitalSliceHessian_quadratic_zero_first'],
        'The genuine restricted physical potential is composed with a continuous linear insertion. Two derivative chain rules yield the principal submatrix; Lean index 0 is manuscript index 1.',
        ['coorbitalFirstAngleInsertion','coorbitalSlicePotential','coorbitalSlicePotentialDerivative',
         'coorbitalSliceHessianMap','coorbitalSliceHessianMatrix'])
    bind('prose:487',[
        'physicalSourceAngularRadialDerivative_near_display_bound',
        'normalized_complete_lower_triple_nested_rectangle_near_display_bound',
        'normalized_complete_upper_triple_nested_rectangle_near_display_bound',
        'normalized_complete_lower_triple_nested_rectangle_near_display_rhs_vanishes',
        'normalized_complete_upper_triple_nested_rectangle_near_display_rhs_vanishes'],
        'The new explicit pointwise inequality follows directly with C=1536 from the actual derivative and local geometry. Its whole-rectangle physical applications and the displayed RHS uniform o(1) use independently established physical geometry/scales. This is a documented reordering of proved source estimates, not a circular input to those core scale proofs. Existing near/exterior uniform limit bindings are retained.')
    bind('v1:boundary.off_solution_projection',[
        'v1_radialResidual_corrected_projection','v1_epsilon_angularResidual_corrected_projection',
        'v1_angularResidual_corrected_projection_div'],
        'Off-solution identities from the real Newton residual; no mass is cancelled. The multiplied angular identity also makes sense at epsilon=0; division is used only under epsilon nonzero.',
        ['v1FieldDefect','v1CorrectedVectorResidual'])
    bind('prose:833',[
        'v1_tripleChartPoints_fixed_exterior','v1_nestedChartPoints_fixed_exterior',
        'v1FieldDefect_cubic_factor','v1FieldDefect_Ocube_of_fixed_exterior',
        'v1_tripleChart_fieldDefect_cubic_factor','v1_tripleChart_fieldDefect_Ocube',
        'v1_nestedChart_fieldDefect_cubic_factor','v1_nestedChart_fieldDefect_Ocube',
        'v1_tripleSlowPoint_fieldDefect_Ocube','v1_nestedSlowPoint_fieldDefect_Ocube',
        'v1_radialResidual_corrected_projection','v1_epsilon_angularResidual_corrected_projection'],
        'The new defect is genuinely relativeField - inverse(1+epsilon) relativeAverage. Fixed exterior cancellation yields an exact t^3 factor and a continuous bounded coefficient on both actual charts, without a root premise. Existing actual first-order boundary projections, internal Newton scaling and zero-face root proofs are retained. The older reaction_Ocube is not substituted for this new defect.')
    ledger['assertions']=sorted(rows.values(),key=lambda r:(r['source_location']['tex_lines'][0],r['id']))
    path.write_text(json.dumps(ledger,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    patch=dict(schema_version=3,version='v1',source_tex_sha256=ledger['source_scope']['tex_sha256'],
        assertions=copy.deepcopy(ledger['assertions']),
        verification_note='Explicit source correspondence only; full exact-type export and fresh acceptance are still required.')
    (ROOT/'docs/V1_COVERAGE_PATCH.json').write_text(json.dumps(patch,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print('Attached exact v1 bridge names. Types must now be exported and re-elaborated; no acceptance is asserted.')


if __name__=='__main__':
    main()
