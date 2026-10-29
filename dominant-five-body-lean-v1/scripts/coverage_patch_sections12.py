"""Source-reviewed binding map for the introduction and coorbital section.

Run with --prepare to emit a Lean environment type export. After that Lean
command succeeds, run with --finish to produce the independent patch and
exact-type audit. Nothing in this script changes the manuscript or proves math.
"""
from pathlib import Path
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / 'docs/FULL_ASSERTIONS.json'
PREFIX = 'DominantFiveBody.'
entries = {x['id']: x for x in json.loads(LEDGER.read_text(encoding='utf-8'))['assertions']}
patch = {}

def bind(key, *names, note=None, definitions=()):
    patch[key] = dict(status='VERIFIED', names=[PREFIX+n for n in names],
        definition_references=[PREFIX+n for n in definitions], remaining_dependencies=[])
    if note:
        patch[key]['proof_route_note'] = note

def context(key, references, note):
    patch[key] = dict(status='CROSS_REFERENCE', names=[], source_assertion_references=references,
        remaining_dependencies=[], proof_route_note=note)

def definitions(key, *names):
    patch[key] = dict(status='DEFINITIONAL', names=[],
        definition_references=[PREFIX+n for n in names], remaining_dependencies=[])

context('prose:58', ['thm:main','thm:coorbital','prop:connection','eq:regular-area','eq:nest-area'],
    'Abstract summary. Each mathematical conclusion is checked at its full source assertion; no separate new premise is introduced.')
patch['prose:64'] = dict(status='BACKGROUND', names=[], remaining_dependencies=[],
    proof_route_note='Prior literature overview. No result in this paragraph is a proof input. The AF chamber seed actually used below is independently proved; the unrelated three-satellite classification is outside the requested substantive proof scope.')
context('prose:66',['thm:main'],'Introductory restatement of the following theorem.')
bind('eq:masses','source_masses',definitions=('masses','PositiveRatio'))
bind('thm:main','main_uniform')
context('prose:72',['thm:main'],'Same source theorem paragraph, already inventoried as thm:main.')
bind('prose:76','main_uniform_unnormalized',definitions=('HullOrder','OrientedSimilar'),
    note='Positive common mass rescaling is proved for the acceleration, mass center, shape space and actual Hessian. Reflections are excluded by determinant +1 in the original definition.')
context('prose:78',['thm:coorbital','prop:connection','eq:regular-area','eq:nest-area'],
    'Proof roadmap referring to separately checked substantive results.')
definitions('prose:82','polarPoint','quarterTurn')
bind('eq:angle-domain','source_angle_domain')
bind('prose:88','unit_satellites_strictConvex_iff_open_semicircle',
    note='Both implications use all five labeled points. The common angular offset is free, hence this is the open-semicircle condition rather than a fixed absolute angular interval.')
context('prose:90',['eq:kernel'],'Notation attribution and introduction to the next defining display.')
bind('eq:kernel','source_scalar_derivatives',definitions=('Coorbital.kernelF','Coorbital.pairPotential','Coorbital.kappa'))
bind('prose:95','coorbitalKernel_neg',definitions=('coorbitalKernel','coorbitalDistance'))
definitions('eq:co-equations','coorbitalResidual','coorbitalPotential','coorbitalDistance','satellitePairs')
bind('prose:101','coorbitalResidual_eq_matrix_sum','coorbitalPotential_coordinate_derivative',
    definitions=('coorbitalMatrix','Coorbital.h'))
bind('eq:kappa','source_scalar_derivatives',definitions=('Coorbital.kappa','Coorbital.kappaPrime'))
bind('prose:111','Coorbital.kernelF_h','Coorbital.kernelF_pi','Coorbital.kernelF_pos_on_short_arc',
    'Coorbital.kernelF_neg_on_long_arc','Coorbital.kappa_h','Coorbital.kernelF_ge_neg_one',
    'kernelF_angle_mul_tendsto_atTop')
bind('kernel.collision_blowup','kernelF_angle_mul_tendsto_atTop')
bind('lem:cycle','angular_hessian_estimate',note='Finite explicit supported cycle decomposition proves the original estimate. The original integral identities are separately verified at display:136; equality cases are checked at display:146.')
context('prose:116',['lem:cycle'],'Hypotheses and notation belonging to the complete numbered lemma.')
definitions('display:118','Coorbital.slopeCoefficient','Coorbital.positiveRemainder')
bind('prose:127','Coorbital.positiveRemainder_pos')
bind('eq:cycle-bound','Coorbital.coorbital_cycle_bound')
bind('prose:132','angularChordHessian_kernel_iff','Coorbital.strictAntiOn_kappa')
bind('display:136','source_integral_comparisons','Coorbital.kappa_intervalIntegrable',
    note='Exact interval integrals and all integrability/endpoint-continuity conditions are proved. Strict comparison follows the already checked mean-value argument for the same strictly decreasing kappa.')
bind('prose:140','Coorbital.kappa_h','Coorbital.positiveRemainder_pos')
bind('prose:142','Coorbital.angularFlow_balanced','Coorbital.four_angular_cycle_decomposition',
    'Coorbital.angularFlow_pos_iff','Coorbital.angularFlow_neg_iff','Coorbital.three_root_gaps',
    'Coorbital.two_root_separation',
    note='For four labels the five supported simple cycles are given by explicit nonnegative coefficients; their six edge equations and support signs are proved. The three- and two-label cases are separately reduced in the same physical model.')
context('prose:144',['display:146','prose:142'],'Notation for the separately checked cycle expressions.')
bind('display:146','Coorbital.two_cycle_display','Coorbital.three_cycle_display',
    'Coorbital.two_denominator_cauchy_eq_iff','Coorbital.two_edge_cycle_eq_zero_iff',
    'Coorbital.three_edge_cycle_eq_zero_iff')
bind('prose:152','Coorbital.two_cycle_display','Coorbital.three_cycle_display',
    'Coorbital.coorbital_cycle_bound','angularChordHessian_kernel_iff','angularHessianMap_constant_right')
bind('thm:coorbital','coorbital_global_complete')
bind('prose:155','coorbital_global_complete','coorbital_cut','coorbitalPhysicalHessian_self')
bind('eq:co-cut','coorbital_cut')
bind('prose:163','Coorbital.four_root_gaps','compact_positive_mass_floor','coorbitalVirial_zero')
bind('display:164','coorbitalVirial_zero')
bind('prose:167','coorbital_negative_terms_lower_bound','coorbitalVirial_pair_with_mass_floor',
    'coorbital_roots_uniform_pair_separation','no_coorbital_root_at_semicircle_boundary',
    'coorbitalMassProjection_isProperMap')
bind('thm:coorbital.mass_floor_collision_exclusion','coorbital_roots_uniform_pair_separation')
bind('thm:coorbital.actual_projection_proper','coorbitalMassProjection_isProperMap')
bind('thm:coorbital.equal_mass_chamber_seed','equalMass_coorbital_existsUnique')
bind('prose:169','coorbital_weightedResidual_zero','coorbital_recover_positive_mass_row',
    'deletedAngularJacobian_isUnit_positive','coorbitalMassProjection_isLocalHomeomorphOn',
    'coorbitalMassProjection_isProperMap','coorbitalMassProjection_fiber_finite',
    'coorbitalMassProjection_isCoveringMapOn','equalMass_coorbital_existsUnique',
    'equalMass_root_reversal_symmetry','coorbital_global_complete',
    note='The needed AF open-semicircle equal-mass seed and its reversal symmetry are independently proved. The full AF full-circle classification is not used as an axiom or claimed formalized.')
definitions('prose:175','coorbitalResidual')
bind('lem:probe','twoSourceProbe')
context('prose:178',['lem:probe'],'Exact hypotheses of the numbered lemma.')
bind('display:181','twoSourceProbe')
bind('prose:184','signedProbe_hasDerivAt','signedProbe_inner_deriv_neg',
    'twoSourceFunction_second_deriv_pos','twoSourceFunction_endpoint',
    'twoSourceFunction_root_strict_secant','signedProbe_reflection','twoSourceProbe')
bind('prop:closed','coorbital_closed_mass_jacobian_complete')
bind('prose:191','coorbital_closed_mass_jacobian_complete','no_one_source_coorbital_root',
    'three_source_support_kernel','two_source_separation','two_source_probe_diagonal_pos')
bind('prose:200','coorbital_three_source_ranks_and_kernel_dimensions',
    'coorbital_three_source_kernel_not_all_zero_at_missing_source',
    'coorbital_three_source_kernel_vector_by_rank','three_source_probe_remainder_lower_bound',
    note='The literal skew-rank and restriction route constructs the perturbing kernel vector. The lower-bound proof now uses that vector, applies the actual cycle form to the coordinate indicator, cancels the proved positive mass, and takes the one-sided continuous limit.')
bind('display:201','three_source_probe_remainder_lower_bound')
context('prose:204',['display:205'],'Ordering phrase introducing the block matrix.')
bind('display:205','coorbitalResidual_hasFDerivAt','angularJacobian_mulVec',
    'angularJacobian_zero_mass_column','angularJacobian_zero_support_diagonal',
    definitions=('angularJacobian',))
bind('prose:208','angularDifferential_kernel_iff_nonnegative','angularDifferential_weighted_zero',
    'angularDifferential_constant','angularDifferential_recover_row',
    'deletedAngularJacobian_isUnit_nonnegative','deletedAngularJacobian_inverse_uniform_on_closed_roots')

imports = ['CoorbitalSourceCalculus','CoorbitalSourceBounds','CoorbitalSemicircleGeometry',
    'ProbeOriginalDerivatives','BoundarySourceCalculus','CycleDecomposition','MassRescaling']
names = sorted({n for e in patch.values() for n in e['names']})
build = ROOT/'logs/source-audit-build'
parser=argparse.ArgumentParser()
parser.add_argument('--prepare',action='store_true')
parser.add_argument('--finish',action='store_true')
args=parser.parse_args()
if args.prepare:
    lean=['import DominantFiveBody.'+x for x in imports]+['import Lean',
      'open scoped BigOperators ContDiff Topology',
      'set_option pp.fullNames true','set_option pp.proofs true','set_option pp.deepTerms true',
      'set_option pp.coercions.types true','set_option pp.funBinderTypes true',
      'open Lean Elab Command in','run_cmd do',
      '  let names : List Name := ['+','.join('``'+n for n in names)+']',
      '  let mut result : Array Json := #[]',
      '  for name in names do','    let info ← getConstInfo name',
      '    let pretty ← liftTermElabM do Meta.ppExpr info.type',
      '    result := result.push (Json.mkObj [("lean_declaration",toJson name.toString),("lean_statement",toJson pretty.pretty)])',
      '  liftIO <| IO.FS.writeFile "logs/source-audit-build/section12-types.json" (Json.pretty (toJson result))']
    (build/'ExportSection12Types.lean').write_text('\n'.join(lean)+'\n',encoding='utf-8')
if args.finish:
    types={x['lean_declaration']:x for x in json.loads((build/'section12-types.json').read_text(encoding='utf-8'))}
    assertions=[]
    for key,record in patch.items():
        base={k:v for k,v in entries[key].items() if k in ['id','source_location','paper_location','exact_claim','claim_kind']}
        base.update({k:v for k,v in record.items() if k!='names'})
        base['lean_bindings']=[types[n] for n in record['names']]
        assertions.append(base)
    (ROOT/'docs/SECTIONS_1_2_COVERAGE_PATCH.json').write_text(json.dumps(dict(
        schema_version=2,source_tex_sha256=hashlib.sha256((ROOT/'source/dominant_five_body_ARMA_rewritten.tex').read_bytes()).hexdigest().upper(),
        scope='Introduction and Section 2; source-reviewed exact claims and independent original-derivation checks.',
        audit_file='Audit/SectionsOneTwo.lean',assertions=assertions),ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    audit=['import DominantFiveBody.'+x for x in imports]+[
        'open scoped BigOperators ContDiff Matrix.Norms.Operator Topology',
        'universe u_1 u_2 u_3 u_4','set_option linter.unusedVariables false','']
    for n in names:
        audit += ['example : '+types[n]['lean_statement']+' := @'+n,'#print axioms '+n,'']
    (ROOT/'Audit/SectionsOneTwo.lean').write_text('\n'.join(audit),encoding='utf-8')
    print(f'{len(assertions)} source entries; {len(names)} exact theorem bindings.')
