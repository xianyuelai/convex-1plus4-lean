"""Independent Section 4 coverage patch; never mutates the full inventory."""
from pathlib import Path
import collections, hashlib, json, os, re, subprocess

ROOT = Path(__file__).resolve().parents[1]
REV = {}
def bind(ids, names, missing=(), route="Original source assertion with actual positive current masses."):
    for ident in ids.split():
        REV[ident] = dict(names=names.split(), missing=list(missing), route=route)
def context(ids, refs):
    for ident in ids.split():
        REV[ident] = dict(names=[], missing=[], route="Source setup or introduction to the indicated assertion.", source_cross_references=refs.split())

bind("prose:322 prose:326 prose:339", "dominant_uniform_geometry_complete")
bind("prose:330", "dominant_ordered_polar_gap_limsup five_projection_large_gap normalized_pairDistance_cube_le")
bind("display:334", "dominant_projectedClusterGap_source normalized_projection_gap_cube_le", route="Exact actual current-mass projected cluster-center separation, g<=Delta, Delta=(M_A^-1+M_B^-1) times the finite cross force, and Delta<=(1+epsilon)/g^2 from the same physical root.")
bind("prose:341", "primary_cluster_potential_lower primary_cluster_inertia_upper complete_cluster_current_center_exterior_bound normalized_cluster_virial", route="Actual current-mass cluster center b, one uniform exterior derivative constant on an open joint neighborhood, and the corresponding member/center secant bound. No positive lower bound for any limiting individual mass is imposed.")
bind("display:342", "normalized_cluster_virial normalized_cluster_virial_le")
bind("prose:345", "primary_cluster_cube_lower no_primary_complete_collision dominant_primary_relative_radius_lower")
bind("prose:347", "normalized_cluster_exterior_average clusterCenter_tendsto_current_weights satellite_complete_cluster_limit_unit dominant_primary_relative_radii_uniform")
bind("prose:349", "strictConvexInOrder_exists_ordered_polar normalized_polar_gauge_angular_rows full_angular_cut")
bind("prose:353", "full_angular_cut_limit_gap_le ordered_full_angular_limit_consecutive_gap_le no_full_angular_unit_root_at_pi")
bind("display:354", "fullAngularMatrix_source_entries")
bind("prose:357", "fullAngularMatrix_pi_entries fullAngularMatrix_pi_det fullAngularMatrix_pi_determinant_limit fullAngularMatrix_det_zero_of_root no_full_angular_sequence_at_pi_by_determinant ordered_full_angular_limit_span_pos dominant_strictConvex_uniform_polar_span", route="The original limiting determinant route: exact boundary matrix, det B=f(2h)^4, genuine moving determinant limit, determinant zero from each actual positive current-mass nullvector, and contradiction. No positivity of a limiting individual mass is required.")
bind("eq:support prose:364", "strictConvex_primaryRelative_all_edges", route="Every directed five-point hull edge in primary-relative coordinates, including a primary endpoint, and every other labeled vertex.")
bind("prose:369", "normalized_complete_pair_scale_complete")
bind("prose:381", "normalized_complete_pairs_cannot_coexist complete_pair_ordered_angles_adjacent")
bind("display:385", "pairExteriorFields_source_formulas")
bind("prose:390", "pairExteriorField_joint_contDiffAt physicalSourceAngularField_joint_contDiffAt pairExterior_joint_neighborhood_derivative_bounds pairExterior_moving_neighborhood_derivative_bounds complete_pair_exterior_error_bound complete_pair_exterior_angular_error_bound", route="One common actual moving target neighborhood and one uniform constant for genuine Cartesian DP and both genuine polar partial derivatives of H, each bounded by C times the sum of current exterior masses. Source and target vary jointly; no mass-share lower bound is used.")
bind("prose:396 eq:pair-prebound", "pair_tangential_coefficient_lower complete_pair_exterior_angular_error_bound complete_pair_angular_prebound_before_radial_exclusion", route="Directly from actual angular roots before any radial-direction exclusion: delta<=4d, sinc(delta)>=1/2, and delta nu/d^3<=C sigma d for one uniform positive C. The theorem has no tangential or radial-limit premise.")
bind("prose:405", "normalized_complete_pair_direction_alternative normalized_complete_pair_selected_tangential")
bind("prose:407 display:408", "physical_pair_direction_polar_ratio_limits complete_pair_direction_support_nonneg polar_support_radial_expansion_exact polar_support_radial_expansion_remainder_bound complete_pair_support_radial_expansion_littleO physical_pair_radial_subsequence_source_package", route="Genuine radial subsequence v=+/-e forces delta=o(d) and absolute radial ratio tending to one. The actual polar support determinant has an exact radial leading term, explicitly bounded remainder, and remainder/d tending to zero; the separate actual support sign remains available.")
bind("prose:411", "normalized_complete_pair_selected_tangential physical_pair_left_endpoint_rectangular_controls")
bind("display:412", "physical_pair_left_endpoint_rectangular_controls pairExteriorAngular_source_derivatives")
bind("prose:416", "physical_pair_left_endpoint_difference_control physical_pair_right_endpoint_difference_control normalized_complete_pair_left_outward_radial_impossible normalized_complete_pair_right_inward_radial_impossible")
bind("prose:418", "normalized_complete_pair_tangential_mass_scale normalized_pair_midpoint_identity")
bind("prose:423", "normalized_complete_pair_radial_bound_of_tangential")
bind("prose:425", "normalized_complete_pair_scale_complete physical_pair_weighted_full_angular_average complete_pair_exterior_difference_quotient_limit normalized_complete_pair_mass_cube_limit")
TRIPLE = "normalized_complete_triple_limiting_exterior normalized_complete_lower_triple_initial_scales normalized_complete_upper_triple_initial_scales normalized_complete_lower_triple_mass_vanishes normalized_complete_upper_triple_mass_vanishes normalized_complete_lower_triple_original_group_geometry normalized_complete_lower_triple_original_group_mass_lower normalized_complete_upper_triple_original_group_complete_geometry"
bind("prop:triple-scale eq:triple-scale prose:428", TRIPLE)
bind("display:441", "tripleExteriorJ_source_formula")
bind("prose:445", "physical_triple_weighted_full_angular_average normalized_complete_triple_limiting_exterior normalized_complete_lower_triple_full_rectangle_derivatives_uniform")
bind("eq:triple-J", "physicalSourceFullAngularField_hasDerivAt_radius physicalSourceFullAngularField_hasDerivAt_angle normalized_complete_lower_triple_full_rectangle_derivatives_uniform", route="Actual epsilon-dependent full physical source field. Both genuine partial derivatives converge uniformly on the entire lower-triple polar rectangle, using the minimum/maximum of all three radii and first/last angles.")
bind("prose:449 display:450", "polar_support_radial_drop_le physical_triple_extreme_source_signs normalized_complete_lower_triple_original_initial_estimates physicalSourceFullAngularField_left_difference_control", route="Actual positive current masses, first/last angular-root equations giving strict J signs, and genuine integrated epsilon-dependent full-J control on the actual moving rectangle. Positive radial and angular constants give the source's generic C convention by enlargement.")
bind("prose:453", "three_radii_spread_le_width normalized_complete_lower_triple_initial_scales")
bind("prose:455", "tripleAngularCoefficient_lower physical_triple_extreme_angular_identity")
bind("display:456", "physical_triple_extreme_angular_identity physical_triple_extreme_mass_width_bound normalized_complete_lower_triple_original_initial_estimates triple_mass_cube_upper_of_extreme_rows", route="Both original intermediate inequalities with actual nu W/d^3 and sigma(J3-J1). The first bound has explicit constant 16 and the second uniform positive constant; the proof uses original positive current masses and exact extreme angular equations.")
bind("prose:459", "normalized_complete_lower_triple_initial_scales normalized_complete_lower_triple_mass_vanishes")
bind("prose:461", "lower_triple_scaled_positions_compact_subsequence satellite_group_internal_projection_zero physical_current_group_projection_average satelliteGroupNearProjection_abs_bound equal_scaled_class_cross_separation finite_exterior_scaled_difference_bound physical_triple_equal_scaled_groups_primary_projection_limit", route="Original arbitrary finite classes of equal scaled limits. Actual compact extraction has at least two groups; current normalized positive weights cancel exactly, and cross-group separation plus near/far bounds are derived from physical roots and the earlier cubic bound.")
bind("display:462", "physical_two_current_groups_projection_difference physical_triple_equal_scaled_groups_primary_projection_limit physical_triple_equal_scaled_groups_primary_vector_limit", route="Original current-group difference identity. Every unit projection has an exact R+epsilon*B representation with R/d tending to zero and B/d bounded; the complete representative F0 vector difference divided by d tends to zero.")
bind("prose:465", "physical_triple_scaled_groups_radial_projection_limit polar_scaled_radius_difference_tendsto_zero polar_scaled_distance_square normalized_complete_lower_triple_original_group_geometry_of_scaled_limits normalized_complete_lower_triple_original_group_geometry normalized_complete_upper_triple_original_group_complete_geometry", route="Original arbitrary equal-limit group argument, actual polar radius differences, exact polar-distance conversion to W/d tending to one, compact extraction on every further subsequence, and the physical upper-block reflection. No regular/nested case split is used in these proof bodies.")
bind("prose:467", "physical_current_group_full_angular_average fullAngularMatrix_cross_distance_abs_bound current_group_near_angular_scaled_abs_bound actual_group_near_angular_scaled_tendsto_zero actual_current_angular_group_representative_scaled_limit physical_triple_original_angular_groups_zero_cube_impossible normalized_complete_lower_triple_original_angular_scaled_zero_cube_impossible normalized_complete_lower_triple_original_group_zero_cube_impossible normalized_complete_lower_triple_original_group_mass_lower normalized_complete_upper_triple_original_group_complete_geometry", route="Original arbitrary current-mass angular group averages. The assumed zero cubic ratio forces cross-group o(d) and every physical J representative scaled limit to zero; actual J derivative 9/4 then collapses distinct scaled limits, contradicting actual diameter compactness. The original-sequence lower bound and physical reflection for the upper block are implemented.")
NEST = "normalized_complete_lower_triple_nested_scale_complete normalized_complete_upper_triple_nested_scale_complete"
bind("prop:nested-scale eq:nested-scale prose:470", NEST, route="Both endpoint blocks, actual normalized roots and current masses. A pair/diameter ratio tending to zero suffices; no shortest-pair premise or current pair-share convergence is added.")
bind("prose:477", "nested_cross_distance_diameter_ratios normalized_complete_lower_triple_nested_directions normalized_complete_lower_triple_nested_radial_limits physical_pair_segment_scaled_displacement_uniform normalized_complete_lower_triple_nested_segment_scaled_geometry_uniform normalized_complete_upper_triple_nested_segment_scaled_geometry_uniform physical_pair_segment_near_distance_uniform normalized_complete_lower_triple_nested_rectangle_near_geometry_uniform normalized_complete_upper_triple_nested_rectangle_near_geometry_uniform", route="Both endpoint blocks, actual smaller pair and signed omega: the entire physical segment has uniform scaled vector limit omega times the limiting angular unit vector. The entire actual polar rectangle has separately proved signed angular, zero radial, and unit distance scaled limits. Pair adjacency follows internally from the physical roots; the reflection is used solely for estimates.")
bind("prose:482", "newtonTargetDerivative_operator_norm_bound pairExteriorField_hasFDerivAt pairExteriorField_fderiv_norm_bound pairExteriorField_fderiv_norm_bound_two_sources normalized_complete_lower_triple_nested_segment_derivative_bound physical_nested_pair_exterior_secant_limit", route="Genuine Cartesian fderiv of the actual P. The Newton derivative operator norm is bounded from its exact action; actual near and far distances and the derived current near-source cubic bound give DP<=128 throughout the actual lower pair segment. The source proof treats the lower block first; the general two-source norm bound is orientation independent.")
bind("eq:nested-field", "pairExteriorAngular_source_derivatives physicalPairExteriorAngularRadialDerivative_eq_selected physicalPairExteriorAngularAngularDerivative_eq_selected")
bind("prose:487", "physical_nested_polar_rectangle_derivatives_individually_uniform normalized_complete_lower_triple_nested_rectangle_individual_limits normalized_complete_upper_triple_nested_rectangle_individual_limits", route="Both endpoint blocks, every target in the actual moving polar rectangle: near H_rho tends uniformly to zero, near H_v-2mu_c/d^3 tends uniformly to zero, and separated exterior contributions tend individually to the signed 3sqrt3/4 and to 9/4.")
bind("eq:nested-derivatives", "normalized_complete_lower_triple_nested_rectangle_controls normalized_complete_upper_triple_nested_rectangle_controls", route="Original full finite-sum derivatives on the entire actual polar rectangle. Both zeta signs and the moving current-mass expression 9/4+2mu_c/d^3 are proved, not supplied as assumptions.")
bind("prose:492", "physical_pair_direction_alternative_of_exterior_vanishes physical_nested_pair_selected_tangential physical_nested_pair_unselected_precise_scales normalized_complete_lower_triple_nested_precise_scales normalized_complete_upper_triple_nested_scale_complete", route="Original radial exclusion and tangential limits; a strict physical secant proof replaces only the rectangle-integration step, and the original rectangle estimates are separately proved.")
bind("display:493", "positive_two_scale_fraction_identity normalized_complete_lower_triple_nested_scale_complete normalized_complete_upper_triple_nested_scale_complete", route="Exact real cubic quotient identity for positive actual scales and triple mass, together with the proved original ratio-zero limit for both endpoint blocks.")
bind("prose:496", "physical_pair_radial_bound_of_exterior_secant_limit normalized_complete_lower_triple_nested_radial_bound normalized_complete_upper_triple_nested_scale_complete")
bind("prose:498 eq:nested-macro-average", "physical_nested_macro_average normalized_nested_macro_average")
bind("prose:502", "physicalSourceFullAngularField_near_scaled_limit physicalSourceFullAngularField_moving_secant_limit normalized_nested_macro_mass_cube_limit_of_first_order_geometry normalized_complete_lower_triple_nested_macro_mass_cube_limit normalized_complete_lower_triple_nested_precise_scales physical_nested_pair_mass_cube_limit_of_tangential nested_precise_two_cube_limits_of_selected normalized_complete_upper_triple_nested_scale_complete", route="Current positive normalized weights, exact macro identity, actual near/far secants, and both precise cubic limits. No convergence of individual current shares is used.")
bind("prose:505", "normalized_ordered_collision_classes_exhaustive low_triple_scale_cases", route="Original physical collision partition followed by an actual shortest/largest distance extraction; spans and two complete pairs are excluded by already proved physical results.")
bind("prose:315", "sinc_source_extension")
context("prose:318", "prop:uniform prop:pair-scale prop:triple-scale prop:nested-scale")
context("prose:360", "eq:distance")
context("prose:400", "eq:pair-vdiff")
context("prose:438", "display:441")

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    inventory=json.loads((ROOT/'docs/FULL_ASSERTIONS.json').read_text(encoding='utf-8'))
    entries=[a for a in inventory['assertions'] if 307<=a['source_location']['tex_lines'][0]<=505]
    for a in entries:
        if a['id'] not in REV and a.get('status')=='VERIFIED':
            bindings=a.get('lean_bindings',[]) or ([a] if a.get('lean_declaration') else [])
            names=[b['lean_declaration'].removeprefix('DominantFiveBody.') for b in bindings]
            if names: REV[a['id']]=dict(names=names,missing=[],route='Previously complete original assertion; re-audited current declaration type and axioms.')
    names=sorted({n for v in REV.values() for n in v['names']})
    modules=set(); found=set()
    for p in (ROOT/'DominantFiveBody').glob('*.lean'):
        txt=p.read_text(encoding='utf-8')
        for n in names:
            if re.search(r'\b(?:theorem|lemma)\s+'+re.escape(n)+r'\b',txt): modules.add('DominantFiveBody.'+p.stem);found.add(n)
    if set(names)-found: raise RuntimeError('Missing declarations: '+repr(set(names)-found))
    audit=ROOT/'Audit/SectionFourSourceCoverage.lean'
    lines=[*[f'import {m}' for m in sorted(modules)],'set_option pp.fullNames true','set_option pp.proofs true','set_option pp.maxSteps 10000000']
    for n in names:
        q='DominantFiveBody.'+n
        lines += [f'#eval IO.println "COVERAGE_BEGIN {q}"',f'#check @{q}',f'#print axioms {q}',f'#eval IO.println "COVERAGE_END {q}"']
    audit.write_text('\n'.join(lines)+'\n',encoding='utf-8')
    env=dict(os.environ);env['LEAN_NUM_THREADS']='2'
    run=subprocess.run(['pwsh','-NoProfile','-File','scripts/lean_checked.ps1','-SourceFile',str(audit.relative_to(ROOT))],cwd=ROOT,env=env,encoding='utf-8',capture_output=True,timeout=600)
    log=run.stdout+run.stderr;lp=ROOT/'docs/COVERAGE_SECTION4_LEAN.log';lp.write_text(log,encoding='utf-8')
    if run.returncode: print(log[-18000:]);raise SystemExit(run.returncode)
    types={}
    for q,block in re.findall(r'COVERAGE_BEGIN ([^\n]+)\n(.*?)COVERAGE_END \1',log,re.S):
        m=re.search("'"+re.escape(q)+r"' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",block)
        if not m: raise RuntimeError('Missing axiom audit '+q)
        typ=block[:m.start()].strip();axs=[] if m[2] is None else [x.strip() for x in m[2].split(',')]
        if '...' in typ or '⋯' in typ or set(axs)-{'propext','Classical.choice','Quot.sound'}: raise RuntimeError('Unacceptable type/axioms '+q)
        types[q.removeprefix('DominantFiveBody.')]=dict(lean_declaration=q,lean_statement=typ,axioms=axs)
    if set(names)!=set(types):raise RuntimeError('Incomplete audited output')
    out=[]
    for a in entries:
        v=REV.get(a['id'],dict(names=[],missing=['No complete current source binding reviewed.'],route='Fail-closed source review.'))
        bs=[dict(types[n],subclaim=v['route']) for n in v['names']]
        item=dict(id=a['id'],source_location=a['source_location'],exact_claim=a['exact_claim'],lean_bindings=bs,remaining_dependencies=v['missing'],proof_route=v['route'],status='SOURCE_CROSS_REFERENCE' if 'source_cross_references'in v else ('OPEN' if v['missing'] else 'VERIFIED'))
        if 'source_cross_references'in v:item['source_cross_references']=v['source_cross_references']
        out.append(item)
    result=dict(schema_version=1,scope='Original Section 4, TeX 307-505',source_tex_sha256=sha(ROOT/'source/dominant_five_body_ARMA_rewritten.tex'),strict_lean_exit_code=run.returncode,audit_file=str(audit.relative_to(ROOT)),audit_sha256=sha(audit),audit_log_sha256=sha(lp),audited_unique_declarations=len(types),status_counts=dict(collections.Counter(x['status']for x in out)),assertions=out)
    dest=ROOT/'docs/COVERAGE_SECTION4_PATCH.json';dest.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:result[k]for k in ['strict_lean_exit_code','audited_unique_declarations','status_counts']},ensure_ascii=False))
if __name__=='__main__':main()
