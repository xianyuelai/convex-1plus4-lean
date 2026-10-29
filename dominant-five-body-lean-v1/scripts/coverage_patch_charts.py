"""Independent, fail-closed source review of original Sections 5--6.

This never changes FULL_ASSERTIONS.json.  The proof binding statements and
axiom sets are read from a strict Lean run, not copied from source comments.
An aggregate keeps OPEN whenever any of its actual assertions is missing.
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
REVIEW = {}

def bind(ids, names, missing=(), route="Original assertion; independently checked declaration type."):
    if isinstance(ids, str):
        ids = [ids]
    if isinstance(names, str):
        names = names.split()
    for ident in ids:
        REVIEW[ident] = dict(names=list(names), missing=list(missing), route=route)

def context(ids, refs, note="Context introducing the immediately following mathematical assertion."):
    for ident in ids.split():
        REVIEW[ident] = dict(names=[], missing=[], route=note, source_cross_references=refs.split())

bind("eq:chi", "singleScaleChi_complete")
bind("prose:513", "pairChartExtendedRows_joint_analyticAt tripleChartExtendedRows_joint_analyticAt nestedChartExtendedRows_joint_analyticAt pairChartExtendedRows_eq_physical tripleChartExtendedRows_eq_physical nestedChartExtendedRows_eq_physical")
bind("eq:hadamard", "hadamard_target_difference", route="Original line-segment integral formula; local C1 on an open set containing the segment suffices.")
bind("display:521", "singleScale_distance_sq singleScale_distance", ["The exact defining W-squared formula must be included as a complete definitional equality package."])
bind("eq:regular-int", "singleScaleRadialTerm_eq_physical singleScaleAngularTerm_eq_physical tripleInternalRadial_eq_physical tripleInternalAngular_eq_physical", ["Bind the complete original finite weighted-sum formula, beyond the checked per-edge physical identities."])
bind("prose:532", "singleScaleRadialTerm_contDiffAt singleScaleAngularTerm_contDiffAt", ["The weighted angular cancellation and the exact weighted radial pair-sum formula are separate original subclaims, not yet bound here."])
bind("display:533", [], ["The exact original i<j weighted radial sum formula remains unbound."])
bind("prose:537", "pairRadialExterior_joint_contDiffAt pairAngularExterior_joint_contDiffAt tripleRadialExterior_joint_contDiffAt tripleAngularExterior_joint_contDiffAt hadamard_target_difference")
bind("prose:539", "noCollision_physical_local_continuation reducedJacobian_at_closed_separated_root_isInvertible", ["Add the explicit largest-mass gauge selection mu_p>=1/4 and its gauge change; the current no-collision continuation uses an equivalent sorting/gauge route."])
bind("display:541", "reducedAngularJacobian_zero_eq_separated reducedJacobian_at_closed_separated_root_isInvertible", ["Bind the full actual seven-by-seven block derivative with radial block 3I4 and zero upper-right block, not solely its invertibility."])
bind("prose:544", "noCollision_physical_local_continuation noCollision_actual_sequence_capture_of_regular_limit angularResidual_weighted_sum")
bind(["eq:pair-chart-mass", "eq:pair-coordinates"], "pairChart_coordinates_complete")
bind("display:557", "pairChartPhysicalRows_zero_iff", ["Bind explicit retained-row vector and the p0>=1/2 omitted-row choice as a formula package."])
bind("prose:561", "pairCoordinateMatrix_det pairRows_recovery", ["Add the explicit quantitative lower mass bound for the omitted exterior row from the chosen p0 half-interval."])
bind("eq:pair-W", "pairChart_pair_distance_sq", ["Bind the exact defining pair W-squared expression together with the physical distance equality."])
bind("prose:567", "pairChartExtendedRows_joint_contDiffAt pairChart_compact_boundary_continuation pairRadialMean_at_boundary pairRadialDifference_at_boundary pairChart_boundary_radial")
bind("display:568", "twoSourcePolarAngular_fderiv_apply", ["Bind the explicit scalar sine-and-distance target-field expression for H; current field definition is an equivalent Cartesian expression."])
bind("eq:pair-boundary", "pairAngularMean_at_boundary pairAngularDifference_at_boundary")
bind("prose:577", "pairChartJacobian_unit_radial pairChartJacobian_unit_radial_difference pairChartJacobian_unit_exterior pairChartJacobian_unit_mean pairChartJacobian_unit_difference")
bind("eq:pair-J", "pairChartJacobian_unit_exterior pairChartJacobian_unit_mean pairChartJacobian_unit_difference", ["Explicitly substitute omega=h, the exterior half-interval choice and kappa(h)=D0 to obtain the displayed a0 formula."])
bind("prose:582", "pairChartJacobian_boundary_isInvertible pairChart_compact_boundary_continuation pairChart_zero_eps_all_scale_faces pairRadial_root_exact_factor pairRadial_root_compact_uniform_bound", ["Bind the exact quantitative |a0|>=9/8 estimate; general invertibility alone does not cover it."])
bind("eq:pair-areas", "pair_areas_boundary_complete pairArea_factor pairAreaQuotient_joint_contDiff")
bind("prose:589", "pairChart_compact_physical_continuation normalized_complete_pair_actual_chart_limits normalized_complete_pair_actual_capture", route="Original assertions, with actual equations, original mass vector and explicit relabeling/gauge recovery; no alpha convergence hypothesis.")
bind("subsec:pair-chart.actual_common_interval_capture", "normalized_complete_pair_actual_capture")
bind("subsec:pair-chart.actual_inverse_limits", "normalized_complete_pair_actual_chart_limits")
bind("eq:internal", "tripleScalar_positive_root_existsUnique tripleScalar_root_unique tripleScalar_root_weighted_center", route="Scalar equations are implemented verbatim. Positive-weight existence uses the alternative Euler-polynomial proof; nonnegative uniqueness uses the alternative maximum-coordinate force comparison.")
bind(["prose:599", "display:600"], [], ["The original displayed potential, its divided-gradient equation, properness on the ordered chamber, and strict convexity are not yet proved. The alternative scalar existence/uniqueness proof does not discharge these source assertions."], route="Original variational derivation remains distinct from the completed alternative Euler-polynomial existence proof.")
bind("prose:604", "tripleScalar_positive_root_existsUnique tripleScalar_root_weighted_center tripleScalarResidual_hasFDerivAt tripleScalar_J_entries_complete", route="Same exact existence/uniqueness/center conclusion; alternative existence derivation explicitly retained.")
bind("eq:internal-J", "tripleScalarResidual_hasFDerivAt tripleScalar_J_entries_complete")
bind("prose:609", "tripleScalarJacobian_strict_row_dominance tripleScalarJacobian_lower_norm_bound tripleScalar_root_unique", ["The integral of J along every ordered segment and its D0 sup-norm lower bound are original additional assertions and have not been bound; uniqueness is proved by a different maximum-coordinate argument."], route="Partial original assertion and complete alternative uniqueness proof.")
bind("eq:LB", "tripleScalar_matrices_complete")
bind("prose:617", "tripleScalar_matrices_complete")
bind("eq:regular-coordinates", "tripleChart_coordinates_complete")
bind("prose:626", "tripleRows_recovery tripleRows_zero_iff tripleChartExtendedRows_eq_physical tripleChartExtendedRows_joint_contDiffAt tripleChartExtendedRows_zero_iff_normalized")
bind("prose:628", "tripleRadialMean_at_boundary tripleRadialDifference_at_boundary tripleChart_boundary_radial")
bind("eq:Hzero", "twoSourcePolarAngular_fderiv_apply", ["Bind the explicit one-source scalar H(rho,v;r) expression, including its denominator exponent, not solely equivalent Cartesian field definitions."])
bind("display:634", "tripleAngularExteriorDifference_at_boundary tripleInternalAngularReduced_at_boundary", ["Bind the full displayed scalar M_i formula in one explicit statement."])
bind("prose:638", "tripleAngularDifference_unit_scalar tripleScalar_centered_gap_root_recovery tripleChartExtendedRows_unit_root tripleChartJacobian_unit_radial tripleChartJacobian_unit_radial_difference tripleChartJacobian_unit_mean tripleChartJacobian_unit_difference")
bind("eq:Kreg", "tripleReducedDifferential_matrix tripleChartJacobian_unit_difference", ["Add the explicit matrix equality K=L J B_alpha, beyond the checked continuous-linear derivative action."])
bind("prose:642", "tripleReducedJacobian_det_ne_zero tripleChart_boundary_continuation_of_scalar_root tripleChart_zero_eps_all_scale_faces tripleChart_convex_physical_continuation", ["Bind the explicit locally uniform O(eps) estimate on r-1,R-1,u; zero-face vanishing and joint smoothness alone have not yet been packaged as that quantitative assertion."])
bind("prose:644", "normalized_complete_lower_triple_regular_actual_capture normalized_complete_upper_triple_regular_actual_capture", route="Actual normalized roots, scaled limits, extraction with positive gaps, boundary scalar equations and common capture are derived without supplied inverse-limit interfaces.")
bind(["eq:nest-masses", "eq:nest-coordinates"], "nestedChart_coordinates_complete")
bind("eq:nest-rows", "nestedRows_recovery", ["Bind all four original row definitions, including their exact divisions, in a complete formula statement."])
bind("eq:nest-recovery", "nestedRows_recovery")
bind("prose:675", "nestedCoordinateMatrix_det nestedChartPhysicalRows_zero_iff nestedChartExtendedRows_zero_iff_normalized", ["The original seven-coordinate determinant absolute value t^4 eta^2 needs its full matrix product identity, not merely one three-coordinate determinant."])
bind("prose:677", "nestedInner_distance nestedOuter_distance", ["Bind all four P_a,P_b,Q_a,Q_b defining expressions explicitly."])
bind("eq:nest-distances", "nestedInner_distance_sq nestedOuter_distance_sq", ["Bind the exact W^2 and V_i^2 definitions in the same complete statement as their actual distances."])
bind("display:684", "nestedRadialExterior_recovery nestedAngularExterior_recovery", ["Bind the complete scalar exterior fields H and K exactly as displayed, including the current reaction vector held fixed in target differentiation."])
bind("display:693", "nestedOuterL_formula nestedInnerM_formula")
bind("eq:nest-angular", "nestedInternalAngular_mean nestedInternalAngular_outer_difference nestedInternalAngular_inner_difference nestedChartExtendedRows_eq_physical", ["Bind the three fully displayed exterior-plus-internal row identities, with the exact H differences and L quotients."])
bind("display:706", "nestedOuterL_formula", ["Bind the three-variable scalar kernel L(r,P,Q) and its exact substitution into L_a,L_b."])
bind("eq:nest-kernel-difference", "nestedOuterL_difference", ["The original three-variable line integral has not been proved. The implemented rationalized Newton divided-field formula is an alternative algebraic derivation of the same quotient and is not this displayed integral."], route="Alternative algebraic divided-kernel derivation; original integral remains open.")
bind("prose:716", [], ["Bind the interval substitution lambda+beta taking [-beta,alpha] to [0,1], together with alpha+beta=1."])
bind("display:719", "nestedOuterN_formula nestedOuterO_formula", ["Bind both inner N and O exact scalar formulas as well as the completed outer formulas."])
bind("prose:727", "nestedInnerJ_factor", ["Bind the exact J expression, including every scale and mass factor, in addition to its smooth factorization."])
bind("eq:nest-radial", "nestedInternalRadial_mean nestedInternalRadial_outer_difference nestedInternalRadial_inner_difference nestedChartExtendedRows_eq_physical", ["Bind the full displayed scalar radial rows including K differences and all J/t terms."])
bind("prose:737", "nestedInnerJ_factor nestedInnerJOverT_joint_contDiffAt nestedOuterN_difference", ["The original three-variable integral representation of (N_b-N_a)/eta remains unproved; the alternative algebraic quotient is complete."], route="Complete smooth J/t and alternative N quotient; original integral route remains open.")
bind("display:738", "nestedOuterN_formula", ["Bind the exact three-variable scalar kernel N(r,P,Q)."])
bind("prose:742", "nestedChartExtendedRows_joint_contDiffAt nestedChart_compact_boundary_continuation", route="Joint regularity for signed independent scales is proved via the explicitly documented rationalized Newton quotient alternative.")
bind("prose:744", "nestedRadialMean_at_boundary nestedRadialOuterDifference_at_boundary nestedRadialInnerDifference_at_boundary")
bind("display:746", "nestedBoundaryKernel_formula nestedInnerM_at_boundary", ["Bind both complete L0 and M0 scalar expressions in one statement."])
bind("eq:nest-boundary", "nestedAngularMean_at_boundary nestedAngularOuterDifference_at_boundary nestedAngularInnerDifference_at_boundary nestedBoundaryKernel_fderiv_apply")
bind("eq:nest-base", "nestedChartExtendedRows_base_root nestedBasePoint_scale", ["Bind the complete seven-coordinate base vector formula including both inverse-third powers."])
bind("prose:763", "nestedChartJacobian_unit_radial nestedChartJacobian_unit_radial_difference nestedBoundaryDerivativeMatrix_triangular_diagonal", ["The complete original angular block requires its non-diagonal entries and C=-27/4 sin(psi)."])
bind("eq:nest-angle-J", "nestedBoundaryDerivativeMatrix_triangular_diagonal", ["The original off-diagonal entries CZ0,Cz0,-6D0 z0/Z0 and the C formula are unbound; determinant and diagonal values do not prove this display."])
bind("prose:771", "nestedBoundaryDerivativeMatrix_det nestedChartJacobian_boundary_isInvertible nestedChart_compact_boundary_continuation nestedChart_zero_eps_all_scale_faces nestedChart_convex_physical_continuation", ["Bind the original first/second scalar-kernel derivative values; the full alpha independence of the derivative; and uniform O(eps) estimates for both u_j."])
bind("display:774", "normalized_complete_lower_triple_nested_original_capture", ["Extract a complete statement for each individual original scale limit and quantitative O(eps) radial estimate; the final capture theorem does not expose all these source limits."])
bind("prose:779", "normalized_complete_lower_triple_nested_original_capture orderedSlice_lower_nested_triple_capture", ["Bind both signed outer-angle inverse limits and explicit seven-variable entry without alpha convergence; the final capture theorem alone omits these detailed original subclaims."])
bind("display:780", "orderedSlice_lower_nested_triple_capture", ["Bind the full four-row sign/label table explicitly; one lower-triple capture case is only a partial table binding."])
bind("prose:789", "nestedChart_convex_physical_continuation nestedContinuationRoot_fixed_mass_endpoint")
bind("display:798", "backgroundProbeField_hasFDerivAt", ["The full displayed Cartesian field F includes the eps satellite source; its exact defining formula must be packaged in a statement."])
bind("prose:802", "backgroundProbeField_zero backgroundProbeField_hasFDerivAt backgroundOperator_coordinates")
bind("eq:bg-matrix", "backgroundOperator_apply backgroundOperator_coordinates backgroundProbeField_hasFDerivAt", ["Bind the complete matrix equality to B in the specified orthonormal basis, not only the equivalent coordinate action."])
bind("prose:809", "backgroundMatrix_trace backgroundMatrix_characteristic_factor backgroundSlowLambda_lt_fast")
bind("eq:slow", "backgroundSlowLambda_eq backgroundSlowLambda_characteristic", ["Bind the exact rationalized d definition and d(0)=D0 together with lambda=eps*d."])
bind("prose:815", "backgroundSlowK_contDiffAt backgroundSlowDirection_contDiffAt backgroundSlowLength_contDiffAt backgroundAngularScale_contDiffAt")
bind("display:816", "backgroundSlow_polar_displacement", ["Bind all four defining formulas k,n,l,b explicitly."])
bind("prose:821", "backgroundSlowDirection_eigen", ["Bind k(0)=0 and l(0)=b(0)=1 explicitly."])
bind("eq:scalar-slow", "tripleScalar_centered_gap_root_recovery nestedAngularRows_scalar_root_recovery", ["Review the full scalar equations, distinctness, weighted center and sum-one package; definition contexts alone are not an independent theorem."])
bind("eq:vector-slow", "backgroundScalarLift_vector_balance")
bind("prose:831", "backgroundSlow_scaling")
bind("prose:833", "tripleBoundaryDisplacement_radial tripleBoundaryDisplacement_angular tripleInternalRadialReduced_vector_projection tripleInternalAngularReduced_vector_projection tripleSlowPoint_root nestedSlowPoint_root", ["The explicit first-order Cartesian Taylor remainder O(t^2), and exterior/reaction O(t^3), remain unbound even though the resulting boundary equations are proved exactly."])
bind("prose:839", "tripleScalar_centered_gap_root_recovery tripleSlowPoint_root")
bind("eq:regular-slow", "tripleSlowPoint_zero tripleSlowPoint_radialPositions tripleSlowPoint_angularPositions", ["Bind the complete seven-coordinate slow root vector rather than only its coordinate projections."])
bind("prose:845", "backgroundSlow_polar_displacement tripleChart_zero_face_parallel_of_local_uniqueness")
bind("eq:regular-parallel", "tripleChart_zero_face_parallel_of_local_uniqueness")
bind("display:852", "nestedChart_coordinates_complete", ["Bind the three scalar positions and their exact eta^3,alpha weights without the common R coordinate."])
bind("prose:856", "nestedAngularRows_scalar_root_recovery nestedSlowPoint_root nestedChart_zero_face_parallel_of_local_uniqueness", ["Bind smoothness of the candidate for eta,alpha and its full seven coordinates; the actual identity and local uniqueness are already proved."])
bind("eq:nest-parallel", "nestedChart_zero_face_parallel_of_local_uniqueness")
bind("prose:864", "nestedChart_zero_face_parallel_of_local_uniqueness nestedChart_zero_face_area_zero_nonnegative_eta")
bind("eq:circle-area", "circle_areas_complete")
bind("prose:872", "circle_areas_complete")
bind("display:875", "triplePointDirection_identity triplePointDirection_at_zero", ["Verify exact naming and source line-segment edge interpretation before accepting both formulas."])
bind("prose:879", "tripleChart_zero_face_area_zero_of_local_uniqueness tripleInternalArea_factor_cubic_along_root")
bind("eq:regular-area", "tripleInternalArea_factor_cubic_along_root")
bind("prose:885", "tripleAreaAlongRoot_deriv_eq_partial tripleChart_zero_eps_all_scale_faces tripleAreaAlongZeroRoot_hasDerivAt")
bind("display:887", "tripleCircleAreaCoefficient_zero tripleCircleAreaCoefficient_zero_pos tripleAreaAlongZeroRoot_hasDerivAt")
bind("prose:890", "tripleChart_internal_area_positive_neighborhood tripleExteriorAreaQuotient_primary_boundary tripleExteriorAreaQuotient_exterior_boundary tripleChart_strictConvex_neighborhood")
bind("display:895", "nestedInnerDirection_identity nestedOuterDirection_identity nestedInternalArea_factor_square")
bind("display:900", "nestedInternalAreaQuotient_zero_formula nestedChart_zero_face_area_zero_nonnegative_eta")
bind("eq:nest-area", "nestedInternalArea_factor_cubic_along_root")
bind("prose:909", "nestedAreaAlongRoot_deriv_eq_partial nestedAreaAlongZeroRoot_hasDerivAt")
bind("display:910", "nestedCircle_coefficient_complete nestedAreaAlongZeroRoot_hasDerivAt")
bind("prose:913", "nestedCircle_coefficient_complete orientedArea_cyclic")
bind("display:915", "nestedMacroArea_unit_boundary nestedExternalAreaQuotient_primary_boundary nestedExternalAreaQuotient_exterior_boundary nestedEdge_signed_base_gap_pos")
bind("prose:925", "tripleChart_convex_physical_continuation nestedChart_convex_physical_continuation", ["For nested alpha in the whole closed interval, explicitly bind a single uniform common product preserving all ten areas; the present convex-physical continuation theorem is centered at each alpha0."])
bind(["prop:chart-interface", "prose:928"], "noCollision_physical_local_continuation pairChart_compact_physical_continuation tripleChart_convex_physical_continuation nestedChart_convex_physical_continuation normalized_noCollision_ordered_capture normalized_complete_pair_actual_capture normalized_complete_lower_triple_regular_actual_capture normalized_complete_upper_triple_regular_actual_capture orderedSlice_lower_nested_triple_capture orderedSlice_smooth_connection_explicit", route="All four actual chart cases, same original masses, strict convexity, shape nondegeneracy, common captured interval, and smoothness including epsilon=0. The stronger original ordered-slice connection theorem supplies the complete smooth branch package.")

context("prose:507", "eq:chi eq:regular-int", "Source declaration of unchanged residuals and coordinate/row use; actual physical equality bindings are attached to prose:513.")
context("prose:518", "eq:hadamard prose:833", "Differentiation convention: sources are fixed in the target difference and move in subsequent joint differentiation; actual joint smoothness bindings use current source coordinates.")
context("prose:520 prose:525", "display:521 eq:regular-int")
context("prose:546", "eq:pair-chart-mass eq:pair-coordinates eq:pair-J")
context("prose:556", "display:557")
context("prose:563", "eq:pair-W")
context("prose:572", "eq:pair-boundary")
context("prose:584", "eq:pair-areas")
context("prose:591", "eq:internal eq:regular-coordinates")
context("prose:611", "eq:LB")
context("prose:633", "display:634")
context("prose:646 prose:653", "eq:nest-masses eq:nest-coordinates")
context("prose:662 prose:668", "eq:nest-rows eq:nest-recovery")
context("prose:683", "display:684")
context("prose:692", "display:693")
context("prose:697", "eq:nest-angular")
context("prose:705 prose:710", "display:706 eq:nest-kernel-difference")
context("prose:718", "display:719")
context("prose:750", "eq:nest-boundary")
context("prose:758", "eq:nest-base")
context("prose:773", "display:774")
context("prose:791", "eq:regular-parallel eq:nest-parallel")
context("prose:795", "display:798 eq:bg-matrix")
context("prose:827", "eq:vector-slow")
context("prose:851", "display:852")
context("prose:866", "eq:circle-area")
context("prose:874", "display:875")
context("prose:894 prose:899 prose:904", "display:895 display:900 eq:nest-area")
context("prose:940", "display:943", "Definition introducing Section 7; outside the chart mathematical review scope.")

# Complete explicit formula packages subsequently proved, without changing
# any quantifier in the source. Candidate formula != actual-root identity.
bind("display:521", "singleScaleWSq_formula_complete singleScale_distance_sq singleScale_distance")
bind("display:557", "pairChartRows_formula_complete pairChartPhysicalRows_zero_iff", ["The exact p0 half-interval choice of keepD still needs an explicit selection equality."])
bind("prose:561", "pairChart_omitted_mass_lower pairCoordinateMatrix_det pairRows_recovery")
bind("eq:pair-W", "pairChartWSq_formula_complete pairChart_distance_sq")
bind("eq:Kreg", "tripleReducedJacobian_formula_complete tripleReducedDifferential_matrix tripleChartJacobian_unit_difference")
bind("eq:nest-rows", "nestedRows_formula_complete")
bind("prose:677", "nestedGaps_formula_complete nestedInner_distance nestedOuter_distance")
bind("eq:nest-distances", "nestedGaps_formula_complete nestedInnerWSq_formula nestedOuterWSq_formula nestedInner_distance nestedOuter_distance")
bind("prose:727", "nestedInnerJ_formula_complete")
bind("eq:nest-base", "nestedBasePoint_formula_complete nestedChartExtendedRows_base_root")
bind("eq:bg-matrix", "backgroundSpectrum_formula_complete backgroundOperator_apply backgroundOperator_coordinates backgroundProbeField_hasFDerivAt")
bind("eq:slow", "backgroundSpectrum_formula_complete backgroundSlow_zero_complete backgroundSlowLambda_eq backgroundSlowLambda_characteristic")
bind("display:816", "backgroundSlow_formula_complete")
bind("prose:821", "backgroundSlow_zero_complete backgroundSlowDirection_eigen")
bind("eq:regular-slow", "tripleSlowPoint_formula_complete tripleSlowPoint_root", ["Bind the equality of the actual common-chart root to this complete candidate vector, rather than the candidate root formula alone."])
bind("display:852", "nestedScalarPositions_formula_complete")
bind("display:706", "nestedScalarAngularKernel_formula nestedScalarAngularKernel_substitution")
bind("eq:nest-kernel-difference", "nestedOuterL_original_integral nestedOriginalScalarPath_endpoints nestedOriginalScalarPath_positive_common_tube", route="Original three-variable line integral specialized to the actual L kernel. Its path regularity is derived on a uniform signed-scale tube over alpha in the whole closed interval.")
bind("prose:716", "nested_kernel_integral_shift")
bind("prose:737", "nestedInnerJ_formula_complete nestedInnerJ_factor nestedInnerJOverT_joint_contDiffAt nestedOuterN_original_integral nestedOriginalScalarPath_positive_common_tube", route="Original N-kernel integral and smooth J/t are proved; the rationalized alternative is not used as a substitute for this source formula.")
bind("display:738", "nestedScalarRadialKernel_formula nestedScalarRadialKernel_substitution")
bind("eq:regular-int", "singleScaleRadialTerm_eq_physical singleScaleAngularTerm_eq_physical tripleInternalRadial_eq_physical tripleInternalAngular_eq_physical tripleInternalRadial_source_formula tripleInternalAngular_source_formula pairInternal_weighted_radial_source")
bind("prose:532", "singleScaleRadialTerm_contDiffAt singleScaleAngularTerm_contDiffAt singleScale_internal_weighted_angular_sum singleScaleWeightedRadialPair_pair_sum tripleInternal_weighted_angular_zero")
bind("display:533", "singleScale_three_weighted_radial_sum singleScale_pair_weighted_radial_sum tripleInternal_weighted_radial_upper_sum pairInternal_weighted_radial_source")
bind("prose:642", "tripleReducedJacobian_det_ne_zero tripleChart_boundary_continuation_of_scalar_root tripleChart_zero_eps_all_scale_faces tripleChart_convex_physical_continuation tripleChart_radial_uniform_epsilon_bound")
bind("prose:771", "nestedBoundaryDerivativeMatrix_det nestedChartJacobian_boundary_isInvertible nestedChart_compact_boundary_continuation nestedChart_zero_eps_all_scale_faces nestedChart_convex_physical_continuation nestedChart_radial_uniform_epsilon_bound", ["Bind the original first/second scalar-kernel derivative values and the full alpha independence of the derivative."])
bind("prose:763", "nestedChartJacobian_unit_radial nestedChartJacobian_unit_radial_difference nestedBoundaryDerivativeMatrix_triangular_diagonal nestedAngularBoundaryMatrix_source")
bind("eq:nest-angle-J", "nestedAngularBoundaryMatrix_source kappaPrime_h_source")
bind("prose:609", "tripleScalarJacobian_strict_row_dominance tripleScalarJacobian_lower_norm_bound tripleOrderedSegment_ordered tripleIntegratedJacobian_entries tripleIntegratedJacobian_lower_norm_bound tripleScalarResidual_ordered_segment_integral tripleScalar_root_unique_by_integratedJacobian", route="Original actual Jacobian integration on every ordered segment, including the retained D0 sup-norm margin and FTC residual difference, proves uniqueness for nonnegative weights.")
bind("prose:874", "triplePointDirection_identity triplePointDirection_at_zero triplePointDirection_joint_contDiff", ["The original line-segment integral construction of the smooth divided edges remains unbound; the explicit sinc extension proves the same identities by a different route."], route="Exact divided-edge identities and smoothness are complete; original integral derivation remains independent.")
bind("prose:925", "nestedChart_all_ten_areas_uniform_product nestedChart_compact_boundary_continuation nestedStrictConvex_of_positive_areas tripleChart_strictConvex_neighborhood", route="One actual-root product radius precedes the universal alpha-in-[0,1] quantifier. All six signed exterior areas, three macro areas, and the internal area are retained explicitly; compactness is applied to proved local root neighborhoods.")
bind(["prose:599", "display:600"], "tripleScalarPotential_source_formula tripleScalarPotential_strictConvexOn tripleScalarPotential_isProperMap tripleScalarPotential_divided_gradient tripleScalarPotential_critical_iff_root tripleScalarPotential_exists_minimizer tripleScalar_potential_root_existsUnique_centered", route="Original displayed potential and actual divided-gradient equations; ordered-chamber properness and strict convexity, followed by an actual variational minimizer, give the unique centered ordered root for every positive weight vector.")
bind("eq:internal", "tripleScalar_potential_root_existsUnique_centered tripleScalar_root_unique_by_integratedJacobian tripleScalar_root_weighted_center", route="Original variational positive-weight existence and the original integrated-Jacobian uniqueness for nonnegative weights, with every divided equation retained.")
bind("prose:604", "tripleScalar_potential_root_existsUnique_centered tripleScalarResidual_hasFDerivAt tripleScalar_J_entries_complete", route="Original scalar potential route proves the unique centered positive-weight root; actual derivative entries include zero weights.")
bind("display:557", "pairChartRows_half_interval_choice pairChartPhysicalRows_zero_iff")
bind("prose:561", "pairChart_omitted_mass_lower_fixed_anchor pairCoordinateMatrix_det pairRows_recovery", route="The omitted row is selected using the fixed limiting p0, with an explicit positive bound on a full current-p neighborhood of that anchor; recovery never divides by a mass.")
bind("eq:pair-J", "pairChartJacobian_exterior_source_a0 pairChartJacobian_unit_mean pairChartJacobian_unit_difference")
bind("prose:582", "pairSourceA0_abs_lower pairChartJacobian_boundary_isInvertible pairChart_compact_boundary_continuation pairChart_zero_eps_all_scale_faces pairRadial_root_exact_factor pairRadial_root_compact_uniform_bound")
bind("display:568", "twoSourcePolarAngular_source_formula twoSourcePolarAngular_fderiv_apply")
bind("display:684", "nestedScalarH_source_formula nestedScalarK_source_formula nestedScalarFields_at_actual_targets nestedRadialExterior_recovery nestedAngularExterior_recovery")
bind("eq:Hzero", "regularTripleScalarH_source_formula")
bind("display:634", "regularTripleBoundaryM_source_formula tripleAngularDifference_boundary_eq_LM tripleAngularMean_boundary_source_H")
bind("prose:874", "polarDividedEdgeIntegral_factor polarDividedEdgeIntegral_zero triplePointDirection_original_integral_all_scales triplePointDirection_joint_contDiff", route="Original line-segment integration is proved for the actual polar target map. Its value agrees with the original divided-edge extension at every signed scale, including zero; joint smoothness is then the proved smoothness of that same actual function.")
bind("display:875", "triplePointDirection_identity triplePointDirection_source_at_zero triplePointDirection_original_integral_all_scales")
bind("display:798", "backgroundProbeField_source_formula backgroundProbeField_hasFDerivAt")
bind("eq:scalar-slow", "scalarSlow_source_equations scalarSlow_positive_seed tripleScalar_centered_gap_root_recovery nestedUnitPoint_scalar_root")
bind("eq:regular-slow", "tripleChart_zero_face_eq_slowPoint_of_local_uniqueness tripleSlowPoint_source_formula tripleSlowPoint_root", route="Actual implicit branch equality to the complete seven-coordinate candidate at epsilon=0, using its own current-alpha zero-epsilon seed gaps and local uniqueness.")
bind("prose:856", "nestedBoundaryScalarPositions_source_formula nestedBoundaryScalarPositions_weighted_center nestedChart_zero_face_eq_slowPoint_of_local_uniqueness nestedSlowPoint_source_formula nestedSlowRootCandidate_contDiffAt nestedSlowRootCandidate_contDiffOn nestedUnitPoint_scalar_root nestedSlowPoint_root", route="Complete nested scalar positions, weighted center, seven-coordinate slow candidate and actual branch identity, including joint candidate smoothness in the independent parameters.")
bind("display:719", "nestedOuterN_formula nestedOuterO_formula nestedInnerN_source_formula nestedInnerO_source_formula")
bind("eq:nest-angular", "nestedAngularRows_source_complete nestedScalarH_source_formula nestedOuterL_formula nestedInnerM_formula")
bind("eq:nest-radial", "nestedRadialRows_source_complete nestedScalarK_source_formula nestedInnerN_source_formula nestedInnerO_source_formula nestedInnerJ_formula_complete")
bind("display:746", "nestedBoundaryKernels_source_complete nestedInnerM_at_boundary")
bind("prose:675", "nestedToFixedSlice_full_matrix nestedToFixedSlice_full_det nestedToFixedSlice_full_abs_det nestedRows_recovery nestedChartPhysicalRows_zero_iff nestedChartExtendedRows_zero_iff_normalized", route="The actual seven-coordinate transformation has its full 1+3+3 block matrix and exact determinant t^4 eta^2 for every alpha, including zero-mass endpoints. Original residual row recovery is retained separately.")
bind("prose:771", "nestedBoundaryKernel_original_derivatives nestedBasePoint_formula_complete nestedBasePoint_regular nestedChartJacobian_boundary_alpha_independent nestedBoundaryDerivativeMatrix_det nestedChartJacobian_boundary_isInvertible nestedChart_compact_boundary_continuation nestedChart_zero_eps_all_scale_faces nestedChart_convex_physical_continuation nestedChart_radial_uniform_epsilon_bound", route="All three original scalar-kernel derivative values and the independence of the entire seven-dimensional derivative from alpha are explicit. The actual compact continuation and quantitative O(epsilon) bounds retain an independent product and all zero-mass endpoints.")
bind("display:774", "normalized_complete_lower_triple_nested_scale_complete normalized_complete_upper_triple_nested_scale_complete normalized_complete_lower_triple_nested_radial_bound nestedSource_individual_inverse_limits nestedSource_radial_Oepsilon_from_original_bound normalized_complete_lower_triple_nested_original_capture", route="Actual lower and upper nested physical scale theorems supply the scalar inverse-limit package and genuine radial O(epsilon) estimate. Individual scale, angular and radial coordinate limits are exposed separately; no alpha convergence is supplied.")
bind("prose:779", "normalized_complete_lower_triple_nested_directions normalized_complete_upper_triple_nested_scale_complete nestedSource_individual_inverse_limits nestedSource_common_balls_without_alpha_limit normalized_complete_lower_triple_nested_original_capture orderedSlice_lower_nested_triple_capture", route="Both signed pair-to-third-body angle limits are original actual-root theorems. Their current-alpha average gives the outer angular coordinate, and all seven variables enter common parameter/root balls without convergence of alpha.")
bind("display:780", "nestedSourceCasePermutation_source nestedSourceCaseTable_source nestedSourceCase_order_is_original", route="All four original sign and label rows are derived from the actual nested hull permutation, with the original five physical labels recovered explicitly.")
bind("prose:539", "closedCoorbital_largest_mass_gauge fixedAngleDeletedResidual_same_eq noCollision_physical_local_continuation reducedJacobian_at_closed_separated_root_isInvertible", route="The source largest-mass choice has mu_p at least one quarter and its explicit gauge recovery. Actual no-collision continuation retains the original four radial and three retained angular rows.")
bind("display:541", "fixedAngle_zero_source_full_block reducedAngularJacobian_zero_full_matrix reducedJacobian_at_closed_separated_root_isInvertible", route="The actual full seven-dimensional derivative has radial block 3I4, zero upper-right block and the original lower angular blocks L,K; the exact full angular matrix and invertibility are checked separately.")
bind("prose:833", (
    "affinePolarPoint_divided_identity affinePolarPoint_cartesian_Osquare "
    "tripleChartPoint_cartesian_Osquare tripleChart_exteriorMass_Ocube "
    "tripleChart_relativeAverage_cubic_identity tripleChart_relativeAverage_Ocube "
    "tripleChart_reaction_Ocube nestedBoundaryDisplacement_to_triple "
    "nestedChartPoint_cartesian_Osquare nestedChart_reaction_Ocube "
    "newtonTargetField_affinePolar_Osquare backgroundProbeField_affinePolar_Osquare "
    "tripleInternalCartesian_scaling tripleInternalVectorQuotient_zero "
    "tripleInternalVectorQuotient_contDiffAt tripleInternalVectorQuotient_Olinear "
    "tripleInternalCartesian_Osquare backgroundProbeField_zero "
    "tripleBoundaryDisplacement_radial tripleBoundaryDisplacement_angular "
    "tripleInternalRadialReduced_vector_projection tripleInternalAngularReduced_vector_projection "
    "tripleRadialExteriorDifference_background tripleAngularExteriorDifference_background "
    "tripleRadialMean_background_zero tripleAngularMean_background_zero "
    "tripleExteriorRadialRow_background_zero tripleSlowPoint_vector_balance "
    "tripleSlowPoint_root nestedSlowPoint_root"
), route="Actual polar Cartesian curves have quadratic Taylor remainders, and the original current exterior mass and reaction change cubically. The true Newton/background field and actual singular internal Cartesian force have independent quadratic remainder theorems; physical internal scaling is on positive t approaching zero. The exact zero-scale radial/tangential projections, vanishing background mean/exterior rows and actual slow roots retain the original first-order proof route, including smooth extension to parameter faces.")

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def generate_audit():
    # Imports include every new independently owned lemma. Main supplies the
    # original chart development; these imports do not weaken any statement.
    renames = {
        "angularResidual_weighted_sum": "weighted_angularResidual_zero",
        "pairChart_pair_distance_sq": "pairChart_distance_sq",
        "nestedAngularRows_scalar_root_recovery": "nestedUnitPoint_scalar_root",
        "nestedInner_distance_sq": "nestedInnerWSq_formula",
        "nestedOuter_distance_sq": "nestedOuterWSq_formula",
        "tripleExteriorAreaQuotient_primary_boundary": "tripleExternalAreaQuotient_primary_boundary",
        "tripleExteriorAreaQuotient_exterior_boundary": "tripleExternalAreaQuotient_exterior_boundary",
    }
    for review in REVIEW.values():
        review["names"] = [renames.get(n,n) for n in review["names"]]
    names = sorted({n for v in REVIEW.values() for n in v["names"]})
    # A theorem need not be a dependency of Main. Include its actual declaring
    # module explicitly; missing modules/decls cause the strict audit to fail.
    modules = set()
    for p in (ROOT / "DominantFiveBody").glob("*.lean"):
        txt = p.read_text(encoding="utf-8")
        if any(re.search(r"\b(?:theorem|lemma)\s+" + re.escape(n) + r"\b", txt) for n in names):
            modules.add("DominantFiveBody."+p.stem)
    lines = ["import DominantFiveBody.Main", "import DominantFiveBody.ChartFormulaCoverage",
             "import DominantFiveBody.HadamardTargetDifference",
             "import DominantFiveBody.JointAnalyticCharts",
             "import DominantFiveBody.NestedBoundaryDeterminant",
             "import DominantFiveBody.SmoothOrderedSliceConnection",
             *["import " + m for m in sorted(modules)],
             "set_option pp.fullNames true", "set_option pp.proofs true", "set_option pp.numericTypes true",
             "set_option pp.maxSteps 10000000"]
    for n in names:
        name = n if n.startswith("DominantFiveBody.") else "DominantFiveBody." + n
        lines += [f'#eval IO.println "COVERAGE_BEGIN {name}"',
                  f"#check @{name}", f"#print axioms {name}",
                  f'#eval IO.println "COVERAGE_END {name}"']
    path = ROOT / "Audit" / "ChartSourceCoverage.lean"
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path, names

def extract(log):
    ans = {}
    for name, block in re.findall(r"COVERAGE_BEGIN ([^\n]+)\n(.*?)COVERAGE_END \1", log, re.S):
        block = block.strip()
        match = re.search(r"'" + re.escape(name) + r"' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", block)
        if not match:
            raise RuntimeError("Missing axiom audit: " + name)
        typ = block[:match.start()].strip()
        if "..." in typ or "⋯" in typ:
            raise RuntimeError("Pretty-printer truncated declaration: " + name)
        axioms = [] if match.group(2) is None else [a.strip() for a in match.group(2).split(",") if a.strip()]
        forbidden = set(axioms) - {"propext", "Classical.choice", "Quot.sound"}
        if forbidden:
            raise RuntimeError("Unapproved axioms in " + name + ": " + str(forbidden))
        ans[name.removeprefix("DominantFiveBody.")] = dict(
            lean_declaration=name, lean_statement=typ, axioms=axioms,
            axiom_audit="Kernel declaration axiom dependency traversal; standard Lean logical axioms only.")
    return ans

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--use-log", help="Reuse a successful already strict-compiled audit log.")
    args = parser.parse_args()
    audit, names = generate_audit()
    log_path = ROOT / "docs" / "COVERAGE_CHARTS_LEAN.log"
    if args.use_log:
        log = Path(args.use_log).read_text(encoding="utf-8")
        exit_code = 0
    else:
        env = dict(os.environ)
        env["PATH"] = "C:/Users/衔月/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/git/cmd;" + env.get("PATH", "")
        env["LEAN_NUM_THREADS"] = "2"
        run = subprocess.run(["pwsh", "-NoProfile", "-File", "scripts/lean_checked.ps1",
                              "-SourceFile", str(audit.relative_to(ROOT))],
                             cwd=ROOT, env=env, encoding="utf-8", capture_output=True, timeout=600)
        log = run.stdout + run.stderr
        exit_code = run.returncode
        log_path.write_text(log, encoding="utf-8")
        if exit_code or re.search(r"error(?:\(|:)|PANIC|internal exception", log, re.I):
            print(log[-18000:])
            raise SystemExit(exit_code or 1)
    if re.search(r"error(?:\(|:)|PANIC|internal exception", log, re.I):
        raise RuntimeError("Reused strict audit log contains an error or internal exception.")
    types = extract(log)
    missing_names = set(names) - set(types)
    if missing_names:
        raise RuntimeError("Incomplete audited output: " + repr(missing_names))
    inventory = json.loads((ROOT / "docs" / "FULL_ASSERTIONS.json").read_text(encoding="utf-8"))
    entries = []
    for assertion in inventory["assertions"]:
        if not 506 <= assertion["source_location"]["tex_lines"][0] <= 941:
            continue
        ident = assertion["id"]
        review = REVIEW.get(ident, dict(names=[], missing=["No independent complete binding yet reviewed for this exact source assertion."], route="OPEN: no promotion from main-theorem success."))
        bindings = [types[n] for n in review["names"]]
        status = "SOURCE_CROSS_REFERENCE" if "source_cross_references" in review else ("OPEN" if review["missing"] else "VERIFIED")
        item = dict(id=ident, source_location=assertion["source_location"], exact_claim=assertion["exact_claim"],
                    status=status, lean_bindings=bindings, remaining_dependencies=review["missing"], proof_route=review["route"])
        if "source_cross_references" in review:
            item["source_cross_references"] = review["source_cross_references"]
        if len(bindings) == 1:
            item["lean_declaration"] = bindings[0]["lean_declaration"]
            item["lean_statement"] = bindings[0]["lean_statement"]
        entries.append(item)
    counts = dict(collections.Counter(x["status"] for x in entries))
    result = dict(schema_version=1, scope="Independent original Sections 5--6, TeX 506--938, plus Section 7 context at 940.",
                  source_tex_sha256=sha(ROOT / "source" / "dominant_five_body_ARMA_rewritten.tex"),
                  strict_lean_exit_code=exit_code, audit_file=str(audit.relative_to(ROOT)),
                  audit_sha256=sha(audit), audit_log_sha256=sha(log_path),
                  audited_unique_declarations=len(types), status_counts=counts,
                  completeness="OPEN entries remain blockers; alternative proofs never discharge unproved original auxiliary assertions.", assertions=entries)
    out = ROOT / "docs" / "COVERAGE_CHARTS_PATCH.json"
    out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    report = ["# Independent original chart source review", "", f"Strict Lean exit code: {exit_code}. Audited declarations: {len(types)}.",
              f"Source assertions: {len(entries)}. Status counts: {counts}.", "",
              "This patch does not change the combined inventory. Every proof binding contains its actual complete current Lean type and audited axioms. A multi-assertion paragraph stays OPEN whenever a listed source subclaim is not proved. Context cross-references introduce formulas and do not stand in for their proofs.", "",
              "Original-versus-alternative routes are recorded per assertion. The original integrated-Jacobian uniqueness argument and nested three-variable kernel integrals are now proved separately from the earlier maximum-coordinate and rationalized-field alternatives. Original variational and divided-edge integral obligations retain their own statuses.", "", "## Remaining original obligations", ""]
    for e in entries:
        if e["status"] == "OPEN":
            report += [f"- `{e['id']}` (TeX {e['source_location']['tex_lines']}): " + " ".join(e["remaining_dependencies"])]
    (ROOT / "docs" / "COVERAGE_CHARTS_REVIEW.md").write_text("\n".join(report) + "\n", encoding="utf-8")
    print(json.dumps({"assertions":len(entries),"counts":counts,"audited":len(types),"patch":str(out)},ensure_ascii=False))

if __name__ == "__main__":
    main()
