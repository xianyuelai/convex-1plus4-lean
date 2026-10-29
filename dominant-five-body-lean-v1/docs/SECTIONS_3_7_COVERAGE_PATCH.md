# 第 3、7 节独立源断言对应补丁

原文逐字及完整 Lean 类型见 SECTIONS_3_7_COVERAGE_PATCH.json。本补丁不修改全文清单。

52 个源条目：{'NON_MATHEMATICAL': 5, 'DEFINITIONAL': 11, 'VERIFIED': 36}；共 139 个完整类型绑定。没有 PARTIAL 条目。

原审计 73473、表示审计 98431 和追加审计 SectionsThreeSevenComplete 均严格通过；追加审计打印 54 个声明的完整类型和公理，仅依赖 propext、Classical.choice、Quot.sound。所有新增编译经共享锁脚本执行。

新增直接证明包括 centeredFromRelative 的全部原坐标恒等式、E=R x直和T及实际Hessian正交性、三图固定质量端点的原角间隙，以及原Q_n集合定义。七方程等价、正对角Hessian、角块可逆、四图全产品、同质量零端点、scalar根提取和实际光滑规范恢复均分别绑定。

CCLM出处句属于外部文献归属；本补丁独立证明该句周围的数学结论及原径向/角向论证步骤，没有把匹配结论写成对外部文本归属的形式认证。

本补丁的源覆盖不代表整篇论文已完成最终构建、全声明公理审计或fresh kernel验收。

| 原文条目 / 行 | 状态 | 实际Lean声明/定义 |
|---|---|---|
| prose:214 / 214–214 | NON_MATHEMATICAL |  |
| eq:cc / 215–218 | DEFINITIONAL | DominantFiveBody.NormalizedCentralConfiguration<br>DominantFiveBody.acceleration<br>DominantFiveBody.weightedPosition<br>DominantFiveBody.pairDistance |
| prose:219 / 219–219 | NON_MATHEMATICAL |  |
| eq:UI / 220–223 | DEFINITIONAL | DominantFiveBody.potential<br>DominantFiveBody.inertia<br>DominantFiveBody.augmentedPotential<br>DominantFiveBody.pairs |
| prose:224 / 224–224 | DEFINITIONAL | DominantFiveBody.polarPoint<br>DominantFiveBody.polarSatellites<br>DominantFiveBody.satellitesRelative<br>DominantFiveBody.relativeAverage<br>DominantFiveBody.relativeField |
| display:225 / 225–229 | DEFINITIONAL | DominantFiveBody.polarPoint<br>DominantFiveBody.polarSatellites<br>DominantFiveBody.satellitesRelative<br>DominantFiveBody.relativeAverage<br>DominantFiveBody.relativeField |
| prose:230 / 230–231 | VERIFIED | DominantFiveBody.centeredFromRelative_source_formulas<br>DominantFiveBody.centeredFromRelative<br>DominantFiveBody.liftRelative |
| prose:233 / 233–233 | NON_MATHEMATICAL |  |
| eq:G / 234–237 | VERIFIED | DominantFiveBody.normalized_centeredFromRelative_iff_vectorRoot<br>DominantFiveBody.vectorResidual |
| prose:238 / 238–238 | VERIFIED | DominantFiveBody.normalized_of_vectorResidual_zero |
| eq:action / 239–244 | VERIFIED | DominantFiveBody.relativeAction_eq_augmentedPotential_div<br>DominantFiveBody.relativeAction |
| eq:action.inertia_reduction / 244–244 | VERIFIED | DominantFiveBody.inertia_centeredFromRelative |
| prose:245 / 245–248 | VERIFIED | DominantFiveBody.inertia_centeredFromRelative<br>DominantFiveBody.relativeActionVectorGradient_eq_CF<br>DominantFiveBody.relativeMassMatrix_posDef<br>DominantFiveBody.relativeAction_critical_iff_vectorRoot |
| eq:action.mass_metric_positive / 246–246 | VERIFIED | DominantFiveBody.relativeMassMatrix_posDef |
| eq:action.actual_critical_equivalence / 248–248 | VERIFIED | DominantFiveBody.relativeAction_critical_iff_vectorRoot |
| prose:250 / 250–251 | DEFINITIONAL | DominantFiveBody.radialResidual<br>DominantFiveBody.angularResidual |
| eq:R / 252–258 | DEFINITIONAL | DominantFiveBody.polarAction_fderiv_apply<br>DominantFiveBody.radialResidual<br>DominantFiveBody.angularResidual |
| eq:T / 252–258 | DEFINITIONAL | DominantFiveBody.polarAction_fderiv_apply<br>DominantFiveBody.radialResidual<br>DominantFiveBody.angularResidual |
| prose:259 / 259–259 | NON_MATHEMATICAL |  |
| eq:polar-gradient / 260–264 | VERIFIED | DominantFiveBody.polarAction_fderiv_apply<br>DominantFiveBody.weighted_angularResidual_zero |
| prose:265 / 265–265 | VERIFIED | DominantFiveBody.angularResidual_omitted_row<br>DominantFiveBody.normalized_centeredFromRelative_iff_vectorRoot<br>DominantFiveBody.reducedPolarResiduals_zero_iff_vectorRoot<br>DominantFiveBody.normalizedCC_of_reducedResidual_zero<br>DominantFiveBody.radialResidual<br>DominantFiveBody.angularResidual |
| prose:267 / 267–267 | VERIFIED | DominantFiveBody.vectorResidual_tangential<br>DominantFiveBody.tangentialResidual_zero_of_normalized<br>DominantFiveBody.tangentialResidual |
| eq:Q / 268–271 | VERIFIED | DominantFiveBody.vectorResidual_tangential<br>DominantFiveBody.tangentialResidual_zero_of_normalized<br>DominantFiveBody.tangentialResidual |
| prose:272 / 272–273 | VERIFIED | DominantFiveBody.relativeField_eq_scaledAverage_of_vectorRoot<br>DominantFiveBody.sectionThree_solution_field_and_tangential_identity |
| lem:hessian / 275–277 | VERIFIED | DominantFiveBody.fixedAngleDeletedJacobian_isInvertible_iff_shape<br>DominantFiveBody.coordinate_row_transform_isInvertible_iff |
| prose:275 / 275–280 | VERIFIED | DominantFiveBody.fixedAngleDeletedJacobian_isInvertible_iff_shape<br>DominantFiveBody.coordinate_row_transform_fderiv_at_root<br>DominantFiveBody.coordinate_row_transform_isInvertible_iff<br>DominantFiveBody.sliceWeightedMetric_apply<br>DominantFiveBody.sliceMassWeights_pos<br>DominantFiveBody.sliceAction_second_fderiv<br>DominantFiveBody.sliceAction_second_fderiv_isInvertible_iff_reducedJacobian |
| lem:hessian.actual_fixed_slice_bridge / 277–277 | VERIFIED | DominantFiveBody.fixedAngleDeletedJacobian_isInvertible_iff_shape<br>DominantFiveBody.coordinate_row_transform_isInvertible_iff |
| prose:282 / 282–284 | DEFINITIONAL | DominantFiveBody.shapeSpace<br>DominantFiveBody.centeredVariationSpace |
| display:285 / 285–287 | VERIFIED | DominantFiveBody.physicalHessian_radial_of_normalizedCC<br>DominantFiveBody.rotationSliceHessian_nondegenerate_iff_shape<br>DominantFiveBody.centered_radial_tangent_direct_sum<br>DominantFiveBody.inertiaTangentSpace |
| prose:288 / 288–291 | VERIFIED | DominantFiveBody.physicalHessian_radial_of_normalizedCC<br>DominantFiveBody.relativeCenteredEquiv<br>DominantFiveBody.relativeAction_eq_augmentedPotential_div<br>DominantFiveBody.rotationSliceHessian_nondegenerate_iff_shape<br>DominantFiveBody.finrank_shapeSpace<br>DominantFiveBody.centered_radial_tangent_hessian_orthogonal |
| prose:293 / 293–293 | NON_MATHEMATICAL |  |
| lem:product / 295–300 | VERIFIED | DominantFiveBody.CompactImplicit.compact_product |
| prose:295 / 295–303 | VERIFIED | DominantFiveBody.CompactImplicit.compact_product |
| prop:local / 305–309 | VERIFIED | DominantFiveBody.coorbital_compact_physical_continuation |
| prose:305 / 305–313 | VERIFIED | DominantFiveBody.coorbital_compact_physical_continuation<br>DominantFiveBody.reducedJacobian_zero_radial_block<br>DominantFiveBody.coorbitalBaseSlice_actual_data<br>DominantFiveBody.reducedAngularJacobian_zero_eq<br>DominantFiveBody.reducedAngularJacobian_zero_isInvertible<br>DominantFiveBody.reducedJacobian_at_coorbital_root_isInvertible |
| prose:315 / 315–316 | VERIFIED | DominantFiveBody.sinc_contDiff<br>Real.sinc_zero |
| prop:chart-interface / 928–931 | VERIFIED | DominantFiveBody.normalized_noCollision_actual_capture<br>DominantFiveBody.normalized_complete_pair_actual_capture<br>DominantFiveBody.normalized_complete_lower_triple_regular_actual_capture<br>DominantFiveBody.normalized_complete_lower_triple_nested_original_capture<br>DominantFiveBody.orderedSlice_smooth_connection_explicit<br>DominantFiveBody.nestedChart_convex_physical_continuation<br>DominantFiveBody.tripleChart_convex_physical_continuation<br>DominantFiveBody.pairChart_compact_physical_continuation<br>DominantFiveBody.noCollision_physical_local_continuation<br>DominantFiveBody.pairChart_fixed_mass_zero_endpoint<br>DominantFiveBody.tripleChart_fixed_mass_zero_endpoint<br>DominantFiveBody.nestedChart_fixed_mass_zero_endpoint |
| prose:928 / 928–938 | VERIFIED | DominantFiveBody.normalized_noCollision_actual_capture<br>DominantFiveBody.normalized_complete_pair_actual_capture<br>DominantFiveBody.normalized_complete_lower_triple_regular_actual_capture<br>DominantFiveBody.normalized_complete_lower_triple_nested_original_capture<br>DominantFiveBody.orderedSlice_smooth_connection_explicit<br>DominantFiveBody.nestedContinuationRoot_fixed_mass_endpoint<br>DominantFiveBody.reducedResidual_fixed_mass_zero_endpoint<br>DominantFiveBody.pairChart_compact_physical_continuation<br>DominantFiveBody.noCollision_physical_local_continuation<br>DominantFiveBody.pairChart_fixed_mass_zero_endpoint<br>DominantFiveBody.tripleChart_fixed_mass_zero_endpoint<br>DominantFiveBody.nestedChart_fixed_mass_zero_endpoint<br>DominantFiveBody.pairToFixedSlice_isInvertible<br>DominantFiveBody.pairFixedRowTransform_isInvertible<br>DominantFiveBody.tripleToFixedSlice_isInvertible<br>DominantFiveBody.tripleFromFixedSlice_isInvertible<br>DominantFiveBody.nestedToFixedSlice_isInvertible<br>DominantFiveBody.nestedFromFixedSlice_isInvertible<br>DominantFiveBody.pairChartExtendedRows_zero_iff_physical<br>DominantFiveBody.tripleChartExtendedRows_zero_iff_physical<br>DominantFiveBody.nestedChartExtendedRows_zero_iff_physical<br>DominantFiveBody.pairChart_endpoint_gap_nonzero<br>DominantFiveBody.tripleChart_endpoint_gaps_nonzero<br>DominantFiveBody.nestedChart_endpoint_gaps_nonzero |
| prose:940 / 940–942 | DEFINITIONAL | DominantFiveBody.orderedSliceRoot<br>DominantFiveBody.sliceRadii<br>DominantFiveBody.sliceAngles<br>DominantFiveBody.slicePhysicalConfiguration |
| display:943 / 943–946 | DEFINITIONAL | DominantFiveBody.orderedSliceRoot<br>DominantFiveBody.sliceRadii<br>DominantFiveBody.sliceAngles<br>DominantFiveBody.slicePhysicalConfiguration |
| prose:947 / 947–947 | VERIFIED | DominantFiveBody.strictConvexCC_existsUnique_normalized_gauged<br>DominantFiveBody.orderedSliceRoot_of_normalized_gauged<br>DominantFiveBody.orderedSliceRoot_physical<br>DominantFiveBody.ordered_slicePhysicalConfiguration_injective<br>DominantFiveBody.orderedSliceRoot_unique_coordinates_of_normalized_gauged<br>DominantFiveBody.orderedSliceRoot_existsUnique_orientedSimilar |
| prop:connection / 949–955 | VERIFIED | DominantFiveBody.orderedSlice_smooth_connection_explicit |
| prose:949 / 949–950 | VERIFIED | DominantFiveBody.orderedSlice_smooth_connection_explicit |
| display:951 / 951–953 | VERIFIED | DominantFiveBody.orderedSlice_smooth_connection_explicit |
| prose:954 / 954–963 | VERIFIED | DominantFiveBody.orderedSlice_smooth_connection_explicit<br>DominantFiveBody.normalized_ordered_polar_limit_geometry<br>DominantFiveBody.normalized_ordered_collision_classes_exhaustive<br>DominantFiveBody.collision_free_triple_scale_subsequence<br>DominantFiveBody.triple_minimum_pair_subsequence<br>DominantFiveBody.orderedSlice_connection<br>DominantFiveBody.tripleScalar_seed_of_regular_scaled_limits<br>DominantFiveBody.triplePhysical_capture_of_regular_scaled_limits<br>DominantFiveBody.pairChart_compact_boundary_continuation<br>DominantFiveBody.nestedChart_compact_boundary_continuation<br>DominantFiveBody.orderedPolarSlice_angles<br>DominantFiveBody.orderedPolarSlice_radii<br>DominantFiveBody.orderedPolarSlice_contDiff<br>DominantFiveBody.orderedPolarSlice_physical_eq_rotation<br>DominantFiveBody.orderedPolarSlice_root_of_normalized<br>DominantFiveBody.orderedPolarSlice_nondegenerate_of_normalized<br>DominantFiveBody.orderedPolarSlice_reindex_undo<br>DominantFiveBody.orderedPolarSlice |
| prose:965 / 965–968 | VERIFIED | DominantFiveBody.orderedSlice_fixedParameterLocalExistence<br>DominantFiveBody.coorbitalBaseSlice_actual_data<br>DominantFiveBody.orderedSlice_smooth_connection_explicit<br>DominantFiveBody.orderedSlice_localContinuationUniqueness |
| prose:970 / 970–973 | VERIFIED | DominantFiveBody.uniform_existence_of_connection<br>DominantFiveBody.orderedSlice_fixedParameterLocalExistence<br>DominantFiveBody.orderedSlice_connection |
| prose:975 / 975–979 | VERIFIED | DominantFiveBody.uniform_uniqueness_of_connection<br>DominantFiveBody.orderedSlice_localContinuationUniqueness<br>DominantFiveBody.orderedSlice_connection |
| display:980 / 980–982 | DEFINITIONAL | DominantFiveBody.mem_branchEqualitySet<br>DominantFiveBody.branchEqualitySet |
| prose:983 / 983–984 | VERIFIED | DominantFiveBody.uniform_uniqueness_of_connection<br>DominantFiveBody.orderedSlice_localContinuationUniqueness<br>DominantFiveBody.orderedSlice_connection |
| prose:986 / 986–987 | VERIFIED | DominantFiveBody.uniform_nondegeneracy_of_connection<br>DominantFiveBody.orderedSlice_connection |
| prose:989 / 989–992 | VERIFIED | DominantFiveBody.main_of_chart_facts<br>DominantFiveBody.main_of_orderedSlice_uniform<br>DominantFiveBody.orderedSlice_uniqueness_to_geometric<br>DominantFiveBody.orderedSlice_nondegeneracy_to_geometric<br>DominantFiveBody.main_uniform |
