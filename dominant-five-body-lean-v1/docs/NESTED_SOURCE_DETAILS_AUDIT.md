# Nested source details and Cartesian Taylor audit

Original nodes: `prose:771`, `display:774`, `prose:779`, `display:780`, and `prose:833` in `source/dominant_five_body_ARMA_rewritten.tex`.

| Original assertion | Actual Lean connection |
| --- | --- |
| Kernel derivatives -2D0, 6D0/Z0, -6D0 | `nestedBoundaryKernel_original_derivatives` differentiates the actual nested boundary kernel. |
| Full boundary derivative independent of alpha | `nestedChartJacobian_boundary_alpha_independent` compares the complete seven-dimensional continuous linear derivatives of actual extended rows. The row equality is established on a neighborhood with positive original denominators. |
| Individual inverse scales and signed capture limits | `nestedSource_individual_inverse_limits` exposes t, eta, d/t, s/(t eta), both signed outer angular differences, radial and angular coordinates, and the whole seven-coordinate vector. |
| Common balls without alpha convergence | `nestedSource_common_balls_without_alpha_limit` centers every parameter ball at that sequence member's current alpha. |
| Inner radial O(epsilon) | `nestedSource_radial_Oepsilon_from_original_bound` converts the already established original bound by the actual positive inverse scale limit. |
| Four original chart cases | `nestedSourceCaseTable_source` gives the literal one-based table. `nestedSourceCasePermutation_source` and `nestedSourceCase_order_is_original` bind it to the actual convex hull order. |
| Polar Cartesian O(t^2) | `tripleChartPoint_cartesian_Osquare` and `nestedChartPoint_cartesian_Osquare` use the actual chart points and actual boundary displacements. |
| Exterior mass and reaction O(t^3) | `tripleChart_exteriorMass_Ocube`, `tripleChart_relativeAverage_cubic_identity`, `tripleChart_reaction_Ocube`, and `nestedChart_reaction_Ocube` use the literal chart mass and reaction average. The reaction factor is an exact all-real-t identity before its asymptotic consequence. |
| Actual background field first-order term | `newtonTargetField_affinePolar_Osquare` and `backgroundProbeField_affinePolar_Osquare` prove genuine quadratic remainders for the original Newton and background fields. The latter uses the true derivative and F(q0)=0. |
| Actual internal first-order term | `tripleInternalCartesian_scaling` is an exact positive-scale identity for mass/distance Cartesian interactions; the smooth quotient at zero equals minus the actual boundary internal force. `tripleInternalCartesian_Osquare` gives the physical interaction remainder O(t^2) as t tends to zero through positive scales. |

The internal physical expansion has the original positive-scale domain. Its local separation hypothesis is positivity of the actual rescaled squared pair distances, as required by the original distinct scalar positions. The background expansion uses the original noncollision and positive background radius conditions. No convergence assumption on alpha is added to capture.

Strict compile receipts:

- `NestedSourceDerivativeDetails.lean`: session 25385, EXIT 0.
- `NestedSourceSignTable.lean`: session 47200, EXIT 0.
- `NestedSourceCaptureDetails.lean`: session 21638, EXIT 0.
- `SlowTaylorOrders.lean`: session 91863, EXIT 0.
- `SlowNewtonTaylor.lean`: session 16630, EXIT 0.
- Final public-helper `SlowInternalTaylor.lean`: session 33550, EXIT 0.
- Current actual info.type export: session 85739, EXIT 0.
- Full exact-type replay of 28 declarations: session 51728, EXIT 0.

All runs use the shared compiler lock, warningAsError=true, and autoImplicit=false. Every printed axiom list is a subset of propext, Classical.choice, Quot.sound. The exact type exporter includes pp.numericTypes=true; the replay contains all 28 complete original info.type expressions and no ellipses. This receipt covers this source group; the project-wide assertion ledger and acceptance decision are produced separately.

## SHA256 binding
- source/dominant_five_body_ARMA_rewritten.tex: 9B080F2516C79F16B3EE1097A2C853D3FE50C9674C309C5BD7826453A52FB5E2
- DominantFiveBody/NestedSourceDerivativeDetails.lean: DCF7735AB649D8B66DC2B5A5E41AE773C7C26F297C9D84412E35970767CE05E4
- DominantFiveBody/NestedSourceSignTable.lean: FEE78A08D2C6522C85064FDB7BDC89C9CC66DA7C45A79A3E586C040EC6A60BE5
- DominantFiveBody/NestedSourceCaptureDetails.lean: 70157A73F3B0625E71E38078778861E9A93C1300CE9C934F1416C055D34549CB
- DominantFiveBody/SlowTaylorOrders.lean: 1F72174FBCAFB875DCD4628C1762DFD2AAC8AF04B1F1A3EAE521117422BE081C
- DominantFiveBody/SlowNewtonTaylor.lean: D070586E6628997D4CC1564AC66D92650342AD305BB454C9D2DE9CEC65E39A99
- DominantFiveBody/SlowInternalTaylor.lean: 3F007AB964D4E8E1A3C5CE22403F772F56A0A26CAE80552D086C798A6A65FCBB
- scripts/audit_nested_source_details.py: F19736CEF23D8F07802D18C6DD1CD38C11C77D5D96088E611EE4DFE4D0248CFA
- Audit/ExportNestedSourceDetails.lean: C95494BA105C6ABA206F25034E1521283A1B6FDAB64F1BE8EFBED0FE49ACD8E3
- Audit/NestedSourceDetails.lean: 01CA671A5CEE39BEEDFF58B8D49598525119A07A1644832434ECB32F0CB899C6
- docs/nested-source-details-types.json: F55109B04FC65CC3DF30D3147C016B9C08584D6151A02C961D1AE3BAF796233A
- docs/nested-source-details-export-axioms-audit.log: 06781F62AD51A61B548FD6BE642AEC39B906B63874D5A09348774071AB92B759
- docs/nested-source-details-complete-axioms-audit.log: 82FAE22E4B11F8B96C13F01263A10D571ED9CB5C3A3D021A983DEB3CC9609D16
