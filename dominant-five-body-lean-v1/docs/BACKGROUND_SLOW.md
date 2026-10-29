# Section 6.1: verified equilateral background

`DominantFiveBody/BackgroundSpectrum.lean` and
`DominantFiveBody/BackgroundSlow.lean` formalize the actual background
matrix, its slow branch, and the scalar-to-vector Newton-force reduction.

## Source correspondence

| Manuscript statement | Lean theorem |
| --- | --- |
| `F(q^0)=0` | `backgroundProbeField_zero` |
| `DF(q^0)=B` with the actual Newton field | `backgroundProbeField_hasFDerivAt`, `backgroundProbeField_fderiv` |
| `eq:bg-matrix` in the radial/tangential orthonormal basis | `backgroundOperator_coordinates` |
| `tr B=3`, `det B=27 eps/(4(1+eps)^2)` | `backgroundMatrix_trace`, `backgroundMatrix_det` |
| `eq:slow`, including the rationalized formula | `backgroundSlowLambda_eq`, `backgroundSlowD_zero` |
| The displayed eigenvalue is the smaller branch | `backgroundMatrix_characteristic_factor`, `backgroundSlowLambda_lt_fast` |
| `Bn=lambda n`, `norm n=1` | `backgroundSlowDirection_eigen`, `backgroundSlowDirection_norm` |
| `a^3=1+eps`, `l^3=D0/d` | `backgroundRadius_cube`, `backgroundSlowLength_cube` |
| `d*l=D0*l^(-2)` | `backgroundSlow_scaling` |
| Smooth dependence on signed small `eps` | `backgroundRadius_contDiffAt`, `backgroundSlowD_contDiffAt`, `backgroundSlowK_contDiffAt`, `backgroundSlowLength_contDiffAt`, `backgroundAngularScale_contDiffAt`, `backgroundSlowDirection_contDiffAt` |
| `eq:scalar-slow` implies the actual `eq:vector-slow` | `backgroundScalarLift_vector_balance` |
| `b` converts tangential to angular displacement | `backgroundSlow_polar_displacement` |
| Weighted center remains zero after the lift | `backgroundScalarLift_weighted_center` |

The exact definitions are `backgroundE0`, `backgroundW0`,
`backgroundProbeCenter`, `backgroundExterior`, `backgroundProbeField`,
`backgroundOperator`, `backgroundSlowDirection`, and `backgroundScalarLift`.
The sign is specified by `tau=1 or tau=-1`. The slow direction and its
smoothness are proved on the actual signed open set `abs eps < 1/4`.
The denominator and discriminant facts are proved; they are not extra
unverified hypotheses.

The vector balance uses the actual `newtonTargetField` for every mutual
interaction and the actual Fréchet derivative of the probe field. It
retains zero scalar weights and requires no weight-positivity assumption.
Distinct scalar positions remain distinct under the lift by
`backgroundScalarLift_injective`.

These modules do not assert that a candidate solves the seven Triple or
Nested chart rows. Those equalities must be proved in the corresponding
chart modules before local IFT uniqueness can establish exact boundary
collinearity. The global connection property and global main theorem are
not completed by these background calculations.

`Audit/BackgroundSlow.lean` records `#print axioms` for the principal
theorems. Strict compilation uses `-DwarningAsError=true`.
