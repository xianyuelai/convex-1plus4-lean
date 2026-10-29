# Verified actual chart bridges

## Equilateral triple exterior rows

`DominantFiveBody/TripleSlowExterior.lean` identifies the actual zero-scale
Newton diagonal and all exterior rows on the equilateral background:

- `tripleSlow_newton_difference` is the genuine derivative of the actual
  exterior Newton field, evaluated on the actual chart displacement.
- `tripleRadialExteriorDifference_background` identifies the radial
  exterior difference with the radial projection of `backgroundOperator`.
- `tripleAngularExteriorDifference_background` identifies epsilon times
  the angular exterior difference with the projection on the actual
  rotated probe position. This identity also includes epsilon zero.
- `tripleRadialMean_background_zero`,
  `tripleAngularMean_background_zero`, and
  `tripleExteriorRadialRow_background_zero` prove the actual mean and
  exterior radial rows vanish. Zero cluster weights remain in the rows.

The hypotheses are the actual equilateral coordinates
`y 0 = y 1 = backgroundRadius eps`, `y 4 = tau * Coorbital.h`,
`0 < 1+eps`, and `tau=1 or tau=-1`. No unknown candidate-root equality
is assumed.

## Nested derivative versus physical shape Hessian

`DominantFiveBody/NestedHessian.lean` uses the true seven coordinate and
row transforms. The raw fixed-angle order is
`(r_p,r_b,r_c,r_a,theta_b,theta_c,theta_a)`.
`nestedToFixedSlice` and `nestedFromFixedSlice` are explicit continuous
linear maps and are proved inverse in both directions for `t*eta != 0`.
The formulas retain alpha endpoints and never divide by a mass fraction.

The actual extension agrees with the transformed physical equations on
an open regular chart. The derivative equality is therefore obtained
from equality in a neighborhood and the chain rule, rather than from
an unproved equality of formal matrices.

`nestedChartDerivative_isInvertible_iff_shape` proves the actual
Fréchet derivative is invertible if and only if the original physical
six-dimensional shape Hessian is nondegenerate. It requires positive
epsilon, t and eta; actual positive mass ratios; a regular chart;
positive physical radii; and an actual root. The centered configuration
and mass labels are exactly the original physical ones.

`Audit/ChartBridges.lean` audits the principal theorems with
`#print axioms`; strict compilation uses `-DwarningAsError=true`.
