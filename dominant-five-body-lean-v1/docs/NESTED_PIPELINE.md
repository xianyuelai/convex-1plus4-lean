# Actual nested continuation and sequence capture

This development concerns the supplied manuscript's nested three-satellite
chart. It does not assert the unconditional global five-body main theorem.

## Implemented links

- `NestedUnitBoundary` proves the actual seven-row roots at all four signed
  unit seeds, for every alpha, from the explicit outer and inner cube scales.
- `NestedJacobian` proves invertibility of the actual derivative at those
  seeds and relates the positive-scale chart derivative to the original
  physical six-dimensional shape Hessian. Its proof eliminates successive
  kernel coordinates; it does not substitute a prescribed Jacobian matrix.
- `NestedContinuation` applies the compact implicit-function theorem in
  independent epsilon, outer scale, inner fraction scale, and alpha. The
  basic root radius and inverse bound are common over alpha in [0,1].
- `NestedAreaPositivity` evaluates all six exterior divided areas and all
  three primary/exterior/cluster triangles in the actual coordinates.
  Outer edges retain the sign of the outer seed; the inner edge is positive.
- `NestedInternalAreaPositivity` differentiates the full implicit root.
  Its source coefficient at the simultaneous scale boundary is z Z^2 / 2.
  The interval integral gives the exact positive cubic area factor.
- `NestedConvexity` verifies the ten triangle signs for all four actual
  original-label hull orders. `NestedConvexContinuation` instantiates the
  zero-face input using the proved actual slow candidate and root uniqueness
  from `NestedCollinearity`.
- `NestedPhysicalCoordinates` gives the exact two current-mass cube-root
  scales, the current inner fraction, and the two-level weighted-coordinate
  inverse. It derives chart regularity and all seven extended equations
  from collision-free normalized physical solutions.
- `NestedSequenceCapture` captures a whole tail in one actual smooth chart
  after extracting alpha convergence from its compact interval. The original
  alpha sequence may oscillate. A common positive epsilon interval retains
  each current positive pair of scales and its current mass fraction.
- `FixedLabelEndpoint` obtains the angular sorting from strict convexity and
  an actual open-semicircle width, then identifies the coorbital endpoint in
  any chosen original-label angle-zero gauge.
- `NestedConnection` converts the nested captured data to the actual Section
  7 `CapturedBranches` structure with physical roots, the original Hessian,
  and an exact fixed-current-mass coorbital endpoint in label-3 gauge.
- `SliceConnection` proves literal local continuation uniqueness in the actual
  seven-dimensional first-angle slice from its actual derivative and IFT.
  Its positive-epsilon root predicate includes strict physical convexity.
- `PolarGaugeTransport` reindexes the masses and labels together and proves
  the exact orientation-preserving rotation to the standard hull/first-angle
  slice. Actual normalized Newton equations, the original shape Hessian,
  and the fixed-current-mass endpoint are transported by proved identities.
- `NestedSliceConnection` converts nested captured branches to the final
  ordered-slice `CapturedBranches` interface. The conversion takes positive
  current outer and inner scales and positive current masses explicitly.
- `CollisionTripleNestedWidth` derives all actual radial differences divided
  by the lower triple diameter tending to zero, and angular width divided
  by diameter tending to one, from an actual smaller pair. Its upper
  reflection counterpart is `CollisionUpperNestedWidth`.
- `CollisionTripleNestedMacro` combines those actual first-order limits with
  the signed directions from `CollisionNestedDirections` and the actual
  current-mass averaged angular equation. The total cluster mass divided
  by the actual diameter cubed tends to 9/4; no individual mass fraction
  convergence is assumed.
- `ReflectionHessianTransport` proves the original physical shape Hessian
  transport under reflection. The rotation orthogonality row changes sign,
  which preserves its zero equation.
- `OrderedSliceReflection` proves the continuous first-angle reflection
  involution, transports actual roots, their original shape Hessians and
  the fixed-current-mass coorbital endpoints, and returns mirrored captured
  branches to the exact original ordered coordinates and mass vector.
- `OrderedSliceMirrorCapture` derives the actual mirrored mass, angle and
  relative-position limits. A complete upper triple becomes a complete
  lower triple at the unit first satellite.
- `OrderedSliceUpperTripleCapture` applies the complete actual lower-triple
  capture theorem to that mirrored sequence and returns its branches to
  the exact original sequence, without a scale or mass-share hypothesis.
- `CollisionTripleCompleteUpper` transports the entire-sequence lower
  geometry and positive cubic mass lower bound to arbitrary complete upper
  triples, without a comparability or smaller-pair input.

## Scope that remains explicit

The basic `NestedSequenceCapture` entry point retains its explicit scaled
coordinate-limit hypotheses. The subsequent actual-scale and inverse-limit
modules are a separate layer: they derive these inputs for an actual smaller
pair in a complete triple before applying the chart. The convex continuation
neighborhood is local about a fixed limiting alpha; compactness of alpha is
used to extract a strictly increasing subsequence before capture. It is not
reported as a uniform convex neighborhood over every alpha anchor. The final
whole-project theorem and ledger status are recorded by the root integration
pass, rather than inferred from this local pipeline document.

The fixed positive-mass epsilon-zero endpoint is distinct from the
simultaneous colliding scale boundary used to construct the chart. Relabeling
is used only to sort and transport equations; `OrientedSimilar` is unchanged.

The exact printed determinant 2187 D0^3 and the full off-diagonal angular
boundary matrix are not claimed in these modules. Actual boundary derivative
invertibility is proved by kernel elimination with the diagonal coefficients.

## Verification

The proof modules are checked with Lean 4.33.1 and the locked mathlib revision,
using `-DwarningAsError=true`. The theorem axiom audit is
`Audit/NestedPipeline.lean`; its saved output is
`docs/nested-pipeline-axioms-audit.log`. The global project audit remains the
responsibility of the root integration pass.

The actual ordered-slice bridge is separately audited in
`Audit/OrderedSlicePipeline.lean`; its saved output is
`docs/ordered-slice-pipeline-axioms-audit.log`.
All thirteen audited declarations passed the strict check and depend only
on `propext`, `Classical.choice`, and `Quot.sound`.

`Audit/ActualScaleTransport.lean` checks the actual cubic lower bound,
nested radial/width and macro limits, physical reflection Hessian transport,
the complete first-angle mirror branch transport and its actual sequence
limits, and the pair/triple/nested original-slice restoration. Its first
28-declaration strict audit is saved as
`docs/actual-scale-transport-axioms-audit.log`; all declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.
