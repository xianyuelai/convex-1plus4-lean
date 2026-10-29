import DominantFiveBody.CoorbitalCovering
import DominantFiveBody.Probe
import DominantFiveBody.BoundaryJacobian
import DominantFiveBody.RelativeMassMetric
import DominantFiveBody.CollisionPairScales
import DominantFiveBody.PairActualCapture
import DominantFiveBody.CollisionNestedScales
import DominantFiveBody.CollisionNestedGeometry
import DominantFiveBody.SingleScaleKernel
import DominantFiveBody.CompactImplicit
open scoped BigOperators ContDiff Matrix.Norms.Operator

-- kernel.collision_blowup
example : Filter.Tendsto
  (fun t : ℝ => t * DominantFiveBody.Coorbital.kernelF t)
  (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := @DominantFiveBody.kernelF_angle_mul_tendsto_atTop
#print axioms DominantFiveBody.kernelF_angle_mul_tendsto_atTop

-- lem:cycle
example : ∀ (n : ℕ) (_hn₂ : 2 ≤ n) (_hn₄ : n ≤ 4) (mass theta : Fin n → ℝ),
  (∀ i, 0 < mass i) → DominantFiveBody.OrderedSemicircle theta →
  (∀ i, DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
  (∀ i j, i < j → 0 < DominantFiveBody.Coorbital.positiveRemainder (theta j-theta i)) ∧
  (∀ u, DominantFiveBody.angularChordHessian mass theta u u =
      DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u ∧
    DominantFiveBody.Coorbital.coorbitalRemainderForm mass theta u ≤
      DominantFiveBody.angularChordHessian mass theta u u) ∧
  (∀ u, (∀ v, DominantFiveBody.angularChordHessian mass theta u v = 0) ↔
    ∀ i j, u i = u j) := @DominantFiveBody.angular_hessian_estimate
#print axioms DominantFiveBody.angular_hessian_estimate

-- eq:cycle-bound
example : ∀ (n : ℕ) (_hn₂ : 2 ≤ n) (_hn₄ : n ≤ 4)
  (mass theta u : Fin n → ℝ), (∀ i, 0 < mass i) →
  (∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi) →
  (∀ i, DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
  DominantFiveBody.Coorbital.coorbitalRemainderForm mass theta u ≤
    DominantFiveBody.Coorbital.coorbitalKappaForm mass theta u := @DominantFiveBody.Coorbital.coorbital_cycle_bound
#print axioms DominantFiveBody.Coorbital.coorbital_cycle_bound

-- thm:coorbital
example : 
  (∀ m : DominantFiveBody.MassRatio, DominantFiveBody.PositiveRatio m →
    ∃! theta : DominantFiveBody.Satellite → ℝ, DominantFiveBody.CoorbitalAngleDomain theta ∧
      ∀ i, DominantFiveBody.coorbitalResidual m theta i = 0) ∧
  ContDiffOn ℝ ∞ DominantFiveBody.coorbitalRootAngles {m | DominantFiveBody.PositiveRatio m} ∧
  (∀ m : DominantFiveBody.MassRatio, DominantFiveBody.PositiveRatio m →
    ∀ u : DominantFiveBody.Satellite → ℝ, u 0 = 0 → u ≠ 0 →
    0 < DominantFiveBody.coorbitalPhysicalHessian m (DominantFiveBody.coorbitalRootAngles m) u u) ∧
  IsProperMap DominantFiveBody.coorbitalMassProjection ∧
  IsCoveringMapOn DominantFiveBody.coorbitalMassProjection Set.univ := @DominantFiveBody.coorbital_global_complete
#print axioms DominantFiveBody.coorbital_global_complete

-- display:164
example : ∀
  (mass theta : DominantFiveBody.Satellite → ℝ), DominantFiveBody.OrderedSemicircle theta →
  (∀ i, DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
  DominantFiveBody.coorbitalVirial mass theta = 0 := @DominantFiveBody.coorbitalVirial_zero
#print axioms DominantFiveBody.coorbitalVirial_zero

-- thm:coorbital.mass_floor_collision_exclusion
example : ∀ (alpha : ℝ), 0 < alpha →
  ∃ d : ℝ, 0 < d ∧ ∀ mass theta : DominantFiveBody.Satellite → ℝ,
  DominantFiveBody.PositiveRatio mass → (∀ i, alpha ≤ mass i) →
  DominantFiveBody.OrderedSemicircle theta →
  (∀ i, DominantFiveBody.Coorbital.angularEquation mass theta i = 0) →
  ∀ i j, i < j → d ≤ theta j-theta i := @DominantFiveBody.coorbital_roots_uniform_pair_separation
#print axioms DominantFiveBody.coorbital_roots_uniform_pair_separation

-- thm:coorbital.actual_projection_proper
example : IsProperMap
  DominantFiveBody.coorbitalMassProjection := @DominantFiveBody.coorbitalMassProjection_isProperMap
#print axioms DominantFiveBody.coorbitalMassProjection_isProperMap

-- thm:coorbital.equal_mass_chamber_seed
example : ∃! theta : DominantFiveBody.Satellite → ℝ,
  DominantFiveBody.CoorbitalAngleDomain theta ∧
    ∀ i, DominantFiveBody.coorbitalResidual DominantFiveBody.equalMassRatio theta i = 0 := @DominantFiveBody.equalMass_coorbital_existsUnique
#print axioms DominantFiveBody.equalMass_coorbital_existsUnique

-- lem:probe
example : ∀ (p q x : ℝ), 0 ≤ p → 0 ≤ q → p+q = 1 → x ≠ 0 →
  x ≠ DominantFiveBody.Coorbital.h → DominantFiveBody.twoSourceSpan x < Real.pi →
  p * DominantFiveBody.coorbitalKernel x +
    q * DominantFiveBody.coorbitalKernel (x-DominantFiveBody.Coorbital.h) = 0 →
  0 < p * DominantFiveBody.Coorbital.kappa |x| +
    q * DominantFiveBody.Coorbital.kappa |x-DominantFiveBody.Coorbital.h| := @DominantFiveBody.twoSourceProbe
#print axioms DominantFiveBody.twoSourceProbe

-- display:181
example : ∀ (p q x : ℝ), 0 ≤ p → 0 ≤ q → p+q = 1 → x ≠ 0 →
  x ≠ DominantFiveBody.Coorbital.h → DominantFiveBody.twoSourceSpan x < Real.pi →
  p * DominantFiveBody.coorbitalKernel x +
    q * DominantFiveBody.coorbitalKernel (x-DominantFiveBody.Coorbital.h) = 0 →
  0 < p * DominantFiveBody.Coorbital.kappa |x| +
    q * DominantFiveBody.Coorbital.kappa |x-DominantFiveBody.Coorbital.h| := @DominantFiveBody.twoSourceProbe
#print axioms DominantFiveBody.twoSourceProbe

-- prop:closed
example : 
  (∀ mass theta : DominantFiveBody.Satellite → ℝ,
    (∀ i, 0 ≤ mass i) → (∑ i, mass i) = 1 →
    DominantFiveBody.SeparatedSemicircle theta →
    (∀ i, DominantFiveBody.coorbitalResidual mass theta i = 0) →
    HasFDerivAt (fun angles i => DominantFiveBody.coorbitalResidual mass angles i)
      (DominantFiveBody.angularDifferential mass theta) theta ∧
    (∀ u, DominantFiveBody.angularDifferential mass theta u = 0 ↔ ∀ i j, u i = u j) ∧
    (∀ p q, 0 < mass p → IsUnit (DominantFiveBody.deletedAngularJacobian mass theta p q))) ∧
  (∀ (K : Set ((DominantFiveBody.Satellite → ℝ) × (DominantFiveBody.Satellite → ℝ)))
    (delta eta : ℝ) (p q : DominantFiveBody.Satellite), IsClosed K → 0 < delta → 0 < eta →
    (∀ z ∈ K, (∀ i, 0 ≤ z.1 i) ∧ (∑ i, z.1 i) = 1 ∧ z.2 0 = 0 ∧
      (∀ i : Fin 3, delta ≤ z.2 i.succ - z.2 i.castSucc) ∧
      z.2 3 - z.2 0 ≤ Real.pi - eta ∧ (1 / 4 : ℝ) ≤ z.1 p ∧
      (∀ i, DominantFiveBody.coorbitalResidual z.1 z.2 i = 0)) →
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ‖(DominantFiveBody.deletedAngularJacobian z.1 z.2 p q)⁻¹‖ ≤ C) := @DominantFiveBody.coorbital_closed_mass_jacobian_complete
#print axioms DominantFiveBody.coorbital_closed_mass_jacobian_complete

-- eq:action
example : ∀
  (eps : ℝ) (mu : DominantFiveBody.MassRatio), (∑ i, mu i) = 1 → eps ≠ 0 → 1+eps ≠ 0 →
  ∀ (q : DominantFiveBody.SatelliteConfiguration), DominantFiveBody.relativeAction eps mu q =
  DominantFiveBody.augmentedPotential (DominantFiveBody.masses eps mu) 1
    (DominantFiveBody.centeredFromRelative eps mu q) / eps := @DominantFiveBody.relativeAction_eq_augmentedPotential_div
#print axioms DominantFiveBody.relativeAction_eq_augmentedPotential_div

-- eq:action.inertia_reduction
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),
  (∑ i, mu i) = 1 → 1+eps ≠ 0 → ∀ (q : DominantFiveBody.SatelliteConfiguration),
  DominantFiveBody.inertia (DominantFiveBody.masses eps mu)
    (DominantFiveBody.centeredFromRelative eps mu q) =
  eps * (∑ i, mu i * ‖q i‖^2) - eps^2/(1+eps) * ‖DominantFiveBody.relativeAverage mu q‖^2 := @DominantFiveBody.inertia_centeredFromRelative
#print axioms DominantFiveBody.inertia_centeredFromRelative

-- eq:action.mass_metric_positive
example : ∀ (eps : ℝ)
  (mu : DominantFiveBody.Satellite → ℝ), -1 < eps → (∀ i, 0 < mu i) →
  (∑ i, mu i) = 1 → (DominantFiveBody.relativeMassMatrix eps mu).PosDef := @DominantFiveBody.relativeMassMatrix_posDef
#print axioms DominantFiveBody.relativeMassMatrix_posDef

-- eq:action.actual_critical_equivalence
example : ∀ (eps : ℝ)
  (mu : DominantFiveBody.MassRatio), -1 < eps → DominantFiveBody.PositiveRatio mu →
  ∀ (q : DominantFiveBody.SatelliteConfiguration), DominantFiveBody.RelativeCollisionFree q →
  (fderiv ℝ (DominantFiveBody.relativeAction eps mu) q = 0 ↔
    (∀ i, DominantFiveBody.vectorResidual eps mu q i = 0)) := @DominantFiveBody.relativeAction_critical_iff_vectorRoot
#print axioms DominantFiveBody.relativeAction_critical_iff_vectorRoot

-- lem:hessian.actual_fixed_slice_bridge
example : ∀
  (p : DominantFiveBody.ContinuationParameter) (y : DominantFiveBody.SliceCoordinates),
  DominantFiveBody.SliceRegular p y → 0 < p.1 → DominantFiveBody.PositiveRatio p.2 →
  DominantFiveBody.reducedResidual p y = 0 →
  ((DominantFiveBody.reducedJacobian p y).IsInvertible ↔
    DominantFiveBody.ShapeHessianNondegenerate (DominantFiveBody.masses p.1 p.2) 1
      (DominantFiveBody.slicePhysicalConfiguration p y)) := @DominantFiveBody.reducedJacobian_isInvertible_iff_shape
#print axioms DominantFiveBody.reducedJacobian_isInvertible_iff_shape

-- lem:product
example : ∀
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] {n : ℕ}
  (F : P → DominantFiveBody.CompactImplicit.Unknown n → DominantFiveBody.CompactImplicit.Unknown n)
  (D K : Set (P × DominantFiveBody.CompactImplicit.Unknown n)),
  IsOpen D → ContDiffOn ℝ ∞ (Function.uncurry F) D → IsCompact K →
  (∀ a ∈ K, a ∈ D ∧ F a.1 a.2 = 0 ∧
    (DominantFiveBody.CompactImplicit.jacobian F a.1 a.2).IsInvertible) →
  ∀ tau : ℝ, 0 < tau → ∃ eta r C : ℝ, 0 < eta ∧ 0 < r ∧ 0 < C ∧ r ≤ tau ∧ eta ≤ r ∧
    ∀ a ∈ K, ∃ psi : P → DominantFiveBody.CompactImplicit.Unknown n,
      psi a.1 = a.2 ∧ ContDiffOn ℝ ∞ psi (Metric.ball a.1 eta) ∧
      ∀ q, dist q a.1 < eta → dist (psi q) a.2 < r/2 ∧ (q,psi q) ∈ D ∧
        (DominantFiveBody.CompactImplicit.jacobian F q (psi q)).IsInvertible ∧
        ‖(DominantFiveBody.CompactImplicit.jacobian F q (psi q)).inverse‖ ≤ C ∧ F q (psi q) = 0 ∧
        (∀ z, dist z a.2 < r → (F q z = 0 ↔ psi q = z)) := @DominantFiveBody.CompactImplicit.compact_product
#print axioms DominantFiveBody.CompactImplicit.compact_product

-- prop:uniform
example : (∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio),0<eps → DominantFiveBody.PositiveRatio mu → ∀ x : DominantFiveBody.Configuration,
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
      Metric.diam (Set.range x)≤4*Real.rpow (1+eps) (1/3)) ∧
    (∀ E : ℝ,0<E → ∃ b : ℝ,0<b ∧ ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
      0<eps → eps≤E → DominantFiveBody.PositiveRatio mu →
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
      ∀ i : DominantFiveBody.Satellite,b≤‖DominantFiveBody.satellitesRelative x i‖) ∧
    (∀ eta : ℝ,0<eta → ∃ delta : ℝ,0<delta ∧
      ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
      0<eps → eps<delta → DominantFiveBody.PositiveRatio mu →
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
      ∀ i : DominantFiveBody.Satellite,|‖DominantFiveBody.satellitesRelative x i‖-1|<eta) ∧
    (∃ (eta eps0 : ℝ),0<eta ∧ 0<eps0 ∧
      ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder) (x : DominantFiveBody.Configuration),
      0<eps → eps<eps0 → DominantFiveBody.PositiveRatio mu →
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x → DominantFiveBody.StrictConvexInOrder sigma x →
      ∃ (r theta : DominantFiveBody.Satellite → ℝ) (phi : ℝ),
        (∀ i,0<r i) ∧ theta 0=0 ∧
        (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
        (∀ i,x (sigma.labels i.succ)-x 0=DominantFiveBody.polarPoint (r i) (theta i+phi)) ∧
        (∀ i,DominantFiveBody.angularResidual eps (mu ∘ DominantFiveBody.hullSatellitePermutation sigma) r theta i=0) ∧
        eta≤theta 3 ∧ theta 3≤Real.pi-eta) ∧
    (∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (sigma : ℕ → DominantFiveBody.HullOrder)
      (x : ℕ → DominantFiveBody.Configuration) (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (phi : ℕ → ℝ),
      (∀ n,0<eps n) → Filter.Tendsto eps Filter.atTop (nhds 0) →
      (∀ n,DominantFiveBody.PositiveRatio (mu n)) →
      (∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
      (∀ n,∀ i,0<r n i) → (∀ n,theta n 0=0) →
      (∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi) →
      (∀ n,∀ i,x n ((sigma n).labels i.succ)-x n 0=
        DominantFiveBody.polarPoint (r n i) (theta n i+phi n)) →
      ∀ k : Fin 3,Filter.limsup (fun n => theta n k.succ-theta n k.castSucc) Filter.atTop≤Real.pi/3) := @DominantFiveBody.dominant_uniform_geometry_complete
#print axioms DominantFiveBody.dominant_uniform_geometry_complete

-- prop:uniform.diameter
example : ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio),
  0 < ε → DominantFiveBody.PositiveRatio μ → ∀ (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses ε μ) x →
  Metric.diam (Set.range x) ≤ 4 * Real.rpow (1 + ε) (1 / 3) := @DominantFiveBody.dominant_normalized_diameter_le
#print axioms DominantFiveBody.dominant_normalized_diameter_le

-- prop:uniform.lower_radius
example : ∀ (E : ℝ), 0 < E →
  ∃ b : ℝ, 0 < b ∧ ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
  0 < ε → ε ≤ E → DominantFiveBody.PositiveRatio μ →
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses ε μ) x →
  ∀ i : DominantFiveBody.Satellite, b ≤ ‖DominantFiveBody.satellitesRelative x i‖ := @DominantFiveBody.dominant_primary_relative_radius_lower
#print axioms DominantFiveBody.dominant_primary_relative_radius_lower

-- prop:uniform.uniform_radius_to_one
example : ∀ (η : ℝ), 0 < η →
  ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (μ : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration),
  0 < ε → ε < δ → DominantFiveBody.PositiveRatio μ →
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses ε μ) x →
  ∀ i : DominantFiveBody.Satellite, |‖DominantFiveBody.satellitesRelative x i‖-1| < η := @DominantFiveBody.dominant_primary_relative_radii_uniform
#print axioms DominantFiveBody.dominant_primary_relative_radii_uniform

-- eq:span
example : ∃ (eta eps0 : ℝ),0<eta ∧ 0<eps0 ∧
      ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder) (x : DominantFiveBody.Configuration),
      0<eps → eps<eps0 → DominantFiveBody.PositiveRatio mu →
      DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x → DominantFiveBody.StrictConvexInOrder sigma x →
      ∃ (r theta : DominantFiveBody.Satellite → ℝ) (phi : ℝ),
        (∀ i,0<r i) ∧ theta 0=0 ∧
        (∀ i j,i<j → 0<theta j-theta i ∧ theta j-theta i<Real.pi) ∧
        (∀ i,x (sigma.labels i.succ)-x 0=DominantFiveBody.polarPoint (r i) (theta i+phi)) ∧
        (∀ i,DominantFiveBody.angularResidual eps (mu ∘ DominantFiveBody.hullSatellitePermutation sigma) r theta i=0) ∧
        eta≤theta 3 ∧ theta 3≤Real.pi-eta := @DominantFiveBody.dominant_strictConvex_uniform_polar_span
#print axioms DominantFiveBody.dominant_strictConvex_uniform_polar_span

-- prop:uniform.actual_sequence_gap_limsup
example : ∀ (eps : ℕ → ℝ)
  (mu : ℕ → DominantFiveBody.MassRatio) (sigma : ℕ → DominantFiveBody.HullOrder)
  (x : ℕ → DominantFiveBody.Configuration)
  (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (phi : ℕ → ℝ),
  (∀ n, 0 < eps n) → Filter.Tendsto eps Filter.atTop (nhds 0) →
  (∀ n, DominantFiveBody.PositiveRatio (mu n)) →
  (∀ n, DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n)) →
  (∀ n, ∀ i, 0 < r n i) → (∀ n, theta n 0 = 0) →
  (∀ n, ∀ i j, i < j → 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  (∀ n, ∀ i, x n ((sigma n).labels i.succ)-x n 0 =
    DominantFiveBody.polarPoint (r n i) (theta n i+phi n)) →
  ∀ k : Fin 3, Filter.limsup (fun n => theta n k.succ-theta n k.castSucc) Filter.atTop ≤ Real.pi/3 := @DominantFiveBody.dominant_ordered_polar_gap_limsup
#print axioms DominantFiveBody.dominant_ordered_polar_gap_limsup

-- prop:uniform.current_cluster_force_cancellation
example : ∀ (m : DominantFiveBody.MassVector)
  (x : DominantFiveBody.Configuration) (S : Finset DominantFiveBody.Label),
  (∑ i ∈ S, ∑ j ∈ S, DominantFiveBody.pairForce m x i j) = 0 := @DominantFiveBody.cluster_internal_force_zero
#print axioms DominantFiveBody.cluster_internal_force_zero

-- prop:uniform.exact_cluster_virial
example : ∀ (m : DominantFiveBody.MassVector),
  DominantFiveBody.PositiveMasses m → ∀ (x : DominantFiveBody.Configuration),
  DominantFiveBody.NormalizedCentralConfiguration m x → ∀ (S : Finset DominantFiveBody.Label),
  S.Nonempty → ∀ (Acenter : DominantFiveBody.Plane),
  DominantFiveBody.clusterPotential m x S = DominantFiveBody.clusterInertia m x S +
  ∑ i ∈ S, m i * inner ℝ (x i-DominantFiveBody.clusterCenter m x S)
    (DominantFiveBody.exteriorAcceleration m x S i-Acenter) := @DominantFiveBody.normalized_cluster_virial
#print axioms DominantFiveBody.normalized_cluster_virial

-- eq:full-cut
example : ∀ (ε : ℝ)
  (μ r theta : DominantFiveBody.Satellite → ℝ),
  (∀ i, DominantFiveBody.angularResidual ε μ r theta i = 0) →
  ∀ (S : Finset DominantFiveBody.Satellite),
  (∑ i ∈ S, ∑ j ∈ Sᶜ, DominantFiveBody.fullAngularPair ε μ r theta i j) = 0 := @DominantFiveBody.full_angular_cut
#print axioms DominantFiveBody.full_angular_cut

-- prop:uniform.actual_ordered_polar_bridge
example : ∀ (eps : ℝ)
  (mu : DominantFiveBody.MassRatio) (sigma : DominantFiveBody.HullOrder)
  (x : DominantFiveBody.Configuration), 0 < eps → DominantFiveBody.PositiveRatio mu →
  DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x →
  DominantFiveBody.StrictConvexInOrder sigma x →
  ∃ (r theta : DominantFiveBody.Satellite → ℝ) (phi : ℝ),
    (∀ i, 0 < r i) ∧ theta 0 = 0 ∧
    (∀ i j, i < j → 0 < theta j-theta i ∧ theta j-theta i < Real.pi) ∧
    (∀ i, x (sigma.labels i.succ)-x 0 = DominantFiveBody.polarPoint (r i) (theta i+phi)) ∧
    (∀ i, DominantFiveBody.angularResidual eps
      (mu ∘ DominantFiveBody.hullSatellitePermutation sigma) r theta i = 0) := @DominantFiveBody.normalized_strictConvex_ordered_angular_rep
#print axioms DominantFiveBody.normalized_strictConvex_ordered_angular_rep

-- prop:uniform.selected_consecutive_gap_limit
example : ∀ (eps : ℕ → ℝ),
  (∀ n, 0 < eps n) → Filter.Tendsto eps Filter.atTop (nhds 0) →
  ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
  (∀ n i, 0 < mu n i) → (∀ n i, 0 < r n i) →
  (∀ n i, DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = 0) →
  (∀ n, ∀ i j, i < j → 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  ∀ (rLimit thetaLimit : DominantFiveBody.Satellite → ℝ), (∀ i, rLimit i = 1) →
  Filter.Tendsto r Filter.atTop (nhds rLimit) →
  Filter.Tendsto theta Filter.atTop (nhds thetaLimit) →
  ∀ k : Fin 3, thetaLimit k.succ-thetaLimit k.castSucc ≤ Real.pi/3 := @DominantFiveBody.ordered_full_angular_limit_consecutive_gap_le
#print axioms DominantFiveBody.ordered_full_angular_limit_consecutive_gap_le

-- prop:uniform.selected_cut_gap_limit
example : ∀ (eps : ℕ → ℝ),
  (∀ n, 0 < eps n) → Filter.Tendsto eps Filter.atTop (nhds 0) →
  ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
  (∀ n i, 0 < mu n i) → (∀ n i, 0 < r n i) →
  (∀ n i, DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = 0) →
  ∀ (rLimit thetaLimit : DominantFiveBody.Satellite → ℝ), (∀ i, rLimit i = 1) →
  Filter.Tendsto r Filter.atTop (nhds rLimit) →
  Filter.Tendsto theta Filter.atTop (nhds thetaLimit) →
  ∀ (S : Finset DominantFiveBody.Satellite), S.Nonempty → Sᶜ.Nonempty →
  (∀ n, ∀ i ∈ S, ∀ j ∈ Sᶜ, 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  ∀ (g : ℝ), (∀ i ∈ S, ∀ j ∈ Sᶜ, g ≤ thetaLimit j-thetaLimit i) → g ≤ Real.pi/3 := @DominantFiveBody.full_angular_cut_limit_gap_le
#print axioms DominantFiveBody.full_angular_cut_limit_gap_le

-- prop:uniform.selected_limit_span_pi_exclusion
example : ∀ (eps : ℕ → ℝ),
  (∀ n, 0 < eps n) → Filter.Tendsto eps Filter.atTop (nhds 0) →
  ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
  (∀ n i, 0 < mu n i) → (∀ n, ∑ i, mu n i = 1) → (∀ n i, 0 < r n i) →
  (∀ n i, DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = 0) →
  (∀ n, ∀ i j, i < j → 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  ∀ (muLimit rLimit thetaLimit : DominantFiveBody.Satellite → ℝ), (∀ i, rLimit i = 1) →
  Filter.Tendsto mu Filter.atTop (nhds muLimit) →
  Filter.Tendsto r Filter.atTop (nhds rLimit) →
  Filter.Tendsto theta Filter.atTop (nhds thetaLimit) → thetaLimit 3-thetaLimit 0 < Real.pi := @DominantFiveBody.ordered_full_angular_limit_span_lt_pi
#print axioms DominantFiveBody.ordered_full_angular_limit_span_lt_pi

-- prop:uniform.selected_limit_span_zero_exclusion
example : ∀ (eps : ℕ → ℝ),
  (∀ n, 0 < eps n) → ∀ (mu r theta : ℕ → DominantFiveBody.Satellite → ℝ),
  (∀ n i, 0 < mu n i) → (∀ n i, 0 < r n i) →
  (∀ n i, DominantFiveBody.angularResidual (eps n) (mu n) (r n) (theta n) i = 0) →
  (∀ n, ∀ i j, i < j → 0 < theta n j-theta n i ∧ theta n j-theta n i < Real.pi) →
  ∀ (rLimit thetaLimit : DominantFiveBody.Satellite → ℝ), (∀ i, rLimit i = 1) →
  Filter.Tendsto r Filter.atTop (nhds rLimit) →
  Filter.Tendsto theta Filter.atTop (nhds thetaLimit) → 0 < thetaLimit 3-thetaLimit 0 := @DominantFiveBody.ordered_full_angular_limit_span_pos
#print axioms DominantFiveBody.ordered_full_angular_limit_span_pos

-- eq:distance
example : ∀ (r s a b : ℝ),
  ‖DominantFiveBody.polarPoint s b-DominantFiveBody.polarPoint r a‖^2 =
    (s-r)^2+4*r*s*Real.sin ((b-a)/2)^2 := @DominantFiveBody.polar_distance_sq
#print axioms DominantFiveBody.polar_distance_sq

-- prop:pair-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (_hconv : ∀ n,DominantFiveBody.StrictConvexInOrder ⟨Equiv.refl DominantFiveBody.Label,rfl⟩ (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a<b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0))
    (u w : DominantFiveBody.Satellite) (_huw : u<w)
    (_hu : u∈DominantFiveBody.pairExteriorLabels a b) (_hw : w∈DominantFiveBody.pairExteriorLabels a b),
b.val=a.val+1 ∧
    Filter.Tendsto (fun n => mu n a+mu n b) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => (theta n b-theta n a)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b)
      Filter.atTop (nhds 1) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in Filter.atTop,|r n b-r n a|≤
      C*eps n*(1-(mu n a+mu n b))*DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b) ∧
    qLimit u≠qLimit w ∧ theta0 w-theta0 u=DominantFiveBody.Coorbital.h ∧
    0≤muLimit u ∧ muLimit u≤1 ∧
    muLimit u*DominantFiveBody.coorbitalKernel (theta0 a-theta0 u)+
      (1-muLimit u)*DominantFiveBody.coorbitalKernel ((theta0 a-theta0 u)-DominantFiveBody.Coorbital.h)=0 ∧
    0<muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
      (1-muLimit u)*DominantFiveBody.Coorbital.kappa |(theta0 a-theta0 u)-DominantFiveBody.Coorbital.h| ∧
    Filter.Tendsto (fun n => (mu n a+mu n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b^3)
      Filter.atTop (nhds (muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
        (1-muLimit u)*DominantFiveBody.Coorbital.kappa |(theta0 a-theta0 u)-DominantFiveBody.Coorbital.h|)) ∧
    (∀ (u' w' : DominantFiveBody.Satellite),u'<w' → ∀ d : DominantFiveBody.Plane,c≠d →
      DominantFiveBody.CompleteLimitingSatellitePair qLimit u' w' d → False) := @DominantFiveBody.normalized_complete_pair_scale_complete
#print axioms DominantFiveBody.normalized_complete_pair_scale_complete

-- eq:pair-scale
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (_hconv : ∀ n,DominantFiveBody.StrictConvexInOrder ⟨Equiv.refl DominantFiveBody.Label,rfl⟩ (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a<b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0))
    (u w : DominantFiveBody.Satellite) (_huw : u<w)
    (_hu : u∈DominantFiveBody.pairExteriorLabels a b) (_hw : w∈DominantFiveBody.pairExteriorLabels a b),
b.val=a.val+1 ∧
    Filter.Tendsto (fun n => mu n a+mu n b) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => (theta n b-theta n a)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b)
      Filter.atTop (nhds 1) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in Filter.atTop,|r n b-r n a|≤
      C*eps n*(1-(mu n a+mu n b))*DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b) ∧
    qLimit u≠qLimit w ∧ theta0 w-theta0 u=DominantFiveBody.Coorbital.h ∧
    0≤muLimit u ∧ muLimit u≤1 ∧
    muLimit u*DominantFiveBody.coorbitalKernel (theta0 a-theta0 u)+
      (1-muLimit u)*DominantFiveBody.coorbitalKernel ((theta0 a-theta0 u)-DominantFiveBody.Coorbital.h)=0 ∧
    0<muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
      (1-muLimit u)*DominantFiveBody.Coorbital.kappa |(theta0 a-theta0 u)-DominantFiveBody.Coorbital.h| ∧
    Filter.Tendsto (fun n => (mu n a+mu n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b^3)
      Filter.atTop (nhds (muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
        (1-muLimit u)*DominantFiveBody.Coorbital.kappa |(theta0 a-theta0 u)-DominantFiveBody.Coorbital.h|)) ∧
    (∀ (u' w' : DominantFiveBody.Satellite),u'<w' → ∀ d : DominantFiveBody.Plane,c≠d →
      DominantFiveBody.CompleteLimitingSatellitePair qLimit u' w' d → False) := @DominantFiveBody.normalized_complete_pair_scale_complete
#print axioms DominantFiveBody.normalized_complete_pair_scale_complete

-- prose:376
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (_hconv : ∀ n,DominantFiveBody.StrictConvexInOrder ⟨Equiv.refl DominantFiveBody.Label,rfl⟩ (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a<b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0))
    (u w : DominantFiveBody.Satellite) (_huw : u<w)
    (_hu : u∈DominantFiveBody.pairExteriorLabels a b) (_hw : w∈DominantFiveBody.pairExteriorLabels a b),
b.val=a.val+1 ∧
    Filter.Tendsto (fun n => mu n a+mu n b) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => (theta n b-theta n a)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b)
      Filter.atTop (nhds 1) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in Filter.atTop,|r n b-r n a|≤
      C*eps n*(1-(mu n a+mu n b))*DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b) ∧
    qLimit u≠qLimit w ∧ theta0 w-theta0 u=DominantFiveBody.Coorbital.h ∧
    0≤muLimit u ∧ muLimit u≤1 ∧
    muLimit u*DominantFiveBody.coorbitalKernel (theta0 a-theta0 u)+
      (1-muLimit u)*DominantFiveBody.coorbitalKernel ((theta0 a-theta0 u)-DominantFiveBody.Coorbital.h)=0 ∧
    0<muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
      (1-muLimit u)*DominantFiveBody.Coorbital.kappa |(theta0 a-theta0 u)-DominantFiveBody.Coorbital.h| ∧
    Filter.Tendsto (fun n => (mu n a+mu n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b^3)
      Filter.atTop (nhds (muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
        (1-muLimit u)*DominantFiveBody.Coorbital.kappa |(theta0 a-theta0 u)-DominantFiveBody.Coorbital.h|)) ∧
    (∀ (u' w' : DominantFiveBody.Satellite),u'<w' → ∀ d : DominantFiveBody.Plane,c≠d →
      DominantFiveBody.CompleteLimitingSatellitePair qLimit u' w' d → False) := @DominantFiveBody.normalized_complete_pair_scale_complete
#print axioms DominantFiveBody.normalized_complete_pair_scale_complete

-- display:377
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (_hconv : ∀ n,DominantFiveBody.StrictConvexInOrder ⟨Equiv.refl DominantFiveBody.Label,rfl⟩ (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a<b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0))
    (u w : DominantFiveBody.Satellite) (_huw : u<w)
    (_hu : u∈DominantFiveBody.pairExteriorLabels a b) (_hw : w∈DominantFiveBody.pairExteriorLabels a b),
b.val=a.val+1 ∧
    Filter.Tendsto (fun n => mu n a+mu n b) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => (theta n b-theta n a)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b)
      Filter.atTop (nhds 1) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in Filter.atTop,|r n b-r n a|≤
      C*eps n*(1-(mu n a+mu n b))*DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b) ∧
    qLimit u≠qLimit w ∧ theta0 w-theta0 u=DominantFiveBody.Coorbital.h ∧
    0≤muLimit u ∧ muLimit u≤1 ∧
    muLimit u*DominantFiveBody.coorbitalKernel (theta0 a-theta0 u)+
      (1-muLimit u)*DominantFiveBody.coorbitalKernel ((theta0 a-theta0 u)-DominantFiveBody.Coorbital.h)=0 ∧
    0<muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
      (1-muLimit u)*DominantFiveBody.Coorbital.kappa |(theta0 a-theta0 u)-DominantFiveBody.Coorbital.h| ∧
    Filter.Tendsto (fun n => (mu n a+mu n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b^3)
      Filter.atTop (nhds (muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
        (1-muLimit u)*DominantFiveBody.Coorbital.kappa |(theta0 a-theta0 u)-DominantFiveBody.Coorbital.h|)) ∧
    (∀ (u' w' : DominantFiveBody.Satellite),u'<w' → ∀ d : DominantFiveBody.Plane,c≠d →
      DominantFiveBody.CompleteLimitingSatellitePair qLimit u' w' d → False) := @DominantFiveBody.normalized_complete_pair_scale_complete
#print axioms DominantFiveBody.normalized_complete_pair_scale_complete

-- prop:pair-scale.actual_two_pair_exclusion
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (_hconv : ∀ n,DominantFiveBody.StrictConvexInOrder ⟨Equiv.refl DominantFiveBody.Label,rfl⟩ (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b u w : DominantFiveBody.Satellite) (_hab : a<b) (_huw : u<w) (c d : DominantFiveBody.Plane) (_hcd : c≠d)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (_hpair2 : DominantFiveBody.CompleteLimitingSatellitePair qLimit u w d)
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0)),
False := @DominantFiveBody.normalized_complete_pairs_cannot_coexist
#print axioms DominantFiveBody.normalized_complete_pairs_cannot_coexist

-- prop:pair-scale.current_exterior_error_bound
example : ∀ (mu : ℕ → DominantFiveBody.MassRatio) (q : ℕ → DominantFiveBody.SatelliteConfiguration)
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n)) (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto q Filter.atTop (nhds qLimit)) (a b : DominantFiveBody.Satellite) (_hab : a≠b)
    (c : DominantFiveBody.Plane) (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c),
∃ C : ℝ,0<C ∧ ∀ᶠ n in Filter.atTop,
      ‖DominantFiveBody.pairExteriorField (mu n) (q n) a b (q n b)-DominantFiveBody.pairExteriorField (mu n) (q n) a b (q n a)‖≤
        C*(1-(mu n a+mu n b))*DominantFiveBody.satelliteDistance (q n) a b := @DominantFiveBody.complete_pair_exterior_error_bound
#print axioms DominantFiveBody.complete_pair_exterior_error_bound

-- eq:pair-qdiff
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a<b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c),
∀ᶠ n in Filter.atTop,
      DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
        DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a)=
      Real.sin (theta n b-theta n a)*
        ((mu n a*r n a+mu n b*r n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites (r n) (theta n)) a b^3-
          mu n a/(r n a)^2-mu n b/(r n b)^2) ∧
      0<DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n b) (theta n b)-
        DominantFiveBody.physicalPairExteriorAngularField (mu n) (r n) (theta n) a b (r n a) (theta n a) := @DominantFiveBody.normalized_complete_pair_tangential_difference_positive
#print axioms DominantFiveBody.normalized_complete_pair_tangential_difference_positive

-- eq:pair-vdiff
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio)
    (x : DominantFiveBody.Configuration) (_hx : DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x)
    (a b : DominantFiveBody.Satellite) (_hab : a≠b),
DominantFiveBody.primaryRadialField (DominantFiveBody.satellitesRelative x b)-DominantFiveBody.primaryRadialField (DominantFiveBody.satellitesRelative x a)+
      eps • (DominantFiveBody.pairExteriorField mu (DominantFiveBody.satellitesRelative x) a b (DominantFiveBody.satellitesRelative x b)-
        DominantFiveBody.pairExteriorField mu (DominantFiveBody.satellitesRelative x) a b (DominantFiveBody.satellitesRelative x a))=
      (eps*(mu a+mu b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative x) a b^3) •
        (DominantFiveBody.satellitesRelative x b-DominantFiveBody.satellitesRelative x a) := @DominantFiveBody.normalized_pair_vector_difference
#print axioms DominantFiveBody.normalized_pair_vector_difference

-- prop:pair-scale.actual_direction_alternative
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a≠b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (v : DominantFiveBody.Plane)
    (_hvt : Filter.Tendsto (fun n => DominantFiveBody.physicalPairDirection (DominantFiveBody.satellitesRelative (x n)) a b)
      Filter.atTop (nhds v)),
(Filter.Tendsto (fun n => eps n*(mu n a+mu n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b^3)
      Filter.atTop (nhds 0) ∧ inner ℝ v c=0) ∨
    (Filter.Tendsto (fun n => eps n*(mu n a+mu n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b^3)
      Filter.atTop (nhds 3) ∧ (v=c ∨ v= -c)) := @DominantFiveBody.normalized_complete_pair_direction_alternative
#print axioms DominantFiveBody.normalized_complete_pair_direction_alternative

-- prop:pair-scale.actual_first_stage
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (_hconv : ∀ n,DominantFiveBody.StrictConvexInOrder ⟨Equiv.refl DominantFiveBody.Label,rfl⟩ (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a<b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0)),
b.val=a.val+1 ∧
    Filter.Tendsto (fun n => (theta n b-theta n a)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b)
      Filter.atTop (nhds 1) ∧
    Filter.Tendsto (fun n => (r n b-r n a)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b)
      Filter.atTop (nhds 0) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in Filter.atTop,
      (mu n a+mu n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b^3≤
        C*(1-(mu n a+mu n b))) ∧
    Filter.Tendsto (fun n => mu n a+mu n b) Filter.atTop (nhds 0) ∧
    (∃ C : ℝ,0<C ∧ ∀ᶠ n in Filter.atTop,
      |r n b-r n a|≤C*eps n*(1-(mu n a+mu n b))*DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b) := @DominantFiveBody.normalized_complete_pair_tangential_mass_scale
#print axioms DominantFiveBody.normalized_complete_pair_tangential_mass_scale

-- eq:midpoint
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio)
    (x : DominantFiveBody.Configuration) (_hx : DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x)
    (r theta : DominantFiveBody.Satellite → ℝ) (_hr : ∀ i,0<r i)
    (_hpolar : DominantFiveBody.satellitesRelative x=DominantFiveBody.polarSatellites r theta)
    (a b : DominantFiveBody.Satellite) (_hab : a≠b),
(DominantFiveBody.primaryRadialScalar (r b)-DominantFiveBody.primaryRadialScalar (r a)-
      (eps*(mu a+mu b)/DominantFiveBody.satelliteDistance (DominantFiveBody.polarSatellites r theta) a b^3)*(r b-r a))*
      Real.cos ((theta b-theta a)/2)=
    -eps*inner ℝ
      (DominantFiveBody.pairExteriorField mu (DominantFiveBody.polarSatellites r theta) a b (DominantFiveBody.polarPoint (r b) (theta b))-
        DominantFiveBody.pairExteriorField mu (DominantFiveBody.polarSatellites r theta) a b (DominantFiveBody.polarPoint (r a) (theta a)))
      (DominantFiveBody.polarPoint 1 ((theta a+theta b)/2)) := @DominantFiveBody.normalized_pair_midpoint_identity
#print axioms DominantFiveBody.normalized_pair_midpoint_identity

-- prop:pair-scale.radial_bound_on_tangential_branch
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a≠b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (_hlambda : Filter.Tendsto
      (fun n => eps n*(mu n a+mu n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b^3)
      Filter.atTop (nhds 0))
    (_hgap : Filter.Tendsto (fun n => theta n b-theta n a) Filter.atTop (nhds 0)),
∃ C : ℝ,0<C ∧ ∀ᶠ n in Filter.atTop,
      |r n b-r n a|≤C*eps n*(1-(mu n a+mu n b))*DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b := @DominantFiveBody.normalized_complete_pair_radial_bound_of_tangential
#print axioms DominantFiveBody.normalized_complete_pair_radial_bound_of_tangential

-- prop:pair-scale.actual_positive_cube_limit
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (_hconv : ∀ n,DominantFiveBody.StrictConvexInOrder ⟨Equiv.refl DominantFiveBody.Label,rfl⟩ (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a<b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0))
    (u w : DominantFiveBody.Satellite) (_huw : u<w)
    (_hu : u∈DominantFiveBody.pairExteriorLabels a b) (_hw : w∈DominantFiveBody.pairExteriorLabels a b),
0<muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
      muLimit w*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 w| ∧
    Filter.Tendsto (fun n => (mu n a+mu n b)/DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a b^3)
      Filter.atTop (nhds (muLimit u*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 u|+
        muLimit w*DominantFiveBody.Coorbital.kappa |theta0 a-theta0 w|)) := @DominantFiveBody.normalized_complete_pair_mass_cube_limit
#print axioms DominantFiveBody.normalized_complete_pair_mass_cube_limit

-- eq:nested-field
example : ∀ (mu r theta : DominantFiveBody.Satellite → ℝ) (a b : DominantFiveBody.Satellite) (rho v : ℝ)
    (_hr : ∀ i,0<r i)
    (_hsep : ∀ j∈DominantFiveBody.pairExteriorLabels a b,DominantFiveBody.polarPoint (r j) (theta j)≠DominantFiveBody.polarPoint rho v),
HasDerivAt (fun s => DominantFiveBody.physicalPairExteriorAngularField mu r theta a b s v)
      (∑ j∈DominantFiveBody.pairExteriorLabels a b,mu j*DominantFiveBody.physicalSourceAngularRadialDerivative (r j) (theta j) rho v) rho ∧
    HasDerivAt (fun w => DominantFiveBody.physicalPairExteriorAngularField mu r theta a b rho w)
      (∑ j∈DominantFiveBody.pairExteriorLabels a b,mu j*DominantFiveBody.physicalSourceAngularAngularDerivative (r j) (theta j) rho v) v := @DominantFiveBody.physical_pair_exterior_angular_derivatives
#print axioms DominantFiveBody.physical_pair_exterior_angular_derivatives

-- prop:nested-scale.actual_current_weight_group_radial
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (q : ℕ → DominantFiveBody.SatelliteConfiguration)
    (_heps : Filter.Tendsto eps Filter.atTop (nhds 0)) (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hroot : ∀ n i,DominantFiveBody.vectorResidual (eps n) (mu n) (q n) i=0)
    (_hcf : ∀ n,DominantFiveBody.RelativeCollisionFree (q n))
    (mu0 : DominantFiveBody.MassRatio) (_hmu : Filter.Tendsto mu Filter.atTop (nhds mu0))
    (a b c p : DominantFiveBody.Satellite) (_hab : a≠b) (_hcp : c≠p)
    (_hc : c∈DominantFiveBody.pairExteriorLabels a b) (_hp : p∈DominantFiveBody.pairExteriorLabels a b)
    (c0 p0 : DominantFiveBody.Plane) (_hcunit : ‖c0‖=1) (_hsep : p0≠c0)
    (_hqa : Filter.Tendsto (fun n => q n a) Filter.atTop (nhds c0))
    (_hqb : Filter.Tendsto (fun n => q n b) Filter.atTop (nhds c0))
    (_hqc : Filter.Tendsto (fun n => q n c) Filter.atTop (nhds c0))
    (_hqp : Filter.Tendsto (fun n => q n p) Filter.atTop (nhds p0))
    (d : ℕ → ℝ) (_hd : ∀ n,0<d n) (_hdiam : ∀ n,d n=DominantFiveBody.tripleLargestDistance (q n) a b c)
    (_hpair : Filter.Tendsto (fun n => DominantFiveBody.satelliteDistance (q n) a b/d n) Filter.atTop (nhds 0))
    (C : ℝ) (_hbound : ∀ᶠ n in Filter.atTop,(mu n a+mu n b+mu n c)/d n^3≤C),
Filter.Tendsto (fun n => inner ℝ ((d n)⁻¹ • (q n a-q n c)) c0) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => inner ℝ ((d n)⁻¹ • (q n b-q n c)) c0) Filter.atTop (nhds 0) := @DominantFiveBody.physical_nested_group_radial_projections_tendsto
#print axioms DominantFiveBody.physical_nested_group_radial_projections_tendsto

-- eq:nested-macro-average
example : ∀ (eps : ℝ) (mu : DominantFiveBody.MassRatio) (x : DominantFiveBody.Configuration)
    (_heps : 0<eps) (_hm : DominantFiveBody.PositiveRatio mu) (_hx : DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses eps mu) x)
    (r theta : DominantFiveBody.Satellite → ℝ) (_hr : ∀ i,0<r i) (_hpolar : DominantFiveBody.satellitesRelative x=DominantFiveBody.polarSatellites r theta)
    (a b c p : DominantFiveBody.Satellite) (_hab : a≠b) (_hcp : c≠p)
    (_hc : c∈DominantFiveBody.pairExteriorLabels a b) (_hp : p∈DominantFiveBody.pairExteriorLabels a b),
(mu a+mu b+mu c)*DominantFiveBody.nestedPairCurrentKernel eps mu r theta a b c+
      (1-(mu a+mu b+mu c))*(DominantFiveBody.nestedPairCurrentExterior eps mu r theta a b p-
        fullAngularMatrix eps r theta c p)=0 := @DominantFiveBody.normalized_nested_macro_average
#print axioms DominantFiveBody.normalized_nested_macro_average

-- prop:nested-scale.actual_macro_cube_bridge
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_hrt : ∀ i,Filter.Tendsto (fun n => r n i) Filter.atTop (nhds 1))
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0))
    (a b c p : DominantFiveBody.Satellite) (_hab : a≠b) (_hcp : c≠p)
    (_hc : c∈DominantFiveBody.pairExteriorLabels a b) (_hp : p∈DominantFiveBody.pairExteriorLabels a b)
    (psi omega : ℝ) (_homega : omega≠0)
    (_hpa : theta0 a=psi) (_hpb : theta0 b=psi) (_hpc : theta0 c=psi)
    (_hsep : theta0 p≠psi) (_hpi : |theta0 p-psi|<Real.pi)
    (d : ℕ → ℝ) (_hd : ∀ n,0<d n) (_hdt : Filter.Tendsto d Filter.atTop (nhds 0))
    (_hrac : Filter.Tendsto (fun n => (r n c-r n a)/d n) Filter.atTop (nhds 0))
    (_hrbc : Filter.Tendsto (fun n => (r n c-r n b)/d n) Filter.atTop (nhds 0))
    (_hgac : Filter.Tendsto (fun n => (theta n c-theta n a)/d n) Filter.atTop (nhds omega))
    (_hgbc : Filter.Tendsto (fun n => (theta n c-theta n b)/d n) Filter.atTop (nhds omega))
    (_hDac : Filter.Tendsto (fun n => DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) a c/d n) Filter.atTop (nhds 1))
    (_hDbc : Filter.Tendsto (fun n => DominantFiveBody.satelliteDistance (DominantFiveBody.satellitesRelative (x n)) b c/d n) Filter.atTop (nhds 1)),
Filter.Tendsto (fun n => (mu n a+mu n b+mu n c)/d n^3)
      Filter.atTop (nhds (DominantFiveBody.Coorbital.kappa |psi-theta0 p|)) := @DominantFiveBody.normalized_nested_macro_mass_cube_limit_of_first_order_geometry
#print axioms DominantFiveBody.normalized_nested_macro_mass_cube_limit_of_first_order_geometry

-- eq:chi
example : ∀ t b : ℝ,
  DominantFiveBody.singleScaleChi t b = t*b^2/2*Real.sinc (t*b/2)^2 ∧
    1-Real.cos (t*b) = t*DominantFiveBody.singleScaleChi t b := @DominantFiveBody.singleScaleChi_complete
#print axioms DominantFiveBody.singleScaleChi_complete

-- subsec:pair-chart.actual_common_interval_capture
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (_hconv : ∀ n,DominantFiveBody.StrictConvexInOrder ⟨Equiv.refl DominantFiveBody.Label,rfl⟩ (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a<b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0))
    (u w : DominantFiveBody.Satellite) (_huw : u<w)
    (_hu : u∈DominantFiveBody.pairExteriorLabels a b) (_hw : w∈DominantFiveBody.pairExteriorLabels a b)
    (e : Equiv.Perm DominantFiveBody.Satellite) (_he0 : e 0=a) (_he1 : e 1=b) (_he2 : e 2=u) (_he3 : e 3=w),
∃ keepD : Bool,Nonempty (DominantFiveBody.PairCapturedBranches eps
      (fun n => DominantFiveBody.pairPhysicalScale (mu n ∘ e)) (fun n => DominantFiveBody.pairExteriorFraction (mu n ∘ e))
      (fun n => DominantFiveBody.pairPhysicalFraction (mu n ∘ e))
      (fun n => DominantFiveBody.pairVariablesFromPolar (DominantFiveBody.pairPhysicalScale (mu n ∘ e)) (DominantFiveBody.pairPhysicalFraction (mu n ∘ e))
        (r n ∘ e) (fun i => theta n (e i)-theta n u)) (theta0 a-theta0 u) keepD) := @DominantFiveBody.normalized_complete_pair_actual_capture
#print axioms DominantFiveBody.normalized_complete_pair_actual_capture

-- subsec:pair-chart.actual_inverse_limits
example : ∀ (eps : ℕ → ℝ) (mu : ℕ → DominantFiveBody.MassRatio) (x : ℕ → DominantFiveBody.Configuration)
    (_heps : ∀ n,0<eps n) (_hepst : Filter.Tendsto eps Filter.atTop (nhds 0))
    (_hm : ∀ n,DominantFiveBody.PositiveRatio (mu n))
    (_hx : ∀ n,DominantFiveBody.NormalizedCentralConfiguration (DominantFiveBody.masses (eps n) (mu n)) (x n))
    (_hconv : ∀ n,DominantFiveBody.StrictConvexInOrder ⟨Equiv.refl DominantFiveBody.Label,rfl⟩ (x n))
    (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (_hr : ∀ n,∀ i,0<r n i)
    (_hpolar : ∀ n,DominantFiveBody.satellitesRelative (x n)=DominantFiveBody.polarSatellites (r n) (theta n))
    (_horder : ∀ n,∀ i j,i<j → 0<theta n j-theta n i ∧ theta n j-theta n i<Real.pi)
    (muLimit : DominantFiveBody.MassRatio) (_hmt : Filter.Tendsto mu Filter.atTop (nhds muLimit))
    (qLimit : DominantFiveBody.SatelliteConfiguration)
    (_hqt : Filter.Tendsto (fun n => DominantFiveBody.satellitesRelative (x n)) Filter.atTop (nhds qLimit))
    (a b : DominantFiveBody.Satellite) (_hab : a<b) (c : DominantFiveBody.Plane)
    (_hpair : DominantFiveBody.CompleteLimitingSatellitePair qLimit a b c)
    (theta0 : DominantFiveBody.Satellite → ℝ) (_hthetat : Filter.Tendsto theta Filter.atTop (nhds theta0))
    (u w : DominantFiveBody.Satellite) (_huw : u<w)
    (_hu : u∈DominantFiveBody.pairExteriorLabels a b) (_hw : w∈DominantFiveBody.pairExteriorLabels a b)
    (e : Equiv.Perm DominantFiveBody.Satellite) (_he0 : e 0=a) (_he1 : e 1=b) (_he2 : e 2=u) (_he3 : e 3=w),
Filter.Tendsto (fun n => DominantFiveBody.pairPhysicalScale (mu n ∘ e)) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => DominantFiveBody.pairExteriorFraction (mu n ∘ e)) Filter.atTop (nhds (muLimit u)) ∧
    Filter.Tendsto (fun n => DominantFiveBody.pairVariablesFromPolar (DominantFiveBody.pairPhysicalScale (mu n ∘ e))
      (DominantFiveBody.pairPhysicalFraction (mu n ∘ e)) (r n ∘ e) (fun i => theta n (e i)-theta n u))
      Filter.atTop (nhds (DominantFiveBody.pairUnitPoint DominantFiveBody.Coorbital.h (theta0 a-theta0 u)
        (DominantFiveBody.pairBoundaryScale (DominantFiveBody.pairProbeDerivative (muLimit u) DominantFiveBody.Coorbital.h (theta0 a-theta0 u))))) := @DominantFiveBody.normalized_complete_pair_actual_chart_limits
#print axioms DominantFiveBody.normalized_complete_pair_actual_chart_limits
