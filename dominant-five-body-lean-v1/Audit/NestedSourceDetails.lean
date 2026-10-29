import DominantFiveBody.NestedSourceDerivativeDetails
import DominantFiveBody.NestedSourceSignTable
import DominantFiveBody.NestedSourceCaptureDetails
import DominantFiveBody.SlowInternalTaylor
open scoped BigOperators ContDiff Topology
universe u_1 u_2 u_3 u_4
set_option linter.unusedVariables false
example : ∀ (psi Z : ℝ),
  Z ≠ (0 : ℝ) →
    HasDerivAt (fun (r : ℝ) => DominantFiveBody.nestedBoundaryKernel (1 : ℝ) psi ((0 : ℝ), r))
      ((-2 : ℝ) / |Z| ^ (3 : ℕ)) Z := @DominantFiveBody.nestedBoundaryKernel_unit_hasDerivAt
#print axioms DominantFiveBody.nestedBoundaryKernel_unit_hasDerivAt

example : ∀ (psi Z : ℝ),
  Z ≠ (0 : ℝ) →
    HasDerivAt (fun (r : ℝ) => deriv (fun (s : ℝ) => DominantFiveBody.nestedBoundaryKernel (1 : ℝ) psi ((0 : ℝ), s)) r)
      ((6 : ℝ) / (|Z| ^ (3 : ℕ) * Z)) Z := @DominantFiveBody.nestedBoundaryKernel_unit_second_hasDerivAt
#print axioms DominantFiveBody.nestedBoundaryKernel_unit_second_hasDerivAt

example : ∀ (psi omega : ℝ),
  |omega| = (1 : ℝ) →
    have Z := omega * DominantFiveBody.pairBoundaryScale DominantFiveBody.tripleD0;
    have z := DominantFiveBody.pairBoundaryScale ((3 : ℝ) * DominantFiveBody.tripleD0);
    deriv (fun (s : ℝ) => DominantFiveBody.nestedBoundaryKernel (1 : ℝ) psi ((0 : ℝ), s)) Z =
        (-2 : ℝ) * DominantFiveBody.tripleD0 ∧
      deriv (fun (r : ℝ) => deriv (fun (s : ℝ) => DominantFiveBody.nestedBoundaryKernel (1 : ℝ) psi ((0 : ℝ), s)) r) Z =
          (6 : ℝ) * DominantFiveBody.tripleD0 / Z ∧
        deriv (fun (s : ℝ) => DominantFiveBody.nestedBoundaryKernel (1 : ℝ) psi ((0 : ℝ), s)) z =
          (-6 : ℝ) * DominantFiveBody.tripleD0 := @DominantFiveBody.nestedBoundaryKernel_original_derivatives
#print axioms DominantFiveBody.nestedBoundaryKernel_original_derivatives

example : ∀ (alpha beta : ℝ) (y : DominantFiveBody.NestedChartVariables),
  DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) ≠
      DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) →
    (0 : ℝ) < y (2 : Fin (7 : ℕ)) ^ (2 : ℕ) + y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) * y (5 : Fin (7 : ℕ)) ^ (2 : ℕ) →
      DominantFiveBody.nestedChartExtendedRows (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha y =
        DominantFiveBody.nestedChartExtendedRows (0 : ℝ) (0 : ℝ) (0 : ℝ) beta y := @DominantFiveBody.nestedChartExtendedRows_boundary_alpha_independent
#print axioms DominantFiveBody.nestedChartExtendedRows_boundary_alpha_independent

example : ∀ (alpha beta psi omega : ℝ),
  |psi| = DominantFiveBody.Coorbital.h →
    |omega| = (1 : ℝ) →
      DominantFiveBody.nestedChartJacobian (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha (DominantFiveBody.nestedBasePoint psi omega) =
        DominantFiveBody.nestedChartJacobian (0 : ℝ) (0 : ℝ) (0 : ℝ) beta (DominantFiveBody.nestedBasePoint psi omega) := @DominantFiveBody.nestedChartJacobian_boundary_alpha_independent
#print axioms DominantFiveBody.nestedChartJacobian_boundary_alpha_independent

example : (fun (k : Fin (4 : ℕ)) (i : DominantFiveBody.Satellite) =>
    (DominantFiveBody.nestedSourceCasePermutation k : DominantFiveBody.Satellite → DominantFiveBody.Satellite) i) =
  ![![(0 : DominantFiveBody.Satellite), (1 : DominantFiveBody.Satellite), (2 : DominantFiveBody.Satellite),
      (3 : DominantFiveBody.Satellite)],
    ![(1 : DominantFiveBody.Satellite), (2 : DominantFiveBody.Satellite), (0 : DominantFiveBody.Satellite),
      (3 : DominantFiveBody.Satellite)],
    ![(1 : DominantFiveBody.Satellite), (2 : DominantFiveBody.Satellite), (3 : DominantFiveBody.Satellite),
      (0 : DominantFiveBody.Satellite)],
    ![(2 : DominantFiveBody.Satellite), (3 : DominantFiveBody.Satellite), (1 : DominantFiveBody.Satellite),
      (0 : DominantFiveBody.Satellite)]] := @DominantFiveBody.nestedSourceCasePermutation_source
#print axioms DominantFiveBody.nestedSourceCasePermutation_source

example : DominantFiveBody.nestedSourceCaseTable =
  ![({(1 : DominantFiveBody.Label), (2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label)},
      {(1 : DominantFiveBody.Label), (2 : DominantFiveBody.Label)}, (4 : DominantFiveBody.Label), (-1 : ℝ), (1 : ℝ)),
    ({(1 : DominantFiveBody.Label), (2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label)},
      {(2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label)}, (4 : DominantFiveBody.Label), (-1 : ℝ), (-1 : ℝ)),
    ({(2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label), (4 : DominantFiveBody.Label)},
      {(2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label)}, (1 : DominantFiveBody.Label), (1 : ℝ), (1 : ℝ)),
    ({(2 : DominantFiveBody.Label), (3 : DominantFiveBody.Label), (4 : DominantFiveBody.Label)},
      {(3 : DominantFiveBody.Label), (4 : DominantFiveBody.Label)}, (1 : DominantFiveBody.Label), (1 : ℝ), (-1 : ℝ))] := @DominantFiveBody.nestedSourceCaseTable_source
#print axioms DominantFiveBody.nestedSourceCaseTable_source

example : ∀ (k : Fin (4 : ℕ)),
  (⇑(DominantFiveBody.nestedSourceCasePermutation k) : DominantFiveBody.Satellite → DominantFiveBody.Satellite) ∘
      (⇑(DominantFiveBody.hullSatellitePermutation
            (DominantFiveBody.nestedBoundaryHullOrder (DominantFiveBody.nestedSourceCaseSigns k).1
              (DominantFiveBody.nestedSourceCaseSigns k).2)) :
        DominantFiveBody.Satellite → DominantFiveBody.Satellite) =
    id := @DominantFiveBody.nestedSourceCase_order_is_original
#print axioms DominantFiveBody.nestedSourceCase_order_is_original

example : ∀ (mu : ℕ → DominantFiveBody.MassRatio),
  (∀ (n : ℕ), DominantFiveBody.PositiveRatio (mu n)) →
    ∀ (r theta : ℕ → DominantFiveBody.Satellite → ℝ) (psi omega : ℝ) (d s : ℕ → ℝ),
      (∀ (n : ℕ), (0 : ℝ) < d n) →
        (∀ (n : ℕ), (0 : ℝ) < s n) →
          Filter.Tendsto d Filter.atTop (𝓝 (0 : ℝ)) →
            Filter.Tendsto (fun (n : ℕ) => s n / d n) Filter.atTop (𝓝 (0 : ℝ)) →
              Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.triplePhysicalClusterMass (mu n) / d n ^ (3 : ℕ))
                  Filter.atTop (𝓝 DominantFiveBody.tripleD0) →
                Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.nestedPhysicalInnerMass (mu n) / s n ^ (3 : ℕ))
                    Filter.atTop (𝓝 ((3 : ℝ) * DominantFiveBody.tripleD0)) →
                  (∀ (i : DominantFiveBody.Satellite), Filter.Tendsto (fun (n : ℕ) => r n i) Filter.atTop (𝓝 (1 : ℝ))) →
                    (∀ (i : DominantFiveBody.TripleLabel),
                        Filter.Tendsto (fun (n : ℕ) => theta n (Fin.castSucc i)) Filter.atTop (𝓝 psi)) →
                      Filter.Tendsto
                          (fun (n : ℕ) =>
                            (r n (2 : DominantFiveBody.Satellite) - r n (0 : DominantFiveBody.Satellite)) / d n)
                          Filter.atTop (𝓝 (0 : ℝ)) →
                        Filter.Tendsto
                            (fun (n : ℕ) =>
                              (r n (2 : DominantFiveBody.Satellite) - r n (1 : DominantFiveBody.Satellite)) / d n)
                            Filter.atTop (𝓝 (0 : ℝ)) →
                          Filter.Tendsto
                              (fun (n : ℕ) =>
                                (theta n (2 : DominantFiveBody.Satellite) - theta n (0 : DominantFiveBody.Satellite)) /
                                  d n)
                              Filter.atTop (𝓝 omega) →
                            Filter.Tendsto
                                (fun (n : ℕ) =>
                                  (theta n (2 : DominantFiveBody.Satellite) -
                                      theta n (1 : DominantFiveBody.Satellite)) /
                                    d n)
                                Filter.atTop (𝓝 omega) →
                              Filter.Tendsto
                                  (fun (n : ℕ) =>
                                    (r n (1 : DominantFiveBody.Satellite) - r n (0 : DominantFiveBody.Satellite)) / s n)
                                  Filter.atTop (𝓝 (0 : ℝ)) →
                                Filter.Tendsto
                                    (fun (n : ℕ) =>
                                      (theta n (1 : DominantFiveBody.Satellite) -
                                          theta n (0 : DominantFiveBody.Satellite)) /
                                        s n)
                                    Filter.atTop (𝓝 (1 : ℝ)) →
                                  Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.nestedPhysicalScale (mu n))
                                      Filter.atTop (𝓝 (0 : ℝ)) ∧
                                    Filter.Tendsto (fun (n : ℕ) => DominantFiveBody.nestedPhysicalEta (mu n))
                                        Filter.atTop (𝓝 (0 : ℝ)) ∧
                                      Filter.Tendsto
                                          (fun (n : ℕ) =>
                                            DominantFiveBody.nestedVariablesFromPolar
                                              (DominantFiveBody.nestedPhysicalScale (mu n))
                                              (DominantFiveBody.nestedPhysicalEta (mu n))
                                              (DominantFiveBody.nestedPhysicalAlpha (mu n)) (r n) (theta n))
                                          Filter.atTop (𝓝 (DominantFiveBody.nestedBasePoint psi omega)) ∧
                                        Filter.Tendsto
                                            (fun (n : ℕ) => d n / DominantFiveBody.nestedPhysicalScale (mu n))
                                            Filter.atTop
                                            (𝓝 (DominantFiveBody.pairBoundaryScale DominantFiveBody.tripleD0)) ∧
                                          Filter.Tendsto
                                              (fun (n : ℕ) =>
                                                s n /
                                                  (DominantFiveBody.nestedPhysicalScale (mu n) *
                                                    DominantFiveBody.nestedPhysicalEta (mu n)))
                                              Filter.atTop
                                              (𝓝
                                                (DominantFiveBody.pairBoundaryScale
                                                  ((3 : ℝ) * DominantFiveBody.tripleD0))) ∧
                                            Filter.Tendsto
                                                (fun (n : ℕ) =>
                                                  DominantFiveBody.nestedRowOuterDifference
                                                    (DominantFiveBody.nestedPhysicalScale (mu n))
                                                    (DominantFiveBody.nestedPhysicalAlpha (mu n)) (r n))
                                                Filter.atTop (𝓝 (0 : ℝ)) ∧
                                              Filter.Tendsto
                                                  (fun (n : ℕ) =>
                                                    DominantFiveBody.nestedRowInnerDifference
                                                      (DominantFiveBody.nestedPhysicalScale (mu n))
                                                      (DominantFiveBody.nestedPhysicalEta (mu n)) (r n))
                                                  Filter.atTop (𝓝 (0 : ℝ)) ∧
                                                Filter.Tendsto
                                                    (fun (n : ℕ) =>
                                                      DominantFiveBody.nestedRowInnerDifference
                                                        (DominantFiveBody.nestedPhysicalScale (mu n))
                                                        (DominantFiveBody.nestedPhysicalEta (mu n)) (theta n))
                                                    Filter.atTop
                                                    (𝓝
                                                      (DominantFiveBody.pairBoundaryScale
                                                        ((3 : ℝ) * DominantFiveBody.tripleD0))) ∧
                                                  Filter.Tendsto
                                                      (fun (n : ℕ) =>
                                                        (theta n (2 : DominantFiveBody.Satellite) -
                                                            theta n (0 : DominantFiveBody.Satellite)) /
                                                          DominantFiveBody.nestedPhysicalScale (mu n))
                                                      Filter.atTop
                                                      (𝓝
                                                        (omega *
                                                          DominantFiveBody.pairBoundaryScale
                                                            DominantFiveBody.tripleD0)) ∧
                                                    Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          (theta n (2 : DominantFiveBody.Satellite) -
                                                              theta n (1 : DominantFiveBody.Satellite)) /
                                                            DominantFiveBody.nestedPhysicalScale (mu n))
                                                        Filter.atTop
                                                        (𝓝
                                                          (omega *
                                                            DominantFiveBody.pairBoundaryScale
                                                              DominantFiveBody.tripleD0)) ∧
                                                      Filter.Tendsto
                                                        (fun (n : ℕ) =>
                                                          DominantFiveBody.nestedRowOuterDifference
                                                            (DominantFiveBody.nestedPhysicalScale (mu n))
                                                            (DominantFiveBody.nestedPhysicalAlpha (mu n)) (theta n))
                                                        Filter.atTop
                                                        (𝓝
                                                          (omega *
                                                            DominantFiveBody.pairBoundaryScale
                                                              DominantFiveBody.tripleD0)) := @DominantFiveBody.nestedSource_individual_inverse_limits
#print axioms DominantFiveBody.nestedSource_individual_inverse_limits

example : ∀ (eps t eta alpha : ℕ → ℝ) (y : ℕ → DominantFiveBody.NestedChartVariables) (psi omega d r : ℝ),
  Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) →
    Filter.Tendsto t Filter.atTop (𝓝 (0 : ℝ)) →
      Filter.Tendsto eta Filter.atTop (𝓝 (0 : ℝ)) →
        Filter.Tendsto y Filter.atTop (𝓝 (DominantFiveBody.nestedBasePoint psi omega)) →
          (0 : ℝ) < d →
            (0 : ℝ) < r →
              ∀ᶠ (n : ℕ) in Filter.atTop,
                Dist.dist (DominantFiveBody.nestedParameter (eps n) (t n) (eta n) (alpha n))
                      (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) (alpha n)) <
                    d ∧
                  Dist.dist (y n) (DominantFiveBody.nestedBasePoint psi omega) < r := @DominantFiveBody.nestedSource_common_balls_without_alpha_limit
#print axioms DominantFiveBody.nestedSource_common_balls_without_alpha_limit

example : ∀ (eps t eta s dr : ℕ → ℝ) (C z0 : ℝ),
  (∀ (n : ℕ), (0 : ℝ) ≤ eps n) →
    (∀ (n : ℕ), (0 : ℝ) < t n) →
      (∀ (n : ℕ), (0 : ℝ) < eta n) →
        (0 : ℝ) < C →
          (0 : ℝ) < z0 →
            (∀ᶠ (n : ℕ) in Filter.atTop, |dr n| ≤ C * eps n * s n) →
              Filter.Tendsto (fun (n : ℕ) => s n / (t n * eta n)) Filter.atTop (𝓝 z0) →
                ∃ (K : ℝ), (0 : ℝ) < K ∧ ∀ᶠ (n : ℕ) in Filter.atTop, |dr n / (t n * eta n)| ≤ K * eps n := @DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound
#print axioms DominantFiveBody.nestedSource_radial_Oepsilon_from_original_bound

example : ∀ (R psi w z t : ℝ),
  DominantFiveBody.affinePolarPoint R psi w z t - DominantFiveBody.polarPoint R psi =
    t • DominantFiveBody.affinePolarDirection R psi w z t := @DominantFiveBody.affinePolarPoint_divided_identity
#print axioms DominantFiveBody.affinePolarPoint_divided_identity

example : ∀ (R psi w z : ℝ),
  (fun (t : ℝ) =>
      DominantFiveBody.affinePolarPoint R psi w z t - DominantFiveBody.polarPoint R psi -
        t • (DominantFiveBody.polarPointDerivative (R, psi) : ℝ × ℝ → DominantFiveBody.Plane) (w, z)) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.affinePolarPoint_cartesian_Osquare
#print axioms DominantFiveBody.affinePolarPoint_cartesian_Osquare

example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (fun (t : ℝ) =>
      DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i) -
          DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) -
        t • DominantFiveBody.tripleBoundaryDisplacement alpha y i) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.tripleChartPoint_cartesian_Osquare
#print axioms DominantFiveBody.tripleChartPoint_cartesian_Osquare

example : ∀ (alpha : DominantFiveBody.TripleVector),
  (fun (t : ℝ) => DominantFiveBody.tripleChartMass t alpha (3 : DominantFiveBody.Satellite) - (1 : ℝ)) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.tripleChart_exteriorMass_Ocube
#print axioms DominantFiveBody.tripleChart_exteriorMass_Ocube

example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  DominantFiveBody.relativeAverage (DominantFiveBody.tripleChartMass t alpha)
        (DominantFiveBody.tripleChartPoints t alpha y) -
      DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) =
    t ^ (3 : ℕ) •
      (∑ i : DominantFiveBody.TripleLabel, alpha i • DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i) -
        DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ)) := @DominantFiveBody.tripleChart_relativeAverage_cubic_identity
#print axioms DominantFiveBody.tripleChart_relativeAverage_cubic_identity

example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (fun (t : ℝ) =>
      DominantFiveBody.relativeAverage (DominantFiveBody.tripleChartMass t alpha)
          (DominantFiveBody.tripleChartPoints t alpha y) -
        DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ)) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.tripleChart_relativeAverage_Ocube
#print axioms DominantFiveBody.tripleChart_relativeAverage_Ocube

example : ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  (fun (t : ℝ) =>
      (eps / ((1 : ℝ) + eps)) •
        (DominantFiveBody.relativeAverage (DominantFiveBody.tripleChartMass t alpha)
            (DominantFiveBody.tripleChartPoints t alpha y) -
          DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ))) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.tripleChart_reaction_Ocube
#print axioms DominantFiveBody.tripleChart_reaction_Ocube

example : ∀ (eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.nestedActualBoundaryClusterDisplacement eta alpha y i =
    DominantFiveBody.tripleBoundaryDisplacement (DominantFiveBody.nestedTripleWeights eta alpha)
      (DominantFiveBody.nestedToTripleVariables eta alpha y) i := @DominantFiveBody.nestedBoundaryDisplacement_to_triple
#print axioms DominantFiveBody.nestedBoundaryDisplacement_to_triple

example : ∀ (eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables) (i : DominantFiveBody.TripleLabel),
  (fun (t : ℝ) =>
      DominantFiveBody.nestedChartPoints t eta alpha y (Fin.castSucc i) -
          DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) -
        t • DominantFiveBody.nestedActualBoundaryClusterDisplacement eta alpha y i) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.nestedChartPoint_cartesian_Osquare
#print axioms DominantFiveBody.nestedChartPoint_cartesian_Osquare

example : ∀ (eps eta alpha : ℝ) (y : DominantFiveBody.NestedChartVariables),
  (fun (t : ℝ) =>
      (eps / ((1 : ℝ) + eps)) •
        (DominantFiveBody.relativeAverage (DominantFiveBody.nestedChartMass t eta alpha)
            (DominantFiveBody.nestedChartPoints t eta alpha y) -
          DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ))) =O[𝓝 (0 : ℝ)]
    fun (t : ℝ) => t ^ (3 : ℕ) := @DominantFiveBody.nestedChart_reaction_Ocube
#print axioms DominantFiveBody.nestedChart_reaction_Ocube

example : ∀ (source : DominantFiveBody.Plane) (R psi w z : ℝ),
  source ≠ DominantFiveBody.polarPoint R psi →
    (fun (t : ℝ) =>
        DominantFiveBody.newtonTargetField source (DominantFiveBody.affinePolarPoint R psi w z t) -
            DominantFiveBody.newtonTargetField source (DominantFiveBody.polarPoint R psi) -
          t •
            (DominantFiveBody.newtonTargetDerivative source (DominantFiveBody.polarPoint R psi) :
                DominantFiveBody.Plane → DominantFiveBody.Plane)
              ((DominantFiveBody.polarPointDerivative (R, psi) : ℝ × ℝ → DominantFiveBody.Plane) (w, z))) =O[𝓝 (0 : ℝ)]
      fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.newtonTargetField_affinePolar_Osquare
#print axioms DominantFiveBody.newtonTargetField_affinePolar_Osquare

example : ∀ (eps tau w z : ℝ),
  (0 : ℝ) < (1 : ℝ) + eps →
    tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
      (fun (t : ℝ) =>
          DominantFiveBody.backgroundProbeField eps
              (DominantFiveBody.affinePolarPoint (DominantFiveBody.backgroundRadius eps)
                (tau * DominantFiveBody.Coorbital.h) w z t) -
            t •
              (DominantFiveBody.backgroundOperator eps tau : DominantFiveBody.Plane → DominantFiveBody.Plane)
                ((DominantFiveBody.polarPointDerivative
                      (DominantFiveBody.backgroundRadius eps, tau * DominantFiveBody.Coorbital.h) :
                    ℝ × ℝ → DominantFiveBody.Plane)
                  (w, z))) =O[𝓝 (0 : ℝ)]
        fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.backgroundProbeField_affinePolar_Osquare
#print axioms DominantFiveBody.backgroundProbeField_affinePolar_Osquare

example : ∀ (t : ℝ) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (0 : ℝ) < t →
    (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq t alpha y i j) →
      ∑ j ∈ Finset.univ.erase i,
          (DominantFiveBody.tripleChartMass t alpha (Fin.castSucc j) /
              DominantFiveBody.satelliteDistance (DominantFiveBody.tripleChartPoints t alpha y) (Fin.castSucc i)
                  (Fin.castSucc j) ^
                (3 : ℕ)) •
            (DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc j) -
              DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i)) =
        t • DominantFiveBody.tripleInternalVectorQuotient t alpha y i := @DominantFiveBody.tripleInternalCartesian_scaling
#print axioms DominantFiveBody.tripleInternalCartesian_scaling

example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.tripleInternalVectorQuotient (0 : ℝ) alpha y i =
    -DominantFiveBody.tripleBoundaryInternalForce alpha y i := @DominantFiveBody.tripleInternalVectorQuotient_zero
#print axioms DominantFiveBody.tripleInternalVectorQuotient_zero

example : ∀ (n : ℕ∞ω) (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq (0 : ℝ) alpha y i j) →
    ContDiffAt ℝ n (fun (t : ℝ) => DominantFiveBody.tripleInternalVectorQuotient t alpha y i) (0 : ℝ) := @DominantFiveBody.tripleInternalVectorQuotient_contDiffAt
#print axioms DominantFiveBody.tripleInternalVectorQuotient_contDiffAt

example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq (0 : ℝ) alpha y i j) →
    (fun (t : ℝ) =>
        DominantFiveBody.tripleInternalVectorQuotient t alpha y i +
          DominantFiveBody.tripleBoundaryInternalForce alpha y i) =O[𝓝 (0 : ℝ)]
      fun (t : ℝ) => t := @DominantFiveBody.tripleInternalVectorQuotient_Olinear
#print axioms DominantFiveBody.tripleInternalVectorQuotient_Olinear

example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  (∀ (j : DominantFiveBody.TripleLabel), j ≠ i → (0 : ℝ) < DominantFiveBody.tripleChartWSq (0 : ℝ) alpha y i j) →
    (fun (t : ℝ) =>
        ∑ j ∈ Finset.univ.erase i,
            (DominantFiveBody.tripleChartMass t alpha (Fin.castSucc j) /
                DominantFiveBody.satelliteDistance (DominantFiveBody.tripleChartPoints t alpha y) (Fin.castSucc i)
                    (Fin.castSucc j) ^
                  (3 : ℕ)) •
              (DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc j) -
                DominantFiveBody.tripleChartPoints t alpha y (Fin.castSucc i)) +
          t • DominantFiveBody.tripleBoundaryInternalForce alpha y i) =O[𝓝[>] (0 : ℝ)]
      fun (t : ℝ) => t ^ (2 : ℕ) := @DominantFiveBody.tripleInternalCartesian_Osquare
#print axioms DominantFiveBody.tripleInternalCartesian_Osquare

