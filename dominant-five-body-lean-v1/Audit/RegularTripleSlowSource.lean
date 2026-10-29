import DominantFiveBody.RegularTripleSourceFormulas
import DominantFiveBody.SlowRootSourceIdentities
open scoped BigOperators ContDiff Topology
universe u_1 u_2 u_3 u_4
set_option linter.unusedVariables false
example : ∀ (rho r v : ℝ),
  ‖DominantFiveBody.polarPoint rho v - DominantFiveBody.polarPoint r (0 : ℝ)‖ ^ (2 : ℕ) =
    rho ^ (2 : ℕ) + r ^ (2 : ℕ) - (2 : ℝ) * rho * r * Real.cos v := @DominantFiveBody.polar_distance_sq_cos
#print axioms DominantFiveBody.polar_distance_sq_cos

example : ∀ (x : ℝ), (0 : ℝ) ≤ x → (√x ^ (3 : ℕ))⁻¹ = x ^ (-3 / 2 : ℝ) := @DominantFiveBody.sqrt_cube_inverse_eq_negative_three_halves
#print axioms DominantFiveBody.sqrt_cube_inverse_eq_negative_three_halves

example : ∀ (rho v r : ℝ),
  DominantFiveBody.regularTripleScalarH r (rho, v) =
    -rho * r * Real.sin v * ((rho ^ (2 : ℕ) + r ^ (2 : ℕ) - (2 : ℝ) * rho * r * Real.cos v) ^ (-3 / 2 : ℝ) - (1 : ℝ)) := @DominantFiveBody.regularTripleScalarH_source_formula
#print axioms DominantFiveBody.regularTripleScalarH_source_formula

example : ∀ (r : ℝ) (x : ℝ × ℝ),
  DominantFiveBody.polarPoint r (0 : ℝ) ≠ DominantFiveBody.polarPoint x.1 x.2 →
    DifferentiableAt ℝ (DominantFiveBody.regularTripleScalarH r) x := @DominantFiveBody.regularTripleScalarH_differentiableAt
#print axioms DominantFiveBody.regularTripleScalarH_differentiableAt

example : ∀ (r : ℝ) (x : ℝ × ℝ) (w z : ℝ),
  (fderiv ℝ (DominantFiveBody.regularTripleScalarH r) x : ℝ × ℝ → ℝ) (w, z) =
    DominantFiveBody.regularTripleScalarH_rho r x * w + DominantFiveBody.regularTripleScalarH_v r x * z := @DominantFiveBody.regularTripleScalarH_fderiv_apply
#print axioms DominantFiveBody.regularTripleScalarH_fderiv_apply

example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables)
  (i : DominantFiveBody.TripleLabel),
  DominantFiveBody.regularTripleBoundaryM alpha y i =
    DominantFiveBody.regularTripleScalarH_rho (y (0 : Fin (7 : ℕ))) (y (1 : Fin (7 : ℕ)), y (4 : Fin (7 : ℕ))) *
          DominantFiveBody.tripleChartRadialPositions alpha y i +
        DominantFiveBody.regularTripleScalarH_v (y (0 : Fin (7 : ℕ))) (y (1 : Fin (7 : ℕ)), y (4 : Fin (7 : ℕ))) *
          DominantFiveBody.tripleChartAngularPositions alpha y i -
      ∑ j ∈ Finset.univ.erase i,
        alpha j * y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) *
            (DominantFiveBody.tripleChartAngularPositions alpha y i -
              DominantFiveBody.tripleChartAngularPositions alpha y j) /
          ((DominantFiveBody.tripleChartRadialPositions alpha y i -
                  DominantFiveBody.tripleChartRadialPositions alpha y j) ^
                (2 : ℕ) +
              y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) *
                (DominantFiveBody.tripleChartAngularPositions alpha y i -
                    DominantFiveBody.tripleChartAngularPositions alpha y j) ^
                  (2 : ℕ)) ^
            (3 / 2 : ℝ) := @DominantFiveBody.regularTripleBoundaryM_source_formula
#print axioms DominantFiveBody.regularTripleBoundaryM_source_formula

example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  DominantFiveBody.polarPoint (y (0 : Fin (7 : ℕ))) (0 : ℝ) ≠
      DominantFiveBody.polarPoint (y (1 : Fin (7 : ℕ))) (y (4 : Fin (7 : ℕ))) →
    DominantFiveBody.tripleAngularDifference (0 : ℝ) (0 : ℝ) alpha y =
      DominantFiveBody.tripleGapMatrix.mulVec (DominantFiveBody.regularTripleBoundaryM alpha y) := @DominantFiveBody.tripleAngularDifference_boundary_eq_LM
#print axioms DominantFiveBody.tripleAngularDifference_boundary_eq_LM

example : ∀ (alpha : DominantFiveBody.TripleVector) (y : DominantFiveBody.TripleChartVariables),
  ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
    DominantFiveBody.tripleAngularMean (0 : ℝ) (0 : ℝ) alpha y =
      -y (1 : Fin (7 : ℕ)) * y (0 : Fin (7 : ℕ)) * Real.sin (y (4 : Fin (7 : ℕ))) *
        ((y (1 : Fin (7 : ℕ)) ^ (2 : ℕ) + y (0 : Fin (7 : ℕ)) ^ (2 : ℕ) -
              (2 : ℝ) * y (1 : Fin (7 : ℕ)) * y (0 : Fin (7 : ℕ)) * Real.cos (y (4 : Fin (7 : ℕ)))) ^
            (-3 / 2 : ℝ) -
          (1 : ℝ)) := @DominantFiveBody.tripleAngularMean_boundary_source_H
#print axioms DominantFiveBody.tripleAngularMean_boundary_source_H

example : ∀ (eps tau : ℝ) (v : DominantFiveBody.TripleGaps),
  DominantFiveBody.tripleSlowPoint eps tau v =
    ![DominantFiveBody.backgroundRadius eps, DominantFiveBody.backgroundRadius eps,
      DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
          DominantFiveBody.backgroundAngularScale eps tau *
        v (0 : Fin (2 : ℕ)),
      DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
          DominantFiveBody.backgroundAngularScale eps tau *
        v (1 : Fin (2 : ℕ)),
      tau * DominantFiveBody.Coorbital.h, DominantFiveBody.backgroundAngularScale eps tau * v (0 : Fin (2 : ℕ)),
      DominantFiveBody.backgroundAngularScale eps tau * v (1 : Fin (2 : ℕ))] := @DominantFiveBody.tripleSlowPoint_source_formula
#print axioms DominantFiveBody.tripleSlowPoint_source_formula

example : ∀ (eps tau Z z : ℝ),
  DominantFiveBody.nestedSlowPoint eps tau Z z =
    ![DominantFiveBody.backgroundRadius eps, DominantFiveBody.backgroundRadius eps,
      DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
          DominantFiveBody.backgroundAngularScale eps tau *
        Z,
      DominantFiveBody.backgroundRadius eps * DominantFiveBody.backgroundSlowK eps tau *
          DominantFiveBody.backgroundAngularScale eps tau *
        z,
      tau * DominantFiveBody.Coorbital.h, DominantFiveBody.backgroundAngularScale eps tau * Z,
      DominantFiveBody.backgroundAngularScale eps tau * z] := @DominantFiveBody.nestedSlowPoint_source_formula
#print axioms DominantFiveBody.nestedSlowPoint_source_formula

example : ∀ (eta alpha Z z : ℝ),
  (DominantFiveBody.tripleCenteringMatrix (DominantFiveBody.nestedTripleWeights eta alpha)).mulVec
      ![eta * z, Z - alpha * eta * z] =
    ![-((1 : ℝ) - eta ^ (3 : ℕ)) * Z - ((1 : ℝ) - alpha) * eta * z, -((1 : ℝ) - eta ^ (3 : ℕ)) * Z + alpha * eta * z,
      eta ^ (3 : ℕ) * Z] := @DominantFiveBody.nestedBoundaryScalarPositions_source_formula
#print axioms DominantFiveBody.nestedBoundaryScalarPositions_source_formula

example : ∀ (eta alpha Z z : ℝ),
  eta ^ (3 : ℕ) * alpha * (-((1 : ℝ) - eta ^ (3 : ℕ)) * Z - ((1 : ℝ) - alpha) * eta * z) +
        eta ^ (3 : ℕ) * ((1 : ℝ) - alpha) * (-((1 : ℝ) - eta ^ (3 : ℕ)) * Z + alpha * eta * z) +
      ((1 : ℝ) - eta ^ (3 : ℕ)) * (eta ^ (3 : ℕ) * Z) =
    (0 : ℝ) := @DominantFiveBody.nestedBoundaryScalarPositions_weighted_center
#print axioms DominantFiveBody.nestedBoundaryScalarPositions_weighted_center

example : ∀ (n : ℕ∞ω) (tau : ℝ) (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables)
  (q : DominantFiveBody.NestedChartParameters),
  |q (0 : Fin (4 : ℕ))| < (1 / 4 : ℝ) →
    ContDiffAt ℝ n branch
        (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ)))) →
      ContDiffAt ℝ n (DominantFiveBody.nestedSlowRootCandidate tau branch) q := @DominantFiveBody.nestedSlowRootCandidate_contDiffAt
#print axioms DominantFiveBody.nestedSlowRootCandidate_contDiffAt

example : ∀ (n : ℕ∞ω) (tau : ℝ) (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables)
  (base : DominantFiveBody.NestedChartParameters) (d : ℝ),
  ContDiffOn ℝ n branch (Metric.ball base d) →
    ContDiffOn ℝ n (DominantFiveBody.nestedSlowRootCandidate tau branch)
      {q : DominantFiveBody.NestedChartParameters |
        |q (0 : Fin (4 : ℕ))| < (1 / 4 : ℝ) ∧
          Dist.dist (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (q (2 : Fin (4 : ℕ))) (q (3 : Fin (4 : ℕ))))
              base <
            d} := @DominantFiveBody.nestedSlowRootCandidate_contDiffOn
#print axioms DominantFiveBody.nestedSlowRootCandidate_contDiffOn

example : ∀ (alpha0 z0 : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleWeights alpha0 →
    DominantFiveBody.TripleOrdered z0 →
      (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha0 z0 i = (0 : ℝ)) →
        ∀ (tau : ℝ),
          tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
            ∀ (eta r : ℝ),
              (0 : ℝ) < eta →
                (0 : ℝ) < r →
                  ∀ (branch : DominantFiveBody.TripleChartParameters → DominantFiveBody.TripleChartVariables),
                    (∀ (q : DominantFiveBody.TripleChartParameters),
                        Dist.dist q (DominantFiveBody.tripleBoundaryParameter alpha0) < eta →
                          ∀ (y : DominantFiveBody.TripleChartVariables),
                            Dist.dist y
                                  (DominantFiveBody.tripleUnitPoint (tau * DominantFiveBody.Coorbital.h)
                                    (DominantFiveBody.tripleGapMatrix.mulVec z0)) <
                                r →
                              (DominantFiveBody.tripleChartParameterRows q y =
                                  (0 : DominantFiveBody.TripleChartVariables) ↔
                                branch q = y)) →
                      ∃ (delta : ℝ),
                        (0 : ℝ) < delta ∧
                          ∀ (eps : ℝ) (alpha : DominantFiveBody.TripleVector),
                            |eps| < delta →
                              Dist.dist alpha alpha0 < delta →
                                ∑ i : DominantFiveBody.TripleLabel, alpha i = (1 : ℝ) →
                                  branch (DominantFiveBody.tripleParameter eps (0 : ℝ) alpha) =
                                    DominantFiveBody.tripleSlowPoint eps tau
                                      (DominantFiveBody.tripleChartAngularGaps
                                        (branch (DominantFiveBody.tripleParameter (0 : ℝ) (0 : ℝ) alpha))) := @DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness
#print axioms DominantFiveBody.tripleChart_zero_face_eq_slowPoint_of_local_uniqueness

example : ∀ (alpha0 tau omega : ℝ),
  tau = (1 : ℝ) ∨ tau = (-1 : ℝ) →
    ∀ (d r : ℝ),
      (0 : ℝ) < d →
        (0 : ℝ) < r →
          ∀ (branch : DominantFiveBody.NestedChartParameters → DominantFiveBody.NestedChartVariables),
            branch (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) =
                DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega →
              ContDiffOn ℝ ∞ branch (Metric.ball (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) d) →
                (∀ (q : DominantFiveBody.NestedChartParameters),
                    Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                      DominantFiveBody.NestedContinuationDomain (q, branch q)) →
                  (∀ (q : DominantFiveBody.NestedChartParameters),
                      Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                        DominantFiveBody.nestedChartParameterRows q (branch q) =
                          (0 : DominantFiveBody.NestedChartVariables)) →
                    (∀ (q : DominantFiveBody.NestedChartParameters),
                        Dist.dist q (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) < d →
                          ∀ (y : DominantFiveBody.NestedChartVariables),
                            Dist.dist y (DominantFiveBody.nestedBasePoint (tau * DominantFiveBody.Coorbital.h) omega) <
                                r →
                              (DominantFiveBody.nestedChartParameterRows q y =
                                  (0 : DominantFiveBody.NestedChartVariables) ↔
                                branch q = y)) →
                      ∃ (delta : ℝ),
                        (0 : ℝ) < delta ∧
                          delta ≤ d ∧
                            ∀ (eps eta alpha : ℝ),
                              Dist.dist (DominantFiveBody.nestedParameter eps (0 : ℝ) eta alpha)
                                    (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) (0 : ℝ) alpha0) <
                                  delta →
                                (0 : ℝ) < eta →
                                  alpha ∈ Set.Icc (0 : ℝ) (1 : ℝ) →
                                    branch (DominantFiveBody.nestedParameter eps (0 : ℝ) eta alpha) =
                                      DominantFiveBody.nestedSlowPoint eps tau
                                        (branch (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) eta alpha)
                                          (5 : Fin (7 : ℕ)))
                                        (branch (DominantFiveBody.nestedParameter (0 : ℝ) (0 : ℝ) eta alpha)
                                          (6 : Fin (7 : ℕ))) := @DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness
#print axioms DominantFiveBody.nestedChart_zero_face_eq_slowPoint_of_local_uniqueness

