import DominantFiveBody.TripleScalarPotentialMinimizer
open scoped BigOperators ContDiff Topology
universe u_1 u_2 u_3 u_4
set_option linter.unusedVariables false
example : ∀ (alpha z : DominantFiveBody.TripleVector),
  DominantFiveBody.tripleScalarPotential alpha z =
    DominantFiveBody.tripleD0 / 2 * ∑ i : DominantFiveBody.TripleLabel, alpha i * z i ^ 2 +
      ∑ p ∈ DominantFiveBody.tripleScalarPairs, alpha p.1 * alpha p.2 / |z p.1 - z p.2| := @DominantFiveBody.tripleScalarPotential_source_formula
#print axioms DominantFiveBody.tripleScalarPotential_source_formula

example : IsOpen DominantFiveBody.tripleScalarChamber := @DominantFiveBody.tripleScalarChamber_isOpen
#print axioms DominantFiveBody.tripleScalarChamber_isOpen

example : Convex ℝ DominantFiveBody.tripleScalarChamber := @DominantFiveBody.tripleScalarChamber_convex
#print axioms DominantFiveBody.tripleScalarChamber_convex

example : ∀ (alpha z : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleOrdered z →
    DominantFiveBody.tripleScalarPotential alpha z =
      DominantFiveBody.tripleD0 / 2 * ∑ i : DominantFiveBody.TripleLabel, alpha i * z i ^ 2 +
        (alpha 0 * alpha 1 / (z 1 - z 0) + alpha 0 * alpha 2 / (z 2 - z 0) + alpha 1 * alpha 2 / (z 2 - z 1)) := @DominantFiveBody.tripleScalarPotential_ordered_formula
#print axioms DominantFiveBody.tripleScalarPotential_ordered_formula

example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 ≤ alpha i) → 0 ≤ DominantFiveBody.tripleScalarPotential alpha z := @DominantFiveBody.tripleScalarPotential_nonneg
#print axioms DominantFiveBody.tripleScalarPotential_nonneg

example : ∀ (alpha x y : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    x ≠ y →
      ∀ (a b : ℝ),
        0 < a →
          0 < b →
            a + b = 1 →
              DominantFiveBody.tripleQuadraticPotential alpha (a • x + b • y) <
                a * DominantFiveBody.tripleQuadraticPotential alpha x +
                  b * DominantFiveBody.tripleQuadraticPotential alpha y := @DominantFiveBody.tripleQuadraticPotential_strictJensen
#print axioms DominantFiveBody.tripleQuadraticPotential_strictJensen

example : ∀ (x y a b : ℝ), 0 < x → 0 < y → 0 ≤ a → 0 ≤ b → a + b = 1 → (a * x + b * y)⁻¹ ≤ a * x⁻¹ + b * y⁻¹ := @DominantFiveBody.inverse_positive_gap_convex
#print axioms DominantFiveBody.inverse_positive_gap_convex

example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    StrictConvexOn ℝ DominantFiveBody.tripleScalarChamber (DominantFiveBody.tripleScalarPotential alpha) := @DominantFiveBody.tripleScalarPotential_strictConvexOn
#print axioms DominantFiveBody.tripleScalarPotential_strictConvexOn

example : ∀ (alpha z : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleOrdered z → ContinuousAt (DominantFiveBody.tripleScalarPotential alpha) z := @DominantFiveBody.tripleScalarPotential_continuousAt
#print axioms DominantFiveBody.tripleScalarPotential_continuousAt

example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    ∀ (C : ℝ),
      0 < C →
        DominantFiveBody.tripleScalarPotential alpha z ≤ C →
          ∀ (i : DominantFiveBody.TripleLabel), |z i| ≤ 1 + 2 * C / (DominantFiveBody.tripleD0 * alpha i) := @DominantFiveBody.tripleScalarPotential_sublevel_coordinate_bounds
#print axioms DominantFiveBody.tripleScalarPotential_sublevel_coordinate_bounds

example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    DominantFiveBody.TripleOrdered z →
      ∀ (C : ℝ),
        0 < C →
          DominantFiveBody.tripleScalarPotential alpha z ≤ C →
            ∀ (i j : DominantFiveBody.TripleLabel), i < j → alpha i * alpha j / C ≤ z j - z i := @DominantFiveBody.tripleScalarPotential_sublevel_gap_bounds
#print axioms DominantFiveBody.tripleScalarPotential_sublevel_gap_bounds

example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    ∀ (c : ℝ),
      IsCompact
        {z : DominantFiveBody.TripleVector |
          DominantFiveBody.TripleOrdered z ∧ DominantFiveBody.tripleScalarPotential alpha z ≤ c} := @DominantFiveBody.tripleScalarPotential_compact_sublevel
#print axioms DominantFiveBody.tripleScalarPotential_compact_sublevel

example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    IsProperMap fun (z : { z : DominantFiveBody.TripleVector // DominantFiveBody.TripleOrdered z }) =>
      DominantFiveBody.tripleScalarPotential alpha (↑z : DominantFiveBody.TripleVector) := @DominantFiveBody.tripleScalarPotential_isProperMap
#print axioms DominantFiveBody.tripleScalarPotential_isProperMap

example : ∀ (alpha z : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleOrdered z →
    HasFDerivAt (DominantFiveBody.tripleScalarPotential alpha)
      (DominantFiveBody.tripleScalarPotentialDerivative alpha z) z := @DominantFiveBody.tripleScalarPotential_hasFDerivAt
#print axioms DominantFiveBody.tripleScalarPotential_hasFDerivAt

example : ∀ (alpha z v : DominantFiveBody.TripleVector),
  DominantFiveBody.TripleOrdered z →
    (fderiv ℝ (DominantFiveBody.tripleScalarPotential alpha) z : DominantFiveBody.TripleVector → ℝ) v =
      ∑ i : DominantFiveBody.TripleLabel, alpha i * DominantFiveBody.tripleScalarResidual alpha z i * v i := @DominantFiveBody.tripleScalarPotential_fderiv_apply
#print axioms DominantFiveBody.tripleScalarPotential_fderiv_apply

example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    DominantFiveBody.TripleOrdered z →
      ∀ (i : DominantFiveBody.TripleLabel),
        (fderiv ℝ (DominantFiveBody.tripleScalarPotential alpha) z : DominantFiveBody.TripleVector → ℝ)
              (Pi.single i 1) /
            alpha i =
          DominantFiveBody.tripleScalarResidual alpha z i := @DominantFiveBody.tripleScalarPotential_divided_gradient
#print axioms DominantFiveBody.tripleScalarPotential_divided_gradient

example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    DominantFiveBody.TripleOrdered z →
      (fderiv ℝ (DominantFiveBody.tripleScalarPotential alpha) z = 0 ↔
        ∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha z i = 0) := @DominantFiveBody.tripleScalarPotential_critical_iff_root
#print axioms DominantFiveBody.tripleScalarPotential_critical_iff_root

example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    ∃ (z : DominantFiveBody.TripleVector),
      DominantFiveBody.TripleOrdered z ∧
        IsMinOn (DominantFiveBody.tripleScalarPotential alpha) DominantFiveBody.tripleScalarChamber z := @DominantFiveBody.tripleScalarPotential_exists_minimizer
#print axioms DominantFiveBody.tripleScalarPotential_exists_minimizer

example : ∀ (alpha z : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    DominantFiveBody.TripleOrdered z →
      fderiv ℝ (DominantFiveBody.tripleScalarPotential alpha) z = 0 →
        IsMinOn (DominantFiveBody.tripleScalarPotential alpha) DominantFiveBody.tripleScalarChamber z := @DominantFiveBody.tripleScalarPotential_critical_isMinOn
#print axioms DominantFiveBody.tripleScalarPotential_critical_isMinOn

example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    ∃! z : DominantFiveBody.TripleVector,
      DominantFiveBody.TripleOrdered z ∧
        ∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha z i = 0 := @DominantFiveBody.tripleScalar_potential_root_existsUnique
#print axioms DominantFiveBody.tripleScalar_potential_root_existsUnique

example : ∀ (alpha : DominantFiveBody.TripleVector),
  (∀ (i : DominantFiveBody.TripleLabel), 0 < alpha i) →
    ∃! z : DominantFiveBody.TripleVector,
      DominantFiveBody.TripleOrdered z ∧
        (∀ (i : DominantFiveBody.TripleLabel), DominantFiveBody.tripleScalarResidual alpha z i = 0) ∧
          ∑ i : DominantFiveBody.TripleLabel, alpha i * z i = 0 := @DominantFiveBody.tripleScalar_potential_root_existsUnique_centered
#print axioms DominantFiveBody.tripleScalar_potential_root_existsUnique_centered

