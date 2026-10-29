import DominantFiveBody.ChartFormulaCoverage

/-! Complete entrywise source definitions, kept as theorem statements for
the independently auditable Section 5--6 coverage ledger. -/

noncomputable section
open scoped BigOperators Matrix ContDiff

namespace DominantFiveBody

theorem singleScaleWSq_formula_complete (R t wi wj zi zj : ℝ) :
    singleScaleWSq R t wi wj zi zj =
      (wi - wj) ^ 2 + (R + t * wi) * (R + t * wj) * (zi - zj) ^ 2 *
        Real.sinc (t * (zi - zj) / 2) ^ 2 := rfl

theorem pairChartWSq_formula_complete (t alpha : ℝ) (y : PairChartVariables) :
    pairChartWSq t alpha y = y 3 ^ 2 + pairChartRadii t alpha y 0 *
      pairChartRadii t alpha y 1 * y 6 ^ 2 * Real.sinc (t * y 6 / 2) ^ 2 := rfl

theorem pairChartRows_formula_complete (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) :
    let R := radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
      (pairChartAngles t alpha y)
    let T := angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
      (pairChartAngles t alpha y)
    pairChartPhysicalRows eps t p alpha keepD y =
      ![R 2, R 3, alpha * R 0 + (1 - alpha) * R 1, (R 1 - R 0) / t,
        T (if keepD then 3 else 2), alpha * T 0 + (1 - alpha) * T 1,
        (T 1 - T 0) / t] := rfl

theorem pairChart_omitted_mass_lower (t p : ℝ) (ht : t ^ 3 ≤ 1 / 2)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (if (1 / 2 : ℝ) ≤ p then (1 - t ^ 3) * p else (1 - t ^ 3) * (1 - p)) ≥ 1 / 4 := by
  split_ifs with h
  · nlinarith
  · have hh : p < 1 / 2 := lt_of_not_ge h
    nlinarith

theorem tripleReducedJacobian_formula_complete (alpha z : TripleVector) :
    tripleReducedJacobian alpha z = tripleGapMatrix * tripleScalarJacobian alpha z *
      tripleCenteringMatrix alpha := rfl

theorem nestedRows_formula_complete (t eta alpha : ℝ) (P : Satellite → ℝ) :
    nestedPairAverage alpha P = alpha * P 0 + (1 - alpha) * P 1 ∧
    nestedRowAverage eta alpha P = eta ^ 3 * (alpha * P 0 + (1 - alpha) * P 1) +
      (1 - eta ^ 3) * P 2 ∧
    nestedRowOuterDifference t alpha P = (P 2 - (alpha * P 0 + (1 - alpha) * P 1)) / t ∧
    nestedRowInnerDifference t eta P = (P 1 - P 0) / (t * eta) := ⟨rfl, rfl, rfl, rfl⟩

theorem nestedGaps_formula_complete (eta alpha : ℝ) (y : NestedChartVariables) :
    nestedOuterRadialGaps eta alpha y =
      ![y 2 + (1 - alpha) * eta * y 3, y 2 - alpha * eta * y 3] ∧
    nestedOuterAngularGaps eta alpha y =
      ![y 5 + (1 - alpha) * eta * y 6, y 5 - alpha * eta * y 6] := ⟨rfl, rfl⟩

theorem nestedInnerJ_formula_complete (eps t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerJ eps t eta alpha y =
      -eps * t * eta * alpha * (1 - alpha) *
        (nestedChartRadii t eta alpha y 0 + nestedChartRadii t eta alpha y 1) *
        singleScaleChi (t * eta) (y 6) * (nestedInnerW t eta alpha y ^ 3)⁻¹ := by
  rw [nestedInnerJ_factor]
  unfold nestedInnerJOverT
  ring

theorem nestedBasePoint_formula_complete (psi omega : ℝ) :
    nestedBasePoint psi omega = ![1, 1, 0, 0, psi,
      omega * tripleD0 ^ (-(1 : ℝ) / 3), (3 * tripleD0) ^ (-(1 : ℝ) / 3)] := rfl

theorem backgroundSpectrum_formula_complete (eps tau : ℝ) :
    backgroundMatrix eps tau =
      !![3 / (1 + eps) * (1 + eps / 4), 3 / (1 + eps) * (tau * Real.sqrt 3 * eps / 4);
        3 / (1 + eps) * (tau * Real.sqrt 3 * eps / 4), 3 / (1 + eps) * (3 * eps / 4)] ∧
    backgroundSlowD eps = 9 / (2 * (1 + eps) ^ 2 *
      (1 + Real.sqrt (1 - 3 * eps / (1 + eps) ^ 2))) ∧
    backgroundSlowLambda eps = eps * backgroundSlowD eps := ⟨rfl, rfl, rfl⟩

theorem backgroundSlow_formula_complete (eps tau : ℝ) :
    backgroundSlowK eps tau = -backgroundMatrix eps tau 0 1 /
      (backgroundMatrix eps tau 0 0 - backgroundSlowLambda eps) ∧
    backgroundSlowDirection eps tau = (Real.sqrt (1 + backgroundSlowK eps tau ^ 2))⁻¹ •
      (backgroundSlowK eps tau • backgroundE0 tau + quarterTurn (backgroundE0 tau)) ∧
    backgroundSlowLength eps = (tripleD0 / backgroundSlowD eps) ^ (1 / 3 : ℝ) ∧
    backgroundAngularScale eps tau = backgroundSlowLength eps /
      (backgroundRadius eps * Real.sqrt (1 + backgroundSlowK eps tau ^ 2)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem backgroundSlow_zero_complete (tau : ℝ) :
    backgroundSlowD 0 = tripleD0 ∧ backgroundSlowK 0 tau = 0 ∧
      backgroundSlowLength 0 = 1 ∧ backgroundAngularScale 0 tau = 1 := by
  norm_num [backgroundSlowD, backgroundDelta, tripleD0, backgroundSlowK,
    backgroundMatrix, backgroundSlowLambda, backgroundSlowLength,
    backgroundAngularScale, backgroundRadius]

theorem tripleSlowPoint_formula_complete (eps tau : ℝ) (g : TripleGaps) :
    tripleSlowPoint eps tau g =
      ![backgroundRadius eps, backgroundRadius eps,
        backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau * g 0,
        backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau * g 1,
        tau * Coorbital.h, backgroundAngularScale eps tau * g 0,
        backgroundAngularScale eps tau * g 1] := rfl

theorem nestedScalarPositions_formula_complete (eta alpha Z z : ℝ) :
    nestedTripleWeights eta alpha = ![eta ^ 3 * alpha, eta ^ 3 * (1 - alpha), 1 - eta ^ 3] ∧
    nestedCoordinates 1 eta alpha 0 Z z =
      ![-(1 - eta ^ 3) * Z - (1 - alpha) * eta * z,
        -(1 - eta ^ 3) * Z + alpha * eta * z, eta ^ 3 * Z] := by
  constructor
  · rfl
  · ext i
    fin_cases i <;> dsimp [nestedCoordinates] <;> ring

end DominantFiveBody
