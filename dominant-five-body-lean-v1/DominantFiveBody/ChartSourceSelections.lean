import DominantFiveBody.ChartExplicitDefinitions
import DominantFiveBody.PairBoundaryInvertibility

/-! The original fixed half-interval row choice and its quantitative
Jacobian coefficient. The row is selected by the limiting p0. -/
noncomputable section
open scoped Matrix
namespace DominantFiveBody
open Coorbital

def pairSourceKeepD (p0 : ℝ) : Bool := decide ((1 / 2 : ℝ) ≤ p0)
def pairSourceA0 (p0 : ℝ) : ℝ :=
  if (1 / 2 : ℝ) ≤ p0 then tripleD0 * p0 else -tripleD0 * (1 - p0)

theorem pairChartRows_half_interval_choice (eps t p alpha p0 : ℝ)
    (y : PairChartVariables) :
    let R := radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
      (pairChartAngles t alpha y)
    let T := angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
      (pairChartAngles t alpha y)
    pairChartPhysicalRows eps t p alpha (pairSourceKeepD p0) y =
      ![R 2, R 3, alpha * R 0 + (1 - alpha) * R 1, (R 1 - R 0) / t,
        T (if (1 / 2 : ℝ) ≤ p0 then 3 else 2), alpha * T 0 + (1 - alpha) * T 1,
        (T 1 - T 0) / t] := by
  simp [pairSourceKeepD, pairChartRows_formula_complete]

theorem pairChart_omitted_mass_lower_fixed_anchor (t p p0 alpha : ℝ)
    (ht : t ^ 3 ≤ 1 / 2) (hp : |p - p0| ≤ 1 / 4) :
    pairChartMass t p alpha (if (1 / 2 : ℝ) ≤ p0 then 2 else 3) ≥ 1 / 8 := by
  obtain ⟨hple, hpge⟩ := abs_le.mp hp
  split_ifs with h
  · change (1 - t ^ 3) * p ≥ 1 / 8
    nlinarith
  · change (1 - t ^ 3) * (1 - p) ≥ 1 / 8
    have hp0 : p0 < 1 / 2 := lt_of_not_ge h
    nlinarith

theorem pairSourceA0_abs_lower (p0 : ℝ) : |pairSourceA0 p0| ≥ 9 / 8 := by
  unfold pairSourceA0 tripleD0
  split_ifs with h
  · rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hp0 : p0 < 1 / 2 := lt_of_not_ge h
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith

theorem pairChartJacobian_exterior_source_a0 (p0 alpha psi z : ℝ)
    (hreg : PairChartRegular 0 0 alpha (pairUnitPoint h psi z)) :
    pairChartJacobian 0 0 p0 alpha (pairSourceKeepD p0) (pairUnitPoint h psi z)
      ![0, 0, 0, 0, 1, 0, 0] 4 = pairSourceA0 p0 := by
  have hh : 0 < h := by unfold h; positivity
  have hpi : |h| < Real.pi := by rw [abs_of_pos hh]; unfold h; linarith [Real.pi_pos]
  have hrow := pairChartJacobian_unit_exterior p0 alpha h psi z (pairSourceKeepD p0)
    hreg hh.ne' hpi ![0, 0, 0, 0, 1, 0, 0] rfl rfl rfl rfl
  refine hrow.trans ?_
  simp [pairSourceKeepD, pairSourceA0, abs_of_pos hh, kappa_h, tripleD0]
  split_ifs <;> ring

end DominantFiveBody
