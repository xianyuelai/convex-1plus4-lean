import DominantFiveBody.NestedExterior
import DominantFiveBody.PairBoundary

/-! Literal scalar target fields used in the pair and nested charts.
Source positions and the reaction vector are fixed in the target argument. -/
noncomputable section
namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem twoSourcePolarAngular_source_formula (p rc rd omega rho v : ℝ) :
    twoSourcePolarAngular p rc rd omega (rho, v) =
      rho * (p * rc * Real.sin (0 - v) *
          ((‖polarPoint rho v - polarPoint rc 0‖ ^ 3)⁻¹ - 1) +
        (1 - p) * rd * Real.sin (omega - v) *
          ((‖polarPoint rho v - polarPoint rd omega‖ ^ 3)⁻¹ - 1)) := by
  have he : twoSourceTargetField p rc rd omega (polarPoint rho v) =
      p • (newtonTargetField (polarPoint rc 0) (polarPoint rho v) - polarPoint rc 0) +
      (1 - p) • (newtonTargetField (polarPoint rd omega) (polarPoint rho v) - polarPoint rd omega) := by
    simp [twoSourceTargetField, smul_sub]
    abel
  unfold twoSourcePolarAngular
  rw [he, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hc := newtonTargetField_angular (1 : ℝ) rho rc v 0
  have hd := newtonTargetField_angular (1 : ℝ) rho rd v omega
  simp only [one_smul] at hc hd
  rw [hc, hd]
  ring

def nestedScalarH (eps t eta alpha : ℝ) (y : NestedChartVariables) (rho v : ℝ) : ℝ :=
  inner ℝ (nestedExteriorAngularField eps t eta alpha y (polarPoint rho v))
    (quarterTurn (polarPoint rho v))

def nestedScalarK (eps t eta alpha : ℝ) (y : NestedChartVariables) (rho v : ℝ) : ℝ :=
  rho - (rho ^ 2)⁻¹ + eps *
    inner ℝ (nestedExteriorRadialField eps t eta alpha y (polarPoint rho v)) (polarPoint 1 v)

theorem nestedScalarH_source_formula (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (rho v : ℝ) :
    nestedScalarH eps t eta alpha y rho v =
      -(1 - t ^ 3) * rho * y 0 * Real.sin v *
        ((‖polarPoint rho v - polarPoint (y 0) 0‖ ^ 3)⁻¹ - (1 + eps)⁻¹) := by
  have hp : nestedChartPoints t eta alpha y 3 = polarPoint (y 0) 0 := rfl
  have he : nestedExteriorAngularField eps t eta alpha y (polarPoint rho v) =
      (1 - t ^ 3) • (newtonTargetField (polarPoint (y 0) 0) (polarPoint rho v) -
        (1 + eps)⁻¹ • polarPoint (y 0) 0) := by
    simp only [nestedExteriorAngularField, nestedExteriorNewtonField, hp, smul_sub,
      smul_smul]
    module
  unfold nestedScalarH
  rw [he, real_inner_smul_left, newtonTargetField_angular]
  simp only [zero_sub, Real.sin_neg]
  ring

theorem nestedScalarK_source_formula (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (rho v : ℝ) :
    nestedScalarK eps t eta alpha y rho v =
      rho - (rho ^ 2)⁻¹ - eps * (1 - t ^ 3) *
        (rho - y 0 * Real.cos v) / ‖polarPoint rho v - polarPoint (y 0) 0‖ ^ 3 -
      eps * (1 + eps)⁻¹ * inner ℝ
        (relativeAverage (nestedChartMass t eta alpha) (nestedChartPoints t eta alpha y))
        (polarPoint 1 v) := by
  have hp : nestedChartPoints t eta alpha y 3 = polarPoint (y 0) 0 := rfl
  unfold nestedScalarK nestedExteriorRadialField nestedExteriorNewtonField
  rw [hp, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    newtonTargetField_radial]
  simp only [zero_sub, Real.cos_neg]
  ring

theorem nestedScalarFields_at_actual_targets (eps t eta alpha : ℝ)
    (y : NestedChartVariables) (i : Satellite) :
    nestedAngularExterior eps t eta alpha y i = nestedScalarH eps t eta alpha y
      (nestedChartRadii t eta alpha y i) (nestedChartAngles t eta alpha y i) ∧
    nestedRadialExterior eps t eta alpha y i = nestedScalarK eps t eta alpha y
      (nestedChartRadii t eta alpha y i) (nestedChartAngles t eta alpha y i) := by
  constructor <;> rfl

end DominantFiveBody
