import DominantFiveBody.BackgroundSlow
import DominantFiveBody.TripleBoundary

/-! # Actual exterior rows on the equilateral zero-scale background

The signed rationalized differences are identified with projections of
the actual probe-field derivative. No candidate root or vector equation
is supplied as an assumption.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

theorem backgroundExterior_ne_probeCenter (eps tau : ℝ) (he : 0 < 1 + eps)
    (ht : tau = 1 ∨ tau = -1) :
    backgroundExterior eps ≠ backgroundProbeCenter eps tau := by
  have hd : backgroundExterior eps - backgroundProbeCenter eps tau =
      backgroundRadius eps • backgroundW0 tau := by
    simp only [backgroundExterior, backgroundProbeCenter, backgroundW0, smul_sub]
  intro hq
  have hn : ‖backgroundExterior eps - backgroundProbeCenter eps tau‖ = backgroundRadius eps := by
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (backgroundRadius_pos eps he),
      backgroundW0_norm tau ht, mul_one]
  rw [hq, sub_self, norm_zero] at hn
  linarith [backgroundRadius_pos eps he]

theorem backgroundExteriorProbeField_value (eps tau : ℝ) (he : 0 < 1 + eps)
    (ht : tau = 1 ∨ tau = -1) :
    newtonTargetField (backgroundExterior eps) (backgroundProbeCenter eps tau) -
      (1 + eps)⁻¹ • backgroundExterior eps =
        -(backgroundRadius eps ^ 3)⁻¹ • backgroundProbeCenter eps tau := by
  have hd : backgroundExterior eps - backgroundProbeCenter eps tau =
      backgroundRadius eps • backgroundW0 tau := by
    simp only [backgroundExterior, backgroundProbeCenter, backgroundW0, smul_sub]
  have hn : ‖backgroundExterior eps - backgroundProbeCenter eps tau‖ = backgroundRadius eps := by
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (backgroundRadius_pos eps he),
      backgroundW0_norm tau ht, mul_one]
  unfold newtonTargetField
  rw [hn, ← backgroundRadius_cube eps he.le]
  module

theorem backgroundOperator_apply_newtonDerivative (eps tau : ℝ) (v : Plane)
    (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1) :
    backgroundOperator eps tau v =
      (1 - (backgroundRadius eps ^ 3)⁻¹) • v +
      (3 * (backgroundRadius eps ^ 3)⁻¹ * inner ℝ (backgroundE0 tau) v) •
        backgroundE0 tau +
      eps • newtonTargetDerivative (backgroundExterior eps) (backgroundProbeCenter eps tau) v := by
  have hd : backgroundExterior eps - backgroundProbeCenter eps tau =
      backgroundRadius eps • backgroundW0 tau := by
    simp only [backgroundExterior, backgroundProbeCenter, backgroundW0, smul_sub]
  have hdp := newtonTargetDerivative_scaled_unit (backgroundExterior eps)
    (backgroundProbeCenter eps tau) (backgroundW0 tau) (backgroundRadius eps)
    (backgroundRadius_pos eps he) (backgroundW0_norm tau ht) hd
  rw [hdp, backgroundRadius_cube eps he.le, backgroundOperator_apply]
  ext k
  simp only [sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, ContinuousLinearMap.id_apply, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  have he0 := ne_of_gt he
  field_simp
  ring

theorem backgroundQuarterTurn_inner_skew (v w : Plane) :
    inner ℝ v (quarterTurn w) = -inner ℝ (quarterTurn v) w := by
  simp [plane_inner_coordinates, quarterTurn, point]

theorem tripleSlow_cluster_point (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (hc : y 1 = backgroundRadius eps) (hpsi : y 4 = tau * Coorbital.h)
    (i : TripleLabel) : tripleChartPoints 0 alpha y i.castSucc = backgroundProbeCenter eps tau := by
  rw [tripleChartPoints_zero_cluster, hc, hpsi, polarPoint_smul_one]
  rfl

theorem tripleSlow_exterior_point (eps : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (hp : y 0 = backgroundRadius eps) :
    tripleChartPoints 0 alpha y 3 = backgroundExterior eps := by
  rw [tripleChartPoints_zero_exterior, hp, polarPoint_smul_one]
  rfl

theorem tripleSlow_relativeAverage (eps : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (hp : y 0 = backgroundRadius eps) :
    relativeAverage (tripleChartMass 0 alpha) (tripleChartPoints 0 alpha y) =
      backgroundExterior eps := by
  simp [relativeAverage, tripleChartMass, Fin.sum_univ_four, tripleSlow_exterior_point eps alpha y hp]

theorem tripleSlow_exterior_fields (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1)
    (hp : y 0 = backgroundRadius eps) (hc : y 1 = backgroundRadius eps)
    (hpsi : y 4 = tau * Coorbital.h) (i : TripleLabel) :
    tripleExteriorRadialField eps 0 alpha y (tripleChartPoints 0 alpha y i.castSucc) =
        -(backgroundRadius eps ^ 3)⁻¹ • backgroundProbeCenter eps tau ∧
      tripleExteriorAngularField eps 0 alpha y (tripleChartPoints 0 alpha y i.castSucc) =
        -(backgroundRadius eps ^ 3)⁻¹ • backgroundProbeCenter eps tau := by
  rw [tripleSlow_cluster_point eps tau alpha y hc hpsi i]
  constructor
  · unfold tripleExteriorRadialField tripleExteriorNewtonField
    rw [tripleSlow_relativeAverage eps alpha y hp, tripleSlow_exterior_point eps alpha y hp]
    simpa [tripleChartMass] using backgroundExteriorProbeField_value eps tau he ht
  · unfold tripleExteriorAngularField tripleExteriorNewtonField
    rw [tripleSlow_exterior_point eps alpha y hp]
    simpa [tripleChartMass] using backgroundExteriorProbeField_value eps tau he ht

theorem tripleSlow_newton_difference (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1)
    (hp : y 0 = backgroundRadius eps) (hc : y 1 = backgroundRadius eps)
    (hpsi : y 4 = tau * Coorbital.h) (i j : TripleLabel) :
    tripleExteriorNewtonDifference 0 alpha y i j =
      newtonTargetDerivative (backgroundExterior eps) (backgroundProbeCenter eps tau)
        (triplePointDirection 0 alpha y i j) := by
  unfold tripleExteriorNewtonDifference
  rw [tripleSlow_exterior_point eps alpha y hp, tripleSlow_cluster_point eps tau alpha y hc hpsi i,
    tripleSlow_cluster_point eps tau alpha y hc hpsi j,
    dividedNewtonTargetField_diagonal _ _ _ (backgroundExterior_ne_probeCenter eps tau he ht),
    (newtonTargetField_hasFDerivAt _ _ (backgroundExterior_ne_probeCenter eps tau he ht)).fderiv]
  simp [tripleChartMass]

theorem tripleSlow_point_direction (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (hc : y 1 = backgroundRadius eps) (hpsi : y 4 = tau * Coorbital.h)
    (i j : TripleLabel) : triplePointDirection 0 alpha y i j =
      (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i) • backgroundE0 tau +
      (backgroundRadius eps * (tripleChartAngularPositions alpha y j -
        tripleChartAngularPositions alpha y i)) • quarterTurn (backgroundE0 tau) := by
  rw [triplePointDirection_at_zero, polarPointDerivative_apply, hc, hpsi,
    polarPoint_rotation_smul]
  simp only [backgroundE0, smul_smul]
  congr 1
  ring

theorem tripleSlow_radial_projection (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (hc : y 1 = backgroundRadius eps) (hpsi : y 4 = tau * Coorbital.h)
    (i j : TripleLabel) :
    inner ℝ (triplePointDirection 0 alpha y i j) (backgroundE0 tau) =
      tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i := by
  rw [tripleSlow_point_direction eps tau alpha y hc hpsi i j]
  have horth : inner ℝ (quarterTurn (backgroundE0 tau)) (backgroundE0 tau) = 0 := by
    rw [real_inner_comm, quarterTurn_inner_self]
  simp only [inner_add_left, real_inner_smul_left, backgroundE0_inner_self,
    horth, mul_one, mul_zero, add_zero]

theorem tripleSlow_angular_projection (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (hc : y 1 = backgroundRadius eps) (hpsi : y 4 = tau * Coorbital.h)
    (i j : TripleLabel) :
    inner ℝ (triplePointDirection 0 alpha y i j) (quarterTurn (backgroundE0 tau)) =
      backgroundRadius eps * (tripleChartAngularPositions alpha y j -
        tripleChartAngularPositions alpha y i) := by
  rw [tripleSlow_point_direction eps tau alpha y hc hpsi i j]
  simp only [inner_add_left, real_inner_smul_left, quarterTurn_inner_self,
    quarterTurn_inner_quarterTurn, backgroundE0_inner_self, mul_one, mul_zero, zero_add]

theorem tripleRadialExteriorDifference_background (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1)
    (hp : y 0 = backgroundRadius eps) (hc : y 1 = backgroundRadius eps)
    (hpsi : y 4 = tau * Coorbital.h) (i j : TripleLabel) :
    tripleRadialExteriorDifference eps 0 alpha y i j =
      inner ℝ (backgroundOperator eps tau (triplePointDirection 0 alpha y i j))
        (backgroundE0 tau) := by
  have hf := (tripleSlow_exterior_fields eps tau alpha y he ht hp hc hpsi i).1
  have hd := tripleSlow_newton_difference eps tau alpha y he ht hp hc hpsi i j
  have hv := tripleSlow_radial_projection eps tau alpha y hc hpsi i j
  have hv' : inner ℝ (backgroundE0 tau) (triplePointDirection 0 alpha y i j) =
      tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i := by
    rw [real_inner_comm]
    exact hv
  unfold tripleRadialExteriorDifference
  rw [tripleChartRadii_cluster, tripleChartRadii_cluster, tripleChartAngles_cluster,
    tripleUnitDirection_at_zero]
  simp only [singleScaleRadius, singleScaleAngle, zero_mul, add_zero, hc, hpsi]
  rw [hf, hd, backgroundOperator_apply_newtonDerivative eps tau _ he ht]
  rw [show polarPoint 1 (tau * Coorbital.h) = backgroundE0 tau from rfl]
  simp only [backgroundProbeCenter, inner_add_left, real_inner_smul_left,
    real_inner_smul_right, hv, hv', backgroundE0_inner_self,
    quarterTurn_inner_self, mul_one, mul_zero, add_zero]
  have ha := ne_of_gt (backgroundRadius_pos eps he)
  field_simp
  ring

theorem tripleAngularExteriorDifference_background (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1)
    (hp : y 0 = backgroundRadius eps) (hc : y 1 = backgroundRadius eps)
    (hpsi : y 4 = tau * Coorbital.h) (i j : TripleLabel) :
    eps * tripleAngularExteriorDifference eps 0 alpha y i j =
      inner ℝ (backgroundOperator eps tau (triplePointDirection 0 alpha y i j))
        (quarterTurn (backgroundProbeCenter eps tau)) := by
  have hf := (tripleSlow_exterior_fields eps tau alpha y he ht hp hc hpsi i).2
  have hd := tripleSlow_newton_difference eps tau alpha y he ht hp hc hpsi i j
  have hv := tripleSlow_angular_projection eps tau alpha y hc hpsi i j
  have hq : quarterTurn (backgroundProbeCenter eps tau) =
      backgroundRadius eps • quarterTurn (backgroundE0 tau) := by
    exact quarterTurnLinear.map_smul (backgroundRadius eps) (backgroundE0 tau)
  have hv' : inner ℝ (quarterTurn (backgroundE0 tau)) (triplePointDirection 0 alpha y i j) =
      backgroundRadius eps * (tripleChartAngularPositions alpha y j -
        tripleChartAngularPositions alpha y i) := by
    rw [real_inner_comm]
    exact hv
  have hcross : inner ℝ (backgroundProbeCenter eps tau)
      (quarterTurn (triplePointDirection 0 alpha y i j)) =
        -(backgroundRadius eps ^ 2 * (tripleChartAngularPositions alpha y j -
          tripleChartAngularPositions alpha y i)) := by
    rw [backgroundQuarterTurn_inner_skew, hq, real_inner_smul_left, hv']
    ring
  unfold tripleAngularExteriorDifference
  rw [hf, hd, tripleSlow_cluster_point eps tau alpha y hc hpsi j,
    backgroundOperator_apply_newtonDerivative eps tau _ he ht, hq]
  simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right,
    hcross, hv, quarterTurn_inner_self,
    mul_zero, add_zero]
  have he0 := ne_of_gt he
  have ha := ne_of_gt (backgroundRadius_pos eps he)
  have ha3 := backgroundRadius_cube eps he.le
  field_simp
  nlinarith [congrArg (fun x => x *
    (tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i)) ha3]

theorem tripleRadialExterior_background_zero (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1)
    (hp : y 0 = backgroundRadius eps) (hc : y 1 = backgroundRadius eps)
    (hpsi : y 4 = tau * Coorbital.h) (i : TripleLabel) :
    tripleRadialExterior eps 0 alpha y i = 0 := by
  rw [tripleRadialExterior, (tripleSlow_exterior_fields eps tau alpha y he ht hp hc hpsi i).1,
    tripleChartRadii_cluster, tripleChartAngles_cluster]
  simp only [singleScaleRadius, singleScaleAngle, zero_mul, add_zero, hc, hpsi,
    backgroundProbeCenter, real_inner_smul_left]
  rw [show polarPoint 1 (tau * Coorbital.h) = backgroundE0 tau from rfl,
    backgroundE0_inner_self, mul_one]
  have ha := ne_of_gt (backgroundRadius_pos eps he)
  have ha3 := backgroundRadius_cube eps he.le
  field_simp
  nlinarith

theorem tripleAngularExterior_background_zero (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1)
    (hp : y 0 = backgroundRadius eps) (hc : y 1 = backgroundRadius eps)
    (hpsi : y 4 = tau * Coorbital.h) (i : TripleLabel) :
    tripleAngularExterior eps 0 alpha y i = 0 := by
  rw [tripleAngularExterior, (tripleSlow_exterior_fields eps tau alpha y he ht hp hc hpsi i).2,
    tripleSlow_cluster_point eps tau alpha y hc hpsi i]
  have hq : quarterTurn (backgroundProbeCenter eps tau) =
      backgroundRadius eps • quarterTurn (backgroundE0 tau) :=
    quarterTurnLinear.map_smul _ _
  rw [hq, backgroundProbeCenter, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, quarterTurn_inner_self, mul_zero, mul_zero, mul_zero]

theorem tripleRadialMean_background_zero (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1)
    (hp : y 0 = backgroundRadius eps) (hc : y 1 = backgroundRadius eps)
    (hpsi : y 4 = tau * Coorbital.h) : tripleRadialMean eps 0 alpha y = 0 := by
  simp [tripleRadialMean, tripleRadialExterior_background_zero eps tau alpha y he ht hp hc hpsi,
    tripleInternalRadialMean, tripleInternalRadial]

theorem tripleAngularMean_background_zero (eps tau : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1)
    (hp : y 0 = backgroundRadius eps) (hc : y 1 = backgroundRadius eps)
    (hpsi : y 4 = tau * Coorbital.h) : tripleAngularMean eps 0 alpha y = 0 := by
  simp [tripleAngularMean, tripleAngularExterior_background_zero eps tau alpha y he ht hp hc hpsi,
    tripleInternalAngularMean, tripleInternalAngular]

theorem tripleExteriorRadialRow_background_zero (eps : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (he : 0 < 1 + eps) (hp : y 0 = backgroundRadius eps) :
    radialResidual eps (tripleChartMass 0 alpha) (tripleChartRadii 0 alpha y)
      (tripleChartAngles 0 alpha y) 3 = 0 := by
  rw [radialResidual, Finset.sum_erase_eq_sub (Finset.mem_univ (3 : Satellite))]
  rw [show polarSatellites (tripleChartRadii 0 alpha y) (tripleChartAngles 0 alpha y) =
    tripleChartPoints 0 alpha y from rfl, tripleSlow_relativeAverage eps alpha y hp]
  simp [tripleChartMass, tripleChartRadii, tripleChartAngles, Fin.sum_univ_four,
    hp,
    backgroundExterior, real_inner_smul_left, polarPoint_norm]
  have ha := ne_of_gt (backgroundRadius_pos eps he)
  have he0 := ne_of_gt he
  have ha3 := backgroundRadius_cube eps he.le
  field_simp
  nlinarith

end DominantFiveBody
