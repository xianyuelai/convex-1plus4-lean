import DominantFiveBody.TripleSlowBoundary
import DominantFiveBody.NestedTripleCoordinates
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Actual Cartesian Taylor orders used in the zero-scale slow argument.
They follow from smooth signed divided differences and an exact cubic
mass/reaction identity, rather than from the boundary equation alone. -/
noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology Asymptotics
namespace DominantFiveBody
set_option maxHeartbeats 1000000

local instance slowTaylorPlaneAddCommGroup : AddCommGroup Plane :=
  (inferInstance : NormedAddCommGroup Plane).toAddCommGroup
local instance slowTaylorPlaneModule : Module ℝ Plane :=
  (inferInstance : NormedSpace ℝ Plane).toModule

def affinePolarPoint (R psi w z t : ℝ) : Plane := polarPoint (R + t * w) (psi + t * z)

def affinePolarDirection (R psi w z t : ℝ) : Plane :=
  w • polarPoint 1 psi +
    ((R + t * w) * z * Real.sinc (t * z / 2)) •
      quarterTurn (polarPoint 1 (psi + t * z / 2))

theorem affinePolarPoint_contDiff (n : ℕ∞ω) (R psi w z : ℝ) :
    ContDiff ℝ n (affinePolarPoint R psi w z) := by
  exact (polarPoint_contDiff n).comp (by fun_prop :
    ContDiff ℝ n (fun t : ℝ => (R + t * w, psi + t * z)))

theorem affinePolarDirection_contDiff (n : ℕ∞ω) (R psi w z : ℝ) :
    ContDiff ℝ n (affinePolarDirection R psi w z) := by
  have hrot : ContDiff ℝ n (fun t : ℝ => quarterTurn (polarPoint 1 (psi + t * z / 2))) :=
    quarterTurnLinear.toContinuousLinearMap.contDiff.comp
      ((polarPoint_contDiff n).comp (by fun_prop :
        ContDiff ℝ n (fun t : ℝ => ((1 : ℝ), psi + t * z / 2))))
  have hs : ContDiff ℝ n (fun t : ℝ => (R + t * w) * z * Real.sinc (t * z / 2)) := by fun_prop
  unfold affinePolarDirection
  exact contDiff_const.add (hs.smul hrot)

theorem affinePolarDirection_zero (R psi w z : ℝ) :
    affinePolarDirection R psi w z 0 = polarPointDerivative (R, psi) (w, z) := by
  rw [polarPointDerivative_apply, polarPoint_rotation_smul]
  simp only [affinePolarDirection, zero_mul, zero_div, add_zero, Real.sinc_zero,
    mul_one, smul_smul]
  congr 1
  ring

theorem affinePolarPoint_divided_identity (R psi w z t : ℝ) :
    affinePolarPoint R psi w z t - polarPoint R psi =
      t • affinePolarDirection R psi w z t := by
  rw [affinePolarPoint, polarPoint_smul_one (R + t * w), polarPoint_smul_one R psi]
  have he := polarUnit_sub_midpoint psi (psi + t * z)
  simp only [add_sub_cancel_left] at he
  have hm : (psi + (psi + t * z)) / 2 = psi + t * z / 2 := by ring
  rw [hm] at he
  calc
    _ = (R + t * w) • (polarPoint 1 (psi + t * z) - polarPoint 1 psi) +
      (t * w) • polarPoint 1 psi := by module
    _ = _ := by rw [he]; unfold affinePolarDirection; module

theorem affinePolarPoint_cartesian_Osquare (R psi w z : ℝ) :
    (fun t : ℝ => affinePolarPoint R psi w z t - polarPoint R psi -
      t • polarPointDerivative (R, psi) (w, z)) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have hD : DifferentiableAt ℝ (affinePolarDirection R psi w z) 0 :=
    ((affinePolarDirection_contDiff 1 R psi w z).differentiable (by norm_num)).differentiableAt
  have hO := hD.hasDerivAt.isBigO_sub
  simp only [sub_zero] at hO
  have hmul := (isBigO_refl (fun t : ℝ => t) (𝓝 (0 : ℝ))).smul hO
  convert! hmul using 1
  · funext t
    rw [affinePolarPoint_divided_identity, ← affinePolarDirection_zero]
    module
  · funext t
    simp only [smul_eq_mul, pow_two]

theorem tripleChartPoint_cartesian_Osquare (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) :
    (fun t : ℝ => tripleChartPoints t alpha y i.castSucc - polarPoint (y 1) (y 4) -
      t • tripleBoundaryDisplacement alpha y i) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have hb : tripleBoundaryDisplacement alpha y i = polarPointDerivative (y 1, y 4)
      (tripleChartRadialPositions alpha y i, tripleChartAngularPositions alpha y i) := by
    rw [tripleBoundaryDisplacement, polarPointDerivative_apply]
  have hp (t : ℝ) : tripleChartPoints t alpha y i.castSucc =
      affinePolarPoint (y 1) (y 4) (tripleChartRadialPositions alpha y i)
        (tripleChartAngularPositions alpha y i) t := by
    change polarPoint (tripleChartRadii t alpha y i.castSucc)
      (tripleChartAngles t alpha y i.castSucc) = _
    rw [tripleChartRadii_cluster, tripleChartAngles_cluster]
    rfl
  simpa only [hp, hb] using affinePolarPoint_cartesian_Osquare (y 1) (y 4)
    (tripleChartRadialPositions alpha y i) (tripleChartAngularPositions alpha y i)

theorem tripleChart_exteriorMass_Ocube (alpha : TripleVector) :
    (fun t : ℝ => tripleChartMass t alpha 3 - 1) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  have h := (isBigO_refl (fun t : ℝ => t ^ 3) (𝓝 (0 : ℝ))).const_mul_left (-1 : ℝ)
  change (fun t : ℝ => (1 - t ^ 3) - 1) =O[𝓝 0] (fun t : ℝ => t ^ 3)
  convert! h using 1
  funext t
  ring

theorem tripleChart_relativeAverage_cubic_identity (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) :
    relativeAverage (tripleChartMass t alpha) (tripleChartPoints t alpha y) - polarPoint (y 0) 0 =
      t ^ 3 • ((∑ i : TripleLabel, alpha i • tripleChartPoints t alpha y i.castSucc) -
        polarPoint (y 0) 0) := by
  unfold relativeAverage
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  change (t ^ 3 * alpha 0) • tripleChartPoints t alpha y 0 +
    (t ^ 3 * alpha 1) • tripleChartPoints t alpha y 1 +
    (t ^ 3 * alpha 2) • tripleChartPoints t alpha y 2 +
    (1 - t ^ 3) • tripleChartPoints t alpha y 3 - polarPoint (y 0) 0 =
    t ^ 3 • (alpha 0 • tripleChartPoints t alpha y 0 +
      alpha 1 • tripleChartPoints t alpha y 1 + alpha 2 • tripleChartPoints t alpha y 2 -
      polarPoint (y 0) 0)
  rw [show tripleChartPoints t alpha y 3 = polarPoint (y 0) 0 from rfl]
  module

theorem tripleChart_relativeAverage_Ocube (alpha : TripleVector) (y : TripleChartVariables) :
    (fun t : ℝ => relativeAverage (tripleChartMass t alpha) (tripleChartPoints t alpha y) -
      polarPoint (y 0) 0) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  have hq (i : TripleLabel) : Continuous (fun t : ℝ => tripleChartPoints t alpha y i.castSucc) := by
    have hp (t : ℝ) : tripleChartPoints t alpha y i.castSucc =
        affinePolarPoint (y 1) (y 4) (tripleChartRadialPositions alpha y i)
          (tripleChartAngularPositions alpha y i) t := by
      change polarPoint (tripleChartRadii t alpha y i.castSucc)
        (tripleChartAngles t alpha y i.castSucc) = _
      rw [tripleChartRadii_cluster, tripleChartAngles_cluster]
      rfl
    simpa only [hp] using (affinePolarPoint_contDiff 0 (y 1) (y 4)
      (tripleChartRadialPositions alpha y i) (tripleChartAngularPositions alpha y i)).continuous
  have hcoef : Continuous (fun t : ℝ =>
      (∑ i : TripleLabel, alpha i • tripleChartPoints t alpha y i.castSucc) - polarPoint (y 0) 0) :=
    (continuous_finsetSum Finset.univ (fun i _ => (hq i).const_smul (alpha i))).sub continuous_const
  have hbound : (fun t : ℝ =>
      (∑ i : TripleLabel, alpha i • tripleChartPoints t alpha y i.castSucc) - polarPoint (y 0) 0)
        =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    isBigO_const_of_tendsto hcoef.continuousAt (by norm_num)
  have hmul := (isBigO_refl (fun t : ℝ => t ^ 3) (𝓝 (0 : ℝ))).smul hbound
  simpa only [tripleChart_relativeAverage_cubic_identity, smul_eq_mul, mul_one] using hmul

theorem tripleChart_reaction_Ocube (eps : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    (fun t : ℝ => (eps / (1 + eps)) •
      (relativeAverage (tripleChartMass t alpha) (tripleChartPoints t alpha y) -
        polarPoint (y 0) 0)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  exact (tripleChart_relativeAverage_Ocube alpha y).const_smul_left (eps / (1 + eps))

def nestedActualBoundaryClusterDisplacement (eta alpha : ℝ) (y : NestedChartVariables)
    (i : TripleLabel) : Plane :=
  nestedCoordinates 1 eta alpha 0 (y 2) (y 3) i • polarPoint 1 (y 4) +
    nestedCoordinates 1 eta alpha 0 (y 5) (y 6) i • quarterTurn (polarPoint (y 1) (y 4))

theorem nestedBoundaryDisplacement_to_triple (eta alpha : ℝ) (y : NestedChartVariables)
    (i : TripleLabel) :
    nestedActualBoundaryClusterDisplacement eta alpha y i =
      tripleBoundaryDisplacement (nestedTripleWeights eta alpha) (nestedToTripleVariables eta alpha y) i := by
  rw [tripleBoundaryDisplacement, nestedToTriple_radialPositions, nestedToTriple_angularPositions]
  rfl

theorem nestedChartPoint_cartesian_Osquare (eta alpha : ℝ) (y : NestedChartVariables)
    (i : TripleLabel) :
    (fun t : ℝ => nestedChartPoints t eta alpha y i.castSucc - polarPoint (y 1) (y 4) -
      t • nestedActualBoundaryClusterDisplacement eta alpha y i) =O[𝓝 0] (fun t : ℝ => t ^ 2) := by
  have h := tripleChartPoint_cartesian_Osquare (nestedTripleWeights eta alpha)
    (nestedToTripleVariables eta alpha y) i
  simp only [nestedToTriple_points, ← nestedBoundaryDisplacement_to_triple] at h
  exact h

theorem nestedChart_reaction_Ocube (eps eta alpha : ℝ) (y : NestedChartVariables) :
    (fun t : ℝ => (eps / (1 + eps)) •
      (relativeAverage (nestedChartMass t eta alpha) (nestedChartPoints t eta alpha y) -
        polarPoint (y 0) 0)) =O[𝓝 0] (fun t : ℝ => t ^ 3) := by
  have h := tripleChart_reaction_Ocube eps (nestedTripleWeights eta alpha)
    (nestedToTripleVariables eta alpha y)
  simp only [nestedToTriple_mass, nestedToTriple_points] at h
  exact h

end DominantFiveBody
