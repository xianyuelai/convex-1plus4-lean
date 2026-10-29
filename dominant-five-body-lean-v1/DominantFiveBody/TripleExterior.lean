import DominantFiveBody.TripleInternal
import DominantFiveBody.PairRegularization

/-! # Actual exterior interaction for a regular triple

All three probe equations use the one exterior source, with actual
target differences rationalized before setting the signed scale to zero.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff

namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem triple_sum_erase_split (f : Satellite → ℝ) (i : TripleLabel) :
    ∑ j ∈ Finset.univ.erase i.castSucc, f j =
      (∑ j ∈ Finset.univ.erase i, f j.castSucc) + f 3 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i.castSucc),
    Finset.sum_erase_eq_sub (Finset.mem_univ i), Fin.sum_univ_four, Fin.sum_univ_three]
  fin_cases i <;> simp <;> ring

def tripleExteriorNewtonField (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (target : Plane) : Plane :=
  tripleChartMass t alpha 3 • newtonTargetField (tripleChartPoints t alpha y 3) target

def tripleExteriorNewtonDifference (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) : Plane :=
  tripleChartMass t alpha 3 • dividedNewtonTargetField (tripleChartPoints t alpha y 3)
    (tripleChartPoints t alpha y i.castSucc) (tripleChartPoints t alpha y j.castSucc)
    (triplePointDirection t alpha y i j)

def tripleExteriorRadialField (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (target : Plane) : Plane :=
  tripleExteriorNewtonField t alpha y target - (1 + eps)⁻¹ •
    relativeAverage (tripleChartMass t alpha) (tripleChartPoints t alpha y)

def tripleExteriorAngularField (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (target : Plane) : Plane :=
  tripleExteriorNewtonField t alpha y target - (1 + eps)⁻¹ •
    (tripleChartMass t alpha 3 • tripleChartPoints t alpha y 3)

def tripleRadialExterior (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : ℝ :=
  tripleChartRadii t alpha y i.castSucc - (tripleChartRadii t alpha y i.castSucc ^ 2)⁻¹ +
    eps * inner ℝ (tripleExteriorRadialField eps t alpha y (tripleChartPoints t alpha y i.castSucc))
      (polarPoint 1 (tripleChartAngles t alpha y i.castSucc))

def tripleAngularExterior (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : ℝ :=
  inner ℝ (tripleExteriorAngularField eps t alpha y (tripleChartPoints t alpha y i.castSucc))
    (quarterTurn (tripleChartPoints t alpha y i.castSucc))

theorem tripleExteriorNewtonDifference_identity (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) (ht : t ≠ 0)
    (hi : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y i.castSucc)
    (hj : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y j.castSucc) :
    tripleExteriorNewtonField t alpha y (tripleChartPoints t alpha y j.castSucc) -
      tripleExteriorNewtonField t alpha y (tripleChartPoints t alpha y i.castSucc) =
        t • tripleExteriorNewtonDifference t alpha y i j := by
  have hg := triplePointDirection_identity t alpha y i j
  have h := dividedNewtonTargetField_eq (tripleChartPoints t alpha y 3)
    (tripleChartPoints t alpha y i.castSucc) (tripleChartPoints t alpha y j.castSucc)
    (triplePointDirection t alpha y i j) t ht hi hj hg
  unfold tripleExteriorNewtonField tripleExteriorNewtonDifference
  rw [h, smul_smul, smul_smul]
  have hc : t * tripleChartMass t alpha 3 * t⁻¹ = tripleChartMass t alpha 3 := by field_simp
  rw [hc, smul_sub]

theorem tripleExteriorRadialField_difference_identity (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) (ht : t ≠ 0)
    (hi : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y i.castSucc)
    (hj : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y j.castSucc) :
    tripleExteriorRadialField eps t alpha y (tripleChartPoints t alpha y j.castSucc) -
      tripleExteriorRadialField eps t alpha y (tripleChartPoints t alpha y i.castSucc) =
        t • tripleExteriorNewtonDifference t alpha y i j := by
  unfold tripleExteriorRadialField
  rw [sub_sub_sub_cancel_right, tripleExteriorNewtonDifference_identity t alpha y i j ht hi hj]

theorem tripleExteriorAngularField_difference_identity (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) (ht : t ≠ 0)
    (hi : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y i.castSucc)
    (hj : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y j.castSucc) :
    tripleExteriorAngularField eps t alpha y (tripleChartPoints t alpha y j.castSucc) -
      tripleExteriorAngularField eps t alpha y (tripleChartPoints t alpha y i.castSucc) =
        t • tripleExteriorNewtonDifference t alpha y i j := by
  unfold tripleExteriorAngularField
  rw [sub_sub_sub_cancel_right, tripleExteriorNewtonDifference_identity t alpha y i j ht hi hj]

theorem tripleRadialExterior_recovery (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) (ht : 0 < t)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq t alpha y i j) :
    radialResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
      (tripleChartAngles t alpha y) i.castSucc =
        tripleRadialExterior eps t alpha y i + tripleInternalRadial eps t alpha y i := by
  rw [radialResidual_newton_projection, triple_sum_erase_split]
  rw [tripleInternalRadial_eq_physical eps t alpha y i ht hW]
  unfold tripleRadialExterior tripleExteriorRadialField tripleExteriorNewtonField
  simp only [inner_sub_left, real_inner_smul_left]
  have hsum : (∑ j ∈ Finset.univ.erase i,
      eps * (tripleChartMass t alpha j.castSucc * inner ℝ
        (newtonTargetField (tripleChartPoints t alpha y j.castSucc)
          (tripleChartPoints t alpha y i.castSucc))
        (polarPoint 1 (tripleChartAngles t alpha y i.castSucc)))) =
      ∑ j ∈ Finset.univ.erase i, -eps * tripleChartMass t alpha j.castSucc *
        (tripleChartRadii t alpha y i.castSucc - tripleChartRadii t alpha y j.castSucc *
          Real.cos (tripleChartAngles t alpha y i.castSucc - tripleChartAngles t alpha y j.castSucc)) /
        satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc ^ 3 := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [tripleChartPoints, polarSatellites, newtonTargetField_radial, satelliteDistance]
    rw [Real.cos_sub, Real.cos_sub]
    ring
  simp only [tripleChartPoints] at hsum
  rw [mul_add, Finset.mul_sum, hsum]
  unfold tripleChartPoints
  ring

theorem tripleAngularExterior_recovery (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) (ht : 0 < t)
    (hW : ∀ j, j ≠ i → 0 < tripleChartWSq t alpha y i j) (heps : 1 + eps ≠ 0) :
    angularResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
      (tripleChartAngles t alpha y) i.castSucc =
        tripleAngularExterior eps t alpha y i + tripleInternalAngular eps t alpha y i := by
  rw [angularResidual_newton_projection, triple_sum_erase_split,
    tripleInternalAngular_eq_physical eps t alpha y i ht hW heps]
  unfold tripleAngularExterior tripleExteriorAngularField tripleExteriorNewtonField
  simp only [inner_sub_left, real_inner_smul_left]
  have hsum : (∑ j ∈ Finset.univ.erase i, tripleChartMass t alpha j.castSucc *
      inner ℝ (newtonTargetField (tripleChartPoints t alpha y j.castSucc)
        (tripleChartPoints t alpha y i.castSucc) - (1 + eps)⁻¹ • tripleChartPoints t alpha y j.castSucc)
        (quarterTurn (tripleChartPoints t alpha y i.castSucc))) =
      ∑ j ∈ Finset.univ.erase i, tripleChartMass t alpha j.castSucc *
        tripleChartRadii t alpha y i.castSucc * tripleChartRadii t alpha y j.castSucc *
        Real.sin (tripleChartAngles t alpha y j.castSucc - tripleChartAngles t alpha y i.castSucc) *
        ((satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc ^ 3)⁻¹ - (1 + eps)⁻¹) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [tripleChartPoints, polarSatellites, newtonTargetField_angular, satelliteDistance]
    ring
  simp only [tripleChartPoints, inner_sub_left, real_inner_smul_left] at hsum
  rw [hsum]
  unfold tripleChartPoints
  ring

end DominantFiveBody
