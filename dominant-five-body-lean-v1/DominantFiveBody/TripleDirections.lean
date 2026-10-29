import DominantFiveBody.TripleChart
import DominantFiveBody.PairDirections

/-! # Actual signed divided edges in the regular triple chart

The parameters are independent ε,t,α₁,α₂,α₃. No normalization or
positivity condition is needed to prove joint smoothness of coordinates.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff

namespace DominantFiveBody

abbrev TripleJointVariables := (Fin 5 → ℝ) × TripleChartVariables
def tripleJointAlpha (p : Fin 5 → ℝ) : TripleVector := ![p 2, p 3, p 4]

@[fun_prop] theorem tripleJointAlpha_contDiff (n : ℕ∞ω) (i : TripleLabel) :
    ContDiff ℝ n (fun v : TripleJointVariables => tripleJointAlpha v.1 i) := by
  fin_cases i <;> simp [tripleJointAlpha] <;> fun_prop

@[fun_prop] theorem tripleChartRadialPositions_joint_contDiff (n : ℕ∞ω) (i : TripleLabel) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleChartRadialPositions (tripleJointAlpha v.1) v.2 i) := by
  fin_cases i
  all_goals simp [tripleChartRadialPositions, tripleCenteringMatrix,
    tripleChartRadialGaps, Matrix.mulVec, dotProduct, Fin.sum_univ_two, tripleJointAlpha]
  all_goals fun_prop

@[fun_prop] theorem tripleChartAngularPositions_joint_contDiff (n : ℕ∞ω) (i : TripleLabel) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleChartAngularPositions (tripleJointAlpha v.1) v.2 i) := by
  fin_cases i
  all_goals simp [tripleChartAngularPositions, tripleCenteringMatrix,
    tripleChartAngularGaps, Matrix.mulVec, dotProduct, Fin.sum_univ_two, tripleJointAlpha]
  all_goals fun_prop

@[fun_prop] theorem tripleChartMass_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleChartMass (v.1 1) (tripleJointAlpha v.1) i) := by
  fin_cases i <;> simp [tripleChartMass, tripleJointAlpha] <;> fun_prop

@[fun_prop] theorem tripleChartRadii_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleChartRadii (v.1 1) (tripleJointAlpha v.1) v.2 i) := by
  fin_cases i
  all_goals simp [tripleChartRadii]
  all_goals fun_prop

@[fun_prop] theorem tripleChartAngles_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleChartAngles (v.1 1) (tripleJointAlpha v.1) v.2 i) := by
  fin_cases i
  all_goals simp [tripleChartAngles]
  all_goals fun_prop

@[fun_prop] theorem tripleChartPoints_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2 i) :=
  (polarPoint_contDiff n).comp
    ((tripleChartRadii_joint_contDiff n i).prodMk (tripleChartAngles_joint_contDiff n i))

@[fun_prop] theorem tripleUnit_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      polarPoint 1 (tripleChartAngles (v.1 1) (tripleJointAlpha v.1) v.2 i)) :=
  (polarPoint_contDiff n).comp
    (contDiff_const.prodMk (tripleChartAngles_joint_contDiff n i))

def tripleUnitDirection (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) : Plane :=
  ((tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i) *
    Real.sinc (t * (tripleChartAngularPositions alpha y j -
      tripleChartAngularPositions alpha y i) / 2)) •
    quarterTurn (polarPoint 1 (y 4 + t *
      (tripleChartAngularPositions alpha y i + tripleChartAngularPositions alpha y j) / 2))

def triplePointDirection (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) : Plane :=
  (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i) •
    polarPoint 1 (tripleChartAngles t alpha y i.castSucc) +
    tripleChartRadii t alpha y j.castSucc • tripleUnitDirection t alpha y i j

theorem tripleUnitDirection_identity (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) :
    polarPoint 1 (tripleChartAngles t alpha y j.castSucc) -
      polarPoint 1 (tripleChartAngles t alpha y i.castSucc) =
        t • tripleUnitDirection t alpha y i j := by
  rw [polarUnit_sub_midpoint]
  have hi : tripleChartAngles t alpha y i.castSucc =
      y 4 + t * tripleChartAngularPositions alpha y i := by fin_cases i <;> rfl
  have hj : tripleChartAngles t alpha y j.castSucc =
      y 4 + t * tripleChartAngularPositions alpha y j := by fin_cases j <;> rfl
  rw [hi, hj]
  have hg : (y 4 + t * tripleChartAngularPositions alpha y j) -
      (y 4 + t * tripleChartAngularPositions alpha y i) =
        t * (tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i) := by ring
  have hm : ((y 4 + t * tripleChartAngularPositions alpha y i) +
      (y 4 + t * tripleChartAngularPositions alpha y j)) / 2 =
        y 4 + t * (tripleChartAngularPositions alpha y i +
          tripleChartAngularPositions alpha y j) / 2 := by ring
  rw [hg, hm, tripleUnitDirection, smul_smul]
  congr 1
  ring

theorem triplePointDirection_identity (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) :
    tripleChartPoints t alpha y j.castSucc - tripleChartPoints t alpha y i.castSucc =
      t • triplePointDirection t alpha y i j := by
  have hr : tripleChartRadii t alpha y j.castSucc - tripleChartRadii t alpha y i.castSucc =
      t * (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i) := by
    have hi : tripleChartRadii t alpha y i.castSucc =
        y 1 + t * tripleChartRadialPositions alpha y i := by fin_cases i <;> rfl
    have hj : tripleChartRadii t alpha y j.castSucc =
        y 1 + t * tripleChartRadialPositions alpha y j := by fin_cases j <;> rfl
    rw [hi, hj]
    ring
  have he := tripleUnitDirection_identity t alpha y i j
  unfold tripleChartPoints polarSatellites
  rw [polarPoint_smul_one (tripleChartRadii t alpha y j.castSucc),
    polarPoint_smul_one (tripleChartRadii t alpha y i.castSucc)]
  calc
    _ = tripleChartRadii t alpha y j.castSucc •
        (polarPoint 1 (tripleChartAngles t alpha y j.castSucc) -
          polarPoint 1 (tripleChartAngles t alpha y i.castSucc)) +
        (tripleChartRadii t alpha y j.castSucc - tripleChartRadii t alpha y i.castSucc) •
          polarPoint 1 (tripleChartAngles t alpha y i.castSucc) := by module
    _ = _ := by rw [he, hr]; simp only [triplePointDirection, smul_add, smul_smul]; module

@[fun_prop] theorem tripleUnitDirection_joint_contDiff (n : ℕ∞ω) (i j : TripleLabel) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleUnitDirection (v.1 1) (tripleJointAlpha v.1) v.2 i j) := by
  unfold tripleUnitDirection
  have hp : ContDiff ℝ n (fun v : TripleJointVariables => polarPoint 1 (v.2 4 + v.1 1 *
      (tripleChartAngularPositions (tripleJointAlpha v.1) v.2 i +
        tripleChartAngularPositions (tripleJointAlpha v.1) v.2 j) / 2)) :=
    (polarPoint_contDiff n).comp (contDiff_const.prodMk (by fun_prop))
  have hc : ContDiff ℝ n (fun v : TripleJointVariables =>
      (tripleChartAngularPositions (tripleJointAlpha v.1) v.2 j -
        tripleChartAngularPositions (tripleJointAlpha v.1) v.2 i) *
      Real.sinc (v.1 1 * (tripleChartAngularPositions (tripleJointAlpha v.1) v.2 j -
        tripleChartAngularPositions (tripleJointAlpha v.1) v.2 i) / 2)) := by fun_prop
  exact hc.smul (quarterTurnLinear.toContinuousLinearMap.contDiff.comp hp)

@[fun_prop] theorem triplePointDirection_joint_contDiff (n : ℕ∞ω) (i j : TripleLabel) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      triplePointDirection (v.1 1) (tripleJointAlpha v.1) v.2 i j) := by
  unfold triplePointDirection
  exact (((tripleChartRadialPositions_joint_contDiff n j).sub
    (tripleChartRadialPositions_joint_contDiff n i)).smul (tripleUnit_joint_contDiff n i.castSucc)).add
    ((tripleChartRadii_joint_contDiff n j.castSucc).smul (tripleUnitDirection_joint_contDiff n i j))

end DominantFiveBody
