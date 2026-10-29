import DominantFiveBody.TripleSmooth
import DominantFiveBody.PairUnitBoundary

/-! # Actual regular-triple zero-scale equations

Source §5.3 `Hzero`: the exterior angular difference is the derivative
of the genuine one-source target field in both radial and angular directions.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem tripleChartPoints_zero_cluster (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : tripleChartPoints 0 alpha y i.castSucc = polarPoint (y 1) (y 4) := by
  fin_cases i <;> simp [tripleChartPoints, polarSatellites, tripleChartRadii, tripleChartAngles]

theorem tripleChartPoints_zero_exterior (alpha : TripleVector) (y : TripleChartVariables) :
    tripleChartPoints 0 alpha y 3 = polarPoint (y 0) 0 := by
  simp [tripleChartPoints, polarSatellites, tripleChartRadii, tripleChartAngles]

theorem tripleUnitDirection_at_zero (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) :
    tripleUnitDirection 0 alpha y i j =
      (tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i) •
        quarterTurn (polarPoint 1 (y 4)) := by simp [tripleUnitDirection]

theorem triplePointDirection_at_zero (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) :
    triplePointDirection 0 alpha y i j = polarPointDerivative (y 1, y 4)
      (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i,
        tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i) := by
  rw [triplePointDirection, tripleUnitDirection_at_zero, polarPointDerivative_apply,
    polarPoint_rotation_smul (y 1) (y 4)]
  simp only [tripleChartRadii_cluster, tripleChartAngles_cluster, singleScaleRadius, singleScaleAngle,
    zero_mul, add_zero, smul_smul]
  rw [mul_comm]

theorem tripleChartWSq_at_zero (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) : tripleChartWSq 0 alpha y i j =
      (tripleChartRadialPositions alpha y i - tripleChartRadialPositions alpha y j) ^ 2 +
      y 1 ^ 2 * (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j) ^ 2 := by
  simp [tripleChartWSq, singleScaleWSq, singleScaleRadius, pow_two]

theorem tripleExteriorAngularField_at_zero (alpha : TripleVector) (y : TripleChartVariables)
    (target : Plane) : tripleExteriorAngularField 0 0 alpha y target =
      twoSourceTargetField 1 (y 0) (y 0) 0 target := by
  simp [tripleExteriorAngularField, tripleExteriorNewtonField, tripleChartMass,
    tripleChartPoints_zero_exterior, twoSourceTargetField]

theorem tripleExteriorNewtonDifference_at_zero (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) (hsep : polarPoint (y 0) 0 ≠ polarPoint (y 1) (y 4)) :
    tripleExteriorNewtonDifference 0 alpha y i j =
      twoSourceTargetDerivative 1 (y 0) (y 0) 0 (polarPoint (y 1) (y 4))
        (polarPointDerivative (y 1, y 4)
          (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i,
            tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i)) := by
  unfold tripleExteriorNewtonDifference
  rw [tripleChartPoints_zero_exterior, tripleChartPoints_zero_cluster,
    tripleChartPoints_zero_cluster, triplePointDirection_at_zero,
    dividedNewtonTargetField_diagonal _ _ _ hsep,
    (newtonTargetField_hasFDerivAt _ _ hsep).fderiv]
  simp [tripleChartMass, twoSourceTargetDerivative]

theorem tripleAngularExteriorDifference_at_boundary (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel)
    (hsep : polarPoint (y 0) 0 ≠ polarPoint (y 1) (y 4)) :
    tripleAngularExteriorDifference 0 0 alpha y i j =
      (fderiv ℝ (twoSourcePolarAngular 1 (y 0) (y 0) 0) (y 1, y 4))
        (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i,
          tripleChartAngularPositions alpha y j - tripleChartAngularPositions alpha y i) := by
  unfold tripleAngularExteriorDifference
  rw [tripleExteriorNewtonDifference_at_zero alpha y i j hsep,
    tripleExteriorAngularField_at_zero, triplePointDirection_at_zero,
    tripleChartPoints_zero_cluster, tripleChartPoints_zero_cluster,
    twoSourcePolarAngular_fderiv_apply _ _ _ _ _ _ hsep hsep]

theorem tripleRadialMean_at_boundary (alpha : TripleVector) (y : TripleChartVariables)
    (ha : ∑ i, alpha i = 1) : tripleRadialMean 0 0 alpha y = y 1 - (y 1 ^ 2)⁻¹ := by
  simp only [tripleRadialMean, tripleRadialExterior, tripleInternalRadialMean,
    tripleInternalRadial, tripleChartRadii_cluster, singleScaleRadius, zero_mul, add_zero,
    mul_zero, Finset.sum_const_zero]
  rw [← Finset.sum_mul, ha, one_mul]

theorem tripleRadialDifference_at_boundary (alpha : TripleVector) (y : TripleChartVariables)
    (ha : ∑ i, alpha i = 1) (k : Fin 2) :
    tripleRadialDifference 0 0 alpha y k =
      tripleChartRadialGaps y k * (1 + 2 * y 1 / (y 1 ^ 2 * y 1 ^ 2)) := by
  have hg := congrFun (congrArg (fun A => A *ᵥ tripleChartRadialGaps y)
    (tripleGapMatrix_centeringMatrix alpha ha)) k
  rw [← Matrix.mulVec_mulVec] at hg
  simp only [Matrix.one_mulVec, tripleGapMatrix_mulVec_entry] at hg
  change tripleChartRadialPositions alpha y k.succ -
    tripleChartRadialPositions alpha y k.castSucc = tripleChartRadialGaps y k at hg
  have hzero : tripleInternalRadialReduced 0 0 alpha y = 0 := by
    ext i
    simp [tripleInternalRadialReduced]
  simp only [tripleRadialDifference, tripleRadialExteriorDifference,
    tripleInternalRadialDifference, hzero, tripleChartRadii_cluster,
    singleScaleRadius, zero_mul, add_zero, Matrix.mulVec_zero, Pi.zero_apply]
  rw [hg]
  congr 2
  ring

theorem tripleAngularMean_at_boundary (alpha : TripleVector) (y : TripleChartVariables)
    (ha : ∑ i, alpha i = 1) : tripleAngularMean 0 0 alpha y =
      twoSourcePolarAngular 1 (y 0) (y 0) 0 (y 1, y 4) := by
  simp only [tripleAngularMean, tripleAngularExterior, tripleInternalAngularMean,
    tripleInternalAngular, zero_mul, mul_zero, Finset.sum_const_zero, add_zero,
    tripleChartPoints_zero_cluster, tripleExteriorAngularField_at_zero]
  rw [← Finset.sum_mul, ha, one_mul]
  rfl

theorem tripleInternalAngularReduced_at_boundary (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) :
    tripleInternalAngularReduced 0 0 alpha y i =
      -∑ j ∈ Finset.univ.erase i, alpha j * y 1 ^ 2 *
        (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j) *
        ((Real.sqrt ((tripleChartRadialPositions alpha y i - tripleChartRadialPositions alpha y j) ^ 2 +
          y 1 ^ 2 * (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j) ^ 2)) ^ 3)⁻¹ := by
  simp only [tripleInternalAngularReduced, tripleChartRadii_cluster, singleScaleRadius,
    zero_mul, add_zero, Real.sinc_zero, mul_one,
    tripleChartW, tripleChartWSq_at_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

def tripleUnitPoint (psi : ℝ) (v : TripleGaps) : TripleChartVariables :=
  ![1, 1, 0, 0, psi, v 0, v 1]

theorem tripleUnitPoint_radialPositions (alpha : TripleVector) (psi : ℝ) (v : TripleGaps) :
    tripleChartRadialPositions alpha (tripleUnitPoint psi v) = 0 := by
  unfold tripleChartRadialPositions
  rw [show tripleChartRadialGaps (tripleUnitPoint psi v) = 0 by
    ext i; fin_cases i <;> rfl, Matrix.mulVec_zero]

theorem tripleUnitPoint_angularPositions (alpha : TripleVector) (psi : ℝ) (v : TripleGaps) :
    tripleChartAngularPositions alpha (tripleUnitPoint psi v) = tripleCenteringMatrix alpha *ᵥ v := by
  congr 1

theorem tripleUnitPoint_regular (alpha : TripleVector) (psi : ℝ) (v : TripleGaps)
    (hpsi : psi ≠ 0) (hpi : |psi| < Real.pi)
    (hdist : ∀ i j, i ≠ j → (tripleCenteringMatrix alpha *ᵥ v) i ≠
      (tripleCenteringMatrix alpha *ᵥ v) j) :
    TripleChartRegular 0 0 alpha (tripleUnitPoint psi v) := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [tripleChartRadii, tripleUnitPoint]
  · intro i j hij
    rw [tripleChartWSq_at_zero, tripleUnitPoint_radialPositions, tripleUnitPoint_angularPositions]
    simpa [tripleUnitPoint] using sq_pos_of_ne_zero (sub_ne_zero.mpr (hdist i j hij))
  · intro i
    rw [tripleChartPoints_zero_exterior, tripleChartPoints_zero_cluster]
    exact polarUnit_ne_of_angle_ne 0 psi hpsi.symm (by simpa using hpi)

theorem tripleInternalAngularReduced_unit_boundary (alpha : TripleVector)
    (psi : ℝ) (v : TripleGaps) (i : TripleLabel) :
    tripleInternalAngularReduced 0 0 alpha (tripleUnitPoint psi v) i =
      -∑ j ∈ Finset.univ.erase i, alpha j *
        tripleScalarForce ((tripleCenteringMatrix alpha *ᵥ v) i -
          (tripleCenteringMatrix alpha *ᵥ v) j) := by
  rw [tripleInternalAngularReduced_at_boundary, tripleUnitPoint_radialPositions,
    tripleUnitPoint_angularPositions]
  simp [tripleUnitPoint, tripleScalarForce, div_eq_mul_inv, Real.sqrt_sq_eq_abs, mul_assoc]

end DominantFiveBody
