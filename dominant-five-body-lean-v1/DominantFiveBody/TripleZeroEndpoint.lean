import DominantFiveBody.TripleContinuation
import DominantFiveBody.PairZeroEndpoint

/-! # Fixed-mass zero endpoints for the regular triple

Positive t remains fixed while ε goes to zero. The endpoint is an
actual distinct four-satellite coorbital root for the same positive masses.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody

theorem tripleRadialPositions_gap (alpha : TripleVector) (y : TripleChartVariables)
    (ha : ∑ i, alpha i = 1) (k : Fin 2) :
    tripleChartRadialPositions alpha y k.succ - tripleChartRadialPositions alpha y k.castSucc =
      tripleChartRadialGaps y k := by
  have h := congrFun (congrArg (fun A => A *ᵥ tripleChartRadialGaps y)
    (tripleGapMatrix_centeringMatrix alpha ha)) k
  rw [← Matrix.mulVec_mulVec] at h
  simpa only [Matrix.one_mulVec, tripleGapMatrix_mulVec_entry, tripleChartRadialPositions] using h

theorem tripleRadialDifference_zero_eps (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ha : ∑ i, alpha i = 1) (k : Fin 2) :
    tripleRadialDifference 0 t alpha y k = tripleChartRadialGaps y k *
      (1 + (tripleChartRadii t alpha y k.castSucc.castSucc +
        tripleChartRadii t alpha y k.succ.castSucc) /
        (tripleChartRadii t alpha y k.castSucc.castSucc ^ 2 *
          tripleChartRadii t alpha y k.succ.castSucc ^ 2)) := by
  have hzero : tripleInternalRadialReduced 0 t alpha y = 0 := by ext i; simp [tripleInternalRadialReduced]
  simp only [tripleRadialDifference, tripleRadialExteriorDifference, zero_mul, add_zero,
    tripleInternalRadialDifference, hzero, Matrix.mulVec_zero, Pi.zero_apply]
  rw [tripleRadialPositions_gap alpha y ha]

/-- Unit radii hold on all signed scale faces at ε=0. There is no
division by t or an individual α coordinate in this proof. -/
theorem tripleChart_zero_eps_all_scale_faces (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ha : ∑ i, alpha i = 1)
    (hr : ∀ i, 0 < tripleChartRadii t alpha y i)
    (hroot : tripleChartExtendedRows 0 t alpha y = 0) :
    (∀ i, tripleChartRadii t alpha y i = 1) ∧ tripleChartRadialGaps y = 0 ∧ y 0 = 1 ∧ y 1 = 1 := by
  have hgap : tripleChartRadialGaps y = 0 := by
    ext k
    have hrow : tripleRadialDifference 0 t alpha y k = 0 := by
      fin_cases k
      · exact congrFun hroot 2
      · exact congrFun hroot 3
    rw [tripleRadialDifference_zero_eps t alpha y ha k] at hrow
    have hpos : 0 < (1 + (tripleChartRadii t alpha y k.castSucc.castSucc +
        tripleChartRadii t alpha y k.succ.castSucc) /
        (tripleChartRadii t alpha y k.castSucc.castSucc ^ 2 *
          tripleChartRadii t alpha y k.succ.castSucc ^ 2)) := by
      have hi := hr k.castSucc.castSucc
      have hj := hr k.succ.castSucc
      positivity
    exact (mul_eq_zero.mp hrow).resolve_right hpos.ne'
  have hw : tripleChartRadialPositions alpha y = 0 := by
    rw [tripleChartRadialPositions, hgap, Matrix.mulVec_zero]
  have hRadii (i : TripleLabel) : tripleChartRadii t alpha y i.castSucc = y 1 := by
    rw [tripleChartRadii_cluster]
    simp [singleScaleRadius, hw]
  have hRp : y 0 = 1 := by
    apply positive_radial_zero_eq_one
    · exact hr 3
    · have hrow : radialResidual 0 (tripleChartMass t alpha) (tripleChartRadii t alpha y)
        (tripleChartAngles t alpha y) 3 = 0 := congrFun hroot 0
      simpa [radialResidual_at_zero, tripleChartRadii] using hrow
  have hR : y 1 = 1 := by
    apply positive_radial_zero_eq_one
    · rw [← hRadii 0]
      exact hr 0
    · have hmean : tripleRadialMean 0 t alpha y = 0 := congrFun hroot 1
      simp only [tripleRadialMean, tripleRadialExterior, tripleInternalRadialMean,
        tripleInternalRadial, tripleInternalRadialReduced, hRadii, zero_mul, mul_zero,
        neg_zero, add_zero, Finset.sum_const_zero] at hmean
      rw [← Finset.sum_mul, ha, one_mul] at hmean
      exact hmean
  refine ⟨?_, hgap, hRp, hR⟩
  intro i
  fin_cases i
  · exact (hRadii 0).trans hR
  · exact (hRadii 1).trans hR
  · exact (hRadii 2).trans hR
  · exact hRp

theorem tripleChart_fixed_mass_zero_endpoint (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : 0 < t) (ha : ∑ i, alpha i = 1)
    (hm : PositiveRatio (tripleChartMass t alpha)) (hreg : TripleChartRegular 0 t alpha y)
    (hr : ∀ i, 0 < tripleChartRadii t alpha y i)
    (hwidth : ∀ i j, |tripleChartAngles t alpha y j - tripleChartAngles t alpha y i| < Real.pi)
    (hroot : tripleChartExtendedRows 0 t alpha y = 0) :
    (∀ i, tripleChartRadii t alpha y i = 1) ∧ tripleChartRadialGaps y = 0 ∧
      RelativeCollisionFree (tripleChartPoints t alpha y) ∧
      SeparatedSemicircle (tripleChartAngles t alpha y) ∧
      ∀ i, coorbitalResidual (tripleChartMass t alpha) (tripleChartAngles t alpha y) i = 0 := by
  have hunit := tripleChart_zero_eps_all_scale_faces t alpha y ha hr hroot
  have hcf := tripleChartPoints_relativeCollisionFree 0 t alpha y ht hreg
  have hsep : SeparatedSemicircle (tripleChartAngles t alpha y) := by
    intro i j hij
    refine ⟨?_, hwidth i j⟩
    intro he
    apply hcf.2 i j hij
    change polarPoint (tripleChartRadii t alpha y i) (tripleChartAngles t alpha y i) =
      polarPoint (tripleChartRadii t alpha y j) (tripleChartAngles t alpha y j)
    rw [hunit.1 i, hunit.1 j, he]
  refine ⟨hunit.1, hunit.2.1, hcf, hsep, ?_⟩
  have hrows := (tripleChartExtendedRows_zero_iff_physical 0 t alpha y ht ha hreg (hm.1 3).ne').mp hroot
  intro i
  have he := hrows.2 i
  have hradii : tripleChartRadii t alpha y = fun _ => 1 := funext hunit.1
  rwa [hradii, angularResidual_unit_eq_coorbital_of_separated _ _ hsep i] at he

theorem tripleChartWidth_isOpen : IsOpen {v : TripleJointVariables |
    ∀ i j, |tripleChartAngles (v.1 1) (tripleJointAlpha v.1) v.2 j -
      tripleChartAngles (v.1 1) (tripleJointAlpha v.1) v.2 i| < Real.pi} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (((tripleChartAngles_joint_contDiff 0 j).continuous.sub
    (tripleChartAngles_joint_contDiff 0 i).continuous).abs) continuous_const

end DominantFiveBody
