import DominantFiveBody.TripleExterior

/-! # Genuine seven-row regular-triple extension

The rows are `(Rₚ,Aᴿ,Bᴿ₁,Bᴿ₂,Aᵀ,Bᵀ₁,Bᵀ₂)`. Each divided row
is defined by an explicit signed extension, with physical equality proved
at positive scale. All zero weight probe rows are retained.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff

namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem tripleGapMatrix_mulVec_entry (P : TripleVector) (k : Fin 2) :
    (tripleGapMatrix *ᵥ P) k = P k.succ - P k.castSucc := by
  fin_cases k <;> simp [tripleGapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

def tripleRadialExteriorDifference (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) : ℝ :=
  (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i) *
    (1 + (tripleChartRadii t alpha y i.castSucc + tripleChartRadii t alpha y j.castSucc) /
      (tripleChartRadii t alpha y i.castSucc ^ 2 * tripleChartRadii t alpha y j.castSucc ^ 2)) +
    eps * (inner ℝ (tripleExteriorNewtonDifference t alpha y i j)
      (polarPoint 1 (tripleChartAngles t alpha y j.castSucc)) +
      inner ℝ (tripleExteriorRadialField eps t alpha y (tripleChartPoints t alpha y i.castSucc))
        (tripleUnitDirection t alpha y i j))

def tripleAngularExteriorDifference (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) : ℝ :=
  inner ℝ (tripleExteriorNewtonDifference t alpha y i j)
    (quarterTurn (tripleChartPoints t alpha y j.castSucc)) +
  inner ℝ (tripleExteriorAngularField eps t alpha y (tripleChartPoints t alpha y i.castSucc))
    (quarterTurn (triplePointDirection t alpha y i j))

def tripleRadialMean (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) : ℝ :=
  (∑ i, alpha i * tripleRadialExterior eps t alpha y i) + tripleInternalRadialMean eps t alpha y

def tripleAngularMean (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) : ℝ :=
  (∑ i, alpha i * tripleAngularExterior eps t alpha y i) + tripleInternalAngularMean eps t alpha y

def tripleRadialDifference (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    TripleGaps := fun k => tripleRadialExteriorDifference eps t alpha y k.castSucc k.succ +
      tripleInternalRadialDifference eps t alpha y k

def tripleAngularDifference (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    TripleGaps := fun k => tripleAngularExteriorDifference eps t alpha y k.castSucc k.succ +
      tripleInternalAngularDifference eps t alpha y k

def tripleChartExtendedRows (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    TripleChartVariables :=
  ![radialResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
      (tripleChartAngles t alpha y) 3,
    tripleRadialMean eps t alpha y, tripleRadialDifference eps t alpha y 0,
    tripleRadialDifference eps t alpha y 1, tripleAngularMean eps t alpha y,
    tripleAngularDifference eps t alpha y 0, tripleAngularDifference eps t alpha y 1]

theorem triple_radial_scalar_difference (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel)
    (hi : tripleChartRadii t alpha y i.castSucc ≠ 0)
    (hj : tripleChartRadii t alpha y j.castSucc ≠ 0) :
    (tripleChartRadii t alpha y j.castSucc - (tripleChartRadii t alpha y j.castSucc ^ 2)⁻¹) -
      (tripleChartRadii t alpha y i.castSucc - (tripleChartRadii t alpha y i.castSucc ^ 2)⁻¹) =
    t * ((tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i) *
      (1 + (tripleChartRadii t alpha y i.castSucc + tripleChartRadii t alpha y j.castSucc) /
        (tripleChartRadii t alpha y i.castSucc ^ 2 * tripleChartRadii t alpha y j.castSucc ^ 2))) := by
  have hg : tripleChartRadii t alpha y j.castSucc - tripleChartRadii t alpha y i.castSucc =
      t * (tripleChartRadialPositions alpha y j - tripleChartRadialPositions alpha y i) := by
    rw [tripleChartRadii_cluster, tripleChartRadii_cluster]
    unfold singleScaleRadius
    ring
  calc
    _ = (tripleChartRadii t alpha y j.castSucc - tripleChartRadii t alpha y i.castSucc) *
        (1 + (tripleChartRadii t alpha y i.castSucc + tripleChartRadii t alpha y j.castSucc) /
          (tripleChartRadii t alpha y i.castSucc ^ 2 * tripleChartRadii t alpha y j.castSucc ^ 2)) := by
      field_simp
      ring
    _ = _ := by rw [hg]; ring

theorem tripleRadialExterior_difference (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) (ht : t ≠ 0)
    (hri : tripleChartRadii t alpha y i.castSucc ≠ 0)
    (hrj : tripleChartRadii t alpha y j.castSucc ≠ 0)
    (hi : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y i.castSucc)
    (hj : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y j.castSucc) :
    tripleRadialExterior eps t alpha y j - tripleRadialExterior eps t alpha y i =
      t * tripleRadialExteriorDifference eps t alpha y i j := by
  have hs := triple_radial_scalar_difference t alpha y i j hri hrj
  have hn := inner_difference_factor
    (tripleExteriorRadialField eps t alpha y (tripleChartPoints t alpha y i.castSucc))
    (tripleExteriorRadialField eps t alpha y (tripleChartPoints t alpha y j.castSucc))
    (polarPoint 1 (tripleChartAngles t alpha y i.castSucc))
    (polarPoint 1 (tripleChartAngles t alpha y j.castSucc))
    (tripleExteriorNewtonDifference t alpha y i j) (tripleUnitDirection t alpha y i j) t
    (tripleExteriorRadialField_difference_identity eps t alpha y i j ht hi hj)
    (tripleUnitDirection_identity t alpha y i j)
  unfold tripleRadialExterior tripleRadialExteriorDifference
  linear_combination hs + eps * hn

theorem tripleAngularExterior_difference (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i j : TripleLabel) (ht : t ≠ 0)
    (hi : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y i.castSucc)
    (hj : tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y j.castSucc) :
    tripleAngularExterior eps t alpha y j - tripleAngularExterior eps t alpha y i =
      t * tripleAngularExteriorDifference eps t alpha y i j := by
  have hq : quarterTurn (tripleChartPoints t alpha y j.castSucc) -
      quarterTurn (tripleChartPoints t alpha y i.castSucc) =
        t • quarterTurn (triplePointDirection t alpha y i j) := by
    have h := congrArg quarterTurnLinear (triplePointDirection_identity t alpha y i j)
    simpa only [map_sub, map_smul, quarterTurnLinear_apply] using h
  have hn := inner_difference_factor
    (tripleExteriorAngularField eps t alpha y (tripleChartPoints t alpha y i.castSucc))
    (tripleExteriorAngularField eps t alpha y (tripleChartPoints t alpha y j.castSucc))
    (quarterTurn (tripleChartPoints t alpha y i.castSucc))
    (quarterTurn (tripleChartPoints t alpha y j.castSucc))
    (tripleExteriorNewtonDifference t alpha y i j) (quarterTurn (triplePointDirection t alpha y i j)) t
    (tripleExteriorAngularField_difference_identity eps t alpha y i j ht hi hj) hq
  exact hn

theorem tripleRadialMean_eq_physical (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : 0 < t)
    (hW : ∀ i j, i ≠ j → 0 < tripleChartWSq t alpha y i j) :
    tripleRadialMean eps t alpha y = tripleRowAverage alpha
      (radialResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
        (tripleChartAngles t alpha y)) := by
  unfold tripleRadialMean tripleInternalRadialMean tripleRowAverage tripleClusterRows
  simp_rw [tripleRadialExterior_recovery eps t alpha y _ ht (fun j hj => hW _ j hj.symm)]
  simp only [mul_add, Finset.sum_add_distrib]

theorem tripleAngularMean_eq_physical (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : 0 < t) (heps : 1 + eps ≠ 0)
    (hW : ∀ i j, i ≠ j → 0 < tripleChartWSq t alpha y i j) :
    tripleAngularMean eps t alpha y = tripleRowAverage alpha
      (angularResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
        (tripleChartAngles t alpha y)) := by
  unfold tripleAngularMean tripleInternalAngularMean tripleRowAverage tripleClusterRows
  simp_rw [tripleAngularExterior_recovery eps t alpha y _ ht
    (fun j hj => hW _ j hj.symm) heps]
  simp only [mul_add, Finset.sum_add_distrib]

theorem tripleRadialDifference_eq_physical (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : 0 < t)
    (hW : ∀ i j, i ≠ j → 0 < tripleChartWSq t alpha y i j)
    (hr : ∀ i : TripleLabel, tripleChartRadii t alpha y i.castSucc ≠ 0)
    (hsep : ∀ i : TripleLabel, tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y i.castSucc) :
    tripleRadialDifference eps t alpha y = tripleRowDifferences t
      (radialResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
        (tripleChartAngles t alpha y)) := by
  ext k
  simp only [tripleRadialDifference, tripleRowDifferences, tripleGapMatrix_mulVec_entry, tripleClusterRows]
  rw [tripleRadialExterior_recovery eps t alpha y k.succ ht (fun j hj => hW _ j hj.symm),
    tripleRadialExterior_recovery eps t alpha y k.castSucc ht (fun j hj => hW _ j hj.symm)]
  apply (eq_div_iff (ne_of_gt ht)).mpr
  have he := tripleRadialExterior_difference eps t alpha y k.castSucc k.succ (ne_of_gt ht)
    (hr k.castSucc) (hr k.succ) (hsep k.castSucc) (hsep k.succ)
  have hi := congrFun (tripleInternalRadial_difference_identity eps t alpha y) k
  simp only [tripleGapMatrix_mulVec_entry, Pi.smul_apply, smul_eq_mul] at hi
  linear_combination -he - hi

theorem tripleAngularDifference_eq_physical (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : 0 < t) (heps : 1 + eps ≠ 0)
    (hW : ∀ i j, i ≠ j → 0 < tripleChartWSq t alpha y i j)
    (hsep : ∀ i : TripleLabel, tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y i.castSucc) :
    tripleAngularDifference eps t alpha y = tripleRowDifferences t
      (angularResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
        (tripleChartAngles t alpha y)) := by
  ext k
  simp only [tripleAngularDifference, tripleRowDifferences, tripleGapMatrix_mulVec_entry, tripleClusterRows]
  rw [tripleAngularExterior_recovery eps t alpha y k.succ ht (fun j hj => hW _ j hj.symm) heps,
    tripleAngularExterior_recovery eps t alpha y k.castSucc ht (fun j hj => hW _ j hj.symm) heps]
  apply (eq_div_iff (ne_of_gt ht)).mpr
  have he := tripleAngularExterior_difference eps t alpha y k.castSucc k.succ (ne_of_gt ht)
    (hsep k.castSucc) (hsep k.succ)
  have hi := congrFun (tripleInternalAngular_difference_identity eps t alpha y) k
  simp only [tripleGapMatrix_mulVec_entry, Pi.smul_apply, smul_eq_mul] at hi
  linear_combination -he - hi

theorem tripleChartExtendedRows_eq_physical (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : 0 < t) (heps : 1 + eps ≠ 0)
    (hW : ∀ i j, i ≠ j → 0 < tripleChartWSq t alpha y i j)
    (hr : ∀ i : TripleLabel, tripleChartRadii t alpha y i.castSucc ≠ 0)
    (hsep : ∀ i : TripleLabel, tripleChartPoints t alpha y 3 ≠ tripleChartPoints t alpha y i.castSucc) :
    tripleChartExtendedRows eps t alpha y = tripleChartPhysicalRows eps t alpha y := by
  unfold tripleChartExtendedRows tripleChartPhysicalRows
  rw [tripleRadialMean_eq_physical eps t alpha y ht hW,
    tripleRadialDifference_eq_physical eps t alpha y ht hW hr hsep,
    tripleAngularMean_eq_physical eps t alpha y ht heps hW,
    tripleAngularDifference_eq_physical eps t alpha y ht heps hW hsep]

end DominantFiveBody
