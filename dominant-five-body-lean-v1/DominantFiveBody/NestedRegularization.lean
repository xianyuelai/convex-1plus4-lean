import DominantFiveBody.NestedExterior
import DominantFiveBody.NestedInternalRecovery

/-! # Actual complete seven-row nested extension and physical equality

This is a signed independent-scale formula. Equality with the original
mass-divided five-body equations is proved only for positive t and η.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody
set_option maxHeartbeats 1000000

theorem nested_sum_erase_split (f : Satellite → ℝ) (i : Fin 3) :
    ∑ j ∈ Finset.univ.erase i.castSucc, f j=(∑ j ∈ Finset.univ.erase i, f j.castSucc)+f 3 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i.castSucc),
    Finset.sum_erase_eq_sub (Finset.mem_univ i),Fin.sum_univ_four,Fin.sum_univ_three]
  fin_cases i <;> simp <;> ring

theorem nestedRadialExterior_recovery (eps t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 3)
    (ht : 0<t) (he : 0<eta) (hW : 0<nestedInnerWSq t eta alpha y)
    (hV : ∀ j, 0<nestedOuterWSq t eta alpha y j) :
    radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
      (nestedChartAngles t eta alpha y) i.castSucc=
      nestedRadialExterior eps t eta alpha y i.castSucc+nestedInternalRadial eps t eta alpha y i.castSucc := by
  rw [radialResidual_newton_projection,nested_sum_erase_split,
    nestedInternalRadial_eq_physical eps t eta alpha y i ht he hW hV]
  unfold nestedRadialExterior nestedExteriorRadialField nestedExteriorNewtonField
  simp only [inner_sub_left,real_inner_smul_left]
  have hsum : (∑ j ∈ Finset.univ.erase i,eps*(nestedChartMass t eta alpha j.castSucc*
      inner ℝ (newtonTargetField (nestedChartPoints t eta alpha y j.castSucc)
        (nestedChartPoints t eta alpha y i.castSucc)) (polarPoint 1 (nestedChartAngles t eta alpha y i.castSucc))))=
      ∑ j ∈ Finset.univ.erase i,nestedRadialPairTerm eps t eta alpha y i.castSucc j.castSucc := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [nestedRadialPairTerm,nestedChartPoints,polarSatellites,newtonTargetField_radial,satelliteDistance]
    ring
  simp only [nestedChartPoints] at hsum
  rw [mul_add,Finset.mul_sum,hsum]
  have hm : nestedChartMass t eta alpha 3=1-t^3 := rfl
  rw [hm]
  unfold nestedChartPoints
  ring

theorem nestedAngularExterior_recovery (eps t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 3)
    (ht : 0<t) (he : 0<eta) (hW : 0<nestedInnerWSq t eta alpha y)
    (hV : ∀ j, 0<nestedOuterWSq t eta alpha y j) (heps : 1+eps≠0) :
    angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
      (nestedChartAngles t eta alpha y) i.castSucc=
      nestedAngularExterior eps t eta alpha y i.castSucc+nestedInternalAngular eps t eta alpha y i.castSucc := by
  rw [angularResidual_newton_projection,nested_sum_erase_split,
    nestedInternalAngular_eq_physical eps t eta alpha y i ht he hW hV heps]
  unfold nestedAngularExterior nestedExteriorAngularField nestedExteriorNewtonField
  simp only [inner_sub_left,real_inner_smul_left]
  have hsum : (∑ j ∈ Finset.univ.erase i,nestedChartMass t eta alpha j.castSucc*
      inner ℝ (newtonTargetField (nestedChartPoints t eta alpha y j.castSucc)
        (nestedChartPoints t eta alpha y i.castSucc)-(1+eps)⁻¹ • nestedChartPoints t eta alpha y j.castSucc)
        (quarterTurn (nestedChartPoints t eta alpha y i.castSucc)))=
      ∑ j ∈ Finset.univ.erase i,nestedAngularPairTerm eps t eta alpha y i.castSucc j.castSucc := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [nestedAngularPairTerm,nestedChartPoints,polarSatellites,newtonTargetField_angular,satelliteDistance]
    ring
  simp only [nestedChartPoints,inner_sub_left,real_inner_smul_left] at hsum
  rw [hsum]
  have hm : nestedChartMass t eta alpha 3=1-t^3 := rfl
  rw [hm]
  unfold nestedChartPoints
  ring

def nestedRadialMean (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  nestedRowAverage eta alpha (nestedRadialExterior eps t eta alpha y)+nestedInternalRadialMean eps t eta alpha y

def nestedRadialOuterDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  alpha*nestedRadialExteriorDifference eps t eta alpha y 0+(1-alpha)*nestedRadialExteriorDifference eps t eta alpha y 1+
    nestedInternalRadialOuterDifference eps t eta alpha y

def nestedRadialInnerDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  nestedRadialExteriorDifference eps t eta alpha y 2+nestedInternalRadialInnerDifference eps t eta alpha y

def nestedAngularMean (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  nestedRowAverage eta alpha (nestedAngularExterior eps t eta alpha y)

def nestedAngularOuterDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  alpha*nestedAngularExteriorDifference eps t eta alpha y 0+(1-alpha)*nestedAngularExteriorDifference eps t eta alpha y 1+
    nestedInternalAngularOuterDifference eps t eta alpha y

def nestedAngularInnerDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  nestedAngularExteriorDifference eps t eta alpha y 2+nestedInternalAngularInnerDifference eps t eta alpha y

def nestedChartExtendedRows (eps t eta alpha : ℝ) (y : NestedChartVariables) : NestedChartVariables :=
  ![radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y) 3,
    nestedRadialMean eps t eta alpha y,nestedRadialOuterDifference eps t eta alpha y,nestedRadialInnerDifference eps t eta alpha y,
    nestedAngularMean eps t eta alpha y,nestedAngularOuterDifference eps t eta alpha y,nestedAngularInnerDifference eps t eta alpha y]

theorem nestedChartExtendedRows_eq_physical (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (heps : 1+eps≠0)
    (hr : ∀ i, nestedChartRadii t eta alpha y i≠0)
    (hW : 0<nestedInnerWSq t eta alpha y) (hV : ∀ j, 0<nestedOuterWSq t eta alpha y j)
    (hsep : ∀ i : Fin 3,nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y i.castSucc) :
    nestedChartExtendedRows eps t eta alpha y=nestedChartPhysicalRows eps t eta alpha y := by
  have hR (i : Fin 3) := nestedRadialExterior_recovery eps t eta alpha y i ht he hW hV
  have hT (i : Fin 3) := nestedAngularExterior_recovery eps t eta alpha y i ht he hW hV heps
  have hsepS (k : NestedEdge) : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeSource k) := by
    fin_cases k
    · exact hsep 0
    · exact hsep 1
    · exact hsep 0
  have hsepT (k : NestedEdge) : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeTarget k) := by
    fin_cases k
    · exact hsep 2
    · exact hsep 2
    · exact hsep 1
  have heR (k : NestedEdge) := nestedRadialExterior_difference eps t eta alpha y k
    (hr (nestedEdgeSource k)) (hr (nestedEdgeTarget k)) (hsepS k) (hsepT k)
  have heT (k : NestedEdge) := nestedAngularExterior_difference eps t eta alpha y k (hsepS k) (hsepT k)
  have hmR := nestedInternalRadial_mean eps t eta alpha y
  have hbR := nestedInternalRadial_outer_difference eps t eta alpha y
  have hcR := nestedInternalRadial_inner_difference eps t eta alpha y hV
  have hmT := nestedInternalAngular_mean eps t eta alpha y
  have hbT := nestedInternalAngular_outer_difference eps t eta alpha y
  have hcT := nestedInternalAngular_inner_difference eps t eta alpha y hV
  have hRa := hR 0
  have hRb := hR 1
  have hRc := hR 2
  have hTa := hT 0
  have hTb := hT 1
  have hTc := hT 2
  dsimp at hRa hRb hRc hTa hTb hTc
  have heR0 := heR 0
  have heR1 := heR 1
  have heR2 := heR 2
  have heT0 := heT 0
  have heT1 := heT 1
  have heT2 := heT 2
  dsimp [nestedEdgeSource,nestedEdgeTarget,nestedEdgeScale] at heR0 heR1 heR2 heT0 heT1 heT2
  dsimp only [nestedChartPhysicalRows]
  ext k
  fin_cases k
  · rfl
  · change nestedRadialMean eps t eta alpha y=nestedRowAverage eta alpha
      (radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y))
    unfold nestedRadialMean nestedRowAverage nestedPairAverage
    unfold nestedRowAverage nestedPairAverage at hmR
    rw [hRa,hRb,hRc]
    linear_combination -hmR
  · change nestedRadialOuterDifference eps t eta alpha y=nestedRowOuterDifference t alpha
      (radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y))
    unfold nestedRowOuterDifference nestedPairAverage
    apply (eq_div_iff ht.ne').mpr
    rw [hRa,hRb,hRc]
    unfold nestedRadialOuterDifference
    unfold nestedPairAverage at hbR
    linear_combination -alpha*heR0-(1-alpha)*heR1-hbR
  · change nestedRadialInnerDifference eps t eta alpha y=nestedRowInnerDifference t eta
      (radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y))
    unfold nestedRowInnerDifference
    apply (eq_div_iff (mul_ne_zero ht.ne' he.ne')).mpr
    rw [hRa,hRb]
    unfold nestedRadialInnerDifference
    linear_combination -heR2-hcR
  · change nestedAngularMean eps t eta alpha y=nestedRowAverage eta alpha
      (angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y))
    unfold nestedAngularMean nestedRowAverage nestedPairAverage
    unfold nestedRowAverage nestedPairAverage at hmT
    rw [hTa,hTb,hTc]
    linear_combination -hmT
  · change nestedAngularOuterDifference eps t eta alpha y=nestedRowOuterDifference t alpha
      (angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y))
    unfold nestedRowOuterDifference nestedPairAverage
    apply (eq_div_iff ht.ne').mpr
    rw [hTa,hTb,hTc]
    unfold nestedAngularOuterDifference
    unfold nestedPairAverage at hbT
    linear_combination -alpha*heT0-(1-alpha)*heT1-hbT
  · change nestedAngularInnerDifference eps t eta alpha y=nestedRowInnerDifference t eta
      (angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y))
    unfold nestedRowInnerDifference
    apply (eq_div_iff (mul_ne_zero ht.ne' he.ne')).mpr
    rw [hTa,hTb]
    unfold nestedAngularInnerDifference
    linear_combination -heT2-hcT

end DominantFiveBody
