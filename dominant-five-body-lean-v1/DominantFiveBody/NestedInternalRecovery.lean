import DominantFiveBody.NestedPhysicalKernels

/-! # Recovery of every genuine internal radial and angular force term -/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody
set_option maxHeartbeats 800000

def nestedRadialPairTerm (eps t eta alpha : ℝ) (y : NestedChartVariables) (i j : Satellite) : ℝ :=
  -eps*nestedChartMass t eta alpha j*(nestedChartRadii t eta alpha y i-nestedChartRadii t eta alpha y j*
    Real.cos (nestedChartAngles t eta alpha y j-nestedChartAngles t eta alpha y i))/
      satelliteDistance (nestedChartPoints t eta alpha y) i j^3

def nestedAngularPairTerm (eps t eta alpha : ℝ) (y : NestedChartVariables) (i j : Satellite) : ℝ :=
  nestedChartMass t eta alpha j*nestedChartRadii t eta alpha y i*nestedChartRadii t eta alpha y j*
    Real.sin (nestedChartAngles t eta alpha y j-nestedChartAngles t eta alpha y i)*
      ((satelliteDistance (nestedChartPoints t eta alpha y) i j^3)⁻¹-(1+eps)⁻¹)

theorem nestedInner_radialA_physical (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hW : 0<nestedInnerWSq t eta alpha y) :
    pairInternalRadialA eps (t*eta) alpha (nestedInnerVariables t eta y)=nestedRadialPairTerm eps t eta alpha y 0 1 := by
  have h := pairInternalRadialA_eq_physical eps (t*eta) alpha (nestedInnerVariables t eta y) (mul_pos ht he) hW
  have h0 := nestedInner_coordinates t eta alpha y 0
  have h1 := nestedInner_coordinates t eta alpha y 1
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartRadii t eta alpha y 0 ∧ pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartAngles t eta alpha y 0 at h0
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartRadii t eta alpha y 1 ∧ pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartAngles t eta alpha y 1 at h1
  unfold satelliteDistance polarSatellites at h
  rw [h0.1,h1.1,h0.2,h1.2] at h
  change pairInternalRadialA eps (t*eta) alpha (nestedInnerVariables t eta y)=
    -eps*(t^3*eta^3*(1-alpha))*(nestedChartRadii t eta alpha y 0-nestedChartRadii t eta alpha y 1*
      Real.cos (nestedChartAngles t eta alpha y 1-nestedChartAngles t eta alpha y 0))/
        ‖polarPoint (nestedChartRadii t eta alpha y 0) (nestedChartAngles t eta alpha y 0)-
          polarPoint (nestedChartRadii t eta alpha y 1) (nestedChartAngles t eta alpha y 1)‖^3
  simpa [pairChartMass,mul_pow] using h

theorem nestedInner_radialB_physical (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hW : 0<nestedInnerWSq t eta alpha y) :
    pairInternalRadialB eps (t*eta) alpha (nestedInnerVariables t eta y)=nestedRadialPairTerm eps t eta alpha y 1 0 := by
  have h := pairInternalRadialB_eq_physical eps (t*eta) alpha (nestedInnerVariables t eta y) (mul_pos ht he) hW
  have h0 := nestedInner_coordinates t eta alpha y 0
  have h1 := nestedInner_coordinates t eta alpha y 1
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartRadii t eta alpha y 0 ∧ pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartAngles t eta alpha y 0 at h0
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartRadii t eta alpha y 1 ∧ pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartAngles t eta alpha y 1 at h1
  unfold satelliteDistance polarSatellites at h
  rw [h0.1,h1.1,h0.2,h1.2] at h
  change pairInternalRadialB eps (t*eta) alpha (nestedInnerVariables t eta y)=
    -eps*(t^3*eta^3*alpha)*(nestedChartRadii t eta alpha y 1-nestedChartRadii t eta alpha y 0*
      Real.cos (nestedChartAngles t eta alpha y 0-nestedChartAngles t eta alpha y 1))/
        ‖polarPoint (nestedChartRadii t eta alpha y 1) (nestedChartAngles t eta alpha y 1)-
          polarPoint (nestedChartRadii t eta alpha y 0) (nestedChartAngles t eta alpha y 0)‖^3
  simpa [pairChartMass,mul_pow] using h

theorem nestedInner_angularA_physical (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hW : 0<nestedInnerWSq t eta alpha y) (heps : 1+eps≠0) :
    pairInternalAngularA eps (t*eta) alpha (nestedInnerVariables t eta y)=nestedAngularPairTerm eps t eta alpha y 0 1 := by
  have h := pairInternalAngularA_eq_physical eps (t*eta) alpha (nestedInnerVariables t eta y) (mul_pos ht he) hW heps
  have h0 := nestedInner_coordinates t eta alpha y 0
  have h1 := nestedInner_coordinates t eta alpha y 1
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartRadii t eta alpha y 0 ∧ pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartAngles t eta alpha y 0 at h0
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartRadii t eta alpha y 1 ∧ pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartAngles t eta alpha y 1 at h1
  unfold satelliteDistance polarSatellites at h
  rw [h0.1,h1.1,h0.2,h1.2] at h
  simpa [nestedAngularPairTerm,nestedChartMass,pairChartMass,mul_pow,satelliteDistance,nestedChartPoints,polarSatellites] using h

theorem nestedInner_angularB_physical (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hW : 0<nestedInnerWSq t eta alpha y) (heps : 1+eps≠0) :
    pairInternalAngularB eps (t*eta) alpha (nestedInnerVariables t eta y)=nestedAngularPairTerm eps t eta alpha y 1 0 := by
  have h := pairInternalAngularB_eq_physical eps (t*eta) alpha (nestedInnerVariables t eta y) (mul_pos ht he) hW heps
  have h0 := nestedInner_coordinates t eta alpha y 0
  have h1 := nestedInner_coordinates t eta alpha y 1
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartRadii t eta alpha y 0 ∧ pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartAngles t eta alpha y 0 at h0
  change pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartRadii t eta alpha y 1 ∧ pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartAngles t eta alpha y 1 at h1
  unfold satelliteDistance polarSatellites at h
  rw [h0.1,h1.1,h0.2,h1.2] at h
  simpa [nestedAngularPairTerm,nestedChartMass,pairChartMass,mul_pow,satelliteDistance,nestedChartPoints,polarSatellites] using h

theorem nestedInternalRadial_eq_physical (eps t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 3)
    (ht : 0<t) (he : 0<eta) (hW : 0<nestedInnerWSq t eta alpha y)
    (hV : ∀ j, 0<nestedOuterWSq t eta alpha y j) :
    nestedInternalRadial eps t eta alpha y i.castSucc=
      ∑ j ∈ Finset.univ.erase i, nestedRadialPairTerm eps t eta alpha y i.castSucc j.castSucc := by
  have ha := nestedInner_radialA_physical eps t eta alpha y ht he hW
  have hb := nestedInner_radialB_physical eps t eta alpha y ht he hW
  have h02 : nestedRadialPairTerm eps t eta alpha y 0 2=eps*t*(1-eta^3)*nestedOuterN t eta alpha y 0 :=
    nestedOuter_radial_summand eps t eta alpha (1-eta^3) y 0 ht (hV 0)
  have h12 : nestedRadialPairTerm eps t eta alpha y 1 2=eps*t*(1-eta^3)*nestedOuterN t eta alpha y 1 :=
    nestedOuter_radial_summand eps t eta alpha (1-eta^3) y 1 ht (hV 1)
  have h20 : nestedRadialPairTerm eps t eta alpha y 2 0= -eps*t*(eta^3*alpha)*nestedOuterO t eta alpha y 0 := by
    convert nestedOuter_radial_reverse_summand eps t eta alpha (eta^3*alpha) y 0 ht (hV 0) using 1
    dsimp [nestedRadialPairTerm,nestedChartMass]
    ring
  have h21 : nestedRadialPairTerm eps t eta alpha y 2 1= -eps*t*(eta^3*(1-alpha))*nestedOuterO t eta alpha y 1 := by
    convert nestedOuter_radial_reverse_summand eps t eta alpha (eta^3*(1-alpha)) y 1 ht (hV 1) using 1
    dsimp [nestedRadialPairTerm,nestedChartMass]
    ring
  fin_cases i <;> simp [Fin.sum_univ_three,Finset.sum_erase_eq_sub,nestedInternalRadial,ha,hb,h02,h12,h20,h21]
  all_goals ring

theorem nestedInternalAngular_eq_physical (eps t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 3)
    (ht : 0<t) (he : 0<eta) (hW : 0<nestedInnerWSq t eta alpha y)
    (hV : ∀ j, 0<nestedOuterWSq t eta alpha y j) (heps : 1+eps≠0) :
    nestedInternalAngular eps t eta alpha y i.castSucc=
      ∑ j ∈ Finset.univ.erase i, nestedAngularPairTerm eps t eta alpha y i.castSucc j.castSucc := by
  have ha := nestedInner_angularA_physical eps t eta alpha y ht he hW heps
  have hb := nestedInner_angularB_physical eps t eta alpha y ht he hW heps
  have h02 : nestedAngularPairTerm eps t eta alpha y 0 2=t*(1-eta^3)*nestedOuterL eps t eta alpha y 0 :=
    nestedOuter_angular_summand eps t eta alpha (1-eta^3) y 0 ht (hV 0) heps
  have h12 : nestedAngularPairTerm eps t eta alpha y 1 2=t*(1-eta^3)*nestedOuterL eps t eta alpha y 1 :=
    nestedOuter_angular_summand eps t eta alpha (1-eta^3) y 1 ht (hV 1) heps
  have h20 : nestedAngularPairTerm eps t eta alpha y 2 0= -t*(eta^3*alpha)*nestedOuterL eps t eta alpha y 0 := by
    convert nestedOuter_angular_reverse_summand eps t eta alpha (eta^3*alpha) y 0 ht (hV 0) heps using 1
    dsimp [nestedAngularPairTerm,nestedChartMass]
    ring
  have h21 : nestedAngularPairTerm eps t eta alpha y 2 1= -t*(eta^3*(1-alpha))*nestedOuterL eps t eta alpha y 1 := by
    convert nestedOuter_angular_reverse_summand eps t eta alpha (eta^3*(1-alpha)) y 1 ht (hV 1) heps using 1
    dsimp [nestedAngularPairTerm,nestedChartMass]
    ring
  fin_cases i <;> simp [Fin.sum_univ_three,Finset.sum_erase_eq_sub,nestedInternalAngular,ha,hb,h02,h12,h20,h21]
  all_goals ring

end DominantFiveBody


