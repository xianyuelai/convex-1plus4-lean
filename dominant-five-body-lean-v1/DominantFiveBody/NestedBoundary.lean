import DominantFiveBody.NestedRecovery
import DominantFiveBody.PairUnitBoundary

/-! # Actual nested zero-scale equations

All boundary expressions are evaluations of nestedChartExtendedRows.
The last angular difference is the derivative of the actual scalar
inverse-cube kernel, rather than an independently stipulated matrix.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody
set_option maxHeartbeats 1000000

def nestedChartJacobian (eps t eta alpha : ℝ) (y : NestedChartVariables) :
    NestedChartVariables →L[ℝ] NestedChartVariables :=
  fderiv ℝ (nestedChartExtendedRows eps t eta alpha) y

def nestedBoundaryDisplacement (y : NestedChartVariables) : NestedEdge → ℝ×ℝ :=
  ![(y 2,y 5),(y 2,y 5),(y 3,y 6)]

theorem nestedChartPoints_zero_cluster (eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 3) :
    nestedChartPoints 0 eta alpha y i.castSucc=polarPoint (y 1) (y 4) := by
  fin_cases i <;> simp [nestedChartPoints,polarSatellites,nestedChartRadii,nestedChartAngles,nestedCoordinates]

theorem nestedChartPoints_zero_exterior (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedChartPoints t eta alpha y 3=polarPoint (y 0) 0 := by
  simp [nestedChartPoints,polarSatellites,nestedChartRadii,nestedChartAngles]

theorem nestedEdgeDirection_at_boundary (alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge) :
    nestedEdgeDirection 0 0 alpha y k=polarPointDerivative (y 1,y 4) (nestedBoundaryDisplacement y k) := by
  fin_cases k
  all_goals simp only [nestedEdgeDirection,nestedOuterDirection,nestedInnerDirection,
    zero_mul,pairPointDirection_at_zero]
  all_goals simp [nestedOuterVariables,nestedInnerVariables,nestedOuterRadialGaps,nestedOuterAngularGaps,
    nestedChartRadii,nestedChartAngles,nestedCoordinates,nestedBoundaryDisplacement]

theorem nestedExteriorAngularField_at_boundary (alpha : ℝ) (y : NestedChartVariables) (q : Plane) :
    nestedExteriorAngularField 0 0 0 alpha y q=twoSourceTargetField 1 (y 0) (y 0) 0 q := by
  simp [nestedExteriorAngularField,nestedExteriorNewtonField,nestedChartPoints_zero_exterior,twoSourceTargetField]

theorem nestedExteriorNewtonDifference_at_boundary (alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge)
    (hsep : polarPoint (y 0) 0≠polarPoint (y 1) (y 4)) :
    nestedExteriorNewtonDifference 0 0 alpha y k=
      twoSourceTargetDerivative 1 (y 0) (y 0) 0 (polarPoint (y 1) (y 4))
        (polarPointDerivative (y 1,y 4) (nestedBoundaryDisplacement y k)) := by
  have hs : nestedChartPoints 0 0 alpha y (nestedEdgeSource k)=polarPoint (y 1) (y 4) := by
    fin_cases k
    · exact nestedChartPoints_zero_cluster 0 alpha y 0
    · exact nestedChartPoints_zero_cluster 0 alpha y 1
    · exact nestedChartPoints_zero_cluster 0 alpha y 0
  have ht : nestedChartPoints 0 0 alpha y (nestedEdgeTarget k)=polarPoint (y 1) (y 4) := by
    fin_cases k
    · exact nestedChartPoints_zero_cluster 0 alpha y 2
    · exact nestedChartPoints_zero_cluster 0 alpha y 2
    · exact nestedChartPoints_zero_cluster 0 alpha y 1
  unfold nestedExteriorNewtonDifference
  rw [nestedChartPoints_zero_exterior,hs,ht,nestedEdgeDirection_at_boundary,
    dividedNewtonTargetField_diagonal _ _ _ hsep,(newtonTargetField_hasFDerivAt _ _ hsep).fderiv]
  simp [twoSourceTargetDerivative]

theorem nestedAngularExteriorDifference_at_boundary (alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge)
    (hsep : polarPoint (y 0) 0≠polarPoint (y 1) (y 4)) :
    nestedAngularExteriorDifference 0 0 0 alpha y k=
      (fderiv ℝ (twoSourcePolarAngular 1 (y 0) (y 0) 0) (y 1,y 4)) (nestedBoundaryDisplacement y k) := by
  have hs : nestedChartPoints 0 0 alpha y (nestedEdgeSource k)=polarPoint (y 1) (y 4) := by
    fin_cases k
    · exact nestedChartPoints_zero_cluster 0 alpha y 0
    · exact nestedChartPoints_zero_cluster 0 alpha y 1
    · exact nestedChartPoints_zero_cluster 0 alpha y 0
  have ht : nestedChartPoints 0 0 alpha y (nestedEdgeTarget k)=polarPoint (y 1) (y 4) := by
    fin_cases k
    · exact nestedChartPoints_zero_cluster 0 alpha y 2
    · exact nestedChartPoints_zero_cluster 0 alpha y 2
    · exact nestedChartPoints_zero_cluster 0 alpha y 1
  unfold nestedAngularExteriorDifference
  rw [nestedExteriorNewtonDifference_at_boundary alpha y k hsep,nestedExteriorAngularField_at_boundary,
    nestedEdgeDirection_at_boundary,hs,ht,twoSourcePolarAngular_fderiv_apply _ _ _ _ _ _ hsep hsep]

theorem nestedRadialMean_at_boundary (alpha : ℝ) (y : NestedChartVariables) :
    nestedRadialMean 0 0 0 alpha y=y 1-(y 1^2)⁻¹ := by
  simp [nestedRadialMean,nestedRowAverage,nestedRadialExterior,nestedInternalRadialMean,
    nestedChartRadii,nestedCoordinates,nestedInnerJ,pairInternalRadialMean]

theorem nestedRadialOuterDifference_at_boundary (alpha : ℝ) (y : NestedChartVariables) :
    nestedRadialOuterDifference 0 0 0 alpha y=y 2*(1+2*y 1/(y 1^2*y 1^2)) := by
  simp [nestedRadialOuterDifference,nestedRadialExteriorDifference,nestedInternalRadialOuterDifference,
    nestedEdgeRadialGap,nestedOuterRadialGaps,nestedEdgeSource,nestedEdgeTarget,nestedChartRadii,nestedCoordinates,nestedInnerJOverT]
  ring

theorem nestedRadialInnerDifference_at_boundary (alpha : ℝ) (y : NestedChartVariables) :
    nestedRadialInnerDifference 0 0 0 alpha y=y 3*(1+2*y 1/(y 1^2*y 1^2)) := by
  simp [nestedRadialInnerDifference,nestedRadialExteriorDifference,nestedInternalRadialInnerDifference,
    nestedEdgeRadialGap,nestedEdgeSource,nestedEdgeTarget,nestedChartRadii,nestedCoordinates,pairInternalRadialDifference]
  left
  ring

theorem nestedAngularMean_at_boundary (alpha : ℝ) (y : NestedChartVariables) :
    nestedAngularMean 0 0 0 alpha y=twoSourcePolarAngular 1 (y 0) (y 0) 0 (y 1,y 4) := by
  simp only [nestedAngularMean,nestedRowAverage,zero_pow (by decide : (3 : ℕ)≠0),zero_mul,zero_add,sub_zero,one_mul]
  change nestedAngularExterior 0 0 0 alpha y (2 : Fin 3).castSucc=_
  rw [nestedAngularExterior,nestedChartPoints_zero_cluster,nestedExteriorAngularField_at_boundary]
  rfl

def nestedBoundaryKernel (R psi : ℝ) (v : ℝ×ℝ) : ℝ :=
  inner ℝ (scaledNewtonField (polarPointDerivative (R,psi) v)) (quarterTurn (polarPoint R psi))

theorem nestedBoundaryKernel_formula (R psi : ℝ) (v : ℝ×ℝ) :
    nestedBoundaryKernel R psi v=R^2*v.2/(Real.sqrt (v.1^2+R^2*v.2^2)^3) := by
  let yp : PairChartVariables := ![0,0,R,v.1,0,psi,v.2]
  have hd := pairPointDirection_at_zero 0 yp
  change pairPointDirection 0 0 yp=polarPointDerivative (R,psi) v at hd
  have hn := pairPointDirection_norm_sq 0 0 yp
  rw [hd] at hn
  have hsq : pairChartWSq 0 0 yp=v.1^2+R^2*v.2^2 := by
    simp [pairChartWSq,pairChartRadii,yp]
    left
    ring
  rw [hsq] at hn
  have hn' : ‖polarPointDerivative (R,psi) v‖=Real.sqrt (v.1^2+R^2*v.2^2) := by
    rw [← hn,Real.sqrt_sq_eq_abs,abs_norm]
  have hi := pairPointDirection_angular_left 0 0 yp
  rw [hd] at hi
  have hi' : inner ℝ (polarPointDerivative (R,psi) v) (quarterTurn (polarPoint R psi))=R^2*v.2 := by
    simpa [yp,pairChartRadii,pairChartAngles,pow_two] using hi
  unfold nestedBoundaryKernel scaledNewtonField
  rw [real_inner_smul_left,hn',hi']
  ring

theorem nestedBoundaryKernel_fderiv_apply (R psi : ℝ) (v w : ℝ×ℝ)
    (hne : polarPointDerivative (R,psi) v≠0) :
    (fderiv ℝ (nestedBoundaryKernel R psi) v) w=
      -inner ℝ (newtonTargetDerivative 0 (-polarPointDerivative (R,psi) v)
        (polarPointDerivative (R,psi) w)) (quarterTurn (polarPoint R psi)) := by
  have hh := (newtonTargetField_hasFDerivAt 0 (-polarPointDerivative (R,psi) v)
    (by simpa using hne)).comp v (-(polarPointDerivative (R,psi))).hasFDerivAt
  have hi := hh.inner ℝ (hasFDerivAt_const (quarterTurn (polarPoint R psi)) v)
  have heq : (fun u : ℝ×ℝ => inner ℝ (newtonTargetField 0 (-polarPointDerivative (R,psi) u))
      (quarterTurn (polarPoint R psi)))=nestedBoundaryKernel R psi := by
    funext u
    rw [nestedBoundaryKernel,scaledNewtonField_eq_target]
  simp only [Function.comp_apply,neg_apply] at hi
  rw [heq] at hi
  rw [hi.fderiv]
  simp [ContinuousLinearMap.comp_apply,fderivInnerCLM_apply]

theorem nestedInnerWSq_at_boundary (alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerWSq 0 0 alpha y=y 3^2+y 1^2*y 6^2 := by
  simp [nestedInnerWSq,pairChartWSq,nestedInnerVariables,pairChartRadii,pow_two]

theorem nestedOuterWSq_at_boundary (alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedOuterWSq 0 0 alpha y i=y 2^2+y 1^2*y 5^2 := by
  fin_cases i <;> simp [nestedOuterWSq,pairChartWSq,nestedOuterVariables,pairChartRadii,
    nestedChartRadii,nestedChartAngles,nestedCoordinates,nestedOuterRadialGaps,nestedOuterAngularGaps,pow_two]

theorem nestedOuterDirection_at_boundary (alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedOuterDirection 0 0 alpha y i=polarPointDerivative (y 1,y 4) (y 2,y 5) := by
  fin_cases i
  · exact nestedEdgeDirection_at_boundary alpha y 0
  · exact nestedEdgeDirection_at_boundary alpha y 1

theorem nestedInnerDirection_at_boundary (alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerDirection 0 0 alpha y=polarPointDerivative (y 1,y 4) (y 3,y 6) :=
  nestedEdgeDirection_at_boundary alpha y 2

theorem nestedOuterL_at_boundary (alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedOuterL 0 0 0 alpha y i=nestedBoundaryKernel (y 1) (y 4) (y 2,y 5) := by
  have hp : nestedChartPoints 0 0 alpha y (i.castAdd 2)=polarPoint (y 1) (y 4) := by
    fin_cases i
    · exact nestedChartPoints_zero_cluster 0 alpha y 0
    · exact nestedChartPoints_zero_cluster 0 alpha y 1
  unfold nestedOuterL nestedOuterAngularField nestedOuterNewton
  rw [nestedOuterDirection_at_boundary,hp]
  simp [nestedBoundaryKernel]

theorem nestedInnerM_at_boundary (alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerM 0 0 0 alpha y=nestedBoundaryKernel (y 1) (y 4) (y 3,y 6) := by
  rw [nestedInnerM_formula,nestedBoundaryKernel_formula,nestedInnerW,nestedInnerWSq_at_boundary]
  simp [nestedChartRadii,nestedCoordinates]
  ring

theorem nestedOuterLDifference_at_boundary (alpha : ℝ) (y : NestedChartVariables)
    (hV : 0<y 2^2+y 1^2*y 5^2) :
    nestedOuterLDifference 0 0 0 alpha y=
      -(fderiv ℝ (nestedBoundaryKernel (y 1) (y 4)) (y 2,y 5)) (y 3,y 6) := by
  have hne : polarPointDerivative (y 1,y 4) (y 2,y 5)≠0 := by
    rw [← nestedOuterDirection_at_boundary alpha y 0]
    exact nestedOuterDirection_ne_zero 0 0 alpha y 0 (by rwa [nestedOuterWSq_at_boundary])
  rw [nestedBoundaryKernel_fderiv_apply _ _ _ _ hne]
  unfold nestedOuterLDifference nestedOuterNewtonDifference
  rw [nestedOuterDirection_at_boundary,nestedOuterDirection_at_boundary,nestedInnerDirection_at_boundary]
  have hp : nestedChartPoints 0 0 alpha y 1=polarPoint (y 1) (y 4) := nestedChartPoints_zero_cluster 0 alpha y 1
  rw [hp,dividedNewtonTargetField_diagonal _ _ _ (by simpa using hne),
    (newtonTargetField_hasFDerivAt _ _ (by simpa using hne)).fderiv]
  simp

theorem nestedAngularOuterDifference_at_boundary (alpha : ℝ) (y : NestedChartVariables)
    (hsep : polarPoint (y 0) 0≠polarPoint (y 1) (y 4)) :
    nestedAngularOuterDifference 0 0 0 alpha y=
      (fderiv ℝ (twoSourcePolarAngular 1 (y 0) (y 0) 0) (y 1,y 4)) (y 2,y 5)-
        nestedBoundaryKernel (y 1) (y 4) (y 2,y 5) := by
  unfold nestedAngularOuterDifference nestedInternalAngularOuterDifference
  rw [nestedAngularExteriorDifference_at_boundary alpha y 0 hsep,nestedAngularExteriorDifference_at_boundary alpha y 1 hsep,
    nestedOuterL_at_boundary,nestedOuterL_at_boundary]
  change alpha*(_ : ℝ)+(1-alpha)*_-(alpha*_+(1-alpha)*_)=_
  dsimp [nestedBoundaryDisplacement]
  ring

theorem nestedAngularInnerDifference_at_boundary (alpha : ℝ) (y : NestedChartVariables)
    (hsep : polarPoint (y 0) 0≠polarPoint (y 1) (y 4)) (hV : 0<y 2^2+y 1^2*y 5^2) :
    nestedAngularInnerDifference 0 0 0 alpha y=
      (fderiv ℝ (twoSourcePolarAngular 1 (y 0) (y 0) 0) (y 1,y 4)) (y 3,y 6)-
        (fderiv ℝ (nestedBoundaryKernel (y 1) (y 4)) (y 2,y 5)) (y 3,y 6)-
          nestedBoundaryKernel (y 1) (y 4) (y 3,y 6) := by
  unfold nestedAngularInnerDifference nestedInternalAngularInnerDifference
  rw [nestedAngularExteriorDifference_at_boundary alpha y 2 hsep,nestedOuterLDifference_at_boundary alpha y hV,
    nestedInnerM_at_boundary]
  dsimp [nestedBoundaryDisplacement]
  ring

end DominantFiveBody
