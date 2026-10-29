import DominantFiveBody.NestedPhysicalKernels

/-! # Actual exterior field and all three divided target differences

Edges 0,1 are a→c,b→c with scale t; edge 2 is a→b with scale tη.
Every divided row is given before setting either scale to zero.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody
set_option maxHeartbeats 800000

abbrev NestedEdge := Fin 3
def nestedEdgeSource : NestedEdge → Satellite := ![0,1,0]
def nestedEdgeTarget : NestedEdge → Satellite := ![2,2,1]
def nestedEdgeScale (t eta : ℝ) : NestedEdge → ℝ := ![t,t,t*eta]
def nestedEdgeRadialGap (eta alpha : ℝ) (y : NestedChartVariables) : NestedEdge → ℝ :=
  ![nestedOuterRadialGaps eta alpha y 0,nestedOuterRadialGaps eta alpha y 1,y 3]
def nestedEdgeDirection (t eta alpha : ℝ) (y : NestedChartVariables) : NestedEdge → Plane :=
  ![nestedOuterDirection t eta alpha y 0,nestedOuterDirection t eta alpha y 1,nestedInnerDirection t eta alpha y]
def nestedEdgeUnitDirection (t eta alpha : ℝ) (y : NestedChartVariables) : NestedEdge → Plane :=
  ![nestedOuterUnitDirection t eta alpha y 0,nestedOuterUnitDirection t eta alpha y 1,nestedInnerUnitDirection t eta alpha y]

theorem nestedEdge_direction_identity (t eta alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge) :
    nestedChartPoints t eta alpha y (nestedEdgeTarget k)-nestedChartPoints t eta alpha y (nestedEdgeSource k)=
      nestedEdgeScale t eta k • nestedEdgeDirection t eta alpha y k := by
  fin_cases k
  · exact nestedOuterDirection_identity t eta alpha y 0
  · exact nestedOuterDirection_identity t eta alpha y 1
  · exact nestedInnerDirection_identity t eta alpha y

theorem nestedEdge_unit_identity (t eta alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge) :
    polarPoint 1 (nestedChartAngles t eta alpha y (nestedEdgeTarget k))-
      polarPoint 1 (nestedChartAngles t eta alpha y (nestedEdgeSource k))=
        nestedEdgeScale t eta k • nestedEdgeUnitDirection t eta alpha y k := by
  fin_cases k
  · exact nestedOuterUnitDirection_identity t eta alpha y 0
  · exact nestedOuterUnitDirection_identity t eta alpha y 1
  · exact nestedInnerUnitDirection_identity t eta alpha y

theorem nestedEdge_radial_identity (t eta alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge) :
    nestedChartRadii t eta alpha y (nestedEdgeTarget k)-nestedChartRadii t eta alpha y (nestedEdgeSource k)=
      nestedEdgeScale t eta k*nestedEdgeRadialGap eta alpha y k := by
  fin_cases k
  · exact (nestedOuter_gaps t eta alpha y 0).1
  · exact (nestedOuter_gaps t eta alpha y 1).1
  · dsimp [nestedEdgeTarget,nestedEdgeSource,nestedEdgeScale,nestedEdgeRadialGap,nestedChartRadii,nestedCoordinates]
    ring

def nestedExteriorNewtonField (t eta alpha : ℝ) (y : NestedChartVariables) (target : Plane) : Plane :=
  (1-t^3) • newtonTargetField (nestedChartPoints t eta alpha y 3) target

def nestedExteriorNewtonDifference (t eta alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge) : Plane :=
  (1-t^3) • dividedNewtonTargetField (nestedChartPoints t eta alpha y 3)
    (nestedChartPoints t eta alpha y (nestedEdgeSource k))
    (nestedChartPoints t eta alpha y (nestedEdgeTarget k)) (nestedEdgeDirection t eta alpha y k)

def nestedExteriorRadialField (eps t eta alpha : ℝ) (y : NestedChartVariables) (target : Plane) : Plane :=
  nestedExteriorNewtonField t eta alpha y target-(1+eps)⁻¹ •
    relativeAverage (nestedChartMass t eta alpha) (nestedChartPoints t eta alpha y)

def nestedExteriorAngularField (eps t eta alpha : ℝ) (y : NestedChartVariables) (target : Plane) : Plane :=
  nestedExteriorNewtonField t eta alpha y target-(1+eps)⁻¹ •
    ((1-t^3) • nestedChartPoints t eta alpha y 3)

def nestedRadialExterior (eps t eta alpha : ℝ) (y : NestedChartVariables) (i : Satellite) : ℝ :=
  nestedChartRadii t eta alpha y i-(nestedChartRadii t eta alpha y i^2)⁻¹+
    eps*inner ℝ (nestedExteriorRadialField eps t eta alpha y (nestedChartPoints t eta alpha y i))
      (polarPoint 1 (nestedChartAngles t eta alpha y i))

def nestedAngularExterior (eps t eta alpha : ℝ) (y : NestedChartVariables) (i : Satellite) : ℝ :=
  inner ℝ (nestedExteriorAngularField eps t eta alpha y (nestedChartPoints t eta alpha y i))
    (quarterTurn (nestedChartPoints t eta alpha y i))

def nestedRadialExteriorDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge) : ℝ :=
  nestedEdgeRadialGap eta alpha y k*(1+
    (nestedChartRadii t eta alpha y (nestedEdgeSource k)+nestedChartRadii t eta alpha y (nestedEdgeTarget k))/
      (nestedChartRadii t eta alpha y (nestedEdgeSource k)^2*nestedChartRadii t eta alpha y (nestedEdgeTarget k)^2))+
    eps*(inner ℝ (nestedExteriorNewtonDifference t eta alpha y k)
      (polarPoint 1 (nestedChartAngles t eta alpha y (nestedEdgeTarget k)))+
      inner ℝ (nestedExteriorRadialField eps t eta alpha y (nestedChartPoints t eta alpha y (nestedEdgeSource k)))
        (nestedEdgeUnitDirection t eta alpha y k))

def nestedAngularExteriorDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge) : ℝ :=
  inner ℝ (nestedExteriorNewtonDifference t eta alpha y k)
    (quarterTurn (nestedChartPoints t eta alpha y (nestedEdgeTarget k)))+
    inner ℝ (nestedExteriorAngularField eps t eta alpha y (nestedChartPoints t eta alpha y (nestedEdgeSource k)))
      (quarterTurn (nestedEdgeDirection t eta alpha y k))

theorem nestedExteriorNewton_difference (t eta alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge)
    (ha : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeSource k))
    (hb : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeTarget k)) :
    nestedExteriorNewtonField t eta alpha y (nestedChartPoints t eta alpha y (nestedEdgeTarget k))-
      nestedExteriorNewtonField t eta alpha y (nestedChartPoints t eta alpha y (nestedEdgeSource k))=
        nestedEdgeScale t eta k • nestedExteriorNewtonDifference t eta alpha y k := by
  unfold nestedExteriorNewtonField nestedExteriorNewtonDifference
  rw [← smul_sub,dividedNewtonTargetField_factor _ _ _ _ _ ha hb (nestedEdge_direction_identity t eta alpha y k)]
  module

theorem nestedRadialExterior_difference (eps t eta alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge)
    (hra : nestedChartRadii t eta alpha y (nestedEdgeSource k)≠0)
    (hrb : nestedChartRadii t eta alpha y (nestedEdgeTarget k)≠0)
    (ha : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeSource k))
    (hb : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeTarget k)) :
    nestedRadialExterior eps t eta alpha y (nestedEdgeTarget k)-nestedRadialExterior eps t eta alpha y (nestedEdgeSource k)=
      nestedEdgeScale t eta k*nestedRadialExteriorDifference eps t eta alpha y k := by
  have hfield : nestedExteriorRadialField eps t eta alpha y (nestedChartPoints t eta alpha y (nestedEdgeTarget k))-
      nestedExteriorRadialField eps t eta alpha y (nestedChartPoints t eta alpha y (nestedEdgeSource k))=
        nestedEdgeScale t eta k • nestedExteriorNewtonDifference t eta alpha y k := by
    unfold nestedExteriorRadialField
    rw [sub_sub_sub_cancel_right,nestedExteriorNewton_difference t eta alpha y k ha hb]
  have hinner := inner_difference_factor _ _ _ _ _ _ (nestedEdgeScale t eta k)
    hfield (nestedEdge_unit_identity t eta alpha y k)
  have hbase : (nestedChartRadii t eta alpha y (nestedEdgeTarget k)-
      (nestedChartRadii t eta alpha y (nestedEdgeTarget k)^2)⁻¹)-
      (nestedChartRadii t eta alpha y (nestedEdgeSource k)-(nestedChartRadii t eta alpha y (nestedEdgeSource k)^2)⁻¹)=
      nestedEdgeScale t eta k*nestedEdgeRadialGap eta alpha y k*(1+
        (nestedChartRadii t eta alpha y (nestedEdgeSource k)+nestedChartRadii t eta alpha y (nestedEdgeTarget k))/
          (nestedChartRadii t eta alpha y (nestedEdgeSource k)^2*nestedChartRadii t eta alpha y (nestedEdgeTarget k)^2)) := by
    rw [← nestedEdge_radial_identity]
    field_simp
    ring
  unfold nestedRadialExterior nestedRadialExteriorDifference
  linear_combination hbase+eps*hinner

theorem nestedAngularExterior_difference (eps t eta alpha : ℝ) (y : NestedChartVariables) (k : NestedEdge)
    (ha : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeSource k))
    (hb : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeTarget k)) :
    nestedAngularExterior eps t eta alpha y (nestedEdgeTarget k)-nestedAngularExterior eps t eta alpha y (nestedEdgeSource k)=
      nestedEdgeScale t eta k*nestedAngularExteriorDifference eps t eta alpha y k := by
  have hfield : nestedExteriorAngularField eps t eta alpha y (nestedChartPoints t eta alpha y (nestedEdgeTarget k))-
      nestedExteriorAngularField eps t eta alpha y (nestedChartPoints t eta alpha y (nestedEdgeSource k))=
        nestedEdgeScale t eta k • nestedExteriorNewtonDifference t eta alpha y k := by
    unfold nestedExteriorAngularField
    rw [sub_sub_sub_cancel_right,nestedExteriorNewton_difference t eta alpha y k ha hb]
  have hrot : quarterTurn (nestedChartPoints t eta alpha y (nestedEdgeTarget k))-
      quarterTurn (nestedChartPoints t eta alpha y (nestedEdgeSource k))=
        nestedEdgeScale t eta k • quarterTurn (nestedEdgeDirection t eta alpha y k) := by
    have h := congrArg quarterTurnLinear (nestedEdge_direction_identity t eta alpha y k)
    simpa only [map_sub,map_smul,quarterTurnLinear_apply] using h
  exact inner_difference_factor _ _ _ _ _ _ (nestedEdgeScale t eta k) hfield hrot

end DominantFiveBody
