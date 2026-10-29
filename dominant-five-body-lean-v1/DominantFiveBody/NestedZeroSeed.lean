import DominantFiveBody.NestedZeroFaces
import DominantFiveBody.NestedUnitBoundary

/-! # Recovery of the actual zero-epsilon nested scalar seed

The seed is obtained from the existing nested branch with eta fixed.
Unit radii, the equilateral angle and all nonzero scaled gaps are derived
from its genuine extended equations and regularity.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

theorem nestedAngularMean_at_zero (eta alpha : ℝ) (y : NestedChartVariables) :
    nestedAngularMean 0 0 eta alpha y=twoSourcePolarAngular 1 (y 0) (y 0) 0 (y 1,y 4) := by
  have hE (i : Fin 3) : nestedAngularExterior 0 0 eta alpha y i.castSucc=
      twoSourcePolarAngular 1 (y 0) (y 0) 0 (y 1,y 4) := by
    rw [nestedAngularExterior,nestedChartPoints_zero_cluster]
    simp [nestedExteriorAngularField,nestedExteriorNewtonField,nestedChartPoints_zero_exterior,
      twoSourcePolarAngular,twoSourceTargetField]
  have h0 := hE 0
  have h1 := hE 1
  have h2 := hE 2
  change nestedAngularExterior 0 0 eta alpha y 0=_ at h0
  change nestedAngularExterior 0 0 eta alpha y 1=_ at h1
  change nestedAngularExterior 0 0 eta alpha y 2=_ at h2
  rw [nestedAngularMean,nestedRowAverage,nestedPairAverage,h0,h1,h2]
  ring

theorem nestedZeroRoot_angle (eta alpha : ℝ) (y : NestedChartVariables)
    (hreg : NestedChartRegular 0 0 eta alpha y)
    (hr : ∀ i,0<nestedChartRadii 0 eta alpha y i)
    (hpi : |y 4|<Real.pi) (hroot : nestedChartExtendedRows 0 0 eta alpha y=0) :
    |y 4|=h := by
  have hu := nestedChart_zero_eps_all_scale_faces 0 eta alpha y hr hroot
  have hy0 := hu.2.2.2.1
  have hy1 := hu.2.2.2.2
  have hne : y 4≠0 := by
    intro hz
    have hh := hreg.2.2.2.2 0
    rw [nestedChartPoints_zero_exterior,nestedChartPoints_zero_cluster,hy0,hy1,hz] at hh
    exact hh rfl
  have hmean : nestedAngularMean 0 0 eta alpha y=0 := congrFun hroot 4
  rw [nestedAngularMean_at_zero,hy0,hy1,
    twoSourcePolarAngular_unit 1 0 (y 4) hne hne hpi (by simpa using hpi)] at hmean
  have hk : coorbitalKernel (y 4)=0 := by simpa using hmean
  exact (coorbitalKernel_zero_iff_abs_eq_h hne hpi).mp hk

theorem nestedZeroRoot_eq_unitPoint (eta alpha tau : ℝ) (y : NestedChartVariables)
    (htau : tau=1 ∨ tau= -1) (hreg : NestedChartRegular 0 0 eta alpha y)
    (hr : ∀ i,0<nestedChartRadii 0 eta alpha y i)
    (hpi : |y 4|<Real.pi) (hclose : |y 4-tau*h|<h)
    (hroot : nestedChartExtendedRows 0 0 eta alpha y=0) :
    y=nestedUnitPoint (tau*h) (y 5) (y 6) := by
  have hu := nestedChart_zero_eps_all_scale_faces 0 eta alpha y hr hroot
  have hangle := nestedZeroRoot_angle eta alpha y hreg hr hpi hroot
  have hh : 0<h := by unfold h; positivity
  have hy4 : y 4=tau*h := by
    have hab := abs_lt.mp hclose
    have hs := sq_abs (y 4)
    rw [hangle] at hs
    rcases htau with rfl | rfl
    · simp only [one_mul] at hab ⊢
      nlinarith
    · simp only [neg_one_mul] at hab ⊢
      nlinarith
  ext i
  fin_cases i
  · exact hu.2.2.2.1
  · exact hu.2.2.2.2
  · exact hu.2.1
  · exact hu.2.2.1
  · exact hy4
  · rfl
  · rfl

theorem nestedUnitPoint_regular_gaps (eps eta alpha psi Z z : ℝ)
    (hreg : NestedChartRegular eps 0 eta alpha (nestedUnitPoint psi Z z)) :
    z≠0 ∧ Z+(1-alpha)*eta*z≠0 ∧ Z-alpha*eta*z≠0 := by
  have hW := hreg.2.2.1
  rw [nestedInnerWSq_formula] at hW
  have hV0 := hreg.2.2.2.1 0
  have hV1 := hreg.2.2.2.1 1
  rw [nestedOuterWSq_formula] at hV0 hV1
  simp only [nestedChartRadii,nestedCoordinates,nestedUnitPoint,nestedOuterRadialGaps,
    nestedOuterAngularGaps] at hW hV0 hV1
  constructor
  · intro hz
    simp [hz] at hW
  constructor
  · intro hz
    simp [hz] at hV0
  · intro hz
    simp [hz] at hV1

end DominantFiveBody
