import DominantFiveBody.NestedChart
import DominantFiveBody.PairInternal

/-! # Explicit two-scale edges and positive-scale distances

The inner edge and each outer edge are actual single-scale polar edges.
Their signed divided directions are everywhere smooth, with no t or η
denominator. Distance equalities require the corresponding positive scale.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

set_option maxHeartbeats 800000

def nestedInnerVariables (t eta : ℝ) (y : NestedChartVariables) : PairChartVariables :=
  ![0,0,y 1-(1-eta^3)*t*y 2,y 3,0,y 4-(1-eta^3)*t*y 5,y 6]

def nestedOuterRadialGaps (eta alpha : ℝ) (y : NestedChartVariables) : Fin 2 → ℝ :=
  ![y 2+(1-alpha)*eta*y 3,y 2-alpha*eta*y 3]

def nestedOuterAngularGaps (eta alpha : ℝ) (y : NestedChartVariables) : Fin 2 → ℝ :=
  ![y 5+(1-alpha)*eta*y 6,y 5-alpha*eta*y 6]

def nestedOuterVariables (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : PairChartVariables :=
  ![0,0,nestedChartRadii t eta alpha y (i.castAdd 2),nestedOuterRadialGaps eta alpha y i,
    0,nestedChartAngles t eta alpha y (i.castAdd 2),nestedOuterAngularGaps eta alpha y i]

theorem nestedInner_coordinates (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) (i.castAdd 2)=
      nestedChartRadii t eta alpha y (i.castAdd 2) ∧
    pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) (i.castAdd 2)=
      nestedChartAngles t eta alpha y (i.castAdd 2) := by
  constructor <;> fin_cases i <;> dsimp [pairChartRadii,pairChartAngles,nestedInnerVariables,
    nestedChartRadii,nestedChartAngles,nestedCoordinates] <;> ring

theorem nestedOuter_coordinates (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    pairChartRadii t 1 (nestedOuterVariables t eta alpha y i) 0=nestedChartRadii t eta alpha y (i.castAdd 2) ∧
    pairChartRadii t 1 (nestedOuterVariables t eta alpha y i) 1=nestedChartRadii t eta alpha y 2 ∧
    pairChartAngles t 1 (nestedOuterVariables t eta alpha y i) 0=nestedChartAngles t eta alpha y (i.castAdd 2) ∧
    pairChartAngles t 1 (nestedOuterVariables t eta alpha y i) 1=nestedChartAngles t eta alpha y 2 := by
  refine ⟨?_,?_,?_,?_⟩ <;> fin_cases i <;> dsimp [pairChartRadii,pairChartAngles,nestedOuterVariables,
    nestedOuterRadialGaps,nestedOuterAngularGaps,nestedChartRadii,nestedChartAngles,nestedCoordinates] <;> ring

def nestedInnerDirection (t eta alpha : ℝ) (y : NestedChartVariables) : Plane :=
  pairPointDirection (t*eta) alpha (nestedInnerVariables t eta y)

def nestedInnerUnitDirection (t eta alpha : ℝ) (y : NestedChartVariables) : Plane :=
  pairUnitDirection (t*eta) alpha (nestedInnerVariables t eta y)

def nestedOuterDirection (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : Plane :=
  pairPointDirection t 1 (nestedOuterVariables t eta alpha y i)

def nestedOuterUnitDirection (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : Plane :=
  pairUnitDirection t 1 (nestedOuterVariables t eta alpha y i)

def nestedInnerWSq (t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  pairChartWSq (t*eta) alpha (nestedInnerVariables t eta y)

def nestedOuterWSq (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : ℝ :=
  pairChartWSq t 1 (nestedOuterVariables t eta alpha y i)

def nestedInnerW (t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  Real.sqrt (nestedInnerWSq t eta alpha y)

def nestedOuterW (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : ℝ :=
  Real.sqrt (nestedOuterWSq t eta alpha y i)

theorem nestedInnerWSq_formula (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerWSq t eta alpha y=y 3^2+
      nestedChartRadii t eta alpha y 0*nestedChartRadii t eta alpha y 1*y 6^2*
        Real.sinc (t*eta*y 6/2)^2 := by
  unfold nestedInnerWSq pairChartWSq
  rw [show pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartRadii t eta alpha y 0 from (nestedInner_coordinates t eta alpha y 0).1,show pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartRadii t eta alpha y 1 from (nestedInner_coordinates t eta alpha y 1).1]
  rfl

theorem nestedOuterWSq_formula (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedOuterWSq t eta alpha y i=nestedOuterRadialGaps eta alpha y i^2+
      nestedChartRadii t eta alpha y (i.castAdd 2)*nestedChartRadii t eta alpha y 2*
        nestedOuterAngularGaps eta alpha y i^2*Real.sinc (t*nestedOuterAngularGaps eta alpha y i/2)^2 := by
  unfold nestedOuterWSq pairChartWSq
  rw [(nestedOuter_coordinates t eta alpha y i).1,(nestedOuter_coordinates t eta alpha y i).2.1]
  rfl

theorem nestedInnerDirection_identity (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedChartPoints t eta alpha y 1-nestedChartPoints t eta alpha y 0=
      (t*eta) • nestedInnerDirection t eta alpha y := by
  have h := pairPointDirection_identity (t*eta) alpha (nestedInnerVariables t eta y)
  rw [show pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartRadii t eta alpha y 0 from (nestedInner_coordinates t eta alpha y 0).1,show pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartRadii t eta alpha y 1 from (nestedInner_coordinates t eta alpha y 1).1,
    show pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartAngles t eta alpha y 0 from (nestedInner_coordinates t eta alpha y 0).2,show pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartAngles t eta alpha y 1 from (nestedInner_coordinates t eta alpha y 1).2] at h
  exact h

theorem nestedInnerUnitDirection_identity (t eta alpha : ℝ) (y : NestedChartVariables) :
    polarPoint 1 (nestedChartAngles t eta alpha y 1)-polarPoint 1 (nestedChartAngles t eta alpha y 0)=
      (t*eta) • nestedInnerUnitDirection t eta alpha y := by
  have h := pairUnitDirection_identity (t*eta) alpha (nestedInnerVariables t eta y)
  rw [show pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartAngles t eta alpha y 0 from (nestedInner_coordinates t eta alpha y 0).2,show pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartAngles t eta alpha y 1 from (nestedInner_coordinates t eta alpha y 1).2] at h
  exact h

theorem nestedOuterDirection_identity (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedChartPoints t eta alpha y 2-nestedChartPoints t eta alpha y (i.castAdd 2)=
      t • nestedOuterDirection t eta alpha y i := by
  have h := pairPointDirection_identity t 1 (nestedOuterVariables t eta alpha y i)
  obtain ⟨hra,hrb,haa,hab⟩ := nestedOuter_coordinates t eta alpha y i
  rw [hra,hrb,haa,hab] at h
  exact h

theorem nestedOuterUnitDirection_identity (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    polarPoint 1 (nestedChartAngles t eta alpha y 2)-polarPoint 1 (nestedChartAngles t eta alpha y (i.castAdd 2))=
      t • nestedOuterUnitDirection t eta alpha y i := by
  have h := pairUnitDirection_identity t 1 (nestedOuterVariables t eta alpha y i)
  rw [(nestedOuter_coordinates t eta alpha y i).2.2.1,(nestedOuter_coordinates t eta alpha y i).2.2.2] at h
  exact h

theorem nestedInner_distance (t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hW : 0<nestedInnerWSq t eta alpha y) :
    satelliteDistance (nestedChartPoints t eta alpha y) 0 1=t*eta*nestedInnerW t eta alpha y := by
  have h := pairChart_distance (t*eta) alpha (nestedInnerVariables t eta y) (mul_pos ht he) hW
  unfold satelliteDistance polarSatellites at h
  rw [show pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartRadii t eta alpha y 0 from (nestedInner_coordinates t eta alpha y 0).1,show pairChartRadii (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartRadii t eta alpha y 1 from (nestedInner_coordinates t eta alpha y 1).1,
    show pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 0=nestedChartAngles t eta alpha y 0 from (nestedInner_coordinates t eta alpha y 0).2,show pairChartAngles (t*eta) alpha (nestedInnerVariables t eta y) 1=nestedChartAngles t eta alpha y 1 from (nestedInner_coordinates t eta alpha y 1).2] at h
  exact h

theorem nestedOuter_distance (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2)
    (ht : 0<t) (hV : 0<nestedOuterWSq t eta alpha y i) :
    satelliteDistance (nestedChartPoints t eta alpha y) (i.castAdd 2) 2=t*nestedOuterW t eta alpha y i := by
  have h := pairChart_distance t 1 (nestedOuterVariables t eta alpha y i) ht hV
  unfold satelliteDistance polarSatellites at h
  obtain ⟨hra,hrb,haa,hab⟩ := nestedOuter_coordinates t eta alpha y i
  rw [hra,hrb,haa,hab] at h
  exact h

@[fun_prop] theorem nestedChartMass_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedChartMass (v.1 1) (v.1 2) (v.1 3) i) := by
  fin_cases i <;> simp [nestedChartMass] <;> fun_prop

@[fun_prop] theorem nestedChartRadii_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedChartRadii (v.1 1) (v.1 2) (v.1 3) v.2 i) := by
  fin_cases i <;> simp [nestedChartRadii,nestedCoordinates] <;> fun_prop

@[fun_prop] theorem nestedChartAngles_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedChartAngles (v.1 1) (v.1 2) (v.1 3) v.2 i) := by
  fin_cases i <;> simp [nestedChartAngles,nestedCoordinates] <;> fun_prop

@[fun_prop] theorem nestedChartPoints_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 i) :=
  (polarPoint_contDiff n).comp ((nestedChartRadii_joint_contDiff n i).prodMk (nestedChartAngles_joint_contDiff n i))

@[fun_prop] theorem nestedUnit_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : NestedJointVariables => polarPoint 1 (nestedChartAngles (v.1 1) (v.1 2) (v.1 3) v.2 i)) :=
  (polarPoint_contDiff n).comp (contDiff_const.prodMk (nestedChartAngles_joint_contDiff n i))

def nestedInnerPairJoint (v : NestedJointVariables) : PairJointVariables :=
  ((![v.1 0,v.1 1*v.1 2,0,v.1 3] : Fin 4 → ℝ),nestedInnerVariables (v.1 1) (v.1 2) v.2)

def nestedOuterPairJoint (i : Fin 2) (v : NestedJointVariables) : PairJointVariables :=
  ((![v.1 0,v.1 1,0,1] : Fin 4 → ℝ),nestedOuterVariables (v.1 1) (v.1 2) (v.1 3) v.2 i)

@[fun_prop] theorem nestedInnerPairJoint_contDiff (n : ℕ∞ω) : ContDiff ℝ n nestedInnerPairJoint := by
  unfold nestedInnerPairJoint
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  · apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [nestedInnerVariables] <;> fun_prop

@[fun_prop] theorem nestedOuterPairJoint_contDiff (n : ℕ∞ω) (i : Fin 2) : ContDiff ℝ n (nestedOuterPairJoint i) := by
  unfold nestedOuterPairJoint
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro j
    fin_cases j <;> simp <;> fun_prop
  · apply contDiff_pi.mpr
    intro j
    fin_cases j <;> simp [nestedOuterVariables]
    all_goals try fun_prop
    all_goals fin_cases i <;> simp [nestedOuterRadialGaps,nestedOuterAngularGaps] <;> fun_prop

@[fun_prop] theorem nestedInnerDirection_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedInnerDirection (v.1 1) (v.1 2) (v.1 3) v.2) :=
  (pairPointDirection_joint_contDiff n).comp (nestedInnerPairJoint_contDiff n)

@[fun_prop] theorem nestedInnerUnitDirection_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedInnerUnitDirection (v.1 1) (v.1 2) (v.1 3) v.2) :=
  (pairUnitDirection_joint_contDiff n).comp (nestedInnerPairJoint_contDiff n)

@[fun_prop] theorem nestedOuterDirection_joint_contDiff (n : ℕ∞ω) (i : Fin 2) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedOuterDirection (v.1 1) (v.1 2) (v.1 3) v.2 i) :=
  (pairPointDirection_joint_contDiff n).comp (nestedOuterPairJoint_contDiff n i)

@[fun_prop] theorem nestedOuterUnitDirection_joint_contDiff (n : ℕ∞ω) (i : Fin 2) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedOuterUnitDirection (v.1 1) (v.1 2) (v.1 3) v.2 i) :=
  (pairUnitDirection_joint_contDiff n).comp (nestedOuterPairJoint_contDiff n i)

end DominantFiveBody

