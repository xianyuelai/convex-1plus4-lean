import DominantFiveBody.PairDirections
import DominantFiveBody.PairInternal

/-! # Actual exterior fields and signed target differences for a complete pair -/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

def pairChartPoints (t alpha : ℝ) (y : PairChartVariables) : SatelliteConfiguration :=
  polarSatellites (pairChartRadii t alpha y) (pairChartAngles t alpha y)

def pairExteriorNewtonField (t p alpha : ℝ) (y : PairChartVariables) (target : Plane) : Plane :=
  pairChartMass t p alpha 2 • newtonTargetField (pairChartPoints t alpha y 2) target+
    pairChartMass t p alpha 3 • newtonTargetField (pairChartPoints t alpha y 3) target

def pairExteriorNewtonDifference (t p alpha : ℝ) (y : PairChartVariables) : Plane :=
  pairChartMass t p alpha 2 • dividedNewtonTargetField
      (pairChartPoints t alpha y 2) (pairChartPoints t alpha y 0)
      (pairChartPoints t alpha y 1) (pairPointDirection t alpha y)+
    pairChartMass t p alpha 3 • dividedNewtonTargetField
      (pairChartPoints t alpha y 3) (pairChartPoints t alpha y 0)
      (pairChartPoints t alpha y 1) (pairPointDirection t alpha y)

def pairExteriorRadialField (eps t p alpha : ℝ) (y : PairChartVariables) (target : Plane) : Plane :=
  pairExteriorNewtonField t p alpha y target-(1+eps)⁻¹ •
    relativeAverage (pairChartMass t p alpha) (pairChartPoints t alpha y)

def pairExteriorAngularField (eps t p alpha : ℝ) (y : PairChartVariables) (target : Plane) : Plane :=
  pairExteriorNewtonField t p alpha y target-(1+eps)⁻¹ •
    (pairChartMass t p alpha 2 • pairChartPoints t alpha y 2+
      pairChartMass t p alpha 3 • pairChartPoints t alpha y 3)

def pairRadialExterior (eps t p alpha : ℝ) (y : PairChartVariables) (i : Satellite) : ℝ :=
  pairChartRadii t alpha y i-(pairChartRadii t alpha y i^2)⁻¹+
    eps*inner ℝ (pairExteriorRadialField eps t p alpha y (pairChartPoints t alpha y i))
      (polarPoint 1 (pairChartAngles t alpha y i))

def pairAngularExterior (eps t p alpha : ℝ) (y : PairChartVariables) (i : Satellite) : ℝ :=
  inner ℝ (pairExteriorAngularField eps t p alpha y (pairChartPoints t alpha y i))
    (quarterTurn (pairChartPoints t alpha y i))

theorem newtonTargetField_radial (r s theta phi : ℝ) :
    inner ℝ (newtonTargetField (polarPoint s phi) (polarPoint r theta))
      (polarPoint 1 theta)=
      -(r-s*Real.cos (phi-theta))/‖polarPoint r theta-polarPoint s phi‖^3 := by
  simp only [newtonTargetField, real_inner_smul_left, inner_sub_left,
    polarPoint_inner_radial, sub_self, Real.cos_zero, mul_one]
  rw [norm_sub_rev]
  ring

theorem newtonTargetField_angular (c r s theta phi : ℝ) :
    inner ℝ (newtonTargetField (polarPoint s phi) (polarPoint r theta)-c • polarPoint s phi)
      (quarterTurn (polarPoint r theta))=
      r*s*Real.sin (phi-theta)*((‖polarPoint r theta-polarPoint s phi‖^3)⁻¹-c) := by
  simp only [newtonTargetField, inner_sub_left, real_inner_smul_left,
    polarPoint_inner_rotation, sub_self, Real.sin_zero, mul_zero, sub_zero]
  rw [norm_sub_rev]
  ring

theorem radialResidual_newton_projection (eps : ℝ) (mu r theta : Satellite → ℝ) (i : Satellite) :
    radialResidual eps mu r theta i=r i-(r i^2)⁻¹+
      eps*(∑ j ∈ Finset.univ.erase i, mu j*inner ℝ
        (newtonTargetField (polarSatellites r theta j) (polarSatellites r theta i))
          (polarPoint 1 (theta i)))-
      eps/(1+eps)*inner ℝ (relativeAverage mu (polarSatellites r theta)) (polarPoint 1 (theta i)) := by
  have hsum : (∑ j ∈ Finset.univ.erase i, mu j*inner ℝ
      (newtonTargetField (polarSatellites r theta j) (polarSatellites r theta i))
      (polarPoint 1 (theta i)))=
      -(∑ j ∈ Finset.univ.erase i, mu j*(r i-r j*Real.cos (theta j-theta i))/
        satelliteDistance (polarSatellites r theta) i j^3) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [polarSatellites,newtonTargetField_radial,satelliteDistance]
    ring
  rw [hsum]
  unfold radialResidual
  ring

theorem angularResidual_newton_projection (eps : ℝ) (mu r theta : Satellite → ℝ) (i : Satellite) :
    angularResidual eps mu r theta i=
      ∑ j ∈ Finset.univ.erase i, mu j*inner ℝ
        (newtonTargetField (polarSatellites r theta j) (polarSatellites r theta i)-
          (1+eps)⁻¹ • polarSatellites r theta j)
        (quarterTurn (polarSatellites r theta i)) := by
  unfold angularResidual
  simp only [polarSatellites,newtonTargetField_angular,satelliteDistance]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pairExteriorNewtonDifference_identity (t p alpha : ℝ) (y : PairChartVariables)
    (ht : t≠0) (hsep : ∀ i ∈ ({2,3} : Finset Satellite),
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 0 ∧
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 1) :
    pairExteriorNewtonField t p alpha y (pairChartPoints t alpha y 1)-
      pairExteriorNewtonField t p alpha y (pairChartPoints t alpha y 0)=
        t • pairExteriorNewtonDifference t p alpha y := by
  have hg : pairChartPoints t alpha y 1-pairChartPoints t alpha y 0=
      t • pairPointDirection t alpha y := pairPointDirection_identity t alpha y
  have h2 := dividedNewtonTargetField_eq (pairChartPoints t alpha y 2)
    (pairChartPoints t alpha y 0) (pairChartPoints t alpha y 1)
    (pairPointDirection t alpha y) t ht (hsep 2 (by simp)).1 (hsep 2 (by simp)).2 hg
  have h3 := dividedNewtonTargetField_eq (pairChartPoints t alpha y 3)
    (pairChartPoints t alpha y 0) (pairChartPoints t alpha y 1)
    (pairPointDirection t alpha y) t ht (hsep 3 (by simp)).1 (hsep 3 (by simp)).2 hg
  unfold pairExteriorNewtonField pairExteriorNewtonDifference
  rw [h2,h3]
  simp only [smul_add,smul_smul]
  have hc2 : t*(pairChartMass t p alpha 2*t⁻¹)=pairChartMass t p alpha 2 := by
    field_simp
  have hc3 : t*(pairChartMass t p alpha 3*t⁻¹)=pairChartMass t p alpha 3 := by
    field_simp
  rw [hc2,hc3]
  module

theorem pairExteriorRadialField_difference_identity (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : t≠0) (hsep : ∀ i ∈ ({2,3} : Finset Satellite),
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 0 ∧
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 1) :
    pairExteriorRadialField eps t p alpha y (pairChartPoints t alpha y 1)-
      pairExteriorRadialField eps t p alpha y (pairChartPoints t alpha y 0)=
        t • pairExteriorNewtonDifference t p alpha y := by
  unfold pairExteriorRadialField
  rw [sub_sub_sub_cancel_right,pairExteriorNewtonDifference_identity t p alpha y ht hsep]

theorem pairExteriorAngularField_difference_identity (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : t≠0) (hsep : ∀ i ∈ ({2,3} : Finset Satellite),
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 0 ∧
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 1) :
    pairExteriorAngularField eps t p alpha y (pairChartPoints t alpha y 1)-
      pairExteriorAngularField eps t p alpha y (pairChartPoints t alpha y 0)=
        t • pairExteriorNewtonDifference t p alpha y := by
  unfold pairExteriorAngularField
  rw [sub_sub_sub_cancel_right,pairExteriorNewtonDifference_identity t p alpha y ht hsep]

theorem pairRadialExteriorA_recovery (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) :
    radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
      (pairChartAngles t alpha y) 0=
      pairRadialExterior eps t p alpha y 0+pairInternalRadialA eps t alpha y := by
  rw [radialResidual_newton_projection]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),Fin.sum_univ_four]
  rw [pairInternalRadialA_eq_physical eps t alpha y ht hW]
  unfold pairRadialExterior pairExteriorRadialField pairExteriorNewtonField pairChartPoints
  simp only [inner_add_left,inner_sub_left,real_inner_smul_left]
  simp [polarSatellites,newtonTargetField_radial,satelliteDistance]
  have hm : pairChartMass t p alpha 1=pairChartMass t 0 alpha 1 := rfl
  rw [hm]
  ring

theorem pairRadialExteriorB_recovery (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) :
    radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
      (pairChartAngles t alpha y) 1=
      pairRadialExterior eps t p alpha y 1+pairInternalRadialB eps t alpha y := by
  rw [radialResidual_newton_projection]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 1),Fin.sum_univ_four]
  rw [pairInternalRadialB_eq_physical eps t alpha y ht hW]
  unfold pairRadialExterior pairExteriorRadialField pairExteriorNewtonField pairChartPoints
  simp only [inner_add_left,inner_sub_left,real_inner_smul_left]
  simp [polarSatellites,newtonTargetField_radial,satelliteDistance]
  have hm : pairChartMass t p alpha 0=pairChartMass t 0 alpha 0 := rfl
  rw [hm]
  ring

theorem pairAngularExteriorA_recovery (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) (heps : 1+eps≠0) :
    angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
      (pairChartAngles t alpha y) 0=
      pairAngularExterior eps t p alpha y 0+pairInternalAngularA eps t alpha y := by
  rw [angularResidual_newton_projection]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0),Fin.sum_univ_four]
  rw [pairInternalAngularA_eq_physical eps t alpha y ht hW heps]
  unfold pairAngularExterior pairExteriorAngularField pairExteriorNewtonField pairChartPoints
  simp [newtonTargetField,polarSatellites,inner_add_left,inner_sub_left,
    real_inner_smul_left,quarterTurn_inner_self,polarPoint_inner_rotation]
  have hm : pairChartMass t p alpha 1=pairChartMass t 0 alpha 1 := rfl
  rw [hm]
  unfold satelliteDistance polarSatellites
  simp only [norm_sub_rev]
  ring

theorem pairAngularExteriorB_recovery (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) (heps : 1+eps≠0) :
    angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
      (pairChartAngles t alpha y) 1=
      pairAngularExterior eps t p alpha y 1+pairInternalAngularB eps t alpha y := by
  rw [angularResidual_newton_projection]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 1),Fin.sum_univ_four]
  rw [pairInternalAngularB_eq_physical eps t alpha y ht hW heps]
  unfold pairAngularExterior pairExteriorAngularField pairExteriorNewtonField pairChartPoints
  simp [newtonTargetField,polarSatellites,inner_add_left,inner_sub_left,
    real_inner_smul_left,quarterTurn_inner_self,polarPoint_inner_rotation]
  have hm : pairChartMass t p alpha 0=pairChartMass t 0 alpha 0 := rfl
  rw [hm]
  unfold satelliteDistance polarSatellites
  simp only [norm_sub_rev]
  ring

@[fun_prop] theorem pairChartPoints_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : PairJointVariables => pairChartPoints (v.1 1) (v.1 3) v.2 i) :=
  (polarPoint_contDiff n).comp
    ((pairChartRadii_joint_contDiff n i).prodMk (pairChartAngles_joint_contDiff n i))

@[fun_prop] theorem pairUnit_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : PairJointVariables => polarPoint 1 (pairChartAngles (v.1 1) (v.1 3) v.2 i)) :=
  (polarPoint_contDiff n).comp (contDiff_const.prodMk (pairChartAngles_joint_contDiff n i))

theorem newtonTargetField_joint_contDiffAt (n : ℕ∞ω) (v : Plane×Plane) (hsep : v.1≠v.2) :
    ContDiffAt ℝ n (fun w : Plane×Plane => newtonTargetField w.1 w.2) v := by
  have hsub : ContDiffAt ℝ n (fun w : Plane×Plane => w.1-w.2) v := contDiffAt_fst.sub contDiffAt_snd
  have hn := hsub.norm ℝ (sub_ne_zero.mpr hsep)
  unfold newtonTargetField
  exact ((hn.pow 3).inv (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsep)))).smul hsub

theorem pairExteriorNewtonField_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables) (i : Satellite)
    (hsep : ∀ j ∈ ({2,3} : Finset Satellite),
      pairChartPoints (v.1 1) (v.1 3) v.2 j≠pairChartPoints (v.1 1) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairExteriorNewtonField (w.1 1) (w.1 2) (w.1 3) w.2
        (pairChartPoints (w.1 1) (w.1 3) w.2 i)) v := by
  have hs (j : Satellite) := ((pairChartPoints_joint_contDiff n j).prodMk
    (pairChartPoints_joint_contDiff n i)).contDiffAt (x := v)
  have h2 := (newtonTargetField_joint_contDiffAt n
    (pairChartPoints (v.1 1) (v.1 3) v.2 2,pairChartPoints (v.1 1) (v.1 3) v.2 i)
    (hsep 2 (by simp))).comp v (hs 2)
  have h3 := (newtonTargetField_joint_contDiffAt n
    (pairChartPoints (v.1 1) (v.1 3) v.2 3,pairChartPoints (v.1 1) (v.1 3) v.2 i)
    (hsep 3 (by simp))).comp v (hs 3)
  exact (((pairChartMass_joint_contDiff n 2).contDiffAt).smul h2).add
    (((pairChartMass_joint_contDiff n 3).contDiffAt).smul h3)

theorem pairExteriorNewtonDifference_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hsep : ∀ j ∈ ({2,3} : Finset Satellite),
      pairChartPoints (v.1 1) (v.1 3) v.2 j≠pairChartPoints (v.1 1) (v.1 3) v.2 0 ∧
      pairChartPoints (v.1 1) (v.1 3) v.2 j≠pairChartPoints (v.1 1) (v.1 3) v.2 1) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairExteriorNewtonDifference (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have hs (j : Satellite) : ContDiffAt ℝ n (fun w : PairJointVariables =>
      ((pairChartPoints (w.1 1) (w.1 3) w.2 j,pairChartPoints (w.1 1) (w.1 3) w.2 0),
        (pairChartPoints (w.1 1) (w.1 3) w.2 1,pairPointDirection (w.1 1) (w.1 3) w.2))) v :=
    (((pairChartPoints_joint_contDiff n j).prodMk (pairChartPoints_joint_contDiff n 0)).prodMk
      ((pairChartPoints_joint_contDiff n 1).prodMk (pairPointDirection_joint_contDiff n))).contDiffAt
  have h2 := (dividedNewtonTargetField_joint_contDiffAt n
    ((pairChartPoints (v.1 1) (v.1 3) v.2 2,pairChartPoints (v.1 1) (v.1 3) v.2 0),
      (pairChartPoints (v.1 1) (v.1 3) v.2 1,pairPointDirection (v.1 1) (v.1 3) v.2))
    (hsep 2 (by simp)).1 (hsep 2 (by simp)).2).comp v (hs 2)
  have h3 := (dividedNewtonTargetField_joint_contDiffAt n
    ((pairChartPoints (v.1 1) (v.1 3) v.2 3,pairChartPoints (v.1 1) (v.1 3) v.2 0),
      (pairChartPoints (v.1 1) (v.1 3) v.2 1,pairPointDirection (v.1 1) (v.1 3) v.2))
    (hsep 3 (by simp)).1 (hsep 3 (by simp)).2).comp v (hs 3)
  exact (((pairChartMass_joint_contDiff n 2).contDiffAt).smul h2).add
    (((pairChartMass_joint_contDiff n 3).contDiffAt).smul h3)

theorem pairAverage_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : PairJointVariables =>
      relativeAverage (pairChartMass (v.1 1) (v.1 2) (v.1 3))
        (pairChartPoints (v.1 1) (v.1 3) v.2)) := by
  unfold relativeAverage
  apply ContDiff.sum
  intro i _
  exact (pairChartMass_joint_contDiff n i).smul (pairChartPoints_joint_contDiff n i)

theorem pairExteriorRadialField_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables) (i : Satellite)
    (heps : 1+v.1 0≠0) (hsep : ∀ j ∈ ({2,3} : Finset Satellite),
      pairChartPoints (v.1 1) (v.1 3) v.2 j≠pairChartPoints (v.1 1) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairExteriorRadialField (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2
        (pairChartPoints (w.1 1) (w.1 3) w.2 i)) v := by
  have hc : ContDiffAt ℝ n (fun w : PairJointVariables => (1+w.1 0)⁻¹) v := by fun_prop
  exact (pairExteriorNewtonField_joint_contDiffAt n v i hsep).sub
    (hc.smul (pairAverage_joint_contDiff n).contDiffAt)

theorem pairExteriorAngularField_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables) (i : Satellite)
    (heps : 1+v.1 0≠0) (hsep : ∀ j ∈ ({2,3} : Finset Satellite),
      pairChartPoints (v.1 1) (v.1 3) v.2 j≠pairChartPoints (v.1 1) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairExteriorAngularField (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2
        (pairChartPoints (w.1 1) (w.1 3) w.2 i)) v := by
  have hc : ContDiffAt ℝ n (fun w : PairJointVariables => (1+w.1 0)⁻¹) v := by fun_prop
  have hX : ContDiff ℝ n (fun w : PairJointVariables =>
      pairChartMass (w.1 1) (w.1 2) (w.1 3) 2 • pairChartPoints (w.1 1) (w.1 3) w.2 2+
      pairChartMass (w.1 1) (w.1 2) (w.1 3) 3 • pairChartPoints (w.1 1) (w.1 3) w.2 3) :=
    ((pairChartMass_joint_contDiff n 2).smul (pairChartPoints_joint_contDiff n 2)).add
      ((pairChartMass_joint_contDiff n 3).smul (pairChartPoints_joint_contDiff n 3))
  exact (pairExteriorNewtonField_joint_contDiffAt n v i hsep).sub (hc.smul hX.contDiffAt)

end DominantFiveBody
