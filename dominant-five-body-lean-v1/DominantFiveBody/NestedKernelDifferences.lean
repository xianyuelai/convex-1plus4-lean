import DominantFiveBody.NestedScaledEdges
import DominantFiveBody.PairRegularization

/-! # Actual internal fields and the two delicate η quotients

We rationalize the inverse-cube difference using the actual scaled edges.
This gives an equivalent algebraic proof of nest-kernel-difference, with
joint smoothness at both independent scale faces. Every moving target and
direction is retained. The original integral derivation is not assumed.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

set_option maxHeartbeats 800000

def scaledNewtonField (d : Plane) : Plane := (‖d‖^3)⁻¹ • d

theorem scaledNewtonField_eq_target (d : Plane) :
    scaledNewtonField d=newtonTargetField 0 (-d) := by simp [scaledNewtonField,newtonTargetField]

theorem dividedNewtonTargetField_factor (source qa qb direction : Plane) (s : ℝ)
    (ha : source≠qa) (hb : source≠qb) (hgap : qb-qa=s • direction) :
    newtonTargetField source qb-newtonTargetField source qa=
      s • dividedNewtonTargetField source qa qb direction := by
  by_cases hs : s=0
  · have he : qb=qa := sub_eq_zero.mp (by simpa only [hs,zero_smul] using hgap)
    simp [hs,he]
  · rw [dividedNewtonTargetField_eq source qa qb direction s hs ha hb hgap,smul_smul,
      mul_inv_cancel₀ hs,one_smul]

theorem scaledNewtonField_contDiffAt (n : ℕ∞ω) (d : Plane) (hd : d≠0) :
    ContDiffAt ℝ n scaledNewtonField d := by
  have hn : ContDiffAt ℝ n (fun x : Plane => ‖x‖) d := contDiffAt_id.norm ℝ hd
  exact ((hn.pow 3).inv (pow_ne_zero 3 (norm_ne_zero_iff.mpr hd))).smul contDiffAt_id

def nestedOuterNewton (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : Plane :=
  scaledNewtonField (nestedOuterDirection t eta alpha y i)

def nestedInnerNewton (t eta alpha : ℝ) (y : NestedChartVariables) : Plane :=
  scaledNewtonField (nestedInnerDirection t eta alpha y)

def nestedOuterNewtonDifference (t eta alpha : ℝ) (y : NestedChartVariables) : Plane :=
  dividedNewtonTargetField 0 (-nestedOuterDirection t eta alpha y 0)
    (-nestedOuterDirection t eta alpha y 1) (nestedInnerDirection t eta alpha y)

theorem nestedOuterNewton_difference (t eta alpha : ℝ) (y : NestedChartVariables)
    (hV : ∀ i, 0<nestedOuterWSq t eta alpha y i) :
    nestedOuterNewton t eta alpha y 1-nestedOuterNewton t eta alpha y 0=
      eta • nestedOuterNewtonDifference t eta alpha y := by
  have hgap : -nestedOuterDirection t eta alpha y 1-(-nestedOuterDirection t eta alpha y 0)=
      eta • nestedInnerDirection t eta alpha y := by
    have h := nestedOuterDirection_difference t eta alpha y
    calc
      _ = -(nestedOuterDirection t eta alpha y 1-nestedOuterDirection t eta alpha y 0) := by abel
      _ = _ := by rw [h]; module
  unfold nestedOuterNewton nestedOuterNewtonDifference
  rw [scaledNewtonField_eq_target,scaledNewtonField_eq_target]
  exact dividedNewtonTargetField_factor _ _ _ _ eta
    (by simpa using nestedOuterDirection_ne_zero t eta alpha y 0 (hV 0))
    (by simpa using nestedOuterDirection_ne_zero t eta alpha y 1 (hV 1)) hgap

def nestedOuterAngularField (eps t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : Plane :=
  nestedOuterNewton t eta alpha y i-(t^3/(1+eps)) • nestedOuterDirection t eta alpha y i

def nestedOuterN (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : ℝ :=
  inner ℝ (nestedOuterNewton t eta alpha y i)
    (polarPoint 1 (nestedChartAngles t eta alpha y (i.castAdd 2)))

def nestedOuterO (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : ℝ :=
  inner ℝ (nestedOuterNewton t eta alpha y i) (polarPoint 1 (nestedChartAngles t eta alpha y 2))

def nestedOuterL (eps t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) : ℝ :=
  inner ℝ (nestedOuterAngularField eps t eta alpha y i)
    (quarterTurn (nestedChartPoints t eta alpha y (i.castAdd 2)))

def nestedOuterNDifference (t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  inner ℝ (nestedOuterNewtonDifference t eta alpha y) (polarPoint 1 (nestedChartAngles t eta alpha y 1))+
    t*inner ℝ (nestedOuterNewton t eta alpha y 0) (nestedInnerUnitDirection t eta alpha y)

def nestedOuterLDifference (eps t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  inner ℝ (nestedOuterNewtonDifference t eta alpha y+
      (t^3/(1+eps)) • nestedInnerDirection t eta alpha y) (quarterTurn (nestedChartPoints t eta alpha y 1))+
    t*inner ℝ (nestedOuterAngularField eps t eta alpha y 0) (quarterTurn (nestedInnerDirection t eta alpha y))

theorem nestedOuterN_difference (t eta alpha : ℝ) (y : NestedChartVariables)
    (hV : ∀ i, 0<nestedOuterWSq t eta alpha y i) :
    nestedOuterN t eta alpha y 1-nestedOuterN t eta alpha y 0=
      eta*nestedOuterNDifference t eta alpha y := by
  have hunit : polarPoint 1 (nestedChartAngles t eta alpha y 1)-
      polarPoint 1 (nestedChartAngles t eta alpha y 0)=
      eta • (t • nestedInnerUnitDirection t eta alpha y) := by
    rw [nestedInnerUnitDirection_identity,smul_smul,mul_comm eta t]
  have h := inner_difference_factor _ _ _ _ _ _ eta (nestedOuterNewton_difference t eta alpha y hV) hunit
  simpa [nestedOuterN,nestedOuterNDifference,real_inner_smul_right,Fin.castAdd] using h

theorem nestedOuterL_difference (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (hV : ∀ i, 0<nestedOuterWSq t eta alpha y i) :
    nestedOuterL eps t eta alpha y 1-nestedOuterL eps t eta alpha y 0=
      eta*nestedOuterLDifference eps t eta alpha y := by
  have hfield : nestedOuterAngularField eps t eta alpha y 1-nestedOuterAngularField eps t eta alpha y 0=
      eta • (nestedOuterNewtonDifference t eta alpha y+
        (t^3/(1+eps)) • nestedInnerDirection t eta alpha y) := by
    unfold nestedOuterAngularField
    calc
      _ = (nestedOuterNewton t eta alpha y 1-nestedOuterNewton t eta alpha y 0)-
          (t^3/(1+eps)) • (nestedOuterDirection t eta alpha y 1-nestedOuterDirection t eta alpha y 0) := by module
      _ = _ := by rw [nestedOuterNewton_difference t eta alpha y hV,nestedOuterDirection_difference]; module
  have hpoint : quarterTurn (nestedChartPoints t eta alpha y 1)-quarterTurn (nestedChartPoints t eta alpha y 0)=
      eta • (t • quarterTurn (nestedInnerDirection t eta alpha y)) := by
    have h := congrArg quarterTurnLinear (nestedInnerDirection_identity t eta alpha y)
    simpa only [map_sub,map_smul,quarterTurnLinear_apply,smul_smul,mul_comm t eta] using h
  have h := inner_difference_factor _ _ _ _ _ _ eta hfield hpoint
  simpa [nestedOuterL,nestedOuterLDifference,real_inner_smul_right,Fin.castAdd] using h

theorem nestedOuterNewton_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Fin 2)
    (hV : 0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedOuterNewton (w.1 1) (w.1 2) (w.1 3) w.2 i) v :=
  (scaledNewtonField_contDiffAt n _ (nestedOuterDirection_ne_zero _ _ _ _ i hV)).comp v
    (nestedOuterDirection_joint_contDiff n i).contDiffAt

theorem nestedInnerNewton_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hW : 0<nestedInnerWSq (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedInnerNewton (w.1 1) (w.1 2) (w.1 3) w.2) v :=
  (scaledNewtonField_contDiffAt n _ (nestedInnerDirection_ne_zero _ _ _ _ hW)).comp v
    (nestedInnerDirection_joint_contDiff n).contDiffAt

theorem nestedOuterNewtonDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hV : ∀ i, 0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedOuterNewtonDifference (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  let f : NestedJointVariables → DividedFieldVariables := fun w =>
    ((0,-nestedOuterDirection (w.1 1) (w.1 2) (w.1 3) w.2 0),
      (-nestedOuterDirection (w.1 1) (w.1 2) (w.1 3) w.2 1,nestedInnerDirection (w.1 1) (w.1 2) (w.1 3) w.2))
  have hf : ContDiff ℝ n f := (contDiff_const.prodMk (nestedOuterDirection_joint_contDiff n 0).neg).prodMk
    ((nestedOuterDirection_joint_contDiff n 1).neg.prodMk (nestedInnerDirection_joint_contDiff n))
  exact (dividedNewtonTargetField_joint_contDiffAt n (f v)
    (by simpa [f] using nestedOuterDirection_ne_zero _ _ _ _ 0 (hV 0))
    (by simpa [f] using nestedOuterDirection_ne_zero _ _ _ _ 1 (hV 1))).comp v hf.contDiffAt

theorem nestedOuterAngularField_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Fin 2)
    (heps : 1+v.1 0≠0) (hV : 0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedOuterAngularField (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2 i) v := by
  have hc : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 1^3/(1+w.1 0)) v := by fun_prop
  exact (nestedOuterNewton_joint_contDiffAt n v i hV).sub (hc.smul (nestedOuterDirection_joint_contDiff n i).contDiffAt)

theorem nestedOuterNDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hV : ∀ i, 0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedOuterNDifference (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have ht : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 1) v := by fun_prop
  exact ((nestedOuterNewtonDifference_joint_contDiffAt n v hV).inner ℝ (nestedUnit_joint_contDiff n 1).contDiffAt).add
    (ht.mul ((nestedOuterNewton_joint_contDiffAt n v 0 (hV 0)).inner ℝ (nestedInnerUnitDirection_joint_contDiff n).contDiffAt))

theorem nestedOuterLDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (heps : 1+v.1 0≠0) (hV : ∀ i, 0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedOuterLDifference (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have hc : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 1^3/(1+w.1 0)) v := by fun_prop
  have ht : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 1) v := by fun_prop
  have hp := quarterTurnLinear.toContinuousLinearMap.contDiff.comp (nestedChartPoints_joint_contDiff n 1)
  have hd := quarterTurnLinear.toContinuousLinearMap.contDiff.comp (nestedInnerDirection_joint_contDiff n)
  exact (((nestedOuterNewtonDifference_joint_contDiffAt n v hV).add
    (hc.smul (nestedInnerDirection_joint_contDiff n).contDiffAt)).inner ℝ hp.contDiffAt).add
      (ht.mul ((nestedOuterAngularField_joint_contDiffAt n v 0 heps (hV 0)).inner ℝ hd.contDiffAt))

end DominantFiveBody
