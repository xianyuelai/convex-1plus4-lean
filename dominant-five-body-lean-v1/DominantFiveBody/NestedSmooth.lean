import DominantFiveBody.NestedRegularization

/-! # Joint regularity on an independent two-scale domain

The domain allows signed t,η and endpoint α. Only actual nonzero radii,
scaled distances and exterior distances are imposed.
-/

noncomputable section
open Set Topology
open scoped BigOperators ContDiff

namespace DominantFiveBody
set_option maxHeartbeats 1000000

def NestedChartRegular (eps t eta alpha : ℝ) (y : NestedChartVariables) : Prop :=
  1+eps≠0 ∧ (∀ i,nestedChartRadii t eta alpha y i≠0) ∧ 0<nestedInnerWSq t eta alpha y ∧
    (∀ i,0<nestedOuterWSq t eta alpha y i) ∧
    ∀ i : Fin 3,nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y i.castSucc

@[fun_prop] theorem nestedEdgeRadialGap_joint_contDiff (n : ℕ∞ω) (k : NestedEdge) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedEdgeRadialGap (v.1 2) (v.1 3) v.2 k) := by
  fin_cases k <;> simp [nestedEdgeRadialGap,nestedOuterRadialGaps] <;> fun_prop

@[fun_prop] theorem nestedEdgeDirection_joint_contDiff (n : ℕ∞ω) (k : NestedEdge) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedEdgeDirection (v.1 1) (v.1 2) (v.1 3) v.2 k) := by
  fin_cases k
  · exact nestedOuterDirection_joint_contDiff n 0
  · exact nestedOuterDirection_joint_contDiff n 1
  · exact nestedInnerDirection_joint_contDiff n

@[fun_prop] theorem nestedEdgeUnitDirection_joint_contDiff (n : ℕ∞ω) (k : NestedEdge) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedEdgeUnitDirection (v.1 1) (v.1 2) (v.1 3) v.2 k) := by
  fin_cases k
  · exact nestedOuterUnitDirection_joint_contDiff n 0
  · exact nestedOuterUnitDirection_joint_contDiff n 1
  · exact nestedInnerUnitDirection_joint_contDiff n

@[fun_prop] theorem nestedAverage_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : NestedJointVariables => relativeAverage (nestedChartMass (v.1 1) (v.1 2) (v.1 3))
      (nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2)) := by
  unfold relativeAverage
  apply ContDiff.sum
  intro i _
  exact (nestedChartMass_joint_contDiff n i).smul (nestedChartPoints_joint_contDiff n i)

theorem nestedExteriorNewtonField_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Satellite)
    (hsep : nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 3≠nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedExteriorNewtonField (w.1 1) (w.1 2) (w.1 3) w.2
      (nestedChartPoints (w.1 1) (w.1 2) (w.1 3) w.2 i)) v := by
  have hp := (nestedChartPoints_joint_contDiff n 3).prodMk (nestedChartPoints_joint_contDiff n i)
  have hh := (newtonTargetField_joint_contDiffAt n _ hsep).comp v hp.contDiffAt
  have hc : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 1^3) v := by fun_prop
  exact hc.smul hh

theorem nestedExteriorRadialField_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Satellite)
    (heps : 1+v.1 0≠0)
    (hsep : nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 3≠nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedExteriorRadialField (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2
      (nestedChartPoints (w.1 1) (w.1 2) (w.1 3) w.2 i)) v := by
  have hc : ContDiffAt ℝ n (fun w : NestedJointVariables => (1+w.1 0)⁻¹) v := by fun_prop
  exact (nestedExteriorNewtonField_joint_contDiffAt n v i hsep).sub (hc.smul (nestedAverage_joint_contDiff n).contDiffAt)

theorem nestedExteriorAngularField_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Satellite)
    (heps : 1+v.1 0≠0)
    (hsep : nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 3≠nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedExteriorAngularField (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2
      (nestedChartPoints (w.1 1) (w.1 2) (w.1 3) w.2 i)) v := by
  have hc : ContDiffAt ℝ n (fun w : NestedJointVariables => (1+w.1 0)⁻¹) v := by fun_prop
  have hm : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 1^3) v := by fun_prop
  exact (nestedExteriorNewtonField_joint_contDiffAt n v i hsep).sub
    (hc.smul (hm.smul (nestedChartPoints_joint_contDiff n 3).contDiffAt))

theorem nestedExteriorNewtonDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (k : NestedEdge)
    (ha : nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 3≠nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 (nestedEdgeSource k))
    (hb : nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 3≠nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 (nestedEdgeTarget k)) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedExteriorNewtonDifference (w.1 1) (w.1 2) (w.1 3) w.2 k) v := by
  let f : NestedJointVariables → DividedFieldVariables := fun w =>
    ((nestedChartPoints (w.1 1) (w.1 2) (w.1 3) w.2 3,
      nestedChartPoints (w.1 1) (w.1 2) (w.1 3) w.2 (nestedEdgeSource k)),
      (nestedChartPoints (w.1 1) (w.1 2) (w.1 3) w.2 (nestedEdgeTarget k),
        nestedEdgeDirection (w.1 1) (w.1 2) (w.1 3) w.2 k))
  have hf : ContDiff ℝ n f := ((nestedChartPoints_joint_contDiff n 3).prodMk
    (nestedChartPoints_joint_contDiff n (nestedEdgeSource k))).prodMk
      ((nestedChartPoints_joint_contDiff n (nestedEdgeTarget k)).prodMk (nestedEdgeDirection_joint_contDiff n k))
  have hc : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 1^3) v := by fun_prop
  exact hc.smul ((dividedNewtonTargetField_joint_contDiffAt n (f v) ha hb).comp v hf.contDiffAt)

theorem nestedChartRegular_edge_separated (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (hreg : NestedChartRegular eps t eta alpha y) (k : NestedEdge) :
    nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeSource k) ∧
      nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y (nestedEdgeTarget k) := by
  fin_cases k
  · exact ⟨hreg.2.2.2.2 0,hreg.2.2.2.2 2⟩
  · exact ⟨hreg.2.2.2.2 1,hreg.2.2.2.2 2⟩
  · exact ⟨hreg.2.2.2.2 0,hreg.2.2.2.2 1⟩

theorem nestedRadialExterior_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Fin 3)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedRadialExterior (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2 i.castSucc) v := by
  have hr := (nestedChartRadii_joint_contDiff n i.castSucc).contDiffAt (x := v)
  have heps : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 0) v := by fun_prop
  exact (hr.sub ((hr.pow 2).inv (pow_ne_zero 2 (hreg.2.1 i.castSucc)))).add
    (heps.mul ((nestedExteriorRadialField_joint_contDiffAt n v i.castSucc hreg.1 (hreg.2.2.2.2 i)).inner ℝ
      (nestedUnit_joint_contDiff n i.castSucc).contDiffAt))

theorem nestedAngularExterior_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Fin 3)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedAngularExterior (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2 i.castSucc) v := by
  have hq := quarterTurnLinear.toContinuousLinearMap.contDiff.comp (nestedChartPoints_joint_contDiff n i.castSucc)
  exact (nestedExteriorAngularField_joint_contDiffAt n v i.castSucc hreg.1 (hreg.2.2.2.2 i)).inner ℝ hq.contDiffAt

theorem nestedRadialExteriorDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (k : NestedEdge)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedRadialExteriorDifference (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2 k) v := by
  have hs := nestedChartRegular_edge_separated _ _ _ _ _ hreg k
  have hra := (nestedChartRadii_joint_contDiff n (nestedEdgeSource k)).contDiffAt (x := v)
  have hrb := (nestedChartRadii_joint_contDiff n (nestedEdgeTarget k)).contDiffAt (x := v)
  have hc := (hra.add hrb).div ((hra.pow 2).mul (hrb.pow 2))
    (mul_ne_zero (pow_ne_zero 2 (hreg.2.1 _)) (pow_ne_zero 2 (hreg.2.1 _)))
  have hone : ContDiffAt ℝ n (fun _ : NestedJointVariables => (1 : ℝ)) v := contDiffAt_const
  have heps : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 0) v := by fun_prop
  exact ((nestedEdgeRadialGap_joint_contDiff n k).contDiffAt.mul (hone.add hc)).add
    (heps.mul (((nestedExteriorNewtonDifference_joint_contDiffAt n v k hs.1 hs.2).inner ℝ
      (nestedUnit_joint_contDiff n (nestedEdgeTarget k)).contDiffAt).add
      ((nestedExteriorRadialField_joint_contDiffAt n v (nestedEdgeSource k) hreg.1 hs.1).inner ℝ
        (nestedEdgeUnitDirection_joint_contDiff n k).contDiffAt)))

theorem nestedAngularExteriorDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (k : NestedEdge)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedAngularExteriorDifference (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2 k) v := by
  have hs := nestedChartRegular_edge_separated _ _ _ _ _ hreg k
  have hp := quarterTurnLinear.toContinuousLinearMap.contDiff.comp (nestedChartPoints_joint_contDiff n (nestedEdgeTarget k))
  have hd := quarterTurnLinear.toContinuousLinearMap.contDiff.comp (nestedEdgeDirection_joint_contDiff n k)
  exact ((nestedExteriorNewtonDifference_joint_contDiffAt n v k hs.1 hs.2).inner ℝ hp.contDiffAt).add
    ((nestedExteriorAngularField_joint_contDiffAt n v (nestedEdgeSource k) hreg.1 hs.1).inner ℝ hd.contDiffAt)

theorem nestedOuterN_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Fin 2)
    (hV : 0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedOuterN (w.1 1) (w.1 2) (w.1 3) w.2 i) v :=
  (nestedOuterNewton_joint_contDiffAt n v i hV).inner ℝ (nestedUnit_joint_contDiff n (i.castAdd 2)).contDiffAt

theorem nestedOuterO_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Fin 2)
    (hV : 0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedOuterO (w.1 1) (w.1 2) (w.1 3) w.2 i) v :=
  (nestedOuterNewton_joint_contDiffAt n v i hV).inner ℝ (nestedUnit_joint_contDiff n 2).contDiffAt

theorem nestedOuterL_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Fin 2)
    (heps : 1+v.1 0≠0) (hV : 0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedOuterL (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2 i) v :=
  (nestedOuterAngularField_joint_contDiffAt n v i heps hV).inner ℝ
    (quarterTurnLinear.toContinuousLinearMap.contDiff.comp (nestedChartPoints_joint_contDiff n (i.castAdd 2))).contDiffAt

theorem nestedInnerJ_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hW : 0<nestedInnerWSq (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedInnerJ (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v :=
  (pairInternalRadialMean_joint_contDiffAt n (nestedInnerPairJoint v) hW).comp v (nestedInnerPairJoint_contDiff n).contDiffAt

theorem nestedInnerJOverT_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hW : 0<nestedInnerWSq (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedInnerJOverT (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have hp : ContDiff ℝ n (fun w : NestedJointVariables => -w.1 0*w.1 2*w.1 3*(1-w.1 3)*
      (nestedChartRadii (w.1 1) (w.1 2) (w.1 3) w.2 0+nestedChartRadii (w.1 1) (w.1 2) (w.1 3) w.2 1)*
        singleScaleChi (w.1 1*w.1 2) (w.2 6)) := by unfold singleScaleChi; fun_prop
  exact hp.contDiffAt.mul (((nestedInnerW_joint_contDiffAt n v hW).pow 3).inv
    (pow_ne_zero 3 (Real.sqrt_pos.mpr hW).ne'))

theorem nestedInternalRadialMean_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedInternalRadialMean (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have hpre : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 0*w.1 1*w.1 2^3*(1-w.1 2^3)) v := by fun_prop
  have ha : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 3) v := by fun_prop
  have hb : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 3) v := by fun_prop
  have hg : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 2^3) v := by fun_prop
  exact (hpre.mul ((ha.mul ((nestedOuterN_joint_contDiffAt n v 0 (hreg.2.2.2.1 0)).sub
    (nestedOuterO_joint_contDiffAt n v 0 (hreg.2.2.2.1 0)))).add
      (hb.mul ((nestedOuterN_joint_contDiffAt n v 1 (hreg.2.2.2.1 1)).sub
        (nestedOuterO_joint_contDiffAt n v 1 (hreg.2.2.2.1 1)))))).add
          (hg.mul (nestedInnerJ_joint_contDiffAt n v hreg.2.2.1))

theorem nestedInternalRadialOuterDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedInternalRadialOuterDifference (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have heps : ContDiffAt ℝ n (fun w : NestedJointVariables => -w.1 0) v := by fun_prop
  have ha : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 3) v := by fun_prop
  have hb : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 3) v := by fun_prop
  have hg : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 2^3) v := by fun_prop
  have hh : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 2^3) v := by fun_prop
  exact (heps.mul ((hg.mul ((ha.mul (nestedOuterO_joint_contDiffAt n v 0 (hreg.2.2.2.1 0))).add
      (hb.mul (nestedOuterO_joint_contDiffAt n v 1 (hreg.2.2.2.1 1))))).add
    (hh.mul ((ha.mul (nestedOuterN_joint_contDiffAt n v 0 (hreg.2.2.2.1 0))).add
      (hb.mul (nestedOuterN_joint_contDiffAt n v 1 (hreg.2.2.2.1 1))))))).sub
        (nestedInnerJOverT_joint_contDiffAt n v hreg.2.2.1)

theorem nestedInternalRadialInnerDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedInternalRadialInnerDifference (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have hp : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 0*(1-w.1 2^3)) v := by fun_prop
  have hi := (pairInternalRadialDifference_joint_contDiffAt n (nestedInnerPairJoint v) hreg.2.2.1).comp v
    (nestedInnerPairJoint_contDiff n).contDiffAt
  exact (hp.mul (nestedOuterNDifference_joint_contDiffAt n v hreg.2.2.2.1)).add hi

theorem nestedInternalAngularOuterDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedInternalAngularOuterDifference (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have ha : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 3) v := by fun_prop
  have hb : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 3) v := by fun_prop
  exact ((ha.mul (nestedOuterL_joint_contDiffAt n v 0 hreg.1 (hreg.2.2.2.1 0))).add
    (hb.mul (nestedOuterL_joint_contDiffAt n v 1 hreg.1 (hreg.2.2.2.1 1)))).neg

theorem nestedInternalAngularInnerDifference_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedInternalAngularInnerDifference (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have hp : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 2^3) v := by fun_prop
  have hi := (pairInternalAngularDifference_joint_contDiffAt n (nestedInnerPairJoint v) hreg.2.2.1 hreg.1).comp v
    (nestedInnerPairJoint_contDiff n).contDiffAt
  exact (hp.mul (nestedOuterLDifference_joint_contDiffAt n v hreg.1 hreg.2.2.2.1)).sub hi.neg

theorem nestedPhysicalRadialExterior_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => radialResidual (w.1 0)
      (nestedChartMass (w.1 1) (w.1 2) (w.1 3)) (nestedChartRadii (w.1 1) (w.1 2) (w.1 3) w.2)
      (nestedChartAngles (w.1 1) (w.1 2) (w.1 3) w.2) 3) v := by
  have hr (j : Satellite) := (nestedChartRadii_joint_contDiff n j).contDiffAt (x := v)
  have ha (j : Satellite) := (nestedChartAngles_joint_contDiff n j).contDiffAt (x := v)
  have hm (j : Satellite) := (nestedChartMass_joint_contDiff n j).contDiffAt (x := v)
  have he : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 0) v := by fun_prop
  have hsum : ContDiffAt ℝ n (fun w : NestedJointVariables =>
      ∑ j ∈ Finset.univ.erase (3 : Satellite),nestedChartMass (w.1 1) (w.1 2) (w.1 3) j*
        (nestedChartRadii (w.1 1) (w.1 2) (w.1 3) w.2 3-nestedChartRadii (w.1 1) (w.1 2) (w.1 3) w.2 j*
          Real.cos (nestedChartAngles (w.1 1) (w.1 2) (w.1 3) w.2 j-nestedChartAngles (w.1 1) (w.1 2) (w.1 3) w.2 3))/
        satelliteDistance (nestedChartPoints (w.1 1) (w.1 2) (w.1 3) w.2) 3 j^3) v := by
    apply ContDiffAt.sum
    intro j hj
    have hneq : nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 3≠nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 j := by
      fin_cases j
      · exact hreg.2.2.2.2 0
      · exact hreg.2.2.2.2 1
      · exact hreg.2.2.2.2 2
      · simp at hj
    have hd := ((nestedChartPoints_joint_contDiff n 3).sub (nestedChartPoints_joint_contDiff n j)).contDiffAt.norm ℝ
      (sub_ne_zero.mpr hneq)
    exact ((hm j).mul ((hr 3).sub ((hr j).mul (((ha j).sub (ha 3)).cos)))).div (hd.pow 3)
      (pow_ne_zero 3 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hneq)))
  exact (((hr 3).sub (((hr 3).pow 2).inv (pow_ne_zero 2 (hreg.2.1 3)))).sub (he.mul hsum)).sub
    ((he.div (contDiffAt_const.add he) hreg.1).mul
      ((nestedAverage_joint_contDiff n).contDiffAt.inner ℝ (nestedUnit_joint_contDiff n 3).contDiffAt))

theorem nestedChartExtendedRows_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedChartExtendedRows (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v := by
  have ha : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 3) v := by fun_prop
  have hb : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 3) v := by fun_prop
  have hg : ContDiffAt ℝ n (fun w : NestedJointVariables => w.1 2^3) v := by fun_prop
  have hh : ContDiffAt ℝ n (fun w : NestedJointVariables => 1-w.1 2^3) v := by fun_prop
  apply contDiffAt_pi.mpr
  intro k
  fin_cases k
  · exact nestedPhysicalRadialExterior_joint_contDiffAt n v hreg
  · exact ((hg.mul ((ha.mul (nestedRadialExterior_joint_contDiffAt n v 0 hreg)).add
      (hb.mul (nestedRadialExterior_joint_contDiffAt n v 1 hreg)))).add
      (hh.mul (nestedRadialExterior_joint_contDiffAt n v 2 hreg))).add
        (nestedInternalRadialMean_joint_contDiffAt n v hreg)
  · exact ((ha.mul (nestedRadialExteriorDifference_joint_contDiffAt n v 0 hreg)).add
      (hb.mul (nestedRadialExteriorDifference_joint_contDiffAt n v 1 hreg))).add
        (nestedInternalRadialOuterDifference_joint_contDiffAt n v hreg)
  · exact (nestedRadialExteriorDifference_joint_contDiffAt n v 2 hreg).add
      (nestedInternalRadialInnerDifference_joint_contDiffAt n v hreg)
  · exact (hg.mul ((ha.mul (nestedAngularExterior_joint_contDiffAt n v 0 hreg)).add
      (hb.mul (nestedAngularExterior_joint_contDiffAt n v 1 hreg)))).add
      (hh.mul (nestedAngularExterior_joint_contDiffAt n v 2 hreg))
  · exact ((ha.mul (nestedAngularExteriorDifference_joint_contDiffAt n v 0 hreg)).add
      (hb.mul (nestedAngularExteriorDifference_joint_contDiffAt n v 1 hreg))).add
        (nestedInternalAngularOuterDifference_joint_contDiffAt n v hreg)
  · exact (nestedAngularExteriorDifference_joint_contDiffAt n v 2 hreg).add
      (nestedInternalAngularInnerDifference_joint_contDiffAt n v hreg)

theorem nestedChartRegular_isOpen : IsOpen {v : NestedJointVariables |
    NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2} := by
  have he : IsOpen {v : NestedJointVariables | 1+v.1 0≠0} := (isClosed_eq (by fun_prop) continuous_const).isOpen_compl
  have hr : IsOpen {v : NestedJointVariables | ∀ i,nestedChartRadii (v.1 1) (v.1 2) (v.1 3) v.2 i≠0} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (isClosed_eq (nestedChartRadii_joint_contDiff 0 i).continuous continuous_const).isOpen_compl
  have hw : IsOpen {v : NestedJointVariables | 0<nestedInnerWSq (v.1 1) (v.1 2) (v.1 3) v.2} :=
    isOpen_lt continuous_const (nestedInnerWSq_joint_contDiff 0).continuous
  have hv : IsOpen {v : NestedJointVariables | ∀ i,0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (nestedOuterWSq_joint_contDiff 0 i).continuous
  have hs : IsOpen {v : NestedJointVariables | ∀ i : Fin 3,
      nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 3≠nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2 i.castSucc} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (isClosed_eq (nestedChartPoints_joint_contDiff 0 3).continuous (nestedChartPoints_joint_contDiff 0 i.castSucc).continuous).isOpen_compl
  exact he.inter (hr.inter (hw.inter (hv.inter hs)))

end DominantFiveBody
