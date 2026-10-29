import DominantFiveBody.NestedDirections

/-! # Nonvanishing scaled edges, including both zero-scale faces

Equalities across t=0 are proved by continuity of explicit formulas from
the dense nonzero-scale set. They do not identify a signed scale with a
physical distance.
-/

noncomputable section
open scoped BigOperators ContDiff
open Set

namespace DominantFiveBody

set_option maxHeartbeats 800000

theorem pairPointDirection_norm_sq (t alpha : ℝ) (y : PairChartVariables) :
    ‖pairPointDirection t alpha y‖^2=pairChartWSq t alpha y := by
  have harg : Continuous (fun s : ℝ => ((![0,s,0,alpha] : Fin 4 → ℝ),y)) := by fun_prop
  have hd : Continuous (fun s : ℝ => ‖pairPointDirection s alpha y‖^2) :=
    (((pairPointDirection_joint_contDiff 0).continuous.comp harg).norm).pow 2
  have hw : Continuous (fun s : ℝ => pairChartWSq s alpha y) :=
    (pairChartWSq_joint_contDiff 0).continuous.comp harg
  have hEq := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hd hw (by
    intro s hs
    have hn : s≠0 := hs
    have h := pairChart_distance_sq s alpha y
    unfold satelliteDistance polarSatellites at h
    rw [norm_sub_rev,pairPointDirection_identity,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at h
    exact mul_left_cancel₀ (pow_ne_zero 2 hn) h)
  exact congrFun hEq t

theorem nestedInnerDirection_norm_sq (t eta alpha : ℝ) (y : NestedChartVariables) :
    ‖nestedInnerDirection t eta alpha y‖^2=nestedInnerWSq t eta alpha y :=
  pairPointDirection_norm_sq (t*eta) alpha (nestedInnerVariables t eta y)

theorem nestedOuterDirection_norm_sq (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    ‖nestedOuterDirection t eta alpha y i‖^2=nestedOuterWSq t eta alpha y i :=
  pairPointDirection_norm_sq t 1 (nestedOuterVariables t eta alpha y i)

theorem nestedInnerDirection_norm (t eta alpha : ℝ) (y : NestedChartVariables) :
    ‖nestedInnerDirection t eta alpha y‖=nestedInnerW t eta alpha y := by
  rw [nestedInnerW,← nestedInnerDirection_norm_sq,Real.sqrt_sq_eq_abs,abs_norm]

theorem nestedOuterDirection_norm (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    ‖nestedOuterDirection t eta alpha y i‖=nestedOuterW t eta alpha y i := by
  rw [nestedOuterW,← nestedOuterDirection_norm_sq,Real.sqrt_sq_eq_abs,abs_norm]

/-- The difference of the two macroscopic divided edges has exactly one
η factor; this identity holds even at t=η=0. -/
theorem nestedOuterDirection_difference (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedOuterDirection t eta alpha y 1-nestedOuterDirection t eta alpha y 0=
      -eta • nestedInnerDirection t eta alpha y := by
  have harg : Continuous (fun s : ℝ => ((![0,s,eta,alpha] : NestedChartParameters),y)) := by fun_prop
  have ha := (nestedOuterDirection_joint_contDiff 0 0).continuous.comp harg
  have hb := (nestedOuterDirection_joint_contDiff 0 1).continuous.comp harg
  have hi := (nestedInnerDirection_joint_contDiff 0).continuous.comp harg
  have hEq := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) (hb.sub ha) (hi.const_smul (-eta)) (by
    intro s hs
    have hn : s≠0 := hs
    change nestedOuterDirection s eta alpha y 1-nestedOuterDirection s eta alpha y 0=
      -eta • nestedInnerDirection s eta alpha y
    apply (smul_right_inj (M := Plane) hn).mp
    rw [smul_sub,← nestedOuterDirection_identity,← nestedOuterDirection_identity]
    change (nestedChartPoints s eta alpha y 2-nestedChartPoints s eta alpha y 1)-
      (nestedChartPoints s eta alpha y 2-nestedChartPoints s eta alpha y 0)=_
    calc
      _ = -(nestedChartPoints s eta alpha y 1-nestedChartPoints s eta alpha y 0) := by abel
      _ = _ := by rw [nestedInnerDirection_identity]; module)
  exact congrFun hEq t

@[fun_prop] theorem nestedInnerWSq_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedInnerWSq (v.1 1) (v.1 2) (v.1 3) v.2) :=
  (pairChartWSq_joint_contDiff n).comp (nestedInnerPairJoint_contDiff n)

@[fun_prop] theorem nestedOuterWSq_joint_contDiff (n : ℕ∞ω) (i : Fin 2) :
    ContDiff ℝ n (fun v : NestedJointVariables => nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :=
  (pairChartWSq_joint_contDiff n).comp (nestedOuterPairJoint_contDiff n i)

theorem nestedInnerW_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables)
    (hW : 0<nestedInnerWSq (v.1 1) (v.1 2) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedInnerW (w.1 1) (w.1 2) (w.1 3) w.2) v :=
  (nestedInnerWSq_joint_contDiff n).contDiffAt.sqrt hW.ne'

theorem nestedOuterW_joint_contDiffAt (n : ℕ∞ω) (v : NestedJointVariables) (i : Fin 2)
    (hW : 0<nestedOuterWSq (v.1 1) (v.1 2) (v.1 3) v.2 i) :
    ContDiffAt ℝ n (fun w : NestedJointVariables => nestedOuterW (w.1 1) (w.1 2) (w.1 3) w.2 i) v :=
  (nestedOuterWSq_joint_contDiff n i).contDiffAt.sqrt hW.ne'

theorem nestedInnerDirection_ne_zero (t eta alpha : ℝ) (y : NestedChartVariables)
    (hW : 0<nestedInnerWSq t eta alpha y) : nestedInnerDirection t eta alpha y≠0 := by
  intro h
  have he := nestedInnerDirection_norm_sq t eta alpha y
  rw [h,norm_zero,zero_pow (by decide : (2 : ℕ)≠0)] at he
  linarith

theorem nestedOuterDirection_ne_zero (t eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2)
    (hW : 0<nestedOuterWSq t eta alpha y i) : nestedOuterDirection t eta alpha y i≠0 := by
  intro h
  have he := nestedOuterDirection_norm_sq t eta alpha y i
  rw [h,norm_zero,zero_pow (by decide : (2 : ℕ)≠0)] at he
  linarith

end DominantFiveBody
