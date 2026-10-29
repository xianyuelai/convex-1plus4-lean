import DominantFiveBody.PairChart
import DominantFiveBody.DividedNewtonField
import DominantFiveBody.LocalContinuation

/-! # Signed-scale divided edges in the complete-pair chart

All formulas are defined without dividing by t. Their identities hold for
every real t, including zero, and retain the independent mass fraction.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

theorem polarUnit_sub_midpoint (a b : ℝ) :
    polarPoint 1 b-polarPoint 1 a =
      ((b-a)*Real.sinc ((b-a)/2)) • quarterTurn (polarPoint 1 ((a+b)/2)) := by
  have ha : a=(a+b)/2-(b-a)/2 := by ring
  have hb : b=(a+b)/2+(b-a)/2 := by ring
  have hs : (b-a)*Real.sinc ((b-a)/2)=2*Real.sin ((b-a)/2) := by
    nlinarith [sinc_mul_argument ((b-a)/2)]
  rw [hs]
  ext k
  fin_cases k <;>
    simp [polarPoint, quarterTurn, point]
  · rw [ha,hb,Real.cos_sub,Real.cos_add]
    ring
  · rw [ha,hb,Real.sin_sub,Real.sin_add]
    ring

def pairUnitDirection (t alpha : ℝ) (y : PairChartVariables) : Plane :=
  (y 6*Real.sinc (t*y 6/2)) •
    quarterTurn (polarPoint 1 (y 5+(alpha-1/2)*t*y 6))

def pairPointDirection (t alpha : ℝ) (y : PairChartVariables) : Plane :=
  y 3 • polarPoint 1 (pairChartAngles t alpha y 0)+
    pairChartRadii t alpha y 1 • pairUnitDirection t alpha y

theorem pairUnitDirection_identity (t alpha : ℝ) (y : PairChartVariables) :
    polarPoint 1 (pairChartAngles t alpha y 1)-
      polarPoint 1 (pairChartAngles t alpha y 0)=t • pairUnitDirection t alpha y := by
  rw [polarUnit_sub_midpoint]
  have hg : pairChartAngles t alpha y 1-pairChartAngles t alpha y 0=t*y 6 := by
    simp only [pairChartAngles, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  have hm : (pairChartAngles t alpha y 0+pairChartAngles t alpha y 1)/2=
      y 5+(alpha-1/2)*t*y 6 := by
    simp only [pairChartAngles, Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  rw [hg,hm,pairUnitDirection,smul_smul]
  congr 1
  ring

theorem pairPointDirection_identity (t alpha : ℝ) (y : PairChartVariables) :
    polarPoint (pairChartRadii t alpha y 1) (pairChartAngles t alpha y 1)-
      polarPoint (pairChartRadii t alpha y 0) (pairChartAngles t alpha y 0)=
        t • pairPointDirection t alpha y := by
  have hr : pairChartRadii t alpha y 1-pairChartRadii t alpha y 0=t*y 3 := by
    simp only [pairChartRadii, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have he := pairUnitDirection_identity t alpha y
  rw [polarPoint_smul_one (pairChartRadii t alpha y 1),
    polarPoint_smul_one (pairChartRadii t alpha y 0)]
  calc
    _ = pairChartRadii t alpha y 1 •
        (polarPoint 1 (pairChartAngles t alpha y 1)-polarPoint 1 (pairChartAngles t alpha y 0))+
        (pairChartRadii t alpha y 1-pairChartRadii t alpha y 0) •
          polarPoint 1 (pairChartAngles t alpha y 0) := by module
    _ = pairChartRadii t alpha y 1 • (t • pairUnitDirection t alpha y)+
        (t*y 3) • polarPoint 1 (pairChartAngles t alpha y 0) := by rw [he,hr]
    _ = _ := by simp only [pairPointDirection, smul_add, smul_smul]; module

abbrev PairJointVariables := (Fin 4 → ℝ)×PairChartVariables

@[fun_prop] theorem pairChartMass_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : PairJointVariables => pairChartMass (v.1 1) (v.1 2) (v.1 3) i) := by
  fin_cases i
  · change ContDiff ℝ n (fun v : PairJointVariables => v.1 1^3*v.1 3)
    fun_prop
  · change ContDiff ℝ n (fun v : PairJointVariables => v.1 1^3*(1-v.1 3))
    fun_prop
  · change ContDiff ℝ n (fun v : PairJointVariables => (1-v.1 1^3)*v.1 2)
    fun_prop
  · change ContDiff ℝ n (fun v : PairJointVariables => (1-v.1 1^3)*(1-v.1 2))
    fun_prop

@[fun_prop] theorem pairChartRadii_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : PairJointVariables => pairChartRadii (v.1 1) (v.1 3) v.2 i) := by
  fin_cases i
  · change ContDiff ℝ n (fun v : PairJointVariables => v.2 2-(1-v.1 3)*v.1 1*v.2 3)
    fun_prop
  · change ContDiff ℝ n (fun v : PairJointVariables => v.2 2+v.1 3*v.1 1*v.2 3)
    fun_prop
  · change ContDiff ℝ n (fun v : PairJointVariables => v.2 0)
    fun_prop
  · change ContDiff ℝ n (fun v : PairJointVariables => v.2 1)
    fun_prop

@[fun_prop] theorem pairChartAngles_joint_contDiff (n : ℕ∞ω) (i : Satellite) :
    ContDiff ℝ n (fun v : PairJointVariables => pairChartAngles (v.1 1) (v.1 3) v.2 i) := by
  fin_cases i
  · change ContDiff ℝ n (fun v : PairJointVariables => v.2 5-(1-v.1 3)*v.1 1*v.2 6)
    fun_prop
  · change ContDiff ℝ n (fun v : PairJointVariables => v.2 5+v.1 3*v.1 1*v.2 6)
    fun_prop
  · change ContDiff ℝ n (fun _ : PairJointVariables => (0 : ℝ))
    fun_prop
  · change ContDiff ℝ n (fun v : PairJointVariables => v.2 4)
    fun_prop

@[fun_prop] theorem pairUnitDirection_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : PairJointVariables => pairUnitDirection (v.1 1) (v.1 3) v.2) := by
  unfold pairUnitDirection
  have harg : ContDiff ℝ n (fun v : PairJointVariables =>
      ((1 : ℝ), v.2 5+(v.1 3-1/2)*v.1 1*v.2 6)) := by fun_prop
  have hp : ContDiff ℝ n (fun v : PairJointVariables =>
      polarPoint 1 (v.2 5+(v.1 3-1/2)*v.1 1*v.2 6)) :=
    (polarPoint_contDiff n).comp harg
  have hq : ContDiff ℝ n (fun v : PairJointVariables =>
      quarterTurn (polarPoint 1 (v.2 5+(v.1 3-1/2)*v.1 1*v.2 6))) :=
    quarterTurnLinear.toContinuousLinearMap.contDiff.comp hp
  exact (by fun_prop : ContDiff ℝ n (fun v : PairJointVariables =>
    v.2 6*Real.sinc (v.1 1*v.2 6/2))).smul hq

@[fun_prop] theorem pairPointDirection_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : PairJointVariables => pairPointDirection (v.1 1) (v.1 3) v.2) := by
  unfold pairPointDirection
  simp only [pairChartRadii,pairChartAngles,Matrix.cons_val_zero,Matrix.cons_val_one]
  have harg : ContDiff ℝ n (fun v : PairJointVariables =>
      ((1 : ℝ), v.2 5-(1-v.1 3)*v.1 1*v.2 6)) := by fun_prop
  have hp : ContDiff ℝ n (fun v : PairJointVariables =>
      polarPoint 1 (v.2 5-(1-v.1 3)*v.1 1*v.2 6)) :=
    (polarPoint_contDiff n).comp harg
  exact ((by fun_prop : ContDiff ℝ n (fun v : PairJointVariables => v.2 3)).smul hp).add
    ((by fun_prop : ContDiff ℝ n (fun v : PairJointVariables =>
      v.2 2+v.1 3*v.1 1*v.2 3)).smul (pairUnitDirection_joint_contDiff n))

end DominantFiveBody
