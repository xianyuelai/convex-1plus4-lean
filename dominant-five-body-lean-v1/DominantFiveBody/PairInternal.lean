import DominantFiveBody.PairChart
import DominantFiveBody.PairDirections

/-! # Complete-pair internal rows, before and after mean-difference

The signed extension has no t, α or 1−α denominator. Equality with the
physical Newtonian terms is asserted only at positive t and positive W².
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

def pairChartWSq (t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  y 3^2+pairChartRadii t alpha y 0*pairChartRadii t alpha y 1*y 6^2*
    Real.sinc (t*y 6/2)^2

def pairChartW (t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  Real.sqrt (pairChartWSq t alpha y)

theorem pairChart_angle_gap (t alpha : ℝ) (y : PairChartVariables) :
    pairChartAngles t alpha y 1-pairChartAngles t alpha y 0=t*y 6 := by
  simp only [pairChartAngles, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem pairChart_radius_gap (t alpha : ℝ) (y : PairChartVariables) :
    pairChartRadii t alpha y 1-pairChartRadii t alpha y 0=t*y 3 := by
  simp only [pairChartRadii, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem pairChart_distance_sq (t alpha : ℝ) (y : PairChartVariables) :
    satelliteDistance (polarSatellites (pairChartRadii t alpha y)
      (pairChartAngles t alpha y)) 0 1^2=t^2*pairChartWSq t alpha y := by
  unfold satelliteDistance polarSatellites
  rw [norm_sub_rev,polar_distance_sq,pairChart_angle_gap,pairChart_radius_gap,
    ← sinc_mul_argument (t*y 6/2)]
  unfold pairChartWSq
  ring

theorem pairChart_distance (t alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) :
    satelliteDistance (polarSatellites (pairChartRadii t alpha y)
      (pairChartAngles t alpha y)) 0 1=t*pairChartW t alpha y := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg ht.le (Real.sqrt_nonneg _))).mp
  change satelliteDistance (polarSatellites (pairChartRadii t alpha y)
    (pairChartAngles t alpha y)) 0 1^2=(t*Real.sqrt (pairChartWSq t alpha y))^2
  rw [pairChart_distance_sq,mul_pow, Real.sq_sqrt hW.le]

def pairInternalRadialA (eps t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  eps*t*(1-alpha)*(y 3-pairChartRadii t alpha y 1*singleScaleChi t (y 6))*
    (pairChartW t alpha y^3)⁻¹

def pairInternalRadialB (eps t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  -eps*t*alpha*(y 3+pairChartRadii t alpha y 0*singleScaleChi t (y 6))*
    (pairChartW t alpha y^3)⁻¹

def pairInternalAngularA (eps t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  t*(1-alpha)*pairChartRadii t alpha y 0*pairChartRadii t alpha y 1*y 6*
    Real.sinc (t*y 6)*((pairChartW t alpha y^3)⁻¹-t^3/(1+eps))

def pairInternalAngularB (eps t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  -t*alpha*pairChartRadii t alpha y 0*pairChartRadii t alpha y 1*y 6*
    Real.sinc (t*y 6)*((pairChartW t alpha y^3)⁻¹-t^3/(1+eps))

def pairInternalRadialMean (eps t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  -eps*t*alpha*(1-alpha)*(pairChartRadii t alpha y 0+pairChartRadii t alpha y 1)*
    singleScaleChi t (y 6)*(pairChartW t alpha y^3)⁻¹

def pairInternalRadialDifference (eps t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  -eps*(y 3+(alpha*pairChartRadii t alpha y 0-(1-alpha)*pairChartRadii t alpha y 1)*
    singleScaleChi t (y 6))*(pairChartW t alpha y^3)⁻¹

def pairInternalAngularDifference (eps t alpha : ℝ) (y : PairChartVariables) : ℝ :=
  -pairChartRadii t alpha y 0*pairChartRadii t alpha y 1*y 6*Real.sinc (t*y 6)*
    ((pairChartW t alpha y^3)⁻¹-t^3/(1+eps))

theorem pairInternalRadial_mean_identity (eps t alpha : ℝ) (y : PairChartVariables) :
    alpha*pairInternalRadialA eps t alpha y+(1-alpha)*pairInternalRadialB eps t alpha y=
      pairInternalRadialMean eps t alpha y := by
  unfold pairInternalRadialA pairInternalRadialB pairInternalRadialMean
  ring

theorem pairInternalRadial_difference_identity (eps t alpha : ℝ) (y : PairChartVariables) :
    pairInternalRadialB eps t alpha y-pairInternalRadialA eps t alpha y=
      t*pairInternalRadialDifference eps t alpha y := by
  unfold pairInternalRadialA pairInternalRadialB pairInternalRadialDifference
  ring

theorem pairInternalAngular_mean_identity (eps t alpha : ℝ) (y : PairChartVariables) :
    alpha*pairInternalAngularA eps t alpha y+(1-alpha)*pairInternalAngularB eps t alpha y=0 := by
  unfold pairInternalAngularA pairInternalAngularB
  ring

theorem pairInternalAngular_difference_identity (eps t alpha : ℝ) (y : PairChartVariables) :
    pairInternalAngularB eps t alpha y-pairInternalAngularA eps t alpha y=
      t*pairInternalAngularDifference eps t alpha y := by
  unfold pairInternalAngularA pairInternalAngularB pairInternalAngularDifference
  ring

theorem pairInternalRadialA_eq_physical (eps t alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) :
    pairInternalRadialA eps t alpha y=
      -eps*pairChartMass t 0 alpha 1*(pairChartRadii t alpha y 0-
        pairChartRadii t alpha y 1*Real.cos (pairChartAngles t alpha y 1-pairChartAngles t alpha y 0))/
      satelliteDistance (polarSatellites (pairChartRadii t alpha y)
        (pairChartAngles t alpha y)) 0 1^3 := by
  rw [pairChart_angle_gap,pairChart_distance t alpha y ht hW]
  have hnum : pairChartRadii t alpha y 0-pairChartRadii t alpha y 1*Real.cos (t*y 6)=
      -t*(y 3-pairChartRadii t alpha y 1*singleScaleChi t (y 6)) := by
    have hc := singleScaleChi_identity t (y 6)
    have hr := pairChart_radius_gap t alpha y
    nlinarith [congrArg (fun x : ℝ => pairChartRadii t alpha y 1*x) hc]
  rw [hnum]
  unfold pairInternalRadialA
  simp only [pairChartMass, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hn : pairChartW t alpha y≠0 := ne_of_gt (Real.sqrt_pos.mpr hW)
  field_simp [ne_of_gt ht,hn]

theorem pairInternalRadialB_eq_physical (eps t alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) :
    pairInternalRadialB eps t alpha y=
      -eps*pairChartMass t 0 alpha 0*(pairChartRadii t alpha y 1-
        pairChartRadii t alpha y 0*Real.cos (pairChartAngles t alpha y 0-pairChartAngles t alpha y 1))/
      satelliteDistance (polarSatellites (pairChartRadii t alpha y)
        (pairChartAngles t alpha y)) 1 0^3 := by
  have hg : pairChartAngles t alpha y 0-pairChartAngles t alpha y 1=-(t*y 6) := by
    linarith [pairChart_angle_gap t alpha y]
  rw [hg,Real.cos_neg]
  have hd : satelliteDistance (polarSatellites (pairChartRadii t alpha y)
      (pairChartAngles t alpha y)) 1 0=t*pairChartW t alpha y := by
    rw [satelliteDistance,norm_sub_rev]
    exact pairChart_distance t alpha y ht hW
  rw [hd]
  have hnum : pairChartRadii t alpha y 1-pairChartRadii t alpha y 0*Real.cos (t*y 6)=
      t*(y 3+pairChartRadii t alpha y 0*singleScaleChi t (y 6)) := by
    have hc := singleScaleChi_identity t (y 6)
    have hr := pairChart_radius_gap t alpha y
    nlinarith [congrArg (fun x : ℝ => pairChartRadii t alpha y 0*x) hc]
  rw [hnum]
  unfold pairInternalRadialB
  simp only [pairChartMass, Matrix.cons_val_zero]
  have hn : pairChartW t alpha y≠0 := ne_of_gt (Real.sqrt_pos.mpr hW)
  field_simp [ne_of_gt ht,hn]

theorem pairInternalAngularA_eq_physical (eps t alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) (heps : 1+eps≠0) :
    pairInternalAngularA eps t alpha y=
      pairChartMass t 0 alpha 1*pairChartRadii t alpha y 0*pairChartRadii t alpha y 1*
        Real.sin (pairChartAngles t alpha y 1-pairChartAngles t alpha y 0)*
        ((satelliteDistance (polarSatellites (pairChartRadii t alpha y)
          (pairChartAngles t alpha y)) 0 1^3)⁻¹-(1+eps)⁻¹) := by
  rw [pairChart_angle_gap,pairChart_distance t alpha y ht hW,
    ← sinc_mul_argument (t*y 6)]
  unfold pairInternalAngularA
  simp only [pairChartMass, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hn : pairChartW t alpha y≠0 := ne_of_gt (Real.sqrt_pos.mpr hW)
  field_simp [ne_of_gt ht,hn,heps]

theorem pairInternalAngularB_eq_physical (eps t alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) (heps : 1+eps≠0) :
    pairInternalAngularB eps t alpha y=
      pairChartMass t 0 alpha 0*pairChartRadii t alpha y 1*pairChartRadii t alpha y 0*
        Real.sin (pairChartAngles t alpha y 0-pairChartAngles t alpha y 1)*
        ((satelliteDistance (polarSatellites (pairChartRadii t alpha y)
          (pairChartAngles t alpha y)) 1 0^3)⁻¹-(1+eps)⁻¹) := by
  have hg : pairChartAngles t alpha y 0-pairChartAngles t alpha y 1=-(t*y 6) := by
    linarith [pairChart_angle_gap t alpha y]
  have hd : satelliteDistance (polarSatellites (pairChartRadii t alpha y)
      (pairChartAngles t alpha y)) 1 0=t*pairChartW t alpha y := by
    rw [satelliteDistance,norm_sub_rev]
    exact pairChart_distance t alpha y ht hW
  rw [hg,hd,Real.sin_neg,← sinc_mul_argument (t*y 6)]
  unfold pairInternalAngularB
  simp only [pairChartMass, Matrix.cons_val_zero]
  have hn : pairChartW t alpha y≠0 := ne_of_gt (Real.sqrt_pos.mpr hW)
  field_simp [ne_of_gt ht,hn,heps]

@[fun_prop] theorem pairChartWSq_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : PairJointVariables => pairChartWSq (v.1 1) (v.1 3) v.2) := by
  unfold pairChartWSq
  fun_prop

theorem pairChartW_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hW : 0<pairChartWSq (v.1 1) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : PairJointVariables => pairChartW (w.1 1) (w.1 3) w.2) v :=
  (pairChartWSq_joint_contDiff n).contDiffAt.sqrt (ne_of_gt hW)

theorem pairInverseCube_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hW : 0<pairChartWSq (v.1 1) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : PairJointVariables => (pairChartW (w.1 1) (w.1 3) w.2^3)⁻¹) v :=
  ((pairChartW_joint_contDiffAt n v hW).pow 3).inv
    (pow_ne_zero 3 (ne_of_gt (Real.sqrt_pos.mpr hW)))

theorem pairInternalRadialMean_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hW : 0<pairChartWSq (v.1 1) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairInternalRadialMean (w.1 0) (w.1 1) (w.1 3) w.2) v := by
  have hp : ContDiff ℝ n (fun w : PairJointVariables =>
      -w.1 0*w.1 1*w.1 3*(1-w.1 3)*
        (pairChartRadii (w.1 1) (w.1 3) w.2 0+pairChartRadii (w.1 1) (w.1 3) w.2 1)*
          singleScaleChi (w.1 1) (w.2 6)) := by
    unfold singleScaleChi
    fun_prop
  exact hp.contDiffAt.mul (pairInverseCube_joint_contDiffAt n v hW)

theorem pairInternalRadialDifference_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hW : 0<pairChartWSq (v.1 1) (v.1 3) v.2) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairInternalRadialDifference (w.1 0) (w.1 1) (w.1 3) w.2) v := by
  have hp : ContDiff ℝ n (fun w : PairJointVariables =>
      -w.1 0*(w.2 3+(w.1 3*pairChartRadii (w.1 1) (w.1 3) w.2 0-
        (1-w.1 3)*pairChartRadii (w.1 1) (w.1 3) w.2 1)*singleScaleChi (w.1 1) (w.2 6))) := by
    unfold singleScaleChi
    fun_prop
  exact hp.contDiffAt.mul (pairInverseCube_joint_contDiffAt n v hW)

theorem pairInternalAngularDifference_joint_contDiffAt (n : ℕ∞ω) (v : PairJointVariables)
    (hW : 0<pairChartWSq (v.1 1) (v.1 3) v.2) (heps : 1+v.1 0≠0) :
    ContDiffAt ℝ n (fun w : PairJointVariables =>
      pairInternalAngularDifference (w.1 0) (w.1 1) (w.1 3) w.2) v := by
  have hp : ContDiff ℝ n (fun w : PairJointVariables =>
      -pairChartRadii (w.1 1) (w.1 3) w.2 0*pairChartRadii (w.1 1) (w.1 3) w.2 1*
        w.2 6*Real.sinc (w.1 1*w.2 6)) := by fun_prop
  have hc : ContDiffAt ℝ n (fun w : PairJointVariables => w.1 1^3/(1+w.1 0)) v := by fun_prop
  exact hp.contDiffAt.mul ((pairInverseCube_joint_contDiffAt n v hW).sub hc)

end DominantFiveBody
