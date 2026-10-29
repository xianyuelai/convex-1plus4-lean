import DominantFiveBody.PairSmooth
import DominantFiveBody.NewtonTargetDerivative
import DominantFiveBody.PolarPointDerivative

/-! # The pair boundary equations from the actual seven-row extension -/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

def twoSourceTargetField (p rc rd omega : ℝ) (target : Plane) : Plane :=
  p • newtonTargetField (polarPoint rc 0) target+
    (1-p) • newtonTargetField (polarPoint rd omega) target-
    (p • polarPoint rc 0+(1-p) • polarPoint rd omega)

def twoSourceTargetDerivative (p rc rd omega : ℝ) (target : Plane) : Plane →L[ℝ] Plane :=
  p • newtonTargetDerivative (polarPoint rc 0) target+
    (1-p) • newtonTargetDerivative (polarPoint rd omega) target

def twoSourcePolarAngular (p rc rd omega : ℝ) (x : ℝ×ℝ) : ℝ :=
  inner ℝ (twoSourceTargetField p rc rd omega (polarPoint x.1 x.2))
    (quarterTurn (polarPoint x.1 x.2))

theorem twoSourceTargetField_hasFDerivAt (p rc rd omega : ℝ) (target : Plane)
    (hc : polarPoint rc 0≠target) (hd : polarPoint rd omega≠target) :
    HasFDerivAt (twoSourceTargetField p rc rd omega)
      (twoSourceTargetDerivative p rc rd omega target) target := by
  convert! (((newtonTargetField_hasFDerivAt (polarPoint rc 0) target hc).const_smul p).add
    ((newtonTargetField_hasFDerivAt (polarPoint rd omega) target hd).const_smul (1-p))).sub_const
      (p • polarPoint rc 0+(1-p) • polarPoint rd omega) using 1

theorem twoSourcePolarAngular_fderiv_apply (p rc rd omega : ℝ) (x v : ℝ×ℝ)
    (hc : polarPoint rc 0≠polarPoint x.1 x.2) (hd : polarPoint rd omega≠polarPoint x.1 x.2) :
    (fderiv ℝ (twoSourcePolarAngular p rc rd omega) x) v=
      inner ℝ (twoSourceTargetDerivative p rc rd omega (polarPoint x.1 x.2)
        (polarPointDerivative x v)) (quarterTurn (polarPoint x.1 x.2))+
      inner ℝ (twoSourceTargetField p rc rd omega (polarPoint x.1 x.2))
        (quarterTurn (polarPointDerivative x v)) := by
  have hp := polarPoint_hasFDerivAt x
  have hf := (twoSourceTargetField_hasFDerivAt p rc rd omega (polarPoint x.1 x.2) hc hd).comp x hp
  have hq := quarterTurnLinear.toContinuousLinearMap.hasFDerivAt.comp x hp
  have h := hf.inner ℝ hq
  have hfd := congrArg (fun L : (ℝ×ℝ) →L[ℝ] ℝ => L v) h.fderiv
  convert! hfd using 1
  simp [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,fderivInnerCLM_apply,add_comm]

theorem twoSourcePolarAngular_differentiableAt (p rc rd omega : ℝ) (x : ℝ×ℝ)
    (hc : polarPoint rc 0≠polarPoint x.1 x.2) (hd : polarPoint rd omega≠polarPoint x.1 x.2) :
    DifferentiableAt ℝ (twoSourcePolarAngular p rc rd omega) x := by
  have hp := polarPoint_hasFDerivAt x
  have hf := (twoSourceTargetField_hasFDerivAt p rc rd omega (polarPoint x.1 x.2) hc hd).comp x hp
  have hq := quarterTurnLinear.toContinuousLinearMap.hasFDerivAt.comp x hp
  convert! (hf.inner ℝ hq).differentiableAt using 1

theorem pairChartPoints_at_zero (alpha : ℝ) (y : PairChartVariables) :
    pairChartPoints 0 alpha y=
      ![polarPoint (y 2) (y 5),polarPoint (y 2) (y 5),polarPoint (y 0) 0,polarPoint (y 1) (y 4)] := by
  ext i k
  fin_cases i <;> simp [pairChartPoints,polarSatellites,pairChartRadii,pairChartAngles]

theorem pairUnitDirection_at_zero (alpha : ℝ) (y : PairChartVariables) :
    pairUnitDirection 0 alpha y=y 6 • quarterTurn (polarPoint 1 (y 5)) := by
  simp [pairUnitDirection]

theorem pairPointDirection_at_zero (alpha : ℝ) (y : PairChartVariables) :
    pairPointDirection 0 alpha y=polarPointDerivative (y 2,y 5) (y 3,y 6) := by
  rw [pairPointDirection,pairUnitDirection_at_zero,polarPointDerivative_apply,
    polarPoint_rotation_smul (y 2) (y 5)]
  simp only [pairChartAngles,pairChartRadii,Matrix.cons_val_zero,Matrix.cons_val_one,
    mul_zero,zero_mul,sub_zero,add_zero,smul_smul]
  rw [mul_comm]

theorem pairExteriorAngularField_at_zero (p alpha : ℝ) (y : PairChartVariables) (target : Plane) :
    pairExteriorAngularField 0 0 p alpha y target=twoSourceTargetField p (y 0) (y 1) (y 4) target := by
  simp [pairExteriorAngularField,pairExteriorNewtonField,twoSourceTargetField,
    pairChartMass,pairChartPoints_at_zero]

theorem pairExteriorNewtonDifference_at_zero (p alpha : ℝ) (y : PairChartVariables)
    (hc : polarPoint (y 0) 0≠polarPoint (y 2) (y 5))
    (hd : polarPoint (y 1) (y 4)≠polarPoint (y 2) (y 5)) :
    pairExteriorNewtonDifference 0 p alpha y=
      twoSourceTargetDerivative p (y 0) (y 1) (y 4) (polarPoint (y 2) (y 5))
        (polarPointDerivative (y 2,y 5) (y 3,y 6)) := by
  unfold pairExteriorNewtonDifference
  simp only [pairChartPoints_at_zero,pairPointDirection_at_zero,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  rw [dividedNewtonTargetField_diagonal _ _ _ hc,dividedNewtonTargetField_diagonal _ _ _ hd,
    (newtonTargetField_hasFDerivAt _ _ hc).fderiv,(newtonTargetField_hasFDerivAt _ _ hd).fderiv]
  simp [pairChartMass,twoSourceTargetDerivative]

theorem pairRadialMean_at_boundary (p alpha : ℝ) (y : PairChartVariables) :
    pairRadialMean 0 0 p alpha y=y 2-(y 2^2)⁻¹ := by
  simp only [pairRadialMean,pairRadialExterior,pairInternalRadialMean,pairChartRadii,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,sub_zero,add_zero,neg_zero]
  ring

theorem pairRadialDifference_at_boundary (p alpha : ℝ) (y : PairChartVariables) :
    pairRadialDifference 0 0 p alpha y=y 3*(1+2*y 2/(y 2^2*y 2^2)) := by
  simp only [pairRadialDifference,pairInternalRadialDifference,pairChartRadii,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,sub_zero,add_zero,neg_zero]
  ring

theorem pairAngularMean_at_boundary (p alpha : ℝ) (y : PairChartVariables) :
    pairAngularMean 0 0 p alpha y=twoSourcePolarAngular p (y 0) (y 1) (y 4) (y 2,y 5) := by
  unfold pairAngularMean pairAngularExterior
  rw [pairExteriorAngularField_at_zero,pairExteriorAngularField_at_zero,pairChartPoints_at_zero]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  unfold twoSourcePolarAngular
  ring

/-- This is the actual boundary row: its exterior term is the derivative
of the full target field, with radial and angular components both retained. -/
theorem pairAngularDifference_at_boundary (p alpha : ℝ) (y : PairChartVariables)
    (hc : polarPoint (y 0) 0≠polarPoint (y 2) (y 5))
    (hd : polarPoint (y 1) (y 4)≠polarPoint (y 2) (y 5)) :
    pairAngularDifference 0 0 p alpha y=
      (fderiv ℝ (twoSourcePolarAngular p (y 0) (y 1) (y 4)) (y 2,y 5)) (y 3,y 6)-
        y 2^2*y 6/(Real.sqrt (y 3^2+y 2^2*y 6^2)^3) := by
  unfold pairAngularDifference
  rw [pairExteriorNewtonDifference_at_zero p alpha y hc hd,
    pairExteriorAngularField_at_zero,pairPointDirection_at_zero,pairChartPoints_at_zero,
    twoSourcePolarAngular_fderiv_apply _ _ _ _ _ _ hc hd]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  have hW : pairChartWSq 0 alpha y=y 3^2+y 2^2*y 6^2 := by
    simp only [pairChartWSq,pairChartRadii,Matrix.cons_val_zero,Matrix.cons_val_one,
      mul_zero,zero_mul,sub_zero,add_zero,zero_div,Real.sinc_zero,one_pow,mul_one]
    ring
  simp only [pairInternalAngularDifference,pairChartW,hW,pairChartRadii,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,sub_zero,add_zero,
    Real.sinc_zero,mul_one]
  ring

end DominantFiveBody
