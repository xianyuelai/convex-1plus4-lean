import DominantFiveBody.NestedBoundary
import DominantFiveBody.TripleJacobian
import DominantFiveBody.PairContinuation

/-! # Actual unit nested equations and their explicit four boundary seeds -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital

def nestedUnitPoint (psi Z z : ℝ) : NestedChartVariables := ![1,1,0,0,psi,Z,z]
def nestedBasePoint (psi omega : ℝ) : NestedChartVariables :=
  nestedUnitPoint psi (omega*pairBoundaryScale tripleD0) (pairBoundaryScale (3*tripleD0))

theorem nestedUnitPoint_radii (alpha psi Z z : ℝ) :
    nestedChartRadii 0 0 alpha (nestedUnitPoint psi Z z)=fun _ => 1 := by
  funext i
  fin_cases i <;> simp [nestedChartRadii,nestedCoordinates,nestedUnitPoint]

theorem nestedBoundaryKernel_unit (psi z : ℝ) :
    nestedBoundaryKernel 1 psi (0,z)=tripleScalarForce z := by
  rw [nestedBoundaryKernel_formula]
  norm_num only [zero_pow,one_pow,one_mul,zero_add]
  rw [Real.sqrt_sq_eq_abs]
  rfl

theorem nestedBoundaryKernel_unit_hasFDerivAt (psi Z : ℝ) (hZ : Z≠0) :
    HasFDerivAt (nestedBoundaryKernel 1 psi)
      (fderiv ℝ (nestedBoundaryKernel 1 psi) (0,Z)) (0,Z) := by
  have hp : polarPointDerivative (1,psi) (0,Z)≠0 := by
    intro hz
    have hh := congrArg (fun q => inner ℝ q (quarterTurn (polarPoint 1 psi))) hz
    rw [polarPointDerivative_apply] at hh
    simp only [zero_smul,zero_add,real_inner_smul_left,quarterTurn_inner_quarterTurn,
      polarPoint_inner_same,mul_one,inner_zero_left] at hh
    exact hZ hh
  have hn := (newtonTargetField_hasFDerivAt 0 (-polarPointDerivative (1,psi) (0,Z))
    (by simpa using hp)).comp (0,Z) (-(polarPointDerivative (1,psi))).hasFDerivAt
  have hi := hn.inner ℝ (hasFDerivAt_const (quarterTurn (polarPoint 1 psi)) (0,Z))
  have heq : (fun u : ℝ×ℝ => inner ℝ (newtonTargetField 0 (-polarPointDerivative (1,psi) u))
      (quarterTurn (polarPoint 1 psi)))=nestedBoundaryKernel 1 psi := by
    funext u
    rw [nestedBoundaryKernel,scaledNewtonField_eq_target]
  simp only [Function.comp_apply,neg_apply] at hi
  rw [heq] at hi
  exact hi.differentiableAt.hasFDerivAt

theorem nestedBoundaryKernel_unit_partial (psi Z z : ℝ) (hZ : Z≠0) :
    (fderiv ℝ (nestedBoundaryKernel 1 psi) (0,Z)) (0,z)=(-2/|Z|^3)*z := by
  have hp : HasDerivAt (fun r : ℝ => ((0 : ℝ),r)) (0,1) Z :=
    (hasDerivAt_const Z 0).prodMk (hasDerivAt_id Z)
  have hd := (nestedBoundaryKernel_unit_hasFDerivAt psi Z hZ).comp_hasDerivAt Z hp
  have hs := (tripleScalarForce_hasDerivAt hZ).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun r => nestedBoundaryKernel_unit psi r))
  have h1 : (fderiv ℝ (nestedBoundaryKernel 1 psi) (0,Z)) (0,1) = -2/|Z|^3 :=
    hd.unique hs
  have he : ((0 : ℝ),z)=z • ((0 : ℝ),1) := by ext <;> simp
  rw [he,map_smul,h1,smul_eq_mul]
  ring

theorem nestedUnit_angularDerivative (psi z : ℝ) (hpsi : psi≠0) (hpi : |psi|<Real.pi) :
    (fderiv ℝ (twoSourcePolarAngular 1 1 1 0) (1,psi)) (0,z)=kappa |psi| * z := by
  have he : ((0 : ℝ),z)=z • ((0 : ℝ),1) := by ext <;> simp
  rw [he,map_smul,twoSourcePolarAngular_unit_partial 1 0 psi hpsi hpsi hpi (by simpa using hpi)]
  simp only [one_mul,sub_self,zero_mul,add_zero,smul_eq_mul]
  ring

theorem nestedAngularMean_unit_boundary (alpha psi Z z : ℝ)
    (hpsi : psi≠0) (hpi : |psi|<Real.pi) :
    nestedAngularMean 0 0 0 alpha (nestedUnitPoint psi Z z) = -coorbitalKernel psi := by
  rw [nestedAngularMean_at_boundary]
  change twoSourcePolarAngular 1 1 1 0 (1,psi)=_
  rw [twoSourcePolarAngular_unit 1 0 psi hpsi hpsi hpi (by simpa using hpi)]
  ring

theorem nestedAngularOuterDifference_unit_boundary (alpha psi Z z : ℝ)
    (hpsi : psi≠0) (hpi : |psi|<Real.pi) :
    nestedAngularOuterDifference 0 0 0 alpha (nestedUnitPoint psi Z z) =
      kappa |psi| * Z-tripleScalarForce Z := by
  have hsep := polarUnit_ne_of_angle_ne 0 psi hpsi.symm (by simpa using hpi)
  rw [nestedAngularOuterDifference_at_boundary alpha _ hsep]
  change (fderiv ℝ (twoSourcePolarAngular 1 1 1 0) (1,psi)) (0,Z)-
    nestedBoundaryKernel 1 psi (0,Z)=_
  rw [nestedUnit_angularDerivative psi Z hpsi hpi,nestedBoundaryKernel_unit]

theorem nestedAngularInnerDifference_unit_boundary (alpha psi Z z : ℝ)
    (hpsi : psi≠0) (hpi : |psi|<Real.pi) (hZ : Z≠0) :
    nestedAngularInnerDifference 0 0 0 alpha (nestedUnitPoint psi Z z) =
      kappa |psi| * z+2/|Z|^3*z-tripleScalarForce z := by
  have hsep := polarUnit_ne_of_angle_ne 0 psi hpsi.symm (by simpa using hpi)
  rw [nestedAngularInnerDifference_at_boundary alpha _ hsep]
  · change (fderiv ℝ (twoSourcePolarAngular 1 1 1 0) (1,psi)) (0,z)-
      (fderiv ℝ (nestedBoundaryKernel 1 psi) (0,Z)) (0,z)-nestedBoundaryKernel 1 psi (0,z)=_
    rw [nestedUnit_angularDerivative psi z hpsi hpi,nestedBoundaryKernel_unit_partial psi Z z hZ,
      nestedBoundaryKernel_unit]
    ring
  · change 0<(0 : ℝ)^2+1^2*Z^2
    simpa using sq_pos_of_ne_zero hZ

theorem nestedUnitPoint_regular (alpha psi Z z : ℝ) (hZ : Z≠0) (hz : z≠0)
    (hpsi : psi≠0) (hpi : |psi|<Real.pi) :
    NestedChartRegular 0 0 0 alpha (nestedUnitPoint psi Z z) := by
  refine ⟨by norm_num,?_,?_,?_,?_⟩
  · intro i
    rw [nestedUnitPoint_radii]
    norm_num
  · rw [nestedInnerWSq_at_boundary]
    change 0<(0 : ℝ)^2+1^2*z^2
    simpa using sq_pos_of_ne_zero hz
  · intro i
    rw [nestedOuterWSq_at_boundary]
    change 0<(0 : ℝ)^2+1^2*Z^2
    simpa using sq_pos_of_ne_zero hZ
  · intro i
    rw [nestedChartPoints_zero_exterior,nestedChartPoints_zero_cluster]
    exact polarUnit_ne_of_angle_ne 0 psi hpsi.symm (by simpa using hpi)

theorem nestedChartExtendedRows_unit_root (alpha psi Z z : ℝ) (hangle : |psi|=h)
    (hZ : Z≠0) (hz : 0<z) (hscaleZ : tripleD0*|Z|^3=1) (hscalez : 3*tripleD0*z^3=1) :
    nestedChartExtendedRows 0 0 0 alpha (nestedUnitPoint psi Z z)=0 := by
  obtain ⟨hpsi,hpi,hkernel,hD⟩ := tripleBoundaryAngle_facts psi hangle
  have hZ3 : |Z|^3≠0 := pow_ne_zero 3 (abs_ne_zero.mpr hZ)
  ext i
  fin_cases i
  · simp [nestedChartExtendedRows,radialResidual,nestedChartRadii,nestedCoordinates,nestedUnitPoint]
  · change nestedRadialMean 0 0 0 alpha (nestedUnitPoint psi Z z)=0
    rw [nestedRadialMean_at_boundary]
    norm_num [nestedUnitPoint]
  · change nestedRadialOuterDifference 0 0 0 alpha (nestedUnitPoint psi Z z)=0
    rw [nestedRadialOuterDifference_at_boundary]
    simp [nestedUnitPoint]
  · change nestedRadialInnerDifference 0 0 0 alpha (nestedUnitPoint psi Z z)=0
    rw [nestedRadialInnerDifference_at_boundary]
    simp [nestedUnitPoint]
  · change nestedAngularMean 0 0 0 alpha (nestedUnitPoint psi Z z)=0
    rw [nestedAngularMean_unit_boundary alpha psi Z z hpsi hpi,hkernel,neg_zero]
  · change nestedAngularOuterDifference 0 0 0 alpha (nestedUnitPoint psi Z z)=0
    rw [nestedAngularOuterDifference_unit_boundary alpha psi Z z hpsi hpi,hD]
    unfold tripleScalarForce
    field_simp
    nlinarith [congrArg (fun a => a*Z) hscaleZ]
  · change nestedAngularInnerDifference 0 0 0 alpha (nestedUnitPoint psi Z z)=0
    rw [nestedAngularInnerDifference_unit_boundary alpha psi Z z hpsi hpi hZ,hD]
    have hdiv : 2/|Z|^3=2*tripleD0 := by
      field_simp
      nlinarith
    rw [hdiv,tripleScalarForce,abs_of_pos hz]
    field_simp
    nlinarith

theorem nestedBasePoint_scale (omega : ℝ) (hw : |omega|=1) :
    tripleD0*|omega*pairBoundaryScale tripleD0|^3=1 ∧
      3*tripleD0*pairBoundaryScale (3*tripleD0)^3=1 := by
  constructor
  · rw [abs_mul,hw,one_mul,abs_of_pos (pairBoundaryScale_pos tripleD0 tripleD0_pos)]
    exact pairBoundaryScale_equation tripleD0 tripleD0_pos
  · exact pairBoundaryScale_equation (3*tripleD0) (mul_pos (by norm_num) tripleD0_pos)

theorem nestedBasePoint_outer_ne_zero (omega : ℝ) (hw : |omega|=1) :
    omega*pairBoundaryScale tripleD0≠0 := by
  have ho : omega≠0 := by intro hz; rw [hz,abs_zero] at hw; norm_num at hw
  exact mul_ne_zero ho (ne_of_gt (pairBoundaryScale_pos tripleD0 tripleD0_pos))

theorem nestedBasePoint_regular (alpha psi omega : ℝ) (hangle : |psi|=h) (hw : |omega|=1) :
    NestedChartRegular 0 0 0 alpha (nestedBasePoint psi omega) := by
  obtain ⟨hpsi,hpi,_,_⟩ := tripleBoundaryAngle_facts psi hangle
  exact nestedUnitPoint_regular alpha psi _ _ (nestedBasePoint_outer_ne_zero omega hw)
    (ne_of_gt (pairBoundaryScale_pos (3*tripleD0) (mul_pos (by norm_num) tripleD0_pos))) hpsi hpi

theorem nestedChartExtendedRows_base_root (alpha psi omega : ℝ) (hangle : |psi|=h) (hw : |omega|=1) :
    nestedChartExtendedRows 0 0 0 alpha (nestedBasePoint psi omega)=0 := by
  obtain ⟨hZ,hz⟩ := nestedBasePoint_scale omega hw
  exact nestedChartExtendedRows_unit_root alpha psi _ _ hangle (nestedBasePoint_outer_ne_zero omega hw)
    (pairBoundaryScale_pos (3*tripleD0) (mul_pos (by norm_num) tripleD0_pos)) hZ hz

end DominantFiveBody
