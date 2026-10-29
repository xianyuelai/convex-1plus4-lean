import DominantFiveBody.NestedUnitBoundary
import DominantFiveBody.NestedHessian

/-! # The genuine nested boundary Jacobian

Kernel elimination differentiates the actual seven rows. The restricted
diagonal coefficients at the base are 3, D0, 3D0 and 9D0.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

theorem nestedChartExtendedRows_hasFDerivAt (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (hreg : NestedChartRegular eps t eta alpha y) :
    HasFDerivAt (nestedChartExtendedRows eps t eta alpha)
      (nestedChartJacobian eps t eta alpha y) y := by
  let p : NestedChartParameters := ![eps,t,eta,alpha]
  have hc : ContDiff ℝ 1 (fun w : NestedChartVariables => (p,w)) := contDiff_const.prodMk contDiff_id
  have hd := (nestedChartExtendedRows_joint_contDiffAt 1 (p,y) hreg).comp y hc.contDiffAt
  exact (hd.differentiableAt (by norm_num)).hasFDerivAt

theorem nestedChartJacobian_apply_of_hasDerivAt (eps t eta alpha : ℝ) (y v : NestedChartVariables)
    (hreg : NestedChartRegular eps t eta alpha y) (i : Fin 7) (a : ℝ)
    (ha : HasDerivAt (fun s : ℝ => nestedChartExtendedRows eps t eta alpha (y+s • v) i) a 0) :
    nestedChartJacobian eps t eta alpha y v i=a := by
  have hp : HasDerivAt (fun s : ℝ => y+s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hf : HasFDerivAt (nestedChartExtendedRows eps t eta alpha)
      (nestedChartJacobian eps t eta alpha y) (y+(0 : ℝ) • v) := by
    simpa using nestedChartExtendedRows_hasFDerivAt eps t eta alpha y hreg
  have hd := hf.comp_hasDerivAt 0 hp
  have hi := (ContinuousLinearMap.proj i : NestedChartVariables →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  exact hi.unique ha

theorem nestedChart_boundary_radial (alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedChartExtendedRows 0 0 0 alpha y i.castSucc.castSucc.castSucc.castSucc.castSucc =
      y i.castSucc.castSucc.castSucc.castSucc.castSucc-
        (y i.castSucc.castSucc.castSucc.castSucc.castSucc^2)⁻¹ := by
  fin_cases i
  · simp [nestedChartExtendedRows,radialResidual,nestedChartRadii]
  · exact nestedRadialMean_at_boundary alpha y

theorem nestedChartJacobian_unit_radial (alpha psi Z z : ℝ)
    (hreg : NestedChartRegular 0 0 0 alpha (nestedUnitPoint psi Z z))
    (v : NestedChartVariables) (i : Fin 2) :
    nestedChartJacobian 0 0 0 alpha (nestedUnitPoint psi Z z) v
      i.castSucc.castSucc.castSucc.castSucc.castSucc =
        3*v i.castSucc.castSucc.castSucc.castSucc.castSucc := by
  let j : Fin 7 := i.castSucc.castSucc.castSucc.castSucc.castSucc
  have hy : nestedUnitPoint psi Z z j=1 := by fin_cases i <;> simp [j,nestedUnitPoint]
  apply nestedChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ hreg
  have hL : HasDerivAt (fun s : ℝ => (nestedUnitPoint psi Z z+s • v) j) (v j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (nestedUnitPoint psi Z z j)
  have hn : (nestedUnitPoint psi Z z+(0 : ℝ) • v) j^2≠0 := by simp [hy]
  have hd := hL.sub ((hasDerivAt_inv hn).comp 0 (hL.pow 2))
  convert! hd using 1
  · funext s
    exact nestedChart_boundary_radial alpha _ i
  · simp [hy]
    ring

theorem nestedChartJacobian_unit_radial_difference (alpha psi Z z : ℝ)
    (hreg : NestedChartRegular 0 0 0 alpha (nestedUnitPoint psi Z z))
    (v : NestedChartVariables) (k : Fin 2) :
    nestedChartJacobian 0 0 0 alpha (nestedUnitPoint psi Z z) v
      k.castSucc.castSucc.castSucc.succ.succ =
        3*v k.castSucc.castSucc.castSucc.succ.succ := by
  let j : Fin 7 := k.castSucc.castSucc.castSucc.succ.succ
  have hR : HasDerivAt (fun s : ℝ => (nestedUnitPoint psi Z z+s • v) 1) (v 1) 0 := by
    simpa [nestedUnitPoint] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add 1
  have hu : HasDerivAt (fun s : ℝ => (nestedUnitPoint psi Z z+s • v) j) (v j) 0 := by
    have hy : nestedUnitPoint psi Z z j=0 := by fin_cases k <;> simp [j,nestedUnitPoint]
    simpa [hy] using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (nestedUnitPoint psi Z z j)
  have hn : (nestedUnitPoint psi Z z+(0 : ℝ) • v) 1^2*
      (nestedUnitPoint psi Z z+(0 : ℝ) • v) 1^2≠0 := by simp [nestedUnitPoint]
  have hd := hu.mul ((hasDerivAt_const (0 : ℝ) 1).add
    ((hR.const_mul 2).div ((hR.pow 2).mul (hR.pow 2)) hn))
  apply nestedChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ hreg
  convert! hd using 1
  · funext s
    fin_cases k
    · exact nestedRadialOuterDifference_at_boundary alpha _
    · exact nestedRadialInnerDifference_at_boundary alpha _
  · fin_cases k <;> simp [nestedUnitPoint,j] <;> ring

theorem nestedUnitPoint_line (psi Z z s : ℝ) (v : NestedChartVariables)
    (hv0 : v 0=0) (hv1 : v 1=0) (hv2 : v 2=0) (hv3 : v 3=0) :
    nestedUnitPoint psi Z z+s • v =
      nestedUnitPoint (psi+s*v 4) (Z+s*v 5) (z+s*v 6) := by
  ext i
  fin_cases i <;> simp [nestedUnitPoint,hv0,hv1,hv2,hv3]

theorem nestedChartJacobian_unit_mean (alpha psi Z z : ℝ)
    (hreg : NestedChartRegular 0 0 0 alpha (nestedUnitPoint psi Z z))
    (hpsi : psi≠0) (hpi : |psi|<Real.pi) (v : NestedChartVariables)
    (hv0 : v 0=0) (hv1 : v 1=0) (hv2 : v 2=0) (hv3 : v 3=0) :
    nestedChartJacobian 0 0 0 alpha (nestedUnitPoint psi Z z) v 4=kappa |psi| * v 4 := by
  apply nestedChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ hreg
  have hp : HasDerivAt (fun s : ℝ => psi+s*v 4) (v 4) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 4)).const_add psi
  have hd := (twoSourcePolarAngular_unit_hasDerivAt 1 0 psi hpsi hpsi hpi
    (by simpa using hpi)).comp_of_eq 0 hp (by simp)
  convert! hd using 1
  · funext s
    rw [nestedUnitPoint_line _ _ _ _ _ hv0 hv1 hv2 hv3]
    exact nestedAngularMean_at_boundary alpha _
  · simp

theorem nestedChartJacobian_unit_outer (alpha psi Z z : ℝ)
    (hreg : NestedChartRegular 0 0 0 alpha (nestedUnitPoint psi Z z))
    (hpsi : psi≠0) (hpi : |psi|<Real.pi) (hZ : Z≠0) (v : NestedChartVariables)
    (hv0 : v 0=0) (hv1 : v 1=0) (hv2 : v 2=0) (hv3 : v 3=0) (hv4 : v 4=0) :
    nestedChartJacobian 0 0 0 alpha (nestedUnitPoint psi Z z) v 5=
      (kappa |psi| + 2/|Z|^3)*v 5 := by
  have hp : HasDerivAt (fun s : ℝ => Z+s*v 5) (v 5) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 5)).const_add Z
  have hd := (hp.const_mul (kappa |psi|)).sub
    ((tripleScalarForce_hasDerivAt hZ).comp_of_eq 0 hp (by simp))
  apply nestedChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ hreg
  convert! hd using 1
  · funext s
    rw [nestedUnitPoint_line _ _ _ _ _ hv0 hv1 hv2 hv3]
    simp only [hv4,mul_zero,add_zero]
    exact nestedAngularOuterDifference_unit_boundary alpha psi _ _ hpsi hpi
  · ring

theorem nestedChartJacobian_unit_inner (alpha psi Z z : ℝ)
    (hreg : NestedChartRegular 0 0 0 alpha (nestedUnitPoint psi Z z))
    (hpsi : psi≠0) (hpi : |psi|<Real.pi) (hZ : Z≠0) (hz : z≠0) (v : NestedChartVariables)
    (hv0 : v 0=0) (hv1 : v 1=0) (hv2 : v 2=0) (hv3 : v 3=0) (hv4 : v 4=0) (hv5 : v 5=0) :
    nestedChartJacobian 0 0 0 alpha (nestedUnitPoint psi Z z) v 6=
      (kappa |psi| + 2/|Z|^3 + 2/|z|^3)*v 6 := by
  have hp : HasDerivAt (fun s : ℝ => z+s*v 6) (v 6) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 6)).const_add z
  have hd := ((hp.const_mul (kappa |psi|)).add (hp.const_mul (2/|Z|^3))).sub
    ((tripleScalarForce_hasDerivAt hz).comp_of_eq 0 hp (by simp))
  apply nestedChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ hreg
  convert! hd using 1
  · funext s
    rw [nestedUnitPoint_line _ _ _ _ _ hv0 hv1 hv2 hv3]
    simp only [hv4,hv5,mul_zero,add_zero]
    exact nestedAngularInnerDifference_unit_boundary alpha psi Z _ hpsi hpi hZ
  · ring

theorem nestedBasePoint_diagonal_scales (omega : ℝ) (hw : |omega|=1) :
    2/|omega*pairBoundaryScale tripleD0|^3=2*tripleD0 ∧
      2/|pairBoundaryScale (3*tripleD0)|^3=6*tripleD0 := by
  obtain ⟨hZ,hz⟩ := nestedBasePoint_scale omega hw
  have hZne := pow_ne_zero 3 (abs_ne_zero.mpr (nestedBasePoint_outer_ne_zero omega hw))
  have hzpos := pairBoundaryScale_pos (3*tripleD0) (mul_pos (by norm_num) tripleD0_pos)
  constructor
  · apply (div_eq_iff hZne).mpr
    nlinarith
  · rw [abs_of_pos hzpos]
    apply (div_eq_iff (pow_ne_zero 3 hzpos.ne')).mpr
    nlinarith

/-- The true seven-dimensional derivative is invertible at all four
signed seeds and all alpha, including alpha zero and one. -/
theorem nestedChartJacobian_boundary_isInvertible (alpha psi omega : ℝ)
    (hangle : |psi|=h) (hw : |omega|=1) :
    (nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega)).IsInvertible := by
  obtain ⟨hpsi,hpi,_,hD⟩ := tripleBoundaryAngle_facts psi hangle
  have hreg := nestedBasePoint_regular alpha psi omega hangle hw
  have hZ := nestedBasePoint_outer_ne_zero omega hw
  have hz := ne_of_gt (pairBoundaryScale_pos (3*tripleD0) (mul_pos (by norm_num) tripleD0_pos))
  obtain ⟨hZscale,hzscale⟩ := nestedBasePoint_diagonal_scales omega hw
  apply euclidean_clm_isInvertible_of_injective
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) v=0 at hv
  simp only [nestedBasePoint] at hv
  have hv0 : v 0=0 := by
    have hd := nestedChartJacobian_unit_radial alpha psi _ _ hreg v 0
    rw [hv] at hd
    change 0=3*v 0 at hd
    linarith
  have hv1 : v 1=0 := by
    have hd := nestedChartJacobian_unit_radial alpha psi _ _ hreg v 1
    rw [hv] at hd
    change 0=3*v 1 at hd
    linarith
  have hv2 : v 2=0 := by
    have hd := nestedChartJacobian_unit_radial_difference alpha psi _ _ hreg v 0
    rw [hv] at hd
    change 0=3*v 2 at hd
    linarith
  have hv3 : v 3=0 := by
    have hd := nestedChartJacobian_unit_radial_difference alpha psi _ _ hreg v 1
    rw [hv] at hd
    change 0=3*v 3 at hd
    linarith
  have hv4 : v 4=0 := by
    have hd := nestedChartJacobian_unit_mean alpha psi _ _ hreg hpsi hpi v hv0 hv1 hv2 hv3
    rw [hv,hD] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (ne_of_gt tripleD0_pos)
  have hv5 : v 5=0 := by
    have hd := nestedChartJacobian_unit_outer alpha psi _ _ hreg hpsi hpi hZ v hv0 hv1 hv2 hv3 hv4
    rw [hv,hD,hZscale] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (ne_of_gt (by nlinarith [tripleD0_pos]))
  have hv6 : v 6=0 := by
    have hd := nestedChartJacobian_unit_inner alpha psi _ _ hreg hpsi hpi hZ hz v
      hv0 hv1 hv2 hv3 hv4 hv5
    rw [hv,hD,hZscale,hzscale] at hd
    exact (mul_eq_zero.mp hd.symm).resolve_left (ne_of_gt (by nlinarith [tripleD0_pos]))
  ext i
  fin_cases i <;> assumption

theorem nestedChartJacobian_isInvertible_iff_shape (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (heps : 0<eps) (ht : 0<t) (he : 0<eta) (hm : PositiveRatio (nestedChartMass t eta alpha))
    (hreg : NestedChartRegular eps t eta alpha y) (hr : ∀ i,0<nestedChartRadii t eta alpha y i)
    (hroot : nestedChartExtendedRows eps t eta alpha y=0) :
    (nestedChartJacobian eps t eta alpha y).IsInvertible ↔
      ShapeHessianNondegenerate (masses eps (nestedChartMass t eta alpha)) 1
        (centeredFromRelative eps (nestedChartMass t eta alpha) (nestedChartPoints t eta alpha y)) :=
  nestedChartDerivative_isInvertible_iff_shape eps t eta alpha y heps ht he hm hreg hr hroot

end DominantFiveBody
