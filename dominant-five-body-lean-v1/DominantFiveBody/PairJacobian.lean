import DominantFiveBody.PairUnitBoundary

/-! # The actual seven-variable pair-chart Jacobian

All derivatives below are derivatives of `pairChartExtendedRows`.  The
kernel elimination first uses the four radial rows and then the three
angular rows; no proposed matrix is substituted for an actual derivative.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital

theorem pairUnitPoint_regular (alpha omega psi z : ℝ)
    (hz : 0<z) (hw0 : omega≠0) (hwpi : |omega|<Real.pi)
    (hpsi0 : psi≠0) (hpsiw : psi≠omega)
    (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi) :
    PairChartRegular 0 0 alpha (pairUnitPoint omega psi z) := by
  refine ⟨by norm_num,?_,?_,?_⟩
  · intro i
    rw [pairUnitPoint_radii]
    norm_num
  · rw [pairUnitPoint_WSq]
    positivity
  · intro i hi j hij
    have hc := polarUnit_ne_of_angle_ne 0 psi hpsi0.symm (by simpa using hpi0)
    have hd := polarUnit_ne_of_angle_ne omega psi hpsiw.symm hpiw
    have hcd := polarUnit_ne_of_angle_ne 0 omega hw0.symm (by simpa using hwpi)
    have hdc := hcd.symm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> fin_cases j <;>
      simp_all [pairChartPoints_at_zero,pairUnitPoint]

theorem pairChartExtendedRows_unit_root (p alpha psi z : ℝ) (keepD : Bool)
    (hz : 0<z) (hpsi0 : psi≠0) (hpsih : psi≠h)
    (hpi0 : |psi|<Real.pi) (hpih : |psi-h|<Real.pi)
    (hroot : p*coorbitalKernel psi+(1-p)*coorbitalKernel (psi-h)=0)
    (hscale : pairProbeDerivative p h psi*z^3=1) :
    pairChartExtendedRows 0 0 p alpha keepD (pairUnitPoint h psi z)=0 := by
  have hh0 : h≠0 := ne_of_gt (by unfold h; positivity)
  have hhpi : |h|<Real.pi := by rw [abs_of_pos (by unfold h; positivity)]; unfold h; linarith [Real.pi_pos]
  have hfh : coorbitalKernel h=0 := by
    rw [coorbitalKernel_eq_positive_formula _ (by unfold h; positivity),kernelF_h]
  funext i
  fin_cases i
  · simp [pairChartExtendedRows,radialResidual,pairChartRadii,pairUnitPoint]
  · simp [pairChartExtendedRows,radialResidual,pairChartRadii,pairUnitPoint]
  · change pairRadialMean 0 0 p alpha (pairUnitPoint h psi z)=0
    rw [pairRadialMean_at_boundary]
    change (1 : ℝ)-(1^2)⁻¹=0
    norm_num
  · change pairRadialDifference 0 0 p alpha (pairUnitPoint h psi z)=0
    rw [pairRadialDifference_at_boundary]
    change (0 : ℝ)*(1+2*1/(1^2*1^2))=0
    norm_num
  · change pairChartExtendedRows 0 0 p alpha keepD (pairUnitPoint h psi z) 4=0
    rw [pairExteriorAngular_unit_boundary _ _ _ _ _ _ hh0 hhpi,hfh]
    cases keepD <;> simp
  · change pairAngularMean 0 0 p alpha (pairUnitPoint h psi z)=0
    rw [pairAngularMean_unit_boundary _ _ _ _ _ hpsi0 hpsih hpi0 hpih,hroot,neg_zero]
  · change pairAngularDifference 0 0 p alpha (pairUnitPoint h psi z)=0
    rw [pairAngularDifference_unit_boundary _ _ _ _ _ hz hpsi0 hpsih hpi0 hpih]
    apply sub_eq_zero.mpr
    rw [←one_div]
    apply (eq_div_iff (pow_ne_zero 2 hz.ne')).mpr
    nlinarith [hscale]

def pairChartJacobian (eps t p alpha : ℝ) (keepD : Bool) (y : PairChartVariables) :
    PairChartVariables →L[ℝ] PairChartVariables :=
  fderiv ℝ (pairChartExtendedRows eps t p alpha keepD) y

theorem pairChartExtendedRows_hasFDerivAt (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (hreg : PairChartRegular eps t alpha y) :
    HasFDerivAt (pairChartExtendedRows eps t p alpha keepD)
      (pairChartJacobian eps t p alpha keepD y) y := by
  have hc : ContDiff ℝ 1 (fun w : PairChartVariables => ((![eps,t,p,alpha] : Fin 4 → ℝ),w)) :=
    contDiff_const.prodMk contDiff_id
  have hd := (pairChartExtendedRows_joint_contDiffAt 1
    ((![eps,t,p,alpha] : Fin 4 → ℝ),y) hreg keepD).comp y hc.contDiffAt
  exact (hd.differentiableAt (by norm_num)).hasFDerivAt

theorem pairChartJacobian_apply_of_hasDerivAt (eps t p alpha : ℝ) (keepD : Bool)
    (y v : PairChartVariables) (hreg : PairChartRegular eps t alpha y)
    (i : Fin 7) (a : ℝ)
    (ha : HasDerivAt (fun s : ℝ => pairChartExtendedRows eps t p alpha keepD (y+s • v) i) a 0) :
    pairChartJacobian eps t p alpha keepD y v i=a := by
  have hp : HasDerivAt (fun s : ℝ => y+s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y
  have hdf : HasFDerivAt (pairChartExtendedRows eps t p alpha keepD)
      (pairChartJacobian eps t p alpha keepD y) (y+(0 : ℝ) • v) := by
    simpa using pairChartExtendedRows_hasFDerivAt eps t p alpha keepD y hreg
  have hd := hdf.comp_hasDerivAt 0 hp
  have hi := (ContinuousLinearMap.proj i : PairChartVariables →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  exact hi.unique ha

theorem pairChart_boundary_radial (p alpha : ℝ) (keepD : Bool) (y : PairChartVariables)
    (i : Fin 3) :
    pairChartExtendedRows 0 0 p alpha keepD y i.castSucc.castSucc.castSucc.castSucc=
      y i.castSucc.castSucc.castSucc.castSucc-(y i.castSucc.castSucc.castSucc.castSucc^2)⁻¹ := by
  fin_cases i
  · simp [pairChartExtendedRows,radialResidual,pairChartRadii]
  · simp [pairChartExtendedRows,radialResidual,pairChartRadii]
  · exact pairRadialMean_at_boundary p alpha y

theorem pairChartJacobian_unit_radial (p alpha omega psi z : ℝ) (keepD : Bool)
    (hreg : PairChartRegular 0 0 alpha (pairUnitPoint omega psi z))
    (v : PairChartVariables) (i : Fin 3) :
    pairChartJacobian 0 0 p alpha keepD (pairUnitPoint omega psi z) v
      i.castSucc.castSucc.castSucc.castSucc=3*v i.castSucc.castSucc.castSucc.castSucc := by
  let j : Fin 7 := i.castSucc.castSucc.castSucc.castSucc
  have hy : pairUnitPoint omega psi z j=1 := by fin_cases i <;> simp [j,pairUnitPoint]
  apply pairChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ _ hreg
  have hL : HasDerivAt (fun s : ℝ => (pairUnitPoint omega psi z+s • v) j) (v j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (pairUnitPoint omega psi z j)
  have hn : (pairUnitPoint omega psi z+(0 : ℝ) • v) j^2≠0 := by simp [hy]
  have hd := hL.sub ((hasDerivAt_inv hn).comp 0 (hL.pow 2))
  convert! hd using 1
  · funext s
    exact pairChart_boundary_radial p alpha keepD _ i
  · simp [hy]
    ring

theorem pairChartJacobian_unit_radial_difference (p alpha omega psi z : ℝ) (keepD : Bool)
    (hreg : PairChartRegular 0 0 alpha (pairUnitPoint omega psi z))
    (v : PairChartVariables) :
    pairChartJacobian 0 0 p alpha keepD (pairUnitPoint omega psi z) v 3=3*v 3 := by
  apply pairChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ _ hreg
  have hR : HasDerivAt (fun s : ℝ => (pairUnitPoint omega psi z+s • v) 2) (v 2) 0 := by
    simpa [pairUnitPoint] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 2)).const_add 1
  have hu : HasDerivAt (fun s : ℝ => (pairUnitPoint omega psi z+s • v) 3) (v 3) 0 := by
    simpa [pairUnitPoint] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 3))
  have hn : (pairUnitPoint omega psi z+(0 : ℝ) • v) 2^2*
      (pairUnitPoint omega psi z+(0 : ℝ) • v) 2^2≠0 := by
    simp only [zero_smul,add_zero]
    change (1 : ℝ)^2*1^2≠0
    norm_num
  have hd := hu.mul ((hasDerivAt_const (0 : ℝ) 1).add
    ((hR.const_mul 2).div ((hR.pow 2).mul (hR.pow 2)) hn))
  convert! hd using 1
  · funext s
    exact pairRadialDifference_at_boundary p alpha _
  · have hy2 : pairUnitPoint omega psi z 2=1 := rfl
    have hy3 : pairUnitPoint omega psi z 3=0 := rfl
    norm_num [hy2,hy3]
    ring

end DominantFiveBody
