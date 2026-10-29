import DominantFiveBody.PairBoundary
import DominantFiveBody.CoorbitalCovering

/-! # Pair boundary angular equations and their actual probe derivative -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital

theorem coorbitalKernel_polar_chord (a b : ℝ) (hne : a≠b) (hpi : |b-a|<Real.pi) :
    coorbitalKernel (b-a)=Real.sin (b-a)*((‖polarPoint 1 a-polarPoint 1 b‖^3)⁻¹-1) := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hp : 0<b-a := sub_pos.mpr hab
    have hlt : b-a<Real.pi := by simpa only [abs_of_pos hp] using hpi
    have hd : ‖polarPoint 1 a-polarPoint 1 b‖=2*Real.sin ((b-a)/2) := by
      simpa only [polarPoint,one_mul] using unit_circle_chord a b hp hlt
    rw [coorbitalKernel_eq_positive_formula _ hp.le,hd]
    simp only [kernelF,inv_pow]
  · have hp : 0<a-b := sub_pos.mpr hba
    have hlt : a-b<Real.pi := by simpa only [abs_of_neg (sub_neg.mpr hba),neg_sub] using hpi
    have hd : ‖polarPoint 1 a-polarPoint 1 b‖=2*Real.sin ((a-b)/2) := by
      rw [norm_sub_rev]
      simpa only [polarPoint,one_mul] using unit_circle_chord b a hp hlt
    rw [show b-a=-(a-b) by ring,coorbitalKernel_neg,
      coorbitalKernel_eq_positive_formula _ hp.le,Real.sin_neg,hd]
    simp only [kernelF,inv_pow,neg_mul]

theorem polarUnit_ne_of_angle_ne (a b : ℝ) (hne : a≠b) (hpi : |b-a|<Real.pi) :
    polarPoint 1 a≠polarPoint 1 b := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hp : 0<b-a := sub_pos.mpr hab
    have hlt : b-a<Real.pi := by simpa only [abs_of_pos hp] using hpi
    have hd : ‖polarPoint 1 a-polarPoint 1 b‖=2*Real.sin ((b-a)/2) := by
      simpa only [polarPoint,one_mul] using unit_circle_chord a b hp hlt
    exact sub_ne_zero.mp (norm_ne_zero_iff.mp (by rw [hd]; exact ne_of_gt (mul_pos (by norm_num) (sin_half_pos hp hlt))))
  · have hp : 0<a-b := sub_pos.mpr hba
    have hlt : a-b<Real.pi := by simpa only [abs_of_neg (sub_neg.mpr hba),neg_sub] using hpi
    have hd : ‖polarPoint 1 a-polarPoint 1 b‖=2*Real.sin ((a-b)/2) := by
      rw [norm_sub_rev]
      simpa only [polarPoint,one_mul] using unit_circle_chord b a hp hlt
    exact sub_ne_zero.mp (norm_ne_zero_iff.mp (by rw [hd]; exact ne_of_gt (mul_pos (by norm_num) (sin_half_pos hp hlt))))

theorem unit_source_target_angular_kernel (theta phi : ℝ)
    (hne : theta≠phi) (hpi : |phi-theta|<Real.pi) :
    inner ℝ (newtonTargetField (polarPoint 1 phi) (polarPoint 1 theta)-polarPoint 1 phi)
      (quarterTurn (polarPoint 1 theta))=coorbitalKernel (phi-theta) := by
  have h := newtonTargetField_angular 1 1 1 theta phi
  simpa only [one_smul,one_mul,coorbitalKernel_polar_chord theta phi hne hpi] using h

theorem twoSourcePolarAngular_unit (p omega psi : ℝ)
    (hpsi0 : psi≠0) (hpsiw : psi≠omega) (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi) :
    twoSourcePolarAngular p 1 1 omega (1,psi)=
      -(p*coorbitalKernel psi+(1-p)*coorbitalKernel (psi-omega)) := by
  have hs : twoSourceTargetField p 1 1 omega (polarPoint 1 psi)=
      p • (newtonTargetField (polarPoint 1 0) (polarPoint 1 psi)-polarPoint 1 0)+
        (1-p) • (newtonTargetField (polarPoint 1 omega) (polarPoint 1 psi)-polarPoint 1 omega) := by
    unfold twoSourceTargetField
    module
  unfold twoSourcePolarAngular
  rw [hs]
  simp only [inner_add_left,real_inner_smul_left]
  rw [unit_source_target_angular_kernel psi 0 hpsi0 (by simpa using hpi0),
    unit_source_target_angular_kernel psi omega hpsiw (by simpa only [abs_sub_comm] using hpiw),
    zero_sub,coorbitalKernel_neg,show omega-psi=-(psi-omega) by ring,coorbitalKernel_neg]
  ring

theorem twoSourcePolarAngular_unit_hasDerivAt (p omega psi : ℝ)
    (hpsi0 : psi≠0) (hpsiw : psi≠omega) (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi) :
    HasDerivAt (fun v : ℝ => twoSourcePolarAngular p 1 1 omega (1,v))
      (p*kappa |psi|+(1-p)*kappa |psi-omega|) psi := by
  have h1 := coorbitalKernel_hasDerivAt hpsi0 hpi0
  have h2 := (coorbitalKernel_hasDerivAt (sub_ne_zero.mpr hpsiw) hpiw).comp psi
    ((hasDerivAt_id psi).sub_const omega)
  have hd : HasDerivAt (fun v : ℝ => -(p*coorbitalKernel v+(1-p)*coorbitalKernel (v-omega)))
      (p*kappa |psi|+(1-p)*kappa |psi-omega|) psi := by
    convert! ((h1.const_mul p).add (h2.const_mul (1-p))).neg using 1
    ring
  have heq : (fun v : ℝ => twoSourcePolarAngular p 1 1 omega (1,v)) =ᶠ[𝓝 psi]
      (fun v : ℝ => -(p*coorbitalKernel v+(1-p)*coorbitalKernel (v-omega))) := by
    have hdist0 : ∀ᶠ v in 𝓝 psi, |v|<Real.pi :=
      (continuous_abs.tendsto psi).eventually (Iio_mem_nhds hpi0)
    have hdistw : ∀ᶠ v in 𝓝 psi, |v-omega|<Real.pi :=
      (show Continuous (fun v : ℝ => |v-omega|) by fun_prop).continuousAt.eventually
        (Iio_mem_nhds hpiw)
    filter_upwards [eventually_ne_nhds hpsi0,eventually_ne_nhds hpsiw,hdist0,hdistw] with v hv0 hvw hvpi0 hvpiw
    exact twoSourcePolarAngular_unit p omega v hv0 hvw hvpi0 hvpiw
  exact hd.congr_of_eventuallyEq heq

theorem twoSourcePolarAngular_unit_partial (p omega psi : ℝ)
    (hpsi0 : psi≠0) (hpsiw : psi≠omega) (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi) :
    (fderiv ℝ (twoSourcePolarAngular p 1 1 omega) (1,psi)) (0,1)=
      p*kappa |psi|+(1-p)*kappa |psi-omega| := by
  have hc : polarPoint 1 0≠polarPoint 1 psi :=
    polarUnit_ne_of_angle_ne 0 psi hpsi0.symm (by simpa using hpi0)
  have hd : polarPoint 1 omega≠polarPoint 1 psi :=
    polarUnit_ne_of_angle_ne omega psi hpsiw.symm hpiw
  have hp : HasDerivAt (fun v : ℝ => ((1 : ℝ),v)) (0,1) psi :=
    (hasDerivAt_const psi 1).prodMk (hasDerivAt_id psi)
  have h := (twoSourcePolarAngular_differentiableAt p 1 1 omega (1,psi) hc hd).hasFDerivAt.comp_hasDerivAt psi hp
  exact h.unique (twoSourcePolarAngular_unit_hasDerivAt p omega psi hpsi0 hpsiw hpi0 hpiw)

def pairUnitPoint (omega psi z : ℝ) : PairChartVariables := ![1,1,1,0,omega,psi,z]

def pairProbeDerivative (p omega psi : ℝ) : ℝ := p*kappa |psi|+(1-p)*kappa |psi-omega|

theorem pairUnitPoint_radii (alpha omega psi z : ℝ) :
    pairChartRadii 0 alpha (pairUnitPoint omega psi z)=fun _ => 1 := by
  funext i
  fin_cases i <;> simp [pairChartRadii,pairUnitPoint]

theorem pairUnitPoint_WSq (alpha omega psi z : ℝ) :
    pairChartWSq 0 alpha (pairUnitPoint omega psi z)=z^2 := by
  simp [pairChartWSq,pairUnitPoint,pairChartRadii]

theorem pairAngularMean_unit_boundary (p alpha omega psi z : ℝ)
    (hpsi0 : psi≠0) (hpsiw : psi≠omega) (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi) :
    pairAngularMean 0 0 p alpha (pairUnitPoint omega psi z)=
      -(p*coorbitalKernel psi+(1-p)*coorbitalKernel (psi-omega)) := by
  rw [pairAngularMean_at_boundary]
  exact twoSourcePolarAngular_unit p omega psi hpsi0 hpsiw hpi0 hpiw

theorem pairAngularDifference_unit_boundary (p alpha omega psi z : ℝ)
    (hz : 0<z) (hpsi0 : psi≠0) (hpsiw : psi≠omega)
    (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi) :
    pairAngularDifference 0 0 p alpha (pairUnitPoint omega psi z)=
      z*pairProbeDerivative p omega psi-(z^2)⁻¹ := by
  have hc : polarPoint 1 0≠polarPoint 1 psi :=
    polarUnit_ne_of_angle_ne 0 psi hpsi0.symm (by simpa using hpi0)
  have hd : polarPoint 1 omega≠polarPoint 1 psi :=
    polarUnit_ne_of_angle_ne omega psi hpsiw.symm hpiw
  rw [pairAngularDifference_at_boundary p alpha _ hc hd]
  change (fderiv ℝ (twoSourcePolarAngular p 1 1 omega) (1,psi)) (0,z)-
    1^2*z/(Real.sqrt (0^2+1^2*z^2)^3)=_
  have hv : ((0 : ℝ),z)=z • ((0 : ℝ),1) := by ext <;> simp
  rw [hv,map_smul,twoSourcePolarAngular_unit_partial p omega psi hpsi0 hpsiw hpi0 hpiw]
  norm_num only [zero_pow,one_pow,one_mul,zero_add,smul_eq_mul,pairProbeDerivative]
  rw [Real.sqrt_sq hz.le]
  field_simp

theorem pairExteriorAngular_unit_boundary (p alpha omega psi z : ℝ) (keepD : Bool)
    (hw0 : omega≠0) (hwpi : |omega|<Real.pi) :
    pairChartExtendedRows 0 0 p alpha keepD (pairUnitPoint omega psi z) 4=
      if keepD then -p*coorbitalKernel omega else (1-p)*coorbitalKernel omega := by
  have hk := coorbitalKernel_polar_chord 0 omega hw0.symm (by simpa using hwpi)
  simp only [sub_zero] at hk
  cases keepD
  · change angularResidual 0 (pairChartMass 0 p alpha)
      (pairChartRadii 0 alpha (pairUnitPoint omega psi z))
      (pairChartAngles 0 alpha (pairUnitPoint omega psi z)) 2=(1-p)*coorbitalKernel omega
    rw [pairUnitPoint_radii]
    unfold angularResidual
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ 2),Fin.sum_univ_four]
    simp [pairChartMass,pairChartAngles,pairUnitPoint,satelliteDistance,polarSatellites] at hk ⊢
    rw [hk]
    ring
  · change angularResidual 0 (pairChartMass 0 p alpha)
      (pairChartRadii 0 alpha (pairUnitPoint omega psi z))
      (pairChartAngles 0 alpha (pairUnitPoint omega psi z)) 3= -p*coorbitalKernel omega
    rw [pairUnitPoint_radii]
    unfold angularResidual
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ 3),Fin.sum_univ_four]
    simp [pairChartMass,pairChartAngles,pairUnitPoint,satelliteDistance,polarSatellites] at hk ⊢
    rw [norm_sub_rev,hk]
    ring

end DominantFiveBody
