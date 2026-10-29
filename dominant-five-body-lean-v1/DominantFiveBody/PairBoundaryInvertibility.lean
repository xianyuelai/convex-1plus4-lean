import DominantFiveBody.PairJacobian

/-! # Invertibility of the genuine complete-pair boundary derivative -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital

theorem pairUnitPoint_line (omega psi z s : ℝ) (v : PairChartVariables)
    (hv0 : v 0=0) (hv1 : v 1=0) (hv2 : v 2=0) (hv3 : v 3=0) :
    pairUnitPoint omega psi z+s • v=
      pairUnitPoint (omega+s*v 4) (psi+s*v 5) (z+s*v 6) := by
  funext i
  fin_cases i <;> simp [pairUnitPoint,hv0,hv1,hv2,hv3]

theorem pairChartJacobian_unit_exterior (p alpha omega psi z : ℝ) (keepD : Bool)
    (hreg : PairChartRegular 0 0 alpha (pairUnitPoint omega psi z))
    (hw0 : omega≠0) (hwpi : |omega|<Real.pi) (v : PairChartVariables)
    (hv0 : v 0=0) (hv1 : v 1=0) (hv2 : v 2=0) (hv3 : v 3=0) :
    pairChartJacobian 0 0 p alpha keepD (pairUnitPoint omega psi z) v 4=
      (if keepD then p*kappa |omega| else -(1-p)*kappa |omega|)*v 4 := by
  apply pairChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ _ hreg
  have hshift : HasDerivAt (fun s : ℝ => omega+s*v 4) (v 4) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 4)).const_add omega
  have hk : HasDerivAt (fun s : ℝ => coorbitalKernel (omega+s*v 4))
      (-kappa |omega| * v 4) 0 := by
    convert! (coorbitalKernel_hasDerivAt hw0 hwpi).comp_of_eq 0 hshift (by simp) using 1
  have hd : HasDerivAt (fun s : ℝ => if keepD then -p*coorbitalKernel (omega+s*v 4)
      else (1-p)*coorbitalKernel (omega+s*v 4))
      ((if keepD then p*kappa |omega| else -(1-p)*kappa |omega|)*v 4) 0 := by
    cases keepD
    · convert! hk.const_mul (1-p) using 1
      simp
      ring
    · convert! hk.const_mul (-p) using 1
      simp
      ring
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ s : ℝ in 𝓝 0, omega+s*v 4≠0 :=
    (isClosed_eq (by fun_prop) continuous_const).isOpen_compl.mem_nhds (by simpa using hw0)
  have hpi : ∀ᶠ s : ℝ in 𝓝 0, |omega+s*v 4|<Real.pi :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hwpi)
  filter_upwards [hn,hpi] with s hs hsp
  rw [pairUnitPoint_line _ _ _ _ _ hv0 hv1 hv2 hv3]
  exact pairExteriorAngular_unit_boundary p alpha _ _ _ keepD hs hsp

theorem pairChartJacobian_unit_mean (p alpha omega psi z : ℝ) (keepD : Bool)
    (hreg : PairChartRegular 0 0 alpha (pairUnitPoint omega psi z))
    (hpsi0 : psi≠0) (hpsiw : psi≠omega) (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi)
    (v : PairChartVariables)
    (hv0 : v 0=0) (hv1 : v 1=0) (hv2 : v 2=0) (hv3 : v 3=0) (hv4 : v 4=0) :
    pairChartJacobian 0 0 p alpha keepD (pairUnitPoint omega psi z) v 5=
      pairProbeDerivative p omega psi*v 5 := by
  apply pairChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ _ hreg
  have hshift : HasDerivAt (fun s : ℝ => psi+s*v 5) (v 5) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 5)).const_add psi
  have hd := (twoSourcePolarAngular_unit_hasDerivAt p omega psi hpsi0 hpsiw hpi0 hpiw).comp_of_eq 0 hshift (by simp)
  convert! hd using 1
  · funext s
    rw [pairUnitPoint_line _ _ _ _ _ hv0 hv1 hv2 hv3]
    simp only [hv4,mul_zero,add_zero]
    exact pairAngularMean_at_boundary p alpha _

theorem pairAngularDifference_unit_hasDerivAt (p alpha omega psi z : ℝ)
    (hz : 0<z) (hpsi0 : psi≠0) (hpsiw : psi≠omega)
    (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi)
    (hscale : pairProbeDerivative p omega psi*z^3=1) :
    HasDerivAt (fun w : ℝ => pairAngularDifference 0 0 p alpha (pairUnitPoint omega psi w))
      (3*pairProbeDerivative p omega psi) z := by
  have hD : pairProbeDerivative p omega psi=1/z^3 := (eq_div_iff (pow_ne_zero 3 hz.ne')).mpr hscale
  have hid := hasDerivAt_id z
  have hd : HasDerivAt (fun w : ℝ => w*pairProbeDerivative p omega psi-(w^2)⁻¹)
      (3*pairProbeDerivative p omega psi) z := by
    convert! (hid.mul_const (pairProbeDerivative p omega psi)).sub
      ((hid.pow 2).inv (pow_ne_zero 2 hz.ne')) using 1
    rw [hD]
    simp only [Pi.pow_apply,id_eq]
    field_simp
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hz] with w hw
  exact pairAngularDifference_unit_boundary p alpha omega psi w hw hpsi0 hpsiw hpi0 hpiw

theorem pairChartJacobian_unit_difference (p alpha omega psi z : ℝ) (keepD : Bool)
    (hreg : PairChartRegular 0 0 alpha (pairUnitPoint omega psi z))
    (hz : 0<z) (hpsi0 : psi≠0) (hpsiw : psi≠omega)
    (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi)
    (hscale : pairProbeDerivative p omega psi*z^3=1) (v : PairChartVariables)
    (hv0 : v 0=0) (hv1 : v 1=0) (hv2 : v 2=0) (hv3 : v 3=0) (hv4 : v 4=0) (hv5 : v 5=0) :
    pairChartJacobian 0 0 p alpha keepD (pairUnitPoint omega psi z) v 6=
      (3*pairProbeDerivative p omega psi)*v 6 := by
  apply pairChartJacobian_apply_of_hasDerivAt _ _ _ _ _ _ _ hreg
  have hshift : HasDerivAt (fun s : ℝ => z+s*v 6) (v 6) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v 6)).const_add z
  have hd := (pairAngularDifference_unit_hasDerivAt p alpha omega psi z hz hpsi0 hpsiw hpi0 hpiw hscale).comp_of_eq 0 hshift (by simp)
  convert! hd using 1
  funext s
  rw [pairUnitPoint_line _ _ _ _ _ hv0 hv1 hv2 hv3]
  simp only [hv4,hv5,mul_zero,add_zero]
  rfl

/-- The `a₀,D,3D` kernel elimination for the actual seven-row derivative.
The mass condition is precisely positivity of the omitted exterior row.
There is no restriction on the pair fraction α. -/
theorem pairChartJacobian_boundary_isInvertible (p alpha psi z : ℝ) (keepD : Bool)
    (hp : 0≤p) (hp1 : p≤1) (hkeep : if keepD then 0<p else p<1)
    (hz : 0<z) (hpsi0 : psi≠0) (hpsih : psi≠h) (hspan : twoSourceSpan psi<Real.pi)
    (hroot : p*coorbitalKernel psi+(1-p)*coorbitalKernel (psi-h)=0)
    (hscale : pairProbeDerivative p h psi*z^3=1) :
    (pairChartJacobian 0 0 p alpha keepD (pairUnitPoint h psi z)).IsInvertible := by
  have hhpos : 0<h := by unfold h; positivity
  have hhpi : |h|<Real.pi := by rw [abs_of_pos hhpos]; unfold h; linarith [Real.pi_pos]
  have hsep := probe_separations_lt_pi hspan
  have hreg := pairUnitPoint_regular alpha h psi z hz hhpos.ne' hhpi hpsi0 hpsih hsep.1 hsep.2
  have hD : 0<pairProbeDerivative p h psi :=
    twoSourceProbe hp (by linarith) (by ring) hpsi0 hpsih hspan hroot
  apply euclidean_clm_isInvertible_of_injective
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change pairChartJacobian 0 0 p alpha keepD (pairUnitPoint h psi z) v=0 at hv
  have hv0 : v 0=0 := by
    have he := pairChartJacobian_unit_radial p alpha h psi z keepD hreg v 0
    rw [hv] at he
    change 0=3*v 0 at he
    linarith
  have hv1 : v 1=0 := by
    have he := pairChartJacobian_unit_radial p alpha h psi z keepD hreg v 1
    rw [hv] at he
    change 0=3*v 1 at he
    linarith
  have hv2 : v 2=0 := by
    have he := pairChartJacobian_unit_radial p alpha h psi z keepD hreg v 2
    rw [hv] at he
    change 0=3*v 2 at he
    linarith
  have hv3 : v 3=0 := by
    have he := pairChartJacobian_unit_radial_difference p alpha h psi z keepD hreg v
    rw [hv] at he
    change 0=3*v 3 at he
    linarith
  have ha : (if keepD then p*kappa |h| else -(1-p)*kappa |h|)≠0 := by
    rw [abs_of_pos hhpos,kappa_h]
    cases keepD <;> simp only [Bool.false_eq_true,if_false,if_true] at hkeep ⊢
    · exact mul_ne_zero (neg_ne_zero.mpr (by linarith)) (by norm_num)
    · exact mul_ne_zero (ne_of_gt hkeep) (by norm_num)
  have hv4 : v 4=0 := by
    have he := pairChartJacobian_unit_exterior p alpha h psi z keepD hreg hhpos.ne' hhpi v hv0 hv1 hv2 hv3
    rw [hv] at he
    exact (mul_eq_zero.mp he.symm).resolve_left ha
  have hv5 : v 5=0 := by
    have he := pairChartJacobian_unit_mean p alpha h psi z keepD hreg hpsi0 hpsih hsep.1 hsep.2 v hv0 hv1 hv2 hv3 hv4
    rw [hv] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hD.ne'
  have hv6 : v 6=0 := by
    have he := pairChartJacobian_unit_difference p alpha h psi z keepD hreg hz hpsi0 hpsih hsep.1 hsep.2 hscale v hv0 hv1 hv2 hv3 hv4 hv5
    rw [hv] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (ne_of_gt (mul_pos (by norm_num) hD))
  funext i
  fin_cases i <;> assumption

end DominantFiveBody
