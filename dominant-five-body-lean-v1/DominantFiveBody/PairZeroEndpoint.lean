import DominantFiveBody.PairContinuation

/-! # The positive-scale, fixed-mass ε=0 endpoint of a complete-pair branch

Here t,p,α stay fixed.  Thus the endpoint retains the same positive mass
ratio; it is distinct from the colliding boundary root at t=0.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

theorem positive_radial_zero_eq_one (r : ℝ) (hr : 0<r) (hg : r-(r^2)⁻¹=0) : r=1 := by
  have he : r^3=1 := by
    have hmul := (eq_div_iff (pow_ne_zero 2 hr.ne')).mp (show r=1/r^2 by simpa only [one_div] using sub_eq_zero.mp hg)
    nlinarith
  exact (pow_eq_one_iff_of_nonneg hr.le (by decide : (3 : ℕ)≠0)).mp he

theorem pairChart_zero_eps_unit_radii (t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (ht : 0<t)
    (hm : PositiveRatio (pairChartMass t p alpha)) (hreg : PairChartRegular 0 t alpha y)
    (hr : ∀ i, 0<pairChartRadii t alpha y i)
    (hroot : pairChartExtendedRows 0 t p alpha keepD y=0) :
    (∀ i, pairChartRadii t alpha y i=1) ∧ y 3=0 := by
  have hrows := (pairChartExtendedRows_zero_iff_physical 0 t p alpha keepD y ht hreg
    (ne_of_gt (hm.1 (if keepD then 2 else 3)))).mp hroot
  have hunit : ∀ i, pairChartRadii t alpha y i=1 := by
    intro i
    apply positive_radial_zero_eq_one _ (hr i)
    simpa only [radialResidual_at_zero] using hrows.1 i
  refine ⟨hunit,?_⟩
  have he := (pairChartRadii_recovery t alpha y ht.ne').2
  rw [hunit 0,hunit 1,sub_self,zero_div] at he
  exact he.symm

theorem angularResidual_unit_eq_coorbital_of_separated (mu theta : Satellite → ℝ)
    (hsep : SeparatedSemicircle theta) (i : Satellite) :
    angularResidual 0 mu (fun _ => 1) theta i=coorbitalResidual mu theta i := by
  unfold angularResidual coorbitalResidual
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i≠j := (Finset.mem_erase.mp hj).1.symm
  rw [coorbitalKernel_polar_chord _ _ (hsep i j hij).1 (hsep i j hij).2]
  simp only [polarSatellites,satelliteDistance,add_zero,mul_one,inv_one]
  ring

/-- All four coorbital equations, including both members of the pair,
hold at the same fixed positive mass ratio.  Positive t and regularity
give actual collision freedom, not merely distinct chart coordinates. -/
theorem pairChart_fixed_mass_zero_endpoint (t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (ht : 0<t)
    (hm : PositiveRatio (pairChartMass t p alpha)) (hreg : PairChartRegular 0 t alpha y)
    (hr : ∀ i, 0<pairChartRadii t alpha y i)
    (hwidth : ∀ i j, |pairChartAngles t alpha y j-pairChartAngles t alpha y i|<Real.pi)
    (hroot : pairChartExtendedRows 0 t p alpha keepD y=0) :
    (∀ i, pairChartRadii t alpha y i=1) ∧ y 3=0 ∧
      RelativeCollisionFree (pairChartPoints t alpha y) ∧
      SeparatedSemicircle (pairChartAngles t alpha y) ∧
      ∀ i, coorbitalResidual (pairChartMass t p alpha) (pairChartAngles t alpha y) i=0 := by
  have hunit := pairChart_zero_eps_unit_radii t p alpha keepD y ht hm hreg hr hroot
  have hcf := pairChartPoints_relativeCollisionFree 0 t alpha y ht hreg
  have hsep : SeparatedSemicircle (pairChartAngles t alpha y) := by
    intro i j hij
    refine ⟨?_,hwidth i j⟩
    intro he
    apply hcf.2 i j hij
    change polarPoint (pairChartRadii t alpha y i) (pairChartAngles t alpha y i)=
      polarPoint (pairChartRadii t alpha y j) (pairChartAngles t alpha y j)
    rw [hunit.1 i,hunit.1 j,he]
  refine ⟨hunit.1,hunit.2,hcf,hsep,?_⟩
  have hrows := (pairChartExtendedRows_zero_iff_physical 0 t p alpha keepD y ht hreg
    (ne_of_gt (hm.1 (if keepD then 2 else 3)))).mp hroot
  intro i
  have he := hrows.2 i
  have hradii : pairChartRadii t alpha y=fun _ => 1 := funext hunit.1
  rwa [hradii,angularResidual_unit_eq_coorbital_of_separated _ _ hsep i] at he

/-- The angular-width condition is an open ambient condition.  It has no
positive lower bound on the pair separation and imposes no ε/t relation. -/
theorem pairChartWidth_isOpen : IsOpen {v : PairJointVariables |
    ∀ i j, |pairChartAngles (v.1 1) (v.1 3) v.2 j-pairChartAngles (v.1 1) (v.1 3) v.2 i|<Real.pi} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (((pairChartAngles_joint_contDiff 0 j).continuous.sub
    (pairChartAngles_joint_contDiff 0 i).continuous).abs) continuous_const

theorem pairChartWidth_at_unit_boundary (alpha omega psi z : ℝ)
    (hwpi : |omega|<Real.pi) (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi) :
    ∀ i j, |pairChartAngles 0 alpha (pairUnitPoint omega psi z) j-
      pairChartAngles 0 alpha (pairUnitPoint omega psi z) i|<Real.pi := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp_all [pairChartAngles,pairUnitPoint,abs_sub_comm,Real.pi_pos]

end DominantFiveBody
