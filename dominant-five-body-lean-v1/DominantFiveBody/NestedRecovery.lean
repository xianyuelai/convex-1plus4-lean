import DominantFiveBody.NestedSmooth
import DominantFiveBody.PairZeroEndpoint

/-! # Physical recovery and the fixed positive-mass zero-ε endpoint

The endpoint keeps t,η,α fixed and positive. It is not the simultaneous
colliding t=η=0 boundary used to construct the implicit branch.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

theorem nestedChartPoints_relativeCollisionFree (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hreg : NestedChartRegular eps t eta alpha y) :
    RelativeCollisionFree (nestedChartPoints t eta alpha y) := by
  have hab : nestedChartPoints t eta alpha y 0≠nestedChartPoints t eta alpha y 1 := by
    apply sub_ne_zero.mp
    apply norm_ne_zero_iff.mp
    change satelliteDistance (nestedChartPoints t eta alpha y) 0 1≠0
    rw [nestedInner_distance t eta alpha y ht he hreg.2.2.1]
    exact mul_ne_zero (mul_ne_zero ht.ne' he.ne') (Real.sqrt_pos.mpr hreg.2.2.1).ne'
  have hac (i : Fin 2) : nestedChartPoints t eta alpha y (i.castAdd 2)≠nestedChartPoints t eta alpha y 2 := by
    apply sub_ne_zero.mp
    apply norm_ne_zero_iff.mp
    change satelliteDistance (nestedChartPoints t eta alpha y) (i.castAdd 2) 2≠0
    rw [nestedOuter_distance t eta alpha y i ht (hreg.2.2.2.1 i)]
    exact mul_ne_zero ht.ne' (Real.sqrt_pos.mpr (hreg.2.2.2.1 i)).ne'
  refine ⟨?_,?_⟩
  · intro i
    apply norm_ne_zero_iff.mp
    change ‖polarPoint (nestedChartRadii t eta alpha y i) (nestedChartAngles t eta alpha y i)‖≠0
    rw [polarPoint_norm]
    exact abs_ne_zero.mpr (hreg.2.1 i)
  · intro i j hij
    have h02 : nestedChartPoints t eta alpha y 0≠nestedChartPoints t eta alpha y 2 := hac 0
    have h12 : nestedChartPoints t eta alpha y 1≠nestedChartPoints t eta alpha y 2 := hac 1
    have h30 : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y 0 := hreg.2.2.2.2 0
    have h31 : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y 1 := hreg.2.2.2.2 1
    have h32 : nestedChartPoints t eta alpha y 3≠nestedChartPoints t eta alpha y 2 := hreg.2.2.2.2 2
    fin_cases i <;> fin_cases j <;> simp_all <;> aesop

theorem nestedChartExtendedRows_zero_iff_physical (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hreg : NestedChartRegular eps t eta alpha y) (hp : 1-t^3≠0) :
    nestedChartExtendedRows eps t eta alpha y=0 ↔
      (∀ i,radialResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
        (nestedChartAngles t eta alpha y) i=0) ∧
      (∀ i,angularResidual eps (nestedChartMass t eta alpha) (nestedChartRadii t eta alpha y)
        (nestedChartAngles t eta alpha y) i=0) := by
  rw [nestedChartExtendedRows_eq_physical eps t eta alpha y ht he hreg.1 hreg.2.1 hreg.2.2.1 hreg.2.2.2.1 hreg.2.2.2.2]
  exact nestedChartPhysicalRows_zero_iff eps t eta alpha y ht.ne' he.ne' hp

theorem nestedChartExtendedRows_zero_iff_normalized (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (heps : 0<eps) (ht : 0<t) (he : 0<eta) (hm : PositiveRatio (nestedChartMass t eta alpha))
    (hreg : NestedChartRegular eps t eta alpha y) (hr : ∀ i,0<nestedChartRadii t eta alpha y i) :
    nestedChartExtendedRows eps t eta alpha y=0 ↔
      NormalizedCentralConfiguration (masses eps (nestedChartMass t eta alpha))
        (centeredFromRelative eps (nestedChartMass t eta alpha) (nestedChartPoints t eta alpha y)) := by
  rw [nestedChartExtendedRows_zero_iff_physical eps t eta alpha y ht he hreg (hm.1 3).ne']
  exact (polarResiduals_zero_iff_vectorRoot eps (nestedChartMass t eta alpha)
    (nestedChartRadii t eta alpha y,nestedChartAngles t eta alpha y) heps hm hr).trans
    (normalized_centeredFromRelative_iff_vectorRoot eps (nestedChartMass t eta alpha)
      (by linarith) hm (nestedChartPoints t eta alpha y)
      (nestedChartPoints_relativeCollisionFree eps t eta alpha y ht he hreg)).symm

theorem nestedChart_zero_eps_unit_radii (t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hp : 1-t^3≠0) (hreg : NestedChartRegular 0 t eta alpha y)
    (hr : ∀ i,0<nestedChartRadii t eta alpha y i) (hroot : nestedChartExtendedRows 0 t eta alpha y=0) :
    (∀ i,nestedChartRadii t eta alpha y i=1) ∧ y 2=0 ∧ y 3=0 := by
  have hrows := (nestedChartExtendedRows_zero_iff_physical 0 t eta alpha y ht he hreg hp).mp hroot
  have hunit : ∀ i,nestedChartRadii t eta alpha y i=1 := by
    intro i
    apply positive_radial_zero_eq_one _ (hr i)
    simpa only [radialResidual_at_zero] using hrows.1 i
  have hinner := nestedEdge_radial_identity t eta alpha y 2
  change nestedChartRadii t eta alpha y 1-nestedChartRadii t eta alpha y 0=t*eta*y 3 at hinner
  rw [hunit 1,hunit 0,sub_self] at hinner
  have hu2 : y 3=0 := (mul_eq_zero.mp hinner.symm).resolve_left (mul_ne_zero ht.ne' he.ne')
  have houter := (nestedOuter_gaps t eta alpha y 0).1
  change nestedChartRadii t eta alpha y 2-nestedChartRadii t eta alpha y 0=t*(y 2+(1-alpha)*eta*y 3) at houter
  rw [hunit 2,hunit 0,hu2,mul_zero,add_zero,sub_self] at houter
  exact ⟨hunit,(mul_eq_zero.mp houter.symm).resolve_left ht.ne',hu2⟩

theorem nestedChart_fixed_mass_zero_endpoint (t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hm : PositiveRatio (nestedChartMass t eta alpha))
    (hreg : NestedChartRegular 0 t eta alpha y) (hr : ∀ i,0<nestedChartRadii t eta alpha y i)
    (hwidth : ∀ i j,|nestedChartAngles t eta alpha y j-nestedChartAngles t eta alpha y i|<Real.pi)
    (hroot : nestedChartExtendedRows 0 t eta alpha y=0) :
    (∀ i,nestedChartRadii t eta alpha y i=1) ∧ y 2=0 ∧ y 3=0 ∧
      RelativeCollisionFree (nestedChartPoints t eta alpha y) ∧ SeparatedSemicircle (nestedChartAngles t eta alpha y) ∧
      ∀ i,coorbitalResidual (nestedChartMass t eta alpha) (nestedChartAngles t eta alpha y) i=0 := by
  have hunit := nestedChart_zero_eps_unit_radii t eta alpha y ht he (hm.1 3).ne' hreg hr hroot
  have hcf := nestedChartPoints_relativeCollisionFree 0 t eta alpha y ht he hreg
  have hsep : SeparatedSemicircle (nestedChartAngles t eta alpha y) := by
    intro i j hij
    refine ⟨?_,hwidth i j⟩
    intro h
    apply hcf.2 i j hij
    change polarPoint (nestedChartRadii t eta alpha y i) (nestedChartAngles t eta alpha y i)=
      polarPoint (nestedChartRadii t eta alpha y j) (nestedChartAngles t eta alpha y j)
    rw [hunit.1 i,hunit.1 j,h]
  refine ⟨hunit.1,hunit.2.1,hunit.2.2,hcf,hsep,?_⟩
  have hrows := (nestedChartExtendedRows_zero_iff_physical 0 t eta alpha y ht he hreg (hm.1 3).ne').mp hroot
  intro i
  have h := hrows.2 i
  have heq : nestedChartRadii t eta alpha y=fun _ => 1 := funext hunit.1
  rwa [heq,angularResidual_unit_eq_coorbital_of_separated _ _ hsep i] at h

end DominantFiveBody
