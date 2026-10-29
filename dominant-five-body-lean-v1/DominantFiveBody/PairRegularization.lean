import DominantFiveBody.PairExterior

/-! # The complete seven-row signed-scale extension for a pair

The formula is joint in ε,t,p,α and all seven unknowns. Physical equality
uses t>0; zero scale is evaluated only in the explicit extension.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

def pairRadialMean (eps t p alpha : ℝ) (y : PairChartVariables) : ℝ :=
  alpha*pairRadialExterior eps t p alpha y 0+
    (1-alpha)*pairRadialExterior eps t p alpha y 1+pairInternalRadialMean eps t alpha y

def pairRadialDifference (eps t p alpha : ℝ) (y : PairChartVariables) : ℝ :=
  y 3*(1+(pairChartRadii t alpha y 0+pairChartRadii t alpha y 1)/
    (pairChartRadii t alpha y 0^2*pairChartRadii t alpha y 1^2))+
  eps*(inner ℝ (pairExteriorNewtonDifference t p alpha y)
      (polarPoint 1 (pairChartAngles t alpha y 1))+
    inner ℝ (pairExteriorRadialField eps t p alpha y (pairChartPoints t alpha y 0))
      (pairUnitDirection t alpha y))+
  pairInternalRadialDifference eps t alpha y

def pairAngularMean (eps t p alpha : ℝ) (y : PairChartVariables) : ℝ :=
  alpha*pairAngularExterior eps t p alpha y 0+
    (1-alpha)*pairAngularExterior eps t p alpha y 1

def pairAngularDifference (eps t p alpha : ℝ) (y : PairChartVariables) : ℝ :=
  inner ℝ (pairExteriorNewtonDifference t p alpha y) (quarterTurn (pairChartPoints t alpha y 1))+
    inner ℝ (pairExteriorAngularField eps t p alpha y (pairChartPoints t alpha y 0))
      (quarterTurn (pairPointDirection t alpha y))+
    pairInternalAngularDifference eps t alpha y

def pairChartExtendedRows (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) : PairChartVariables :=
  let R := radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)
  let T := angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)
  ![R 2,R 3,pairRadialMean eps t p alpha y,pairRadialDifference eps t p alpha y,
    T (if keepD then 3 else 2),pairAngularMean eps t p alpha y,pairAngularDifference eps t p alpha y]

theorem inner_difference_factor (A B e f D v : Plane) (t : ℝ)
    (hB : B-A=t • D) (hf : f-e=t • v) :
    inner ℝ B f-inner ℝ A e=t*(inner ℝ D f+inner ℝ A v) := by
  have hBeq : B=A+t • D := by rw [← hB]; abel
  have hfeq : f=e+t • v := by rw [← hf]; abel
  rw [hBeq,hfeq]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right]
  ring

theorem pair_radial_scalar_difference (t alpha : ℝ) (y : PairChartVariables)
    (ha : pairChartRadii t alpha y 0≠0) (hb : pairChartRadii t alpha y 1≠0) :
    (pairChartRadii t alpha y 1-(pairChartRadii t alpha y 1^2)⁻¹)-
      (pairChartRadii t alpha y 0-(pairChartRadii t alpha y 0^2)⁻¹)=
    t*(y 3*(1+(pairChartRadii t alpha y 0+pairChartRadii t alpha y 1)/
      (pairChartRadii t alpha y 0^2*pairChartRadii t alpha y 1^2))) := by
  calc
    _ = (pairChartRadii t alpha y 1-pairChartRadii t alpha y 0)*
        (1+(pairChartRadii t alpha y 0+pairChartRadii t alpha y 1)/
          (pairChartRadii t alpha y 0^2*pairChartRadii t alpha y 1^2)) := by
      field_simp
      ring
    _ = _ := by rw [pairChart_radius_gap]; ring

theorem pairRadialExterior_difference (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : t≠0) (ha : pairChartRadii t alpha y 0≠0) (hb : pairChartRadii t alpha y 1≠0)
    (hsep : ∀ i ∈ ({2,3} : Finset Satellite),
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 0 ∧
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 1) :
    pairRadialExterior eps t p alpha y 1-pairRadialExterior eps t p alpha y 0=
      t*(pairRadialDifference eps t p alpha y-pairInternalRadialDifference eps t alpha y) := by
  have hi := inner_difference_factor
    (pairExteriorRadialField eps t p alpha y (pairChartPoints t alpha y 0))
    (pairExteriorRadialField eps t p alpha y (pairChartPoints t alpha y 1))
    (polarPoint 1 (pairChartAngles t alpha y 0)) (polarPoint 1 (pairChartAngles t alpha y 1))
    (pairExteriorNewtonDifference t p alpha y) (pairUnitDirection t alpha y) t
    (pairExteriorRadialField_difference_identity eps t p alpha y ht hsep)
    (pairUnitDirection_identity t alpha y)
  have hg := pair_radial_scalar_difference t alpha y ha hb
  unfold pairRadialExterior pairRadialDifference
  linear_combination hg+eps*hi

theorem pairAngularExterior_difference (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : t≠0) (hsep : ∀ i ∈ ({2,3} : Finset Satellite),
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 0 ∧
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 1) :
    pairAngularExterior eps t p alpha y 1-pairAngularExterior eps t p alpha y 0=
      t*(pairAngularDifference eps t p alpha y-pairInternalAngularDifference eps t alpha y) := by
  have hq : quarterTurn (pairChartPoints t alpha y 1)-quarterTurn (pairChartPoints t alpha y 0)=
      t • quarterTurn (pairPointDirection t alpha y) := by
    have h := congrArg quarterTurnLinear (pairPointDirection_identity t alpha y)
    simpa only [map_sub,map_smul,quarterTurnLinear_apply,pairChartPoints,polarSatellites] using h
  have hi := inner_difference_factor
    (pairExteriorAngularField eps t p alpha y (pairChartPoints t alpha y 0))
    (pairExteriorAngularField eps t p alpha y (pairChartPoints t alpha y 1))
    (quarterTurn (pairChartPoints t alpha y 0)) (quarterTurn (pairChartPoints t alpha y 1))
    (pairExteriorNewtonDifference t p alpha y) (quarterTurn (pairPointDirection t alpha y)) t
    (pairExteriorAngularField_difference_identity eps t p alpha y ht hsep) hq
  unfold pairAngularExterior pairAngularDifference
  linear_combination hi

theorem pairRadialMean_eq_physical (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) :
    pairRadialMean eps t p alpha y=pairRowAverage alpha
      (radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)) := by
  unfold pairRowAverage pairRadialMean
  rw [pairRadialExteriorA_recovery eps t p alpha y ht hW,
    pairRadialExteriorB_recovery eps t p alpha y ht hW]
  have hi := pairInternalRadial_mean_identity eps t alpha y
  linear_combination -hi

theorem pairAngularMean_eq_physical (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) (heps : 1+eps≠0) :
    pairAngularMean eps t p alpha y=pairRowAverage alpha
      (angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)) := by
  unfold pairRowAverage pairAngularMean
  rw [pairAngularExteriorA_recovery eps t p alpha y ht hW heps,
    pairAngularExteriorB_recovery eps t p alpha y ht hW heps]
  have hi := pairInternalAngular_mean_identity eps t alpha y
  linear_combination -hi

theorem pairRadialDifference_eq_physical (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y)
    (ha : pairChartRadii t alpha y 0≠0) (hb : pairChartRadii t alpha y 1≠0)
    (hsep : ∀ i ∈ ({2,3} : Finset Satellite),
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 0 ∧
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 1) :
    pairRadialDifference eps t p alpha y=pairRowDifference t
      (radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)) := by
  unfold pairRowDifference
  rw [pairRadialExteriorA_recovery eps t p alpha y ht hW,
    pairRadialExteriorB_recovery eps t p alpha y ht hW]
  apply (eq_div_iff (ne_of_gt ht)).mpr
  have he := pairRadialExterior_difference eps t p alpha y (ne_of_gt ht) ha hb hsep
  have hi := pairInternalRadial_difference_identity eps t alpha y
  linear_combination -he-hi

theorem pairAngularDifference_eq_physical (eps t p alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hW : 0<pairChartWSq t alpha y) (heps : 1+eps≠0)
    (hsep : ∀ i ∈ ({2,3} : Finset Satellite),
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 0 ∧
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 1) :
    pairAngularDifference eps t p alpha y=pairRowDifference t
      (angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y) (pairChartAngles t alpha y)) := by
  unfold pairRowDifference
  rw [pairAngularExteriorA_recovery eps t p alpha y ht hW heps,
    pairAngularExteriorB_recovery eps t p alpha y ht hW heps]
  apply (eq_div_iff (ne_of_gt ht)).mpr
  have he := pairAngularExterior_difference eps t p alpha y (ne_of_gt ht) hsep
  have hi := pairInternalAngular_difference_identity eps t alpha y
  linear_combination -he-hi

/-- All seven rows equal the actual physical mean/difference equations.
No satellite mass fraction is canceled, and α may be an endpoint. -/
theorem pairChartExtendedRows_eq_physical (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (ht : 0<t) (hW : 0<pairChartWSq t alpha y)
    (heps : 1+eps≠0) (ha : pairChartRadii t alpha y 0≠0) (hb : pairChartRadii t alpha y 1≠0)
    (hsep : ∀ i ∈ ({2,3} : Finset Satellite),
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 0 ∧
      pairChartPoints t alpha y i≠pairChartPoints t alpha y 1) :
    pairChartExtendedRows eps t p alpha keepD y=pairChartPhysicalRows eps t p alpha keepD y := by
  unfold pairChartExtendedRows pairChartPhysicalRows
  rw [pairRadialMean_eq_physical eps t p alpha y ht hW,
    pairRadialDifference_eq_physical eps t p alpha y ht hW ha hb hsep,
    pairAngularMean_eq_physical eps t p alpha y ht hW heps,
    pairAngularDifference_eq_physical eps t p alpha y ht hW heps hsep]

end DominantFiveBody
