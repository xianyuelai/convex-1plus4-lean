import DominantFiveBody.PairZeroEndpoint

/-! # Recovering pair-chart parameters from the original physical variables -/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

def pairVariablesFromPolar (t alpha : ℝ) (r theta : Satellite → ℝ) : PairChartVariables :=
  ![r 2,r 3,alpha*r 0+(1-alpha)*r 1,(r 1-r 0)/t,theta 3,
    alpha*theta 0+(1-alpha)*theta 1,(theta 1-theta 0)/t]

theorem pairVariablesFromPolar_radii (t alpha : ℝ) (r theta : Satellite → ℝ) (ht : t≠0) :
    pairChartRadii t alpha (pairVariablesFromPolar t alpha r theta)=r := by
  funext i
  fin_cases i
  · change (alpha*r 0+(1-alpha)*r 1)-(1-alpha)*t*((r 1-r 0)/t)=r 0
    field_simp
    ring
  · change (alpha*r 0+(1-alpha)*r 1)+alpha*t*((r 1-r 0)/t)=r 1
    field_simp
    ring
  · rfl
  · rfl

theorem pairVariablesFromPolar_angles (t alpha : ℝ) (r theta : Satellite → ℝ)
    (ht : t≠0) (hfixed : theta 2=0) :
    pairChartAngles t alpha (pairVariablesFromPolar t alpha r theta)=theta := by
  funext i
  fin_cases i
  · change (alpha*theta 0+(1-alpha)*theta 1)-(1-alpha)*t*((theta 1-theta 0)/t)=theta 0
    field_simp
    ring
  · change (alpha*theta 0+(1-alpha)*theta 1)+alpha*t*((theta 1-theta 0)/t)=theta 1
    field_simp
    ring
  · exact hfixed.symm
  · rfl

theorem pairVariablesFromPolar_points (t alpha : ℝ) (r theta : Satellite → ℝ)
    (ht : t≠0) (hfixed : theta 2=0) :
    pairChartPoints t alpha (pairVariablesFromPolar t alpha r theta)=polarSatellites r theta := by
  unfold pairChartPoints
  rw [pairVariablesFromPolar_radii _ _ _ _ ht,pairVariablesFromPolar_angles _ _ _ _ ht hfixed]

def pairPhysicalScale (mu : MassRatio) : ℝ := (mu 0+mu 1)^((1 : ℝ)/3)
def pairPhysicalFraction (mu : MassRatio) : ℝ := mu 0/(mu 0+mu 1)
def pairExteriorFraction (mu : MassRatio) : ℝ := mu 2/(mu 2+mu 3)

theorem pairPhysicalScale_cube (mu : MassRatio) (hm : PositiveRatio mu) :
    pairPhysicalScale mu^3=mu 0+mu 1 := by
  unfold pairPhysicalScale
  rw [←Real.rpow_mul_natCast (add_pos (hm.1 0) (hm.1 1)).le]
  norm_num

theorem pairPhysicalParameters_bounds (mu : MassRatio) (hm : PositiveRatio mu) :
    0<pairPhysicalScale mu ∧ pairPhysicalScale mu<1 ∧
      0<pairPhysicalFraction mu ∧ pairPhysicalFraction mu<1 ∧
      0<pairExteriorFraction mu ∧ pairExteriorFraction mu<1 := by
  have hnu : 0<mu 0+mu 1 := add_pos (hm.1 0) (hm.1 1)
  have hsigma : 0<mu 2+mu 3 := add_pos (hm.1 2) (hm.1 3)
  have hsum : mu 0+mu 1+mu 2+mu 3=1 := by simpa only [Fin.sum_univ_four] using hm.2
  have ht : 0<pairPhysicalScale mu := Real.rpow_pos_of_pos hnu _
  have htc : pairPhysicalScale mu^3=mu 0+mu 1 := pairPhysicalScale_cube mu hm
  have ht1 : pairPhysicalScale mu<1 := by
    by_contra hn
    have hle := le_of_not_gt hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sq_nonneg (pairPhysicalScale mu))]
  exact ⟨ht,ht1,div_pos (hm.1 0) hnu,(div_lt_one hnu).mpr (by linarith [hm.1 1]),
    div_pos (hm.1 2) hsigma,(div_lt_one hsigma).mpr (by linarith [hm.1 3])⟩

theorem pairPhysicalParameters_mass (mu : MassRatio) (hm : PositiveRatio mu) :
    pairChartMass (pairPhysicalScale mu) (pairExteriorFraction mu) (pairPhysicalFraction mu)=mu := by
  have hnu : mu 0+mu 1≠0 := ne_of_gt (add_pos (hm.1 0) (hm.1 1))
  have hsigma : mu 2+mu 3≠0 := ne_of_gt (add_pos (hm.1 2) (hm.1 3))
  have hsum : mu 0+mu 1+mu 2+mu 3=1 := by simpa only [Fin.sum_univ_four] using hm.2
  unfold pairChartMass
  rw [pairPhysicalScale_cube mu hm]
  have hext : 1-(mu 0+mu 1)=mu 2+mu 3 := by linarith
  rw [hext]
  funext i
  fin_cases i
  · change (mu 0+mu 1)*(mu 0/(mu 0+mu 1))=mu 0
    field_simp
  · change (mu 0+mu 1)*(1-mu 0/(mu 0+mu 1))=mu 1
    field_simp
    ring
  · change (mu 2+mu 3)*(mu 2/(mu 2+mu 3))=mu 2
    field_simp
  · change (mu 2+mu 3)*(1-mu 2/(mu 2+mu 3))=mu 3
    field_simp
    ring

/-- Exact inversion of the mass and polar coordinates for every positive
mass vector in the fixed c-angle gauge.  No lower fraction bound is used. -/
theorem pairPhysicalCoordinates_recover (mu : MassRatio) (hm : PositiveRatio mu)
    (r theta : Satellite → ℝ) (hfixed : theta 2=0) :
    let t := pairPhysicalScale mu
    let alpha := pairPhysicalFraction mu
    let p := pairExteriorFraction mu
    let y := pairVariablesFromPolar t alpha r theta
    pairChartMass t p alpha=mu ∧ pairChartRadii t alpha y=r ∧
      pairChartAngles t alpha y=theta ∧ pairChartPoints t alpha y=polarSatellites r theta := by
  have ht := (pairPhysicalParameters_bounds mu hm).1.ne'
  exact ⟨pairPhysicalParameters_mass mu hm,pairVariablesFromPolar_radii _ _ _ _ ht,
    pairVariablesFromPolar_angles _ _ _ _ ht hfixed,pairVariablesFromPolar_points _ _ _ _ ht hfixed⟩

theorem pairVariablesFromPolar_regular (eps t alpha : ℝ) (r theta : Satellite → ℝ)
    (heps : 1+eps≠0) (ht : 0<t) (hr : ∀ i, 0<r i) (hfixed : theta 2=0)
    (hcf : RelativeCollisionFree (polarSatellites r theta)) :
    PairChartRegular eps t alpha (pairVariablesFromPolar t alpha r theta) := by
  let y := pairVariablesFromPolar t alpha r theta
  have hradii := pairVariablesFromPolar_radii t alpha r theta ht.ne'
  have hpoints := pairVariablesFromPolar_points t alpha r theta ht.ne' hfixed
  refine ⟨heps,?_,?_,?_⟩
  · intro i
    rw [hradii]
    exact (hr i).ne'
  · have hd : 0<satelliteDistance (pairChartPoints t alpha y) 0 1 := by
      rw [hpoints]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (hcf.2 0 1 (by decide)))
    have he := pairChart_distance_sq t alpha y
    change satelliteDistance (pairChartPoints t alpha y) 0 1^2=t^2*pairChartWSq t alpha y at he
    have hmul : 0<t^2*pairChartWSq t alpha y := by rw [←he]; positivity
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos ht)).mp hmul
  · intro i _ j hij
    rw [hpoints]
    exact hcf.2 i j hij

/-- A real normalized physical solution, expressed in the actual inverse
coordinates, is a zero of the extended chart.  No chart membership or
regularity assumption is taken from a capture interface. -/
theorem pairPhysicalCoordinates_root (eps : ℝ) (mu : MassRatio) (heps : 0<eps)
    (hm : PositiveRatio mu) (r theta : Satellite → ℝ) (hr : ∀ i, 0<r i)
    (hfixed : theta 2=0) (hcf : RelativeCollisionFree (polarSatellites r theta))
    (hx : NormalizedCentralConfiguration (masses eps mu)
      (centeredFromRelative eps mu (polarSatellites r theta))) (keepD : Bool) :
    pairChartExtendedRows eps (pairPhysicalScale mu) (pairExteriorFraction mu) (pairPhysicalFraction mu)
      keepD (pairVariablesFromPolar (pairPhysicalScale mu) (pairPhysicalFraction mu) r theta)=0 := by
  obtain ⟨hmass,hradii,_,hpoints⟩ := pairPhysicalCoordinates_recover mu hm r theta hfixed
  have ht := (pairPhysicalParameters_bounds mu hm).1
  have hreg := pairVariablesFromPolar_regular eps (pairPhysicalScale mu) (pairPhysicalFraction mu)
    r theta (by linarith) ht hr hfixed hcf
  apply (pairChartExtendedRows_zero_iff_normalized _ _ _ _ keepD _ heps ht
    (by rwa [hmass]) hreg (by intro i; rw [hradii]; exact hr i)).mpr
  simpa only [hmass,hpoints] using hx

end DominantFiveBody
