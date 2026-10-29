import DominantFiveBody.PairSmooth

/-! # Exact recovery of the normalized five-body equations from the pair chart -/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

theorem pairChartMass_positive (t p alpha : ℝ)
    (ht : 0<t) (ht1 : t<1) (hp : 0<p) (hp1 : p<1) (ha : 0<alpha) (ha1 : alpha<1) :
    PositiveRatio (pairChartMass t p alpha) := by
  have htc : 0<1-t^3 := sub_pos.mpr (pow_lt_one₀ ht.le ht1 (by decide))
  have hpc : 0<1-p := sub_pos.mpr hp1
  have hac : 0<1-alpha := sub_pos.mpr ha1
  refine ⟨?_,pairChartMass_sum t p alpha⟩
  intro i
  fin_cases i
  · change 0<t^3*alpha
    positivity
  · change 0<t^3*(1-alpha)
    positivity
  · change 0<(1-t^3)*p
    positivity
  · change 0<(1-t^3)*(1-p)
    positivity

theorem pairChartPoints_relativeCollisionFree (eps t alpha : ℝ) (y : PairChartVariables)
    (ht : 0<t) (hreg : PairChartRegular eps t alpha y) :
    RelativeCollisionFree (pairChartPoints t alpha y) := by
  have hab : pairChartPoints t alpha y 0≠pairChartPoints t alpha y 1 := by
    apply sub_ne_zero.mp
    apply norm_ne_zero_iff.mp
    change satelliteDistance (polarSatellites (pairChartRadii t alpha y)
      (pairChartAngles t alpha y)) 0 1≠0
    rw [pairChart_distance t alpha y ht hreg.2.2.1]
    exact mul_ne_zero (ne_of_gt ht) (ne_of_gt (Real.sqrt_pos.mpr hreg.2.2.1))
  constructor
  · intro i
    apply norm_ne_zero_iff.mp
    change ‖polarPoint (pairChartRadii t alpha y i) (pairChartAngles t alpha y i)‖≠0
    rw [polarPoint_norm]
    exact abs_ne_zero.mpr (hreg.2.1 i)
  · intro i j hij
    by_cases hi : i∈({2,3} : Finset Satellite)
    · exact hreg.2.2.2 i hi j hij
    by_cases hj : j∈({2,3} : Finset Satellite)
    · exact Ne.symm (hreg.2.2.2 j hj i hij.symm)
    have hi01 : i=0 ∨ i=1 := by fin_cases i <;> simp_all
    have hj01 : j=0 ∨ j=1 := by fin_cases j <;> simp_all
    rcases hi01 with rfl | rfl <;> rcases hj01 with rfl | rfl
    · exact (hij rfl).elim
    · exact hab
    · exact hab.symm
    · exact (hij rfl).elim

theorem pairChartExtendedRows_zero_iff_physical (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (ht : 0<t) (hreg : PairChartRegular eps t alpha y)
    (homit : pairChartMass t p alpha (if keepD then 2 else 3)≠0) :
    pairChartExtendedRows eps t p alpha keepD y=0 ↔
      (∀ i, radialResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
        (pairChartAngles t alpha y) i=0) ∧
      (∀ i, angularResidual eps (pairChartMass t p alpha) (pairChartRadii t alpha y)
        (pairChartAngles t alpha y) i=0) := by
  rw [pairChartExtendedRows_eq_physical eps t p alpha keepD y ht hreg.2.2.1 hreg.1
    (hreg.2.1 0) (hreg.2.1 1) (pairChartRegular_external_pair _ _ _ _ hreg)]
  exact pairChartPhysicalRows_zero_iff eps t p alpha keepD y (ne_of_gt ht) homit

/-- Positive physical scales recover the original centered multiplier-one
equations. All masses are checked positive before using the mass metric. -/
theorem pairChartExtendedRows_zero_iff_normalized (eps t p alpha : ℝ) (keepD : Bool)
    (y : PairChartVariables) (heps : 0<eps) (ht : 0<t)
    (hm : PositiveRatio (pairChartMass t p alpha))
    (hreg : PairChartRegular eps t alpha y) (hr : ∀ i, 0<pairChartRadii t alpha y i) :
    pairChartExtendedRows eps t p alpha keepD y=0 ↔
      NormalizedCentralConfiguration (masses eps (pairChartMass t p alpha))
        (centeredFromRelative eps (pairChartMass t p alpha) (pairChartPoints t alpha y)) := by
  rw [pairChartExtendedRows_zero_iff_physical eps t p alpha keepD y ht hreg
    (ne_of_gt (hm.1 (if keepD then 2 else 3)))]
  exact (polarResiduals_zero_iff_vectorRoot eps (pairChartMass t p alpha)
    (pairChartRadii t alpha y,pairChartAngles t alpha y) heps hm hr).trans
    (normalized_centeredFromRelative_iff_vectorRoot eps (pairChartMass t p alpha)
      (by linarith) hm (pairChartPoints t alpha y)
      (pairChartPoints_relativeCollisionFree eps t alpha y ht hreg)).symm

end DominantFiveBody
