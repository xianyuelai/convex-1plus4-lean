import DominantFiveBody.TripleSmooth

/-! # Exact physical equation recovery for the regular triple

The omitted exterior angular row is recovered only after its mass is
proved nonzero. Cluster row recovery cancels no individual weight.
-/

noncomputable section
open scoped BigOperators Matrix

namespace DominantFiveBody

theorem tripleChartMass_positive (t : ℝ) (alpha : TripleVector)
    (ht : 0 < t) (ht1 : t < 1) (ha : ∀ i, 0 < alpha i) (hasum : ∑ i, alpha i = 1) :
    PositiveRatio (tripleChartMass t alpha) := by
  have htc : 0 < 1 - t ^ 3 := sub_pos.mpr (pow_lt_one₀ ht.le ht1 (by decide))
  refine ⟨?_, tripleChartMass_sum t alpha hasum⟩
  intro i
  fin_cases i
  · exact mul_pos (pow_pos ht 3) (ha 0)
  · exact mul_pos (pow_pos ht 3) (ha 1)
  · exact mul_pos (pow_pos ht 3) (ha 2)
  · exact htc

theorem tripleChartPhysicalRows_zero_iff (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : t ≠ 0) (ha : ∑ i, alpha i = 1)
    (homit : tripleChartMass t alpha 3 ≠ 0) :
    tripleChartPhysicalRows eps t alpha y = 0 ↔
      (∀ i, radialResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
        (tripleChartAngles t alpha y) i = 0) ∧
      (∀ i, angularResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
        (tripleChartAngles t alpha y) i = 0) := by
  let R := radialResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y) (tripleChartAngles t alpha y)
  let T := angularResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y) (tripleChartAngles t alpha y)
  change tripleChartPhysicalRows eps t alpha y = 0 ↔ (∀ i, R i = 0) ∧ ∀ i, T i = 0
  constructor
  · intro h
    have hRp : R 3 = 0 := congrFun h 0
    have hRA : tripleRowAverage alpha R = 0 := congrFun h 1
    have hRB : tripleRowDifferences t R = 0 := by
      ext i
      fin_cases i
      · exact congrFun h 2
      · exact congrFun h 3
    have hTA : tripleRowAverage alpha T = 0 := congrFun h 4
    have hTB : tripleRowDifferences t T = 0 := by
      ext i
      fin_cases i
      · exact congrFun h 5
      · exact congrFun h 6
    have hRc := (tripleRows_zero_iff t alpha R ht ha).mp ⟨hRA, hRB⟩
    have hTc := (tripleRows_zero_iff t alpha T ht ha).mp ⟨hTA, hTB⟩
    have hTother : ∀ i, i ≠ 3 → T i = 0 := by
      intro i hi
      fin_cases i
      · exact congrFun hTc 0
      · exact congrFun hTc 1
      · exact congrFun hTc 2
      · exact False.elim (hi rfl)
    have hTp : T 3 = 0 := angularResidual_omitted_row eps (tripleChartMass t alpha)
      (tripleChartRadii t alpha y) (tripleChartAngles t alpha y) 3 homit hTother
    constructor
    · intro i
      fin_cases i
      · exact congrFun hRc 0
      · exact congrFun hRc 1
      · exact congrFun hRc 2
      · exact hRp
    · intro i
      by_cases hi : i = 3
      · simpa only [hi] using hTp
      · exact hTother i hi
  · rintro ⟨hR, hT⟩
    have hRc : R = 0 := funext hR
    have hTc : T = 0 := funext hT
    unfold tripleChartPhysicalRows
    change ![R 3, tripleRowAverage alpha R, tripleRowDifferences t R 0,
      tripleRowDifferences t R 1, tripleRowAverage alpha T, tripleRowDifferences t T 0,
      tripleRowDifferences t T 1] = 0
    rw [hRc, hTc]
    have hz : tripleClusterRows (0 : Satellite → ℝ) = 0 := rfl
    ext i
    fin_cases i <;> simp [tripleRowAverage, tripleRowDifferences, hz, tripleClusterRows]

theorem tripleChartPoints_relativeCollisionFree (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : 0 < t) (hreg : TripleChartRegular eps t alpha y) :
    RelativeCollisionFree (tripleChartPoints t alpha y) := by
  have hcluster (i j : TripleLabel) (hij : i ≠ j) :
      tripleChartPoints t alpha y i.castSucc ≠ tripleChartPoints t alpha y j.castSucc := by
    apply sub_ne_zero.mp
    apply norm_ne_zero_iff.mp
    change satelliteDistance (tripleChartPoints t alpha y) i.castSucc j.castSucc ≠ 0
    rw [tripleChart_cluster_distance t alpha y i j ht (hreg.2.2.1 i j hij)]
    exact mul_ne_zero ht.ne' (ne_of_gt (Real.sqrt_pos.mpr (hreg.2.2.1 i j hij)))
  constructor
  · intro i
    apply norm_ne_zero_iff.mp
    change ‖polarPoint (tripleChartRadii t alpha y i) (tripleChartAngles t alpha y i)‖ ≠ 0
    rw [polarPoint_norm]
    exact abs_ne_zero.mpr (hreg.2.1 i)
  · intro i j hij
    by_cases hi3 : i = 3
    · subst i
      exact tripleChartRegular_exterior_distinct eps t alpha y hreg j hij.symm
    by_cases hj3 : j = 3
    · subst j
      exact (tripleChartRegular_exterior_distinct eps t alpha y hreg i hij).symm
    have hi' : i.val ≠ 3 := fun h => hi3 (Fin.ext h)
    have hj' : j.val ≠ 3 := fun h => hj3 (Fin.ext h)
    have hi : i.val < 3 := by have hi4 := i.isLt; omega
    have hj : j.val < 3 := by have hj4 := j.isLt; omega
    let a : TripleLabel := ⟨i.val, hi⟩
    let b : TripleLabel := ⟨j.val, hj⟩
    have hai : a.castSucc = i := Fin.ext rfl
    have hbj : b.castSucc = j := Fin.ext rfl
    have hab : a ≠ b := by intro h; apply hij; rw [← hai, ← hbj, h]
    rw [← hai, ← hbj]
    exact hcluster a b hab

theorem tripleChartExtendedRows_zero_iff_physical (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ht : 0 < t) (ha : ∑ i, alpha i = 1)
    (hreg : TripleChartRegular eps t alpha y) (homit : tripleChartMass t alpha 3 ≠ 0) :
    tripleChartExtendedRows eps t alpha y = 0 ↔
      (∀ i, radialResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
        (tripleChartAngles t alpha y) i = 0) ∧
      (∀ i, angularResidual eps (tripleChartMass t alpha) (tripleChartRadii t alpha y)
        (tripleChartAngles t alpha y) i = 0) := by
  rw [tripleChartExtendedRows_eq_physical eps t alpha y ht hreg.1 hreg.2.2.1
    (fun i => hreg.2.1 i.castSucc) hreg.2.2.2]
  exact tripleChartPhysicalRows_zero_iff eps t alpha y ht.ne' ha homit

theorem tripleChartExtendedRows_zero_iff_normalized (eps t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (heps : 0 < eps) (ht : 0 < t)
    (ha : ∑ i, alpha i = 1) (hm : PositiveRatio (tripleChartMass t alpha))
    (hreg : TripleChartRegular eps t alpha y) (hr : ∀ i, 0 < tripleChartRadii t alpha y i) :
    tripleChartExtendedRows eps t alpha y = 0 ↔
      NormalizedCentralConfiguration (masses eps (tripleChartMass t alpha))
        (centeredFromRelative eps (tripleChartMass t alpha) (tripleChartPoints t alpha y)) := by
  rw [tripleChartExtendedRows_zero_iff_physical eps t alpha y ht ha hreg (ne_of_gt (hm.1 3))]
  exact (polarResiduals_zero_iff_vectorRoot eps (tripleChartMass t alpha)
    (tripleChartRadii t alpha y, tripleChartAngles t alpha y) heps hm hr).trans
    (normalized_centeredFromRelative_iff_vectorRoot eps (tripleChartMass t alpha)
      (by linarith) hm (tripleChartPoints t alpha y)
      (tripleChartPoints_relativeCollisionFree eps t alpha y ht hreg)).symm

end DominantFiveBody
