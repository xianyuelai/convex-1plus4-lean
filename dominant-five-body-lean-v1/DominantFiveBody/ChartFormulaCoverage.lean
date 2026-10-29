import DominantFiveBody.Main

/-! Explicit multi-formula statements for the Section 5--6 source ledger. -/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Set

namespace DominantFiveBody

theorem pairChart_coordinates_complete (t p alpha : ℝ) (y : PairChartVariables) :
    pairChartMass t p alpha =
      ![t ^ 3 * alpha, t ^ 3 * (1 - alpha), (1 - t ^ 3) * p, (1 - t ^ 3) * (1 - p)] ∧
    pairChartRadii t alpha y =
      ![y 2 - (1 - alpha) * t * y 3, y 2 + alpha * t * y 3, y 0, y 1] ∧
    pairChartAngles t alpha y =
      ![y 5 - (1 - alpha) * t * y 6, y 5 + alpha * t * y 6, 0, y 4] :=
  ⟨rfl, rfl, rfl⟩

theorem tripleChart_coordinates_complete (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    tripleChartMass t alpha = ![t ^ 3 * alpha 0, t ^ 3 * alpha 1,
      t ^ 3 * alpha 2, 1 - t ^ 3] ∧
    tripleChartRadialPositions alpha y = tripleCenteringMatrix alpha *ᵥ ![y 2, y 3] ∧
    tripleChartAngularPositions alpha y = tripleCenteringMatrix alpha *ᵥ ![y 5, y 6] ∧
    tripleChartRadii t alpha y = ![y 1 + t * tripleChartRadialPositions alpha y 0,
      y 1 + t * tripleChartRadialPositions alpha y 1,
      y 1 + t * tripleChartRadialPositions alpha y 2, y 0] ∧
    tripleChartAngles t alpha y = ![y 4 + t * tripleChartAngularPositions alpha y 0,
      y 4 + t * tripleChartAngularPositions alpha y 1,
      y 4 + t * tripleChartAngularPositions alpha y 2, 0] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nestedChart_coordinates_complete (t eta alpha : ℝ) (y : NestedChartVariables) :
    nestedChartMass t eta alpha = ![t ^ 3 * eta ^ 3 * alpha,
      t ^ 3 * eta ^ 3 * (1 - alpha), t ^ 3 * (1 - eta ^ 3), 1 - t ^ 3] ∧
    nestedCoordinates t eta alpha (y 1) (y 2) (y 3) =
      ![y 1 - (1 - eta ^ 3) * t * y 2 - (1 - alpha) * t * eta * y 3,
        y 1 - (1 - eta ^ 3) * t * y 2 + alpha * t * eta * y 3,
        y 1 + eta ^ 3 * t * y 2] ∧
    nestedCoordinates t eta alpha (y 4) (y 5) (y 6) =
      ![y 4 - (1 - eta ^ 3) * t * y 5 - (1 - alpha) * t * eta * y 6,
        y 4 - (1 - eta ^ 3) * t * y 5 + alpha * t * eta * y 6,
        y 4 + eta ^ 3 * t * y 5] ∧
    nestedChartRadii t eta alpha y =
      Fin.append (nestedCoordinates t eta alpha (y 1) (y 2) (y 3)) (fun _ : Fin 1 => y 0) ∧
    nestedChartAngles t eta alpha y =
      Fin.append (nestedCoordinates t eta alpha (y 4) (y 5) (y 6)) (fun _ : Fin 1 => 0) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  all_goals funext i
  all_goals fin_cases i <;> rfl

theorem tripleScalar_matrices_complete (alpha : TripleVector) (ha : ∑ i, alpha i = 1) :
    tripleGapMatrix = !![-1, 1, 0; 0, -1, 1] ∧
    tripleCenteringMatrix alpha = !![-(alpha 1 + alpha 2), -alpha 2;
      alpha 0, -alpha 2; alpha 0, alpha 0 + alpha 1] ∧
    tripleGapMatrix * tripleCenteringMatrix alpha = 1 ∧
    (∀ v : TripleGaps, ∑ i, alpha i * (tripleCenteringMatrix alpha *ᵥ v) i = 0) :=
  ⟨rfl, rfl, tripleGapMatrix_centeringMatrix alpha ha,
    tripleCenteringMatrix_weighted_center alpha⟩

theorem tripleScalar_J_entries_complete (alpha z : TripleVector) :
    (∀ i, tripleScalarJacobian alpha z i i =
      tripleD0 + 2 * ∑ j ∈ Finset.univ.erase i, alpha j / |z i - z j| ^ 3) ∧
    (∀ i j, i ≠ j → tripleScalarJacobian alpha z i j = -2 * alpha j / |z i - z j| ^ 3) := by
  constructor
  · intro i
    simp [tripleScalarJacobian]
  · intro i j hij
    simp [tripleScalarJacobian, hij]

theorem circle_areas_complete (A B C : ℝ) (hAB : A < B) (hBC : B < C)
    (hspan : C < A + Real.pi) :
    det2 (polarPoint 1 B - polarPoint 1 A) (polarPoint 1 C - polarPoint 1 A) =
      4 * Real.sin ((B - A) / 2) * Real.sin ((C - B) / 2) * Real.sin ((C - A) / 2) ∧
    0 < det2 (polarPoint 1 B - polarPoint 1 A) (polarPoint 1 C - polarPoint 1 A) ∧
    det2 (polarPoint 1 A) (polarPoint 1 B) = Real.sin (B - A) ∧
    0 < det2 (polarPoint 1 A) (polarPoint 1 B) := by
  have hproduct : det2 (polarPoint 1 B - polarPoint 1 A)
      (polarPoint 1 C - polarPoint 1 A) =
      4 * Real.sin ((B - A) / 2) * Real.sin ((C - B) / 2) *
        Real.sin ((C - A) / 2) := by
    rw [unit_polar_triangle_det, Real.sin_add_sin]
    rw [show ((B - A) + (C - B)) / 2 = (C - A) / 2 by ring]
    rw [show C - A = 2 * ((C - A) / 2) by ring, Real.sin_two_mul]
    have hc : Real.cos (((B - A) - (C - B)) / 2) - Real.cos ((C - A) / 2) =
        2 * Real.sin ((B - A) / 2) * Real.sin ((C - B) / 2) := by
      rw [Real.cos_sub_cos]
      rw [show ((((B - A) - (C - B)) / 2 + (C - A) / 2) / 2) =
        (B - A) / 2 by ring]
      rw [show ((((B - A) - (C - B)) / 2 - (C - A) / 2) / 2) =
        -((C - B) / 2) by ring, Real.sin_neg]
      ring
    rw [show 2 * ((C - A) / 2) / 2 = (C - A) / 2 by ring]
    calc
      _ = 2 * Real.sin ((C - A) / 2) *
          (Real.cos (((B - A) - (C - B)) / 2) - Real.cos ((C - A) / 2)) := by ring
      _ = _ := by rw [hc]; ring
  refine ⟨hproduct, unit_polar_triangle_det_pos A B C
      (sub_pos.mpr hAB) (sub_pos.mpr hBC) (by linarith),
    unit_polar_det A B, ?_⟩
  rw [unit_polar_det]
  exact Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hAB) (by linarith)

theorem pair_areas_boundary_complete (alpha omega psi z : ℝ)
    (hz : 0 < z) (hpsi0 : psi ≠ 0) (hpsiw : psi ≠ omega)
    (hpi0 : |psi| < Real.pi) (hpiw : |psi - omega| < Real.pi) :
    pairAreaQuotient 0 alpha (pairUnitPoint omega psi z) 0 = z ∧
    pairAreaQuotient 0 alpha (pairUnitPoint omega psi z) 3 = z * (1 - Real.cos psi) ∧
    pairAreaQuotient 0 alpha (pairUnitPoint omega psi z) 4 = z * (1 - Real.cos (omega - psi)) ∧
    (∀ j ∈ ({0, 3, 4} : Finset Label),
      0 < pairAreaQuotient 0 alpha (pairUnitPoint omega psi z) j) :=
  ⟨pairAreaQuotient_primary_boundary alpha omega psi z,
    pairAreaQuotient_c_boundary alpha omega psi z,
    pairAreaQuotient_d_boundary alpha omega psi z,
    pairAreaQuotient_boundary_positive alpha omega psi z hz hpsi0 hpsiw hpi0 hpiw⟩

theorem nestedCircle_coefficient_complete (alpha Z z : ℝ) (hZ : Z ≠ 0) (hz : 0 < z) :
    nestedCircleAreaCoefficient 0 0 alpha Z z = z * Z ^ 2 / 2 ∧
      0 < nestedCircleAreaCoefficient 0 0 alpha Z z :=
  ⟨nestedCircleAreaCoefficient_base alpha Z z,
    nestedCircleAreaCoefficient_base_pos alpha Z z hZ hz⟩

end DominantFiveBody
