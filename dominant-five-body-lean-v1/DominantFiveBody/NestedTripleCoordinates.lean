import DominantFiveBody.NestedAreas
import DominantFiveBody.TripleBoundary

/-! # Exact nested-to-regular triple coordinate and row transformations

For eta nonzero the same actual points are described by successive
regular gaps (eta u2, u1-alpha eta u2). This bridge retains the endpoint
weights; invertibility divides only by eta, never by an individual weight.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 1000000

def nestedTripleWeights (eta alpha : ℝ) : TripleVector :=
  ![eta^3*alpha,eta^3*(1-alpha),1-eta^3]

def nestedToTripleVariables (eta alpha : ℝ) (y : NestedChartVariables) : TripleChartVariables :=
  ![y 0,y 1,eta*y 3,y 2-alpha*eta*y 3,y 4,eta*y 6,y 5-alpha*eta*y 6]

theorem nestedTripleWeights_sum (eta alpha : ℝ) : ∑ i,nestedTripleWeights eta alpha i=1 := by
  simp [nestedTripleWeights,Fin.sum_univ_three]
  ring

theorem nestedToTripleVariables_injective (eta alpha : ℝ) (he : eta≠0) :
    Function.Injective (nestedToTripleVariables eta alpha) := by
  intro y z hyz
  have h (i : Fin 7) := congrFun hyz i
  have h3 : y 3=z 3 := mul_left_cancel₀ he (h 2)
  have h6 : y 6=z 6 := mul_left_cancel₀ he (h 5)
  ext i
  fin_cases i
  · exact h 0
  · exact h 1
  · have hh := h 3; change y 2-alpha*eta*y 3=z 2-alpha*eta*z 3 at hh; rw [h3] at hh; change y 2=z 2; linarith only [hh]
  · exact h3
  · exact h 4
  · have hh := h 6; change y 5-alpha*eta*y 6=z 5-alpha*eta*z 6 at hh; rw [h6] at hh; change y 5=z 5; linarith only [hh]
  · exact h6

@[simp] theorem nestedToTripleVariables_zero (eta alpha : ℝ) :
    nestedToTripleVariables eta alpha 0=0 := by
  ext i
  fin_cases i <;> simp [nestedToTripleVariables]

theorem nestedToTripleVariables_contDiff (n : ℕ∞ω) (eta alpha : ℝ) :
    ContDiff ℝ n (nestedToTripleVariables eta alpha) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [nestedToTripleVariables] <;> fun_prop

theorem nestedToTriple_radialPositions (eta alpha : ℝ) (y : NestedChartVariables) :
    tripleChartRadialPositions (nestedTripleWeights eta alpha) (nestedToTripleVariables eta alpha y)=
      nestedCoordinates 1 eta alpha 0 (y 2) (y 3) := by
  ext i
  fin_cases i
  all_goals simp [tripleChartRadialPositions,tripleChartRadialGaps,tripleCenteringMatrix,
    nestedToTripleVariables,nestedTripleWeights,nestedCoordinates,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  all_goals ring

theorem nestedToTriple_angularPositions (eta alpha : ℝ) (y : NestedChartVariables) :
    tripleChartAngularPositions (nestedTripleWeights eta alpha) (nestedToTripleVariables eta alpha y)=
      nestedCoordinates 1 eta alpha 0 (y 5) (y 6) := by
  ext i
  fin_cases i
  all_goals simp [tripleChartAngularPositions,tripleChartAngularGaps,tripleCenteringMatrix,
    nestedToTripleVariables,nestedTripleWeights,nestedCoordinates,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  all_goals ring

theorem nestedToTriple_radii (t eta alpha : ℝ) (y : NestedChartVariables) :
    tripleChartRadii t (nestedTripleWeights eta alpha) (nestedToTripleVariables eta alpha y)=
      nestedChartRadii t eta alpha y := by
  ext i
  fin_cases i
  all_goals simp only [tripleChartRadii,nestedToTriple_radialPositions]
  all_goals dsimp [nestedToTripleVariables,nestedChartRadii,nestedCoordinates]
  all_goals ring

theorem nestedToTriple_angles (t eta alpha : ℝ) (y : NestedChartVariables) :
    tripleChartAngles t (nestedTripleWeights eta alpha) (nestedToTripleVariables eta alpha y)=
      nestedChartAngles t eta alpha y := by
  ext i
  fin_cases i
  all_goals simp only [tripleChartAngles,nestedToTriple_angularPositions]
  all_goals dsimp [nestedToTripleVariables,nestedChartAngles,nestedCoordinates]
  all_goals ring

theorem nestedToTriple_points (t eta alpha : ℝ) (y : NestedChartVariables) :
    tripleChartPoints t (nestedTripleWeights eta alpha) (nestedToTripleVariables eta alpha y)=
      nestedChartPoints t eta alpha y := by
  simp only [tripleChartPoints,nestedChartPoints,nestedToTriple_radii,nestedToTriple_angles]

theorem nestedToTriple_mass (t eta alpha : ℝ) :
    tripleChartMass t (nestedTripleWeights eta alpha)=nestedChartMass t eta alpha := by
  ext i
  fin_cases i <;> simp [tripleChartMass,nestedTripleWeights,nestedChartMass,mul_assoc]

theorem nestedToTriple_physicalRows (eps t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : t≠0) (he : eta≠0) :
    tripleChartPhysicalRows eps t (nestedTripleWeights eta alpha) (nestedToTripleVariables eta alpha y)=
      nestedToTripleVariables eta alpha (nestedChartPhysicalRows eps t eta alpha y) := by
  simp only [tripleChartPhysicalRows,nestedToTriple_mass,nestedToTriple_radii,nestedToTriple_angles]
  ext i
  fin_cases i
  all_goals dsimp [nestedChartPhysicalRows,nestedToTripleVariables,tripleRowAverage,
    tripleRowDifferences,tripleClusterRows,nestedRowAverage,nestedPairAverage,
    nestedRowInnerDifference,nestedRowOuterDifference,nestedTripleWeights,
    tripleGapMatrix,Matrix.mulVec,dotProduct]
  all_goals simp only [Fin.sum_univ_three]
  all_goals dsimp
  all_goals field_simp
  all_goals ring

theorem nestedToTriple_regular_zero (eps eta alpha : ℝ) (y : NestedChartVariables)
    (he : eta≠0) (hreg : NestedChartRegular eps 0 eta alpha y) :
    TripleChartRegular eps 0 (nestedTripleWeights eta alpha) (nestedToTripleVariables eta alpha y) := by
  refine ⟨hreg.1,?_,?_,?_⟩
  · simpa only [nestedToTriple_radii] using hreg.2.1
  · have hW : 0<y 3^2+y 1^2*y 6^2 := by
      simpa [nestedInnerWSq_formula,nestedChartRadii,nestedCoordinates,pow_two] using hreg.2.2.1
    have hV (i : Fin 2) : 0<nestedOuterRadialGaps eta alpha y i^2+
        y 1^2*nestedOuterAngularGaps eta alpha y i^2 := by
      have hh := hreg.2.2.2.1 i
      rw [nestedOuterWSq_formula] at hh
      fin_cases i <;> simpa [nestedChartRadii,nestedCoordinates,pow_two] using hh
    intro i j hij
    rw [tripleChartWSq_at_zero,nestedToTriple_radialPositions,nestedToTriple_angularPositions]
    have hin : 0<eta^2*(y 3^2+y 1^2*y 6^2) := mul_pos (sq_pos_of_ne_zero he) hW
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    all_goals dsimp [nestedCoordinates,nestedToTripleVariables]
    · nlinarith only [hin]
    · convert hV 0 using 1
      dsimp [nestedOuterRadialGaps,nestedOuterAngularGaps]
      ring
    · nlinarith only [hin]
    · convert hV 1 using 1
      dsimp [nestedOuterRadialGaps,nestedOuterAngularGaps]
      ring
    · convert hV 0 using 1
      dsimp [nestedOuterRadialGaps,nestedOuterAngularGaps]
      ring
    · convert hV 1 using 1
      dsimp [nestedOuterRadialGaps,nestedOuterAngularGaps]
      ring
  · simpa only [nestedToTriple_points] using hreg.2.2.2.2

end DominantFiveBody
