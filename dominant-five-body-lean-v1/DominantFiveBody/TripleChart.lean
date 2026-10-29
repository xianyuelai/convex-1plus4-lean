import DominantFiveBody.TripleScalarSeed
import DominantFiveBody.SingleScaleKernel
import DominantFiveBody.ResidualEquivalence

/-! # The actual regular three-cluster chart

Source §5.3. Cluster labels 0,1,2 are the paper's 1,2,3;
the exterior satellite p has label 3. Unknowns are exactly
`(r,R,u₁,u₂,ψ,v₁,v₂)`. All three divided cluster rows are retained.
-/

noncomputable section
open scoped BigOperators Matrix

namespace DominantFiveBody
set_option maxHeartbeats 800000

abbrev TripleChartVariables := Fin 7 → ℝ

def tripleChartRadialGaps (y : TripleChartVariables) : TripleGaps := ![y 2, y 3]
def tripleChartAngularGaps (y : TripleChartVariables) : TripleGaps := ![y 5, y 6]

def tripleChartRadialPositions (alpha : TripleVector) (y : TripleChartVariables) : TripleVector :=
  tripleCenteringMatrix alpha *ᵥ tripleChartRadialGaps y
def tripleChartAngularPositions (alpha : TripleVector) (y : TripleChartVariables) : TripleVector :=
  tripleCenteringMatrix alpha *ᵥ tripleChartAngularGaps y

def tripleChartMass (t : ℝ) (alpha : TripleVector) : MassRatio :=
  ![t ^ 3 * alpha 0, t ^ 3 * alpha 1, t ^ 3 * alpha 2, 1 - t ^ 3]

def tripleChartRadii (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) : Satellite → ℝ :=
  ![y 1 + t * tripleChartRadialPositions alpha y 0,
    y 1 + t * tripleChartRadialPositions alpha y 1,
    y 1 + t * tripleChartRadialPositions alpha y 2, y 0]

def tripleChartAngles (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) : Satellite → ℝ :=
  ![y 4 + t * tripleChartAngularPositions alpha y 0,
    y 4 + t * tripleChartAngularPositions alpha y 1,
    y 4 + t * tripleChartAngularPositions alpha y 2, 0]

def tripleChartPoints (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) : Satellite → Plane :=
  polarSatellites (tripleChartRadii t alpha y) (tripleChartAngles t alpha y)

def tripleClusterRows (P : Satellite → ℝ) : TripleVector := fun i => P i.castSucc

def tripleRowAverage (alpha : TripleVector) (P : Satellite → ℝ) : ℝ :=
  ∑ i, alpha i * tripleClusterRows P i

def tripleRowDifferences (t : ℝ) (P : Satellite → ℝ) : TripleGaps :=
  fun i => (tripleGapMatrix *ᵥ tripleClusterRows P) i / t

theorem tripleChartMass_sum (t : ℝ) (alpha : TripleVector) (ha : ∑ i, alpha i = 1) :
    ∑ i, tripleChartMass t alpha i = 1 := by
  rw [Fin.sum_univ_three] at ha
  simp [tripleChartMass, Fin.sum_univ_four]
  linear_combination t ^ 3 * ha

theorem tripleCentering_gap_decomposition (alpha P : TripleVector) (ha : ∑ i, alpha i = 1) :
    P = (fun _ => ∑ i, alpha i * P i) +
      tripleCenteringMatrix alpha *ᵥ (tripleGapMatrix *ᵥ P) := by
  rw [Fin.sum_univ_three] at ha
  ext i
  fin_cases i
  all_goals simp [tripleCenteringMatrix, tripleGapMatrix, dotProduct, Fin.sum_univ_three]
  · linear_combination -(P 0) * ha
  · linear_combination -(P 1) * ha
  · linear_combination -(P 2) * ha

/-- The paper's inverse row formula has no division by a mass.
It recovers probe rows at every zero-weight endpoint. -/
theorem tripleRows_recovery (t : ℝ) (alpha : TripleVector) (P : Satellite → ℝ)
    (ht : t ≠ 0) (ha : ∑ i, alpha i = 1) :
    tripleClusterRows P = (fun _ => tripleRowAverage alpha P) +
      t • (tripleCenteringMatrix alpha *ᵥ tripleRowDifferences t P) := by
  rw [tripleCentering_gap_decomposition alpha (tripleClusterRows P) ha]
  congr 1
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, tripleRowDifferences,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem tripleRows_zero_iff (t : ℝ) (alpha : TripleVector) (P : Satellite → ℝ)
    (ht : t ≠ 0) (ha : ∑ i, alpha i = 1) :
    tripleRowAverage alpha P = 0 ∧ tripleRowDifferences t P = 0 ↔ tripleClusterRows P = 0 := by
  constructor
  · rintro ⟨hA, hB⟩
    rw [tripleRows_recovery t alpha P ht ha, hA, hB]
    ext i; simp
  · intro hzero
    constructor
    · simp [tripleRowAverage, hzero]
    · ext i; simp [tripleRowDifferences, hzero]

def tripleChartPhysicalRows (eps t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    TripleChartVariables :=
  let R := fun i => radialResidual eps (tripleChartMass t alpha)
    (tripleChartRadii t alpha y) (tripleChartAngles t alpha y) i
  let T := fun i => angularResidual eps (tripleChartMass t alpha)
    (tripleChartRadii t alpha y) (tripleChartAngles t alpha y) i
  ![R 3, tripleRowAverage alpha R, tripleRowDifferences t R 0,
    tripleRowDifferences t R 1, tripleRowAverage alpha T,
    tripleRowDifferences t T 0, tripleRowDifferences t T 1]

end DominantFiveBody
