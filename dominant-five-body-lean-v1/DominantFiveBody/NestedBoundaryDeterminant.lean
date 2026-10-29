import DominantFiveBody.NestedJacobian
import Mathlib.LinearAlgebra.Matrix.Block

/-! Exact determinant of the actual seven-row nested boundary derivative. -/

noncomputable section
open scoped BigOperators Matrix

namespace DominantFiveBody

set_option maxHeartbeats 1000000

def nestedBoundaryDerivativeMatrix (alpha psi omega : ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  fun i j => nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) (Pi.single j 1) i

theorem nestedBoundaryDerivativeMatrix_triangular_diagonal (alpha psi omega : ℝ)
    (hangle : |psi| = Coorbital.h) (hw : |omega| = 1) :
    (nestedBoundaryDerivativeMatrix alpha psi omega).IsLowerTriangular ∧
      (fun i => nestedBoundaryDerivativeMatrix alpha psi omega i i) =
        ![3, 3, 3, 3, tripleD0, 3 * tripleD0, 9 * tripleD0] := by
  obtain ⟨hpsi, hpi, _, hD⟩ := tripleBoundaryAngle_facts psi hangle
  have hreg := nestedBasePoint_regular alpha psi omega hangle hw
  have hZ := nestedBasePoint_outer_ne_zero omega hw
  have hz := ne_of_gt (pairBoundaryScale_pos (3 * tripleD0)
    (mul_pos (by norm_num) tripleD0_pos))
  obtain ⟨hZscale, hzscale⟩ := nestedBasePoint_diagonal_scales omega hw
  have hr0 (v : NestedChartVariables) :
      nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) v 0 = 3 * v 0 :=
    nestedChartJacobian_unit_radial alpha psi _ _ hreg v 0
  have hr1 (v : NestedChartVariables) :
      nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) v 1 = 3 * v 1 :=
    nestedChartJacobian_unit_radial alpha psi _ _ hreg v 1
  have hr2 (v : NestedChartVariables) :
      nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) v 2 = 3 * v 2 :=
    nestedChartJacobian_unit_radial_difference alpha psi _ _ hreg v 0
  have hr3 (v : NestedChartVariables) :
      nestedChartJacobian 0 0 0 alpha (nestedBasePoint psi omega) v 3 = 3 * v 3 :=
    nestedChartJacobian_unit_radial_difference alpha psi _ _ hreg v 1
  have hm (j : Fin 7) (hj : 4 ≤ j) :
      nestedBoundaryDerivativeMatrix alpha psi omega 4 j =
        tripleD0 * (Pi.single j (1 : ℝ) : NestedChartVariables) 4 := by
    have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    have hj2 : j ≠ 2 := by omega
    have hj3 : j ≠ 3 := by omega
    simpa only [hD, nestedBoundaryDerivativeMatrix, nestedBasePoint] using nestedChartJacobian_unit_mean alpha psi _ _ hreg hpsi hpi
      (Pi.single j 1) (by simp [hj0]) (by simp [hj1]) (by simp [hj2]) (by simp [hj3])
  have ho (j : Fin 7) (hj : 5 ≤ j) :
      nestedBoundaryDerivativeMatrix alpha psi omega 5 j =
        (3 * tripleD0) * (Pi.single j (1 : ℝ) : NestedChartVariables) 5 := by
    have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by omega
    have hj2 : j ≠ 2 := by omega
    have hj3 : j ≠ 3 := by omega
    have hj4 : j ≠ 4 := by omega
    have hd := nestedChartJacobian_unit_outer alpha psi _ _ hreg hpsi hpi hZ
      (Pi.single j 1) (by simp [hj0]) (by simp [hj1]) (by simp [hj2]) (by simp [hj3])
      (by simp [hj4])
    rw [hD, hZscale] at hd
    change nestedChartJacobian 0 0 0 alpha
      (nestedUnitPoint psi (omega * pairBoundaryScale tripleD0) (pairBoundaryScale (3 * tripleD0)))
      (Pi.single j 1) 5 = _
    rw [hd]
    ring
  have hi : nestedBoundaryDerivativeMatrix alpha psi omega 6 6 = 9 * tripleD0 := by
    have hd := nestedChartJacobian_unit_inner alpha psi _ _ hreg hpsi hpi hZ hz
      (Pi.single (6 : Fin 7) 1) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    simp only [hD, hZscale, hzscale, Pi.single_eq_same, mul_one] at hd
    change nestedBoundaryDerivativeMatrix alpha psi omega 6 6 = _ at hd
    rw [hd]
    ring
  constructor
  · intro i j hij
    change i < j at hij
    fin_cases i <;> dsimp only at hij
    · change (0 : Fin 7) < j at hij
      simp [nestedBoundaryDerivativeMatrix, hr0, ne_of_gt hij]
    · change (1 : Fin 7) < j at hij
      simp [nestedBoundaryDerivativeMatrix, hr1, ne_of_gt hij]
    · change (2 : Fin 7) < j at hij
      simp [nestedBoundaryDerivativeMatrix, hr2, ne_of_gt hij]
    · change (3 : Fin 7) < j at hij
      simp [nestedBoundaryDerivativeMatrix, hr3, ne_of_gt hij]
    · change (4 : Fin 7) < j at hij
      change nestedBoundaryDerivativeMatrix alpha psi omega 4 j = 0
      rw [hm j (by omega)]
      simp [ne_of_gt hij]
    · change (5 : Fin 7) < j at hij
      change nestedBoundaryDerivativeMatrix alpha psi omega 5 j = 0
      rw [ho j (by omega)]
      simp [ne_of_gt hij]
    · change (6 : Fin 7) < j at hij
      omega
  · funext i
    fin_cases i
    · simp [nestedBoundaryDerivativeMatrix, hr0]
    · simp [nestedBoundaryDerivativeMatrix, hr1]
    · simp [nestedBoundaryDerivativeMatrix, hr2]
    · simp [nestedBoundaryDerivativeMatrix, hr3]
    · simpa using hm 4 (by decide)
    · simpa using ho 5 (by decide)
    · simpa using hi

theorem nestedBoundaryDerivativeMatrix_det (alpha psi omega : ℝ)
    (hangle : |psi| = Coorbital.h) (hw : |omega| = 1) :
    (nestedBoundaryDerivativeMatrix alpha psi omega).det = 2187 * tripleD0 ^ 3 := by
  obtain ⟨htri, hdiag⟩ := nestedBoundaryDerivativeMatrix_triangular_diagonal alpha psi omega hangle hw
  rw [Matrix.det_of_isLowerTriangular _ htri, hdiag]
  norm_num [Fin.prod_univ_succ]
  ring

end DominantFiveBody
