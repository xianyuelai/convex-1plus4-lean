import DominantFiveBody.NestedHessian

/-! The full seven-coordinate determinant in the manuscript's nested chart.
Both three-coordinate blocks are retained, including alpha endpoints. -/
noncomputable section
open scoped BigOperators Matrix
namespace DominantFiveBody

def nestedCoordinateBlock (t eta alpha : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if j=0 then 1 else
    if j=1 then (if i=1 then eta^3*t else -(1-eta^3)*t) else
    if i=0 then alpha*t*eta else if i=1 then 0 else -(1-alpha)*t*eta

theorem nestedCoordinateBlock_det (t eta alpha : ℝ) :
    (nestedCoordinateBlock t eta alpha).det = -(t^2*eta) := by
  rw [Matrix.det_fin_three]
  dsimp [nestedCoordinateBlock]
  ring

def nestedCoordinateIndex : (Fin 1 ⊕ (Fin 3 ⊕ Fin 3)) ≃ Fin 7 :=
  (Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv

theorem nestedToFixedSlice_full_matrix (t eta alpha : ℝ) :
    (LinearMap.toMatrix' (nestedToFixedSlice t eta alpha).toLinearMap).submatrix
      nestedCoordinateIndex nestedCoordinateIndex =
      Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        (Matrix.fromBlocks (nestedCoordinateBlock t eta alpha) 0 0
          (nestedCoordinateBlock t eta alpha)) := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  all_goals fin_cases i <;> fin_cases j
  all_goals simp [LinearMap.toMatrix'_apply,nestedCoordinateIndex,finSumFinEquiv,nestedToFixedSlice,
    nestedVariableProjection,nestedCoordinateBlock,Matrix.submatrix_apply,smul_eq_mul]
  all_goals ring

theorem nestedToFixedSlice_full_det (t eta alpha : ℝ) :
    (LinearMap.toMatrix' (nestedToFixedSlice t eta alpha).toLinearMap).det = t^4*eta^2 := by
  have h := congrArg Matrix.det (nestedToFixedSlice_full_matrix t eta alpha)
  rw [Matrix.det_submatrix_equiv_self,Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,nestedCoordinateBlock_det] at h
  calc
    _ = _ := h
    _ = _ := by ring

theorem nestedToFixedSlice_full_abs_det (t eta alpha : ℝ) :
    |(LinearMap.toMatrix' (nestedToFixedSlice t eta alpha).toLinearMap).det| = t^4*eta^2 := by
  rw [nestedToFixedSlice_full_det,abs_of_nonneg]
  positivity

end DominantFiveBody
