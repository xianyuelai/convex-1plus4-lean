import DominantFiveBody.NestedConvexity
import DominantFiveBody.HullOrderTransport

/-! The four original nested sign/label cases, with the chart permutation
derived from its actual convex hull order. Labels 1,...,4 are the original
satellite labels and 0 is the dominant body. -/
noncomputable section
open scoped BigOperators Matrix
namespace DominantFiveBody

def nestedSourceCaseSigns : Fin 4 → ℝ × ℝ :=
  ![(-1, 1), (-1, -1), (1, 1), (1, -1)]

def nestedSourceCasePermutation (k : Fin 4) : Equiv.Perm Satellite :=
  (hullSatellitePermutation (nestedBoundaryHullOrder (nestedSourceCaseSigns k).1
    (nestedSourceCaseSigns k).2)).symm

theorem nestedSourceCasePermutation_source :
    (fun k i => nestedSourceCasePermutation k i) =
      ![![0, 1, 2, 3], ![1, 2, 0, 3], ![1, 2, 3, 0], ![2, 3, 1, 0]] := by
  funext k i
  fin_cases k <;> fin_cases i
  all_goals norm_num [nestedSourceCasePermutation, nestedSourceCaseSigns, hullSatellitePermutation,
    nestedBoundaryHullOrder, tripleBoundaryHullOrder, nestedClusterPermutation,
    tripleRightOrder, standardHullOrder, pairMiddleOrder, Equiv.trans_apply]
  all_goals rfl

def nestedSourceCaseTable (k : Fin 4) : Finset Label × Finset Label × Label × (ℝ × ℝ) :=
  (({(nestedSourceCasePermutation k 0).succ, (nestedSourceCasePermutation k 1).succ,
      (nestedSourceCasePermutation k 2).succ} : Finset Label),
    ({(nestedSourceCasePermutation k 0).succ, (nestedSourceCasePermutation k 1).succ} : Finset Label),
    (nestedSourceCasePermutation k 3).succ, nestedSourceCaseSigns k)

/-- All four rows of source display:780, derived from the physical chart
label map and its genuine convex hull order. -/
theorem nestedSourceCaseTable_source : nestedSourceCaseTable =
    ![({1, 2, 3}, {1, 2}, 4, (-1, 1)),
      ({1, 2, 3}, {2, 3}, 4, (-1, -1)),
      ({2, 3, 4}, {2, 3}, 1, (1, 1)),
      ({2, 3, 4}, {3, 4}, 1, (1, -1))] := by
  have hp (k : Fin 4) (i : Satellite) := congrFun (congrFun nestedSourceCasePermutation_source k) i
  funext k
  fin_cases k
  all_goals simp [nestedSourceCaseTable, nestedSourceCaseSigns, hp]
  all_goals decide

theorem nestedSourceCase_order_is_original (k : Fin 4) :
    (nestedSourceCasePermutation k : Satellite → Satellite) ∘
      hullSatellitePermutation (nestedBoundaryHullOrder (nestedSourceCaseSigns k).1
        (nestedSourceCaseSigns k).2) = id := by
  funext i
  exact Equiv.symm_apply_apply _ i

end DominantFiveBody
