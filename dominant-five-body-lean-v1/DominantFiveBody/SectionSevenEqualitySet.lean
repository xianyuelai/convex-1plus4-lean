import DominantFiveBody.UniformThreshold
import DominantFiveBody.LocalContinuation

/-! The original local notation Q_n in the branch comparison of Section 7. -/
namespace DominantFiveBody

def branchEqualitySet (radius : ℝ) (first second : ℝ → SliceCoordinates) : Set ℝ :=
  {s | s∈Set.Ico 0 radius ∧ first s=second s}

theorem mem_branchEqualitySet (radius s : ℝ) (first second : ℝ → SliceCoordinates) :
    s∈branchEqualitySet radius first second ↔
      0≤s ∧ s<radius ∧ first s=second s := by
  simp only [branchEqualitySet,Set.mem_ofPred_eq,Set.mem_Ico,and_assoc]

end DominantFiveBody
