import DominantFiveBody.PairSmooth
import DominantFiveBody.TripleSmooth
import DominantFiveBody.NestedSmooth

/-! The Section 5 signed-scale extensions are real analytic. The original
joint regularity proofs hold at order omega, not merely at every finite
order, so their analyticity follows from the kernel-checked omega theorem. -/

noncomputable section
open scoped ContDiff

namespace DominantFiveBody

theorem pairChartExtendedRows_joint_analyticAt (v : PairJointVariables) (keepD : Bool)
    (hreg : PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2) :
    AnalyticAt ℝ (fun w : PairJointVariables =>
      pairChartExtendedRows (w.1 0) (w.1 1) (w.1 2) (w.1 3) keepD w.2) v :=
  (pairChartExtendedRows_joint_contDiffAt ω v hreg keepD).analyticAt

theorem tripleChartExtendedRows_joint_analyticAt (v : TripleJointVariables)
    (hreg : TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2) :
    AnalyticAt ℝ (fun w : TripleJointVariables =>
      tripleChartExtendedRows (w.1 0) (w.1 1) (tripleJointAlpha w.1) w.2) v :=
  (tripleChartExtendedRows_joint_contDiffAt ω v hreg).analyticAt

theorem nestedChartExtendedRows_joint_analyticAt (v : NestedJointVariables)
    (hreg : NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2) :
    AnalyticAt ℝ (fun w : NestedJointVariables =>
      nestedChartExtendedRows (w.1 0) (w.1 1) (w.1 2) (w.1 3) w.2) v :=
  (nestedChartExtendedRows_joint_contDiffAt ω v hreg).analyticAt

end DominantFiveBody
