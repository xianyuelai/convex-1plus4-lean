import DominantFiveBody.TripleActualCaptureLimits
import DominantFiveBody.FixedLabelEndpoint

/-! # Same-mass, same-label coorbital endpoints of captured triple branches -/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody

theorem TripleCapturedBranches.fixedLabelEndpoint
    (eps t : ℕ → ℝ) (alpha : ℕ → TripleVector) (y : ℕ → TripleChartVariables) (tau : ℝ)
    (captured : TripleCapturedBranches eps t alpha y tau)
    (hm : ∀ n, PositiveRatio (tripleChartMass (t n) (alpha n))) :
    ∀ n, tripleChartAngles (t (captured.tailStart + n)) (alpha (captured.tailStart + n))
      (captured.branch n 0) =
        fixedLabelCoorbitalEndpointAngles
          (tripleChartMass (t (captured.tailStart + n)) (alpha (captured.tailStart + n)))
          (tripleBoundaryHullOrder tau) 3 := by
  intro n
  have hs : (0 : ℝ) ∈ Ico 0 captured.radius := ⟨le_rfl, captured.radius_pos⟩
  have hend := captured.endpoints n
  have hsafe := captured.safe n 0 hs
  have hwidth : ∀ i j, |tripleChartAngles (t (captured.tailStart + n)) (alpha (captured.tailStart + n))
      (captured.branch n 0) j - tripleChartAngles (t (captured.tailStart + n)) (alpha (captured.tailStart + n))
      (captured.branch n 0) i| < Real.pi := by
    simpa only [triplePhysicalRegularSet, tripleParameter_alpha, tripleParameter_scale] using hsafe.2
  have hrad : tripleChartRadii (t (captured.tailStart + n)) (alpha (captured.tailStart + n))
      (captured.branch n 0) = fun _ => 1 := funext hend.1
  apply actualCoorbitalAngles_eq_fixedLabelEndpoint _ _ 3 _ (hm (captured.tailStart + n)) rfl hwidth
  · simpa only [tripleChartPoints, hrad] using captured.convex n 0 hs
  · exact hend.2.2.2

end DominantFiveBody
