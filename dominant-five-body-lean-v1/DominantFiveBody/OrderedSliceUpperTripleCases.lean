import DominantFiveBody.OrderedSliceTripleCases
import DominantFiveBody.TripleUpperActualCapture

/-! Actual upper-triple capture in the original ordered first-angle slice. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 900000

theorem orderedSlice_upper_regular_triple_capture
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n, orderedSliceRoot (p n) (eps n) (y n))
    (muLimit thetaLimit : MassRatio) (qLimit : SatelliteConfiguration)
    (hmt : Tendsto (fun n => (p n).val) atTop (𝓝 muLimit))
    (htt : Tendsto (fun n => sliceAngles (y n)) atTop (𝓝 thetaLimit))
    (hqt : Tendsto (fun n => sliceSatellites (y n)) atTop (𝓝 qLimit))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 center)
    (eta : ℝ) (heta : 0 < eta)
    (hcomparable : ∀ᶠ n in atTop, ∀ i j : TripleLabel, i ≠ j →
      eta * tripleHighDiameter (sliceSatellites (y n)) ≤
        satelliteDistance (sliceSatellites (y n)) i.succ j.succ) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint p eps y) := by
  obtain ⟨phi, hphi, ⟨c⟩⟩ := normalized_complete_upper_triple_regular_actual_capture eps
    (fun n => (p n).val) (fun n => slicePhysicalConfiguration (eps n, (p n).val) (y n))
    heps hepst (fun n => (p n).property)
    (fun n => (orderedSliceRoot_physical (p n) (eps n) (heps n) (y n) (hy n)).1)
    (fun n => (hy n).2.2.1) (fun n => sliceRadii (y n)) (fun n => sliceAngles (y n))
    (fun n => (hy n).1.2.1) (fun n => slicePhysicalConfiguration_satellitesRelative _ _)
    (fun n => (hy n).2.1) muLimit hmt qLimit
    (by simpa only [slicePhysicalConfiguration_satellitesRelative] using hqt)
    thetaLimit htt center htriple eta heta
    (by simpa only [slicePhysicalConfiguration_satellitesRelative] using hcomparable)
  have hc := c.toOriginalOrderedSlice (fun n => (p (phi n)).val) (eps ∘ phi)
    (fun n => sliceRadii (y (phi n))) (fun n => sliceAngles (y (phi n)))
    upperTripleChartPermutation 1 (fun n => (p (phi n)).property)
    (fun _ => rfl) (fun n => (hy (phi n)).2.1)
  have hc' : Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (p ∘ phi) (eps ∘ phi) (y ∘ phi)) := by
    simpa only [polarSlice_reconstruct, Subtype.coe_eta, Function.comp_def] using hc
  exact hc'.map (CapturedBranches.liftSubsequence p eps y phi hphi)

end DominantFiveBody
