import DominantFiveBody.OrderedSliceTripleCases
import DominantFiveBody.NestedActualCapture

/-! Actual nested lower triples are captured in the original ordered slice. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 900000

theorem orderedSlice_lower_nested_triple_capture
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n, orderedSliceRoot (p n) (eps n) (y n))
    (muLimit thetaLimit : MassRatio) (qLimit : SatelliteConfiguration)
    (hmt : Tendsto (fun n => (p n).val) atTop (𝓝 muLimit))
    (htt : Tendsto (fun n => sliceAngles (y n)) atTop (𝓝 thetaLimit))
    (hqt : Tendsto (fun n => sliceSatellites (y n)) atTop (𝓝 qLimit))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (a b c : TripleLabel) (hab : a < b) (hca : c ≠ a) (hcb : c ≠ b)
    (hpair : Tendsto (fun n => satelliteDistance (sliceSatellites (y n)) a.castSucc b.castSucc /
      tripleLowDiameter (sliceSatellites (y n))) atTop (𝓝 0)) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint p eps y) := by
  have hc := normalized_complete_lower_triple_nested_original_capture eps (fun n => (p n).val)
    (fun n => slicePhysicalConfiguration (eps n, (p n).val) (y n)) heps hepst (fun n => (p n).property)
    (fun n => (orderedSliceRoot_physical (p n) (eps n) (heps n) (y n) (hy n)).1)
    (fun n => (hy n).2.2.1) (fun n => sliceRadii (y n)) (fun n => sliceAngles (y n))
    (fun n => (hy n).1.2.1) (fun n => slicePhysicalConfiguration_satellitesRelative _ _)
    (fun _ => rfl) (fun n => (hy n).2.1) muLimit hmt qLimit
    (by simpa only [slicePhysicalConfiguration_satellitesRelative] using hqt)
    thetaLimit htt center htriple a b c hab hca hcb
    (by simpa only [slicePhysicalConfiguration_satellitesRelative] using hpair)
  simpa only [polarSlice_reconstruct, Subtype.coe_eta] using hc

end DominantFiveBody
