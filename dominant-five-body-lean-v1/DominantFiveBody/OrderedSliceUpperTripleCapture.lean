import DominantFiveBody.OrderedSliceMirrorCapture
import DominantFiveBody.OrderedSliceLowerTripleCapture

/-! Complete actual upper triples are captured through the proved
first-angle involution and returned to the original mass and coordinates.
No scale or mass-share convergence is required as an input.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody

theorem orderedSlice_upper_triple_capture
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n,orderedSliceRoot (p n) (eps n) (y n))
    (muLimit thetaLimit : MassRatio) (qLimit : SatelliteConfiguration)
    (hmt : Tendsto (fun n => (p n).val) atTop (𝓝 muLimit))
    (htt : Tendsto (fun n => sliceAngles (y n)) atTop (𝓝 thetaLimit))
    (hqt : Tendsto (fun n => sliceSatellites (y n)) atTop (𝓝 qLimit))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 center) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint p eps y) := by
  obtain ⟨hy',hmt',htt',hqt',htriple'⟩ := orderedSlice_upper_triple_mirror_limits
    p eps y heps hepst hy muLimit thetaLimit qLimit hmt htt hqt center htriple
  obtain ⟨c⟩ := orderedSlice_lower_triple_capture (fun n => mirrorPositiveMassRatio (p n))
    eps (fun n => mirrorSlice (y n)) heps hepst hy' (muLimit ∘ Fin.revPerm)
    (firstAngleMirrorAngles thetaLimit) (polarSatellites (fun _ => 1) (firstAngleMirrorAngles thetaLimit))
    hmt' htt' hqt' (polarPoint 1 0) htriple'
  exact captured_mirrorOrderedSlice_undo p eps y c

end DominantFiveBody
