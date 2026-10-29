import DominantFiveBody.OrderedSliceNestedCases

/-! Exhaustion of the two actual lower-triple regimes in Section 7. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody

theorem orderedSlice_lower_triple_capture
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n,orderedSliceRoot (p n) (eps n) (y n))
    (muLimit thetaLimit : MassRatio) (qLimit : SatelliteConfiguration)
    (hmt : Tendsto (fun n => (p n).val) atTop (𝓝 muLimit))
    (htt : Tendsto (fun n => sliceAngles (y n)) atTop (𝓝 thetaLimit))
    (hqt : Tendsto (fun n => sliceSatellites (y n)) atTop (𝓝 qLimit))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint p eps y) := by
  have hcf (n : ℕ) : RelativeCollisionFree (sliceSatellites (y n)) := by
    have hh := satellitesRelative_collisionFree _
      (orderedSliceRoot_physical (p n) (eps n) (heps n) (y n) (hy n)).1.1
    simpa only [slicePhysicalConfiguration_satellitesRelative] using hh
  obtain ⟨phi,hphi,hnested|⟨eta,heta,hcomp⟩⟩ := low_triple_scale_cases
    (fun n => sliceSatellites (y n)) hcf
  · obtain ⟨a,b,c,hab,hca,hcb,hpair⟩ := hnested
    have hc := orderedSlice_lower_nested_triple_capture (p ∘ phi) (eps ∘ phi) (y ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hy (phi n))
      muLimit thetaLimit qLimit (hmt.comp hphi.tendsto_atTop) (htt.comp hphi.tendsto_atTop)
      (hqt.comp hphi.tendsto_atTop) center htriple a b c hab hca hcb hpair
    exact hc.map (CapturedBranches.liftSubsequence p eps y phi hphi)
  · have hc := orderedSlice_lower_regular_triple_capture (p ∘ phi) (eps ∘ phi) (y ∘ phi)
      (fun n => heps (phi n)) (hepst.comp hphi.tendsto_atTop) (fun n => hy (phi n))
      muLimit thetaLimit qLimit (hmt.comp hphi.tendsto_atTop) (htt.comp hphi.tendsto_atTop)
      (hqt.comp hphi.tendsto_atTop) center htriple eta heta (Eventually.of_forall hcomp)
    exact hc.map (CapturedBranches.liftSubsequence p eps y phi hphi)

end DominantFiveBody
