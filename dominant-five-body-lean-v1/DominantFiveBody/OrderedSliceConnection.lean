import DominantFiveBody.OrderedSliceUpperTripleCapture

/-! Proposition 7.1: every actual convex root sequence is captured.
The finite collision classification and every scale case have concrete
physical implementations. No analytical interface is assumed here. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody

theorem orderedSlice_connection :
    ConnectionProperty orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint := by
  intro p eps y heps hepst hy
  obtain ⟨phi,muLimit,thetaLimit,hphi,hmt,htt,_,_,hqt,hcases⟩ :=
    orderedSlice_collision_subsequence p eps y heps hepst hy
  have heps' (n : ℕ) : 0<(eps ∘ phi) n := heps (phi n)
  have hepst' : Tendsto (eps ∘ phi) atTop (𝓝 0) := hepst.comp hphi.tendsto_atTop
  have hy' (n : ℕ) : orderedSliceRoot ((p ∘ phi) n) ((eps ∘ phi) n) ((y ∘ phi) n) := hy (phi n)
  have hc : Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (p ∘ phi) (eps ∘ phi) (y ∘ phi)) := by
    rcases hcases with hsep|⟨a,b,hab,hpair⟩|⟨anchor,hanchor,center,htriple⟩
    · exact orderedSlice_noCollision_capture (p ∘ phi) (eps ∘ phi) (y ∘ phi)
        heps' hepst' hy' muLimit thetaLimit _ hmt htt hqt hsep
    · exact orderedSlice_pair_capture (p ∘ phi) (eps ∘ phi) (y ∘ phi)
        heps' hepst' hy' muLimit thetaLimit _ hmt htt hqt a b hab _ hpair
    · rcases hanchor with rfl|rfl
      · exact orderedSlice_upper_triple_capture (p ∘ phi) (eps ∘ phi) (y ∘ phi)
          heps' hepst' hy' muLimit thetaLimit _ hmt htt hqt center htriple
      · exact orderedSlice_lower_triple_capture (p ∘ phi) (eps ∘ phi) (y ∘ phi)
          heps' hepst' hy' muLimit thetaLimit _ hmt htt hqt center htriple
  exact hc.map (CapturedBranches.liftSubsequence p eps y phi hphi)

end DominantFiveBody
