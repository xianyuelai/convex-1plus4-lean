import DominantFiveBody.SliceConnection

/-!
# Smoothness of the actual captured branches

Proposition 7.1 calls for smooth branches in the original seven-coordinate
slice.  The capture structure records continuity, actual roots, actual
shape nondegeneracy and the fixed-mass coorbital endpoint.  These data
already imply smoothness: at every point, including zero, the actual
seven-row Jacobian is invertible; the implicit function theorem and
continuity identify the captured branch with its local smooth solution.
-/

noncomputable section
open scoped ContDiff
open Filter Set Topology

namespace DominantFiveBody

set_option maxHeartbeats 800000

/-- A continuous family of actual continuation roots is smooth throughout
its half-open connection interval, including the coorbital endpoint. -/
theorem orderedSlice_contDiffOn_of_continuationRoots
    (mu : PositiveMassRatio) (radius : ℝ) (branch : ℝ → SliceCoordinates)
    (hc : ContinuousOn branch (Ico 0 radius))
    (hroots : ∀ s ∈ Ico 0 radius,
      ContinuationRoot orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
        mu s (branch s)) :
    ContDiffOn ℝ ∞ branch (Ico 0 radius) := by
  intro s hs
  obtain ⟨hreg, hzero, hJ⟩ :=
    orderedSliceContinuationRoot_actual_data mu s (branch s) (hroots s hs)
  obtain ⟨psi, _, hsmooth, _, huniq⟩ :=
    reducedResidual_local_implicitFunction (s, mu.val) (branch s) hreg hzero hJ
  have hparam : ContDiff ℝ ∞ (fun t : ℝ => (t, mu.val)) :=
    contDiff_id.prodMk contDiff_const
  have hlocalSmooth : ContDiffAt ℝ ∞ (fun t : ℝ => psi (t, mu.val)) s :=
    hsmooth.comp s hparam.contDiffAt
  have hgraph : ContinuousWithinAt
      (fun t : ℝ => ((t, mu.val), branch t)) (Ico 0 radius) s :=
    hparam.continuous.continuousWithinAt.prodMk (hc s hs)
  have heq : branch =ᶠ[𝓝[Ico 0 radius] s] (fun t : ℝ => psi (t, mu.val)) := by
    filter_upwards [hgraph.tendsto.eventually huniq, self_mem_nhdsWithin] with t ht htdom
    have hz := (orderedSliceContinuationRoot_actual_data mu t (branch t)
      (hroots t htdom)).2.1
    exact (ht.mp hz).symm
  exact hlocalSmooth.contDiffWithinAt.congr_of_eventuallyEq_of_mem heq hs

namespace CapturedBranches

/-- The actual capture data contain all hypotheses needed for the smooth
branches asserted in the manuscript's Proposition 7.1. -/
theorem orderedSlice_contDiffOn
    {p : ℕ → PositiveMassRatio} {eps : ℕ → ℝ} {y : ℕ → SliceCoordinates}
    (c : CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint p eps y)
    (n : ℕ) :
    ContDiffOn ℝ ∞ (c.branch n) (Ico 0 c.radius) := by
  exact orderedSlice_contDiffOn_of_continuationRoots (p (c.subseq n)) c.radius
    (c.branch n) (c.continuous n) (fun s hs => c.continuationRoot n hs.1 hs.2)

end CapturedBranches
end DominantFiveBody
