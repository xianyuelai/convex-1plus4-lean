import DominantFiveBody.OrderedSliceConnection
import DominantFiveBody.SmoothCapturedBranches

/-!
# Proposition 7.1 with its original smoothness assertion

Every actual strictly convex root sequence approaching zero admits a
captured subsequence with a common positive radius and smooth original
seven-coordinate branches.  Endpoint identification, root equations,
strict convexity, actual shape nondegeneracy and the exact sequence hits
are retained from the concrete capture theorem.
-/

noncomputable section
open scoped ContDiff
open Filter Set Topology

namespace DominantFiveBody

/-- Original Proposition 7.1, including smoothness on the common half-open
interval.  The existing capture data are retained without reconstruction. -/
theorem orderedSlice_smooth_connection
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n, orderedSliceRoot (p n) (eps n) (y n)) :
    ∃ c : CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint p eps y,
      ∀ n, ContDiffOn ℝ ∞ (c.branch n) (Ico 0 c.radius) := by
  obtain ⟨c⟩ := orderedSlice_connection p eps y heps hepst hy
  exact ⟨c, c.orderedSlice_contDiffOn⟩

/-- An explicit seven-coordinate statement of Proposition 7.1: the mass
parameters and root sequence keep their original labels after extraction. -/
theorem orderedSlice_smooth_connection_explicit
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n, 0 < eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n, orderedSliceRoot (p n) (eps n) (y n)) :
    ∃ (phi : ℕ → ℕ) (radius : ℝ) (Gamma : ℕ → ℝ → SliceCoordinates),
      StrictMono phi ∧ 0 < radius ∧ (∀ n, eps (phi n) < radius) ∧
      (∀ n, ContDiffOn ℝ ∞ (Gamma n) (Ico 0 radius)) ∧
      (∀ n, Gamma n (eps (phi n)) = y (phi n)) ∧
      (∀ n s, 0 < s → s < radius → orderedSliceRoot (p (phi n)) s (Gamma n s)) ∧
      (∀ n s, 0 < s → s < radius →
        orderedSliceNondegenerate (p (phi n)) s (Gamma n s)) ∧
      (∀ n, Gamma n 0 = orderedSliceEndpoint (p (phi n))) := by
  obtain ⟨c, hsmooth⟩ := orderedSlice_smooth_connection p eps y heps hepst hy
  exact ⟨c.subseq, c.radius, c.branch, c.subseq_strictMono, c.radius_pos,
    c.parameters_lt_radius, hsmooth, c.hits, c.roots, c.nondegenerate_at, c.endpoints⟩

end DominantFiveBody
