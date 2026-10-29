import DominantFiveBody.OrderedSliceSequences
import DominantFiveBody.TripleActualCapture
import DominantFiveBody.TripleOriginalOrderedCapture

/-! Actual regular-triple capture in the original ordered slice.
The scale separation used below is extracted from actual pair distances.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 900000

theorem orderedSlice_lower_regular_triple_capture
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n,orderedSliceRoot (p n) (eps n) (y n))
    (muLimit thetaLimit : MassRatio) (qLimit : SatelliteConfiguration)
    (hmt : Tendsto (fun n => (p n).val) atTop (𝓝 muLimit))
    (htt : Tendsto (fun n => sliceAngles (y n)) atTop (𝓝 thetaLimit))
    (hqt : Tendsto (fun n => sliceSatellites (y n)) atTop (𝓝 qLimit))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 3 center)
    (eta : ℝ) (heta : 0<eta)
    (hcomparable : ∀ᶠ n in atTop,∀ i j : TripleLabel,i≠j →
      eta*tripleLowDiameter (sliceSatellites (y n))≤
        satelliteDistance (sliceSatellites (y n)) i.castSucc j.castSucc) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint p eps y) := by
  obtain ⟨phi,hphi,⟨c⟩⟩ := normalized_complete_lower_triple_regular_actual_capture eps
    (fun n => (p n).val) (fun n => slicePhysicalConfiguration (eps n,(p n).val) (y n))
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
    (Equiv.refl Satellite) (-1) (fun n => (p (phi n)).property)
    (fun _ => rfl) (fun n => (hy (phi n)).2.1)
  have hc' : Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (p ∘ phi) (eps ∘ phi) (y ∘ phi)) := by
    simpa only [polarSlice_reconstruct,Subtype.coe_eta,Function.comp_def] using hc
  exact hc'.map (CapturedBranches.liftSubsequence p eps y phi hphi)

theorem tripleLargestDistance_low (q : SatelliteConfiguration) :
    tripleLargestDistance q 0 1 2=tripleLowDiameter q := by
  simp only [tripleLargestDistance,tripleLowDiameter,satelliteDistance]
  rw [norm_sub_rev (q 0) (q 1),norm_sub_rev (q 0) (q 2),norm_sub_rev (q 1) (q 2)]

theorem low_triple_comparable_of_three (q : SatelliteConfiguration) (k : ℝ)
    (h : k*tripleLowDiameter q≤satelliteDistance q 0 1 ∧
      k*tripleLowDiameter q≤satelliteDistance q 0 2 ∧
      k*tripleLowDiameter q≤satelliteDistance q 1 2) :
    ∀ i j : TripleLabel,i≠j → k*tripleLowDiameter q≤satelliteDistance q i.castSucc j.castSucc := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h.1
  · exact h.2.1
  · change k*tripleLowDiameter q≤‖q 1-q 0‖
    rw [norm_sub_rev]
    exact h.1
  · exact (hij rfl).elim
  · exact h.2.2
  · change k*tripleLowDiameter q≤‖q 2-q 0‖
    rw [norm_sub_rev]
    exact h.2.1
  · change k*tripleLowDiameter q≤‖q 2-q 1‖
    rw [norm_sub_rev]
    exact h.2.2
  · exact (hij rfl).elim

/-- A genuine subsequence either has a fixed inner pair whose distance
is negligible compared with the triple diameter, or all distances are
uniformly comparable. The three labels stay in the actual lower block. -/
theorem low_triple_scale_cases (q : ℕ → SatelliteConfiguration)
    (hq : ∀ n,RelativeCollisionFree (q n)) :
    ∃ phi : ℕ → ℕ,StrictMono phi ∧
      ((∃ a b c : TripleLabel,a<b ∧ c≠a ∧ c≠b ∧
        Tendsto (fun n => satelliteDistance (q (phi n)) a.castSucc b.castSucc/
          tripleLowDiameter (q (phi n))) atTop (𝓝 0)) ∨
       ∃ eta : ℝ,0<eta ∧ ∀ (n : ℕ) (i j : TripleLabel),i≠j →
         eta*tripleLowDiameter (q (phi n))≤satelliteDistance (q (phi n)) i.castSucc j.castSucc) := by
  obtain ⟨phi,hphi,hnested|⟨eta,heta,hcomp⟩⟩ := collision_free_triple_scale_subsequence q
    0 1 2 (by decide) (by decide) (by decide) hq
  · obtain ⟨psi,u,v,w,hpsi,hlabels,hmin⟩ := triple_minimum_pair_subsequence (q ∘ phi) 0 1 2
    refine ⟨phi ∘ psi,hphi.comp hpsi,Or.inl ?_⟩
    have hlim := hnested.comp hpsi.tendsto_atTop
    have hh : Tendsto (fun n => satelliteDistance (q ((phi ∘ psi) n)) u v /
        tripleLowDiameter (q ((phi ∘ psi) n))) atTop (𝓝 0) := by
      change Tendsto (fun n => tripleShortestDistance (q (phi (psi n))) 0 1 2 /
        tripleLargestDistance (q (phi (psi n))) 0 1 2) atTop (𝓝 0) at hlim
      have he (n : ℕ) : satelliteDistance (q (phi (psi n))) u v =
          tripleShortestDistance (q (phi (psi n))) 0 1 2 := hmin n
      simpa only [Function.comp_apply,he,tripleLargestDistance_low] using hlim
    rcases hlabels with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
    · exact ⟨0,1,2,by decide,by decide,by decide,hh⟩
    · exact ⟨0,2,1,by decide,by decide,by decide,hh⟩
    · exact ⟨1,2,0,by decide,by decide,by decide,hh⟩
  · refine ⟨phi,hphi,Or.inr ⟨eta,heta,?_⟩⟩
    intro n
    apply low_triple_comparable_of_three (q (phi n)) eta
    simpa only [tripleLargestDistance_low] using hcomp n

end DominantFiveBody
