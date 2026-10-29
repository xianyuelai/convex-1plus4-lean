import DominantFiveBody.OrderedSliceApplication
import DominantFiveBody.NoCollisionSliceConnection
import DominantFiveBody.PairOriginalOrderedCapture

/-! Actual ordered slice sequences and composition of their captured
subsequences. All roots here retain the physical convexity condition. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
universe u v
namespace DominantFiveBody

def CapturedBranches.liftSubsequence
    {P : Type u} {Y : Type v} [TopologicalSpace Y]
    {root nondegenerate : P → ℝ → Y → Prop} {endpoint : P → Y}
    (p : ℕ → P) (eps : ℕ → ℝ) (y : ℕ → Y)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (c : CapturedBranches root nondegenerate endpoint (p ∘ phi) (eps ∘ phi) (y ∘ phi)) :
    CapturedBranches root nondegenerate endpoint p eps y where
  subseq := phi ∘ c.subseq
  subseq_strictMono := hphi.comp c.subseq_strictMono
  radius := c.radius
  radius_pos := c.radius_pos
  parameters_lt_radius := c.parameters_lt_radius
  branch := c.branch
  continuous := c.continuous
  hits := c.hits
  roots := c.roots
  nondegenerate_at := c.nondegenerate_at
  endpoints := c.endpoints

theorem polarSlice_reconstruct (y : SliceCoordinates) :
    polarSlice (sliceRadii y) (sliceAngles y)=y := by
  apply sliceCoordinates_ext
  · exact polarSlice_radii _ _
  · exact polarSlice_angles _ _ rfl

theorem orderedSlice_collision_subsequence
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n,orderedSliceRoot (p n) (eps n) (y n)) :
    ∃ (phi : ℕ → ℕ) (muLimit thetaLimit : MassRatio),StrictMono phi ∧
      Tendsto (fun n => (p (phi n)).val) atTop (𝓝 muLimit) ∧
      Tendsto (fun n => sliceAngles (y (phi n))) atTop (𝓝 thetaLimit) ∧
      (∀ i,0≤muLimit i) ∧ (∑ i,muLimit i=1) ∧
      let qLimit := polarSatellites (fun _ => 1) thetaLimit
      Tendsto (fun n => sliceSatellites (y (phi n))) atTop (𝓝 qLimit) ∧
      (Function.Injective qLimit ∨
        (∃ a b : Satellite,a<b ∧ CompleteLimitingSatellitePair qLimit a b (qLimit a)) ∨
        (∃ p : Satellite,(p=0 ∨ p=3) ∧ ∃ c,CompleteLimitingSatelliteTriple qLimit p c)) := by
  have hh := normalized_ordered_collision_subsequence eps (fun n => (p n).val)
    (fun n => slicePhysicalConfiguration (eps n,(p n).val) (y n)) heps hepst
    (fun n => (p n).property)
    (fun n => (orderedSliceRoot_physical (p n) (eps n) (heps n) (y n) (hy n)).1)
    (fun n => (hy n).2.2.1) (fun n => sliceRadii (y n)) (fun n => sliceAngles (y n))
    (fun n => (hy n).1.2.1) (fun n => slicePhysicalConfiguration_satellitesRelative _ _)
    (fun _ => rfl) (fun n => (hy n).2.1)
  simpa only [Function.comp_def,slicePhysicalConfiguration_satellitesRelative] using hh

/-- The no-collision case is fully connected in exactly the original
ordered slice and mass variables used by the final theorem. -/
theorem orderedSlice_noCollision_capture
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n,orderedSliceRoot (p n) (eps n) (y n))
    (muLimit thetaLimit : MassRatio) (qLimit : SatelliteConfiguration)
    (hmt : Tendsto (fun n => (p n).val) atTop (𝓝 muLimit))
    (htt : Tendsto (fun n => sliceAngles (y n)) atTop (𝓝 thetaLimit))
    (hqt : Tendsto (fun n => sliceSatellites (y n)) atTop (𝓝 qLimit))
    (hsep : Function.Injective qLimit) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint p eps y) := by
  have hh := normalized_noCollision_ordered_capture eps (fun n => (p n).val)
    (fun n => slicePhysicalConfiguration (eps n,(p n).val) (y n)) heps hepst
    (fun n => (p n).property)
    (fun n => (orderedSliceRoot_physical (p n) (eps n) (heps n) (y n) (hy n)).1)
    (fun n => sliceRadii (y n)) (fun n => sliceAngles (y n)) (fun n => (hy n).1.2.1)
    (fun n => slicePhysicalConfiguration_satellitesRelative _ _) (fun _ => rfl)
    (fun n => (hy n).2.1) muLimit hmt qLimit
    (by simpa only [slicePhysicalConfiguration_satellitesRelative] using hqt) thetaLimit htt hsep
  simpa only [polarSlice_reconstruct] using hh

theorem pairExterior_layout (a b : Satellite) (hab : a<b) :
    ∃ u w : Satellite,u<w ∧ u∈pairExteriorLabels a b ∧ w∈pairExteriorLabels a b ∧
      ∃ e : Equiv.Perm Satellite,e 0=a ∧ e 1=b ∧ e 2=u ∧ e 3=w := by
  fin_cases a <;> fin_cases b <;> norm_num at hab
  · exact ⟨2,3,by decide,by decide,by decide,
      Equiv.ofBijective (![0,1,2,3] : Satellite → Satellite) (by decide),rfl,rfl,rfl,rfl⟩
  · exact ⟨1,3,by decide,by decide,by decide,
      Equiv.ofBijective (![0,2,1,3] : Satellite → Satellite) (by decide),rfl,rfl,rfl,rfl⟩
  · exact ⟨1,2,by decide,by decide,by decide,
      Equiv.ofBijective (![0,3,1,2] : Satellite → Satellite) (by decide),rfl,rfl,rfl,rfl⟩
  · exact ⟨0,3,by decide,by decide,by decide,
      Equiv.ofBijective (![1,2,0,3] : Satellite → Satellite) (by decide),rfl,rfl,rfl,rfl⟩
  · exact ⟨0,2,by decide,by decide,by decide,
      Equiv.ofBijective (![1,3,0,2] : Satellite → Satellite) (by decide),rfl,rfl,rfl,rfl⟩
  · exact ⟨0,1,by decide,by decide,by decide,
      Equiv.ofBijective (![2,3,0,1] : Satellite → Satellite) (by decide),rfl,rfl,rfl,rfl⟩

theorem orderedSlice_pair_capture
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n,orderedSliceRoot (p n) (eps n) (y n))
    (muLimit thetaLimit : MassRatio) (qLimit : SatelliteConfiguration)
    (hmt : Tendsto (fun n => (p n).val) atTop (𝓝 muLimit))
    (htt : Tendsto (fun n => sliceAngles (y n)) atTop (𝓝 thetaLimit))
    (hqt : Tendsto (fun n => sliceSatellites (y n)) atTop (𝓝 qLimit))
    (a b : Satellite) (hab : a<b) (center : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b center) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint p eps y) := by
  obtain ⟨u,w,huw,hu,hw,e,he0,he1,he2,he3⟩ := pairExterior_layout a b hab
  have hh := normalized_complete_pair_ordered_capture eps (fun n => (p n).val)
    (fun n => slicePhysicalConfiguration (eps n,(p n).val) (y n)) heps hepst
    (fun n => (p n).property)
    (fun n => (orderedSliceRoot_physical (p n) (eps n) (heps n) (y n) (hy n)).1)
    (fun n => (hy n).2.2.1) (fun n => sliceRadii (y n)) (fun n => sliceAngles (y n))
    (fun n => (hy n).1.2.1) (fun n => slicePhysicalConfiguration_satellitesRelative _ _)
    (fun _ => rfl) (fun n => (hy n).2.1) muLimit hmt qLimit
    (by simpa only [slicePhysicalConfiguration_satellitesRelative] using hqt) a b hab center hpair
    thetaLimit htt u w huw hu hw e he0 he1 he2 he3
  simpa only [polarSlice_reconstruct] using hh

end DominantFiveBody
