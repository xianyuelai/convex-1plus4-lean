import DominantFiveBody.NoCollisionActualCapture
import DominantFiveBody.PolarGaugeTransport

/-! The actual separated chart supplies the Section 7 connection data
in a single ordered first-angle coordinate space. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 600000

@[simp] theorem hullSatellitePermutation_satelliteHullOrder (e : Equiv.Perm Satellite) :
    hullSatellitePermutation (satelliteHullOrder e)=e := by
  apply Equiv.ext
  intro i
  apply Fin.succ_injective
  rw [hullSatellitePermutation_succ]
  rfl

theorem angle_width_of_ordered_permutation (theta : Satellite → ℝ) (e : Equiv.Perm Satellite)
    (h : OrderedSemicircle (theta ∘ e)) : ∀ i j,|theta j-theta i|<Real.pi := by
  intro i j
  by_cases hij : i=j
  · subst j
    simpa only [sub_self,abs_zero] using Real.pi_pos
  · have hh := separatedSemicircle_of_ordered _ h (e.symm i) (e.symm j) (e.symm.injective.ne hij)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hh.2

def noCollisionOrderedSlice (e : Equiv.Perm Satellite) (y : SliceCoordinates) : SliceCoordinates :=
  orderedPolarSlice (satelliteHullOrder e) (sliceRadii y) (sliceAngles y)

theorem noCollisionOrderedSlice_contDiff (n : ℕ∞ω) (e : Equiv.Perm Satellite) :
    ContDiff ℝ n (noCollisionOrderedSlice e) := by
  change ContDiff ℝ n (fun y => orderedPolarSlice (satelliteHullOrder e) (sliceRadii y) (sliceAngles y))
  have hh := (orderedPolarSlice_contDiff n (satelliteHullOrder e)).comp
    ((contDiff_pi.mpr (sliceRadii_contDiff n)).prodMk (contDiff_pi.mpr (sliceAngles_contDiff n)))
  simpa only [Function.comp_def] using hh

theorem NoCollisionCapturedBranches.toOrderedSliceCapturedBranches
    (nu : ℕ → MassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (c : NoCollisionCapturedBranches nu eps y) (hm : ∀ n,PositiveRatio (nu n)) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨nu n ∘ c.order,positiveRatio_satellitePermutation _ (hm n) c.order⟩ : PositiveMassRatio))
      eps (fun n => noCollisionOrderedSlice c.order (y n))) := by
  let sigma := satelliteHullOrder c.order
  have hwidth (n : ℕ) (s : ℝ) (hs : s∈Ico 0 c.radius) :
      ∀ i j,|sliceAngles (c.branch n s) j-sliceAngles (c.branch n s) i|<Real.pi :=
    angle_width_of_ordered_permutation _ c.order (c.ordered_angles n s hs)
  have hx (n : ℕ) (s : ℝ) (hs : 0<s) (hsr : s<c.radius) :
      NormalizedCentralConfiguration (masses s (nu (c.tailStart+n)))
        (centeredFromRelative s (nu (c.tailStart+n)) (polarSatellites (sliceRadii (c.branch n s)) (sliceAngles (c.branch n s)))) := by
    have hh := normalizedCC_of_reducedResidual_zero (s,nu (c.tailStart+n)) (c.branch n s)
      (c.regular_roots n s ⟨hs.le,hsr⟩).1 hs (hm _) (c.regular_roots n s ⟨hs.le,hsr⟩).2
    simpa only [slicePhysicalConfiguration,relativeCenteredContinuous_apply,sliceSatellites] using hh
  have hc (n : ℕ) (s : ℝ) (hs : 0<s) (hsr : s<c.radius) :
      StrictConvexInOrder sigma (liftRelative (polarSatellites (sliceRadii (c.branch n s)) (sliceAngles (c.branch n s)))) := by
    apply (strictConvex_centeredFromRelative_iff sigma s (nu (c.tailStart+n)) _).mp
    simpa only [slicePhysicalConfiguration,relativeCenteredContinuous_apply,sliceSatellites]
      using (c.physical_roots n s hs hsr).2
  refine ⟨{
    subseq := fun n => c.tailStart+n
    subseq_strictMono := c.tail_strictMono
    radius := c.radius
    radius_pos := c.radius_pos
    parameters_lt_radius := c.parameters_lt_radius
    branch := fun n s => noCollisionOrderedSlice c.order (c.branch n s)
    continuous := ?_
    hits := ?_
    roots := ?_
    nondegenerate_at := ?_
    endpoints := ?_ }⟩
  · intro n
    exact (noCollisionOrderedSlice_contDiff 0 c.order).continuous.comp_continuousOn (c.continuous n)
  · intro n
    rw [c.hits]
  · intro n s hs hsr
    have hh := orderedPolarSlice_root_of_normalized s (nu (c.tailStart+n)) sigma
      (sliceRadii (c.branch n s)) (sliceAngles (c.branch n s)) (hm _) hs
      (c.regular_roots n s ⟨hs.le,hsr⟩).1.2.1 (hwidth n s ⟨hs.le,hsr⟩)
      (hc n s hs hsr) (hx n s hs hsr)
    simpa only [sigma,hullSatellitePermutation_satelliteHullOrder,noCollisionOrderedSlice] using hh
  · intro n s hs hsr
    have hn := c.nondegenerate n s hs hsr
    simp only [slicePhysicalConfiguration,relativeCenteredContinuous_apply,sliceSatellites] at hn
    have hh := orderedPolarSlice_nondegenerate_of_normalized s (nu (c.tailStart+n)) sigma
      (sliceRadii (c.branch n s)) (sliceAngles (c.branch n s)) (hm _)
      (c.regular_roots n s ⟨hs.le,hsr⟩).1.2.1 (hx n s hs hsr) hn
    simpa only [sigma,hullSatellitePermutation_satelliteHullOrder,noCollisionOrderedSlice] using hh
  · intro n
    have hz : (0 : ℝ)∈Ico 0 c.radius := ⟨le_rfl,c.radius_pos⟩
    have hu : sliceRadii (c.branch n 0)=(fun _ => 1) := funext (c.endpoints n).1
    have hh := orderedPolarSlice_endpoint (nu (c.tailStart+n)) sigma (sliceAngles (c.branch n 0))
      (hm _) (hwidth n 0 hz)
      (unit_polar_strictConvex_permutation _ c.order (c.ordered_angles n 0 hz)) (c.endpoints n).2.2.1
    simpa only [sigma,hullSatellitePermutation_satelliteHullOrder,noCollisionOrderedSlice,hu,
      orderedSliceEndpoint] using hh

theorem orderedSemicircle_sorting_inverse (theta : Satellite → ℝ)
    (htheta : OrderedSemicircle theta) (e f : Equiv.Perm Satellite) (a : ℝ)
    (hsort : OrderedSemicircle ((fun i => theta (e i)-a) ∘ f)) : f=e.symm := by
  have ht : StrictMono theta := fun i j hij => sub_pos.mp (htheta i j hij).1
  have hf : StrictMono (fun i => e (f i)) := by
    intro i j hij
    apply ht.lt_iff_lt.mp
    have hh := (hsort i j hij).1
    change 0<(theta (e (f j))-a)-(theta (e (f i))-a) at hh
    linarith
  apply Equiv.ext
  intro i
  apply e.injective
  rw [Equiv.apply_symm_apply]
  exact hf.apply_eq

theorem noCollisionOrderedSlice_undo (e : Equiv.Perm Satellite) (r theta : Satellite → ℝ)
    (hzero : theta 0=0) :
    noCollisionOrderedSlice e.symm (polarSlice (r ∘ e) (fun i => theta (e i)-theta (e 0)))=
      polarSlice r theta := by
  apply sliceCoordinates_ext
  · simp only [noCollisionOrderedSlice,orderedPolarSlice_radii,polarSlice_radii,
      hullSatellitePermutation_satelliteHullOrder,Function.comp_assoc,
      Equiv.self_comp_symm,Function.comp_id]
  · have hz : (fun i => theta (e i)-theta (e 0)) 0=0 := sub_self _
    simp only [noCollisionOrderedSlice,orderedPolarSlice_angles,
      hullSatellitePermutation_satelliteHullOrder,polarSlice_angles (r ∘ e) (fun i => theta (e i)-theta (e 0)) hz,
      polarSlice_angles r theta hzero,Equiv.apply_symm_apply,hzero,zero_sub]
    funext i
    ring

theorem orderedPolarSlice_reindex_undo (sigma : HullOrder) (e : Equiv.Perm Satellite)
    (r theta : Satellite → ℝ) (a : ℝ) (he : hullSatellitePermutation sigma=e.symm)
    (hzero : theta 0=0) :
    orderedPolarSlice sigma (r ∘ e) (fun i => theta (e i)-a)=polarSlice r theta := by
  apply sliceCoordinates_ext
  · simp only [orderedPolarSlice_radii,he,polarSlice_radii,Function.comp_assoc,
      Equiv.self_comp_symm,Function.comp_id]
  · simp only [orderedPolarSlice_angles,he,Equiv.apply_symm_apply,polarSlice_angles r theta hzero,hzero,zero_sub]
    funext i
    ring

/-- Capturing after choosing a surviving positive mass does not change
the current mass vector or the original ordered coordinates. -/
theorem NoCollisionCapturedBranches.toOriginalOrderedSlice
    (mu : ℕ → MassRatio) (eps : ℕ → ℝ) (r theta : ℕ → Satellite → ℝ)
    (e : Equiv.Perm Satellite)
    (c : NoCollisionCapturedBranches (fun n => mu n ∘ e) eps
      (fun n => polarSlice (r n ∘ e) (fun i => theta n (e i)-theta n (e 0))))
    (hm : ∀ n,PositiveRatio (mu n)) (hzero : ∀ n,theta n 0=0)
    (horder : ∀ n,OrderedSemicircle (theta n)) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) eps (fun n => polarSlice (r n) (theta n))) := by
  have hs := c.ordered_angles 0 (eps (c.tailStart+0))
    ⟨(c.parameters_pos 0).le,c.parameters_lt_radius 0⟩
  rw [c.hits] at hs
  rw [polarSlice_angles (r (c.tailStart+0) ∘ e)
    (fun i => theta (c.tailStart+0) (e i)-theta (c.tailStart+0) (e 0)) (sub_self _)] at hs
  have he := orderedSemicircle_sorting_inverse (theta (c.tailStart+0)) (horder (c.tailStart+0))
    e c.order (theta (c.tailStart+0) (e 0)) hs
  have hcapture := c.toOrderedSliceCapturedBranches (fun n => mu n ∘ e) eps _
    (fun n => positiveRatio_satellitePermutation _ (hm n) e)
  have hmcomp : (fun n => (⟨(mu n ∘ e) ∘ c.order,
      positiveRatio_satellitePermutation _ (positiveRatio_satellitePermutation _ (hm n) e) c.order⟩ : PositiveMassRatio))=
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) := by
    funext n
    apply Subtype.ext
    change (mu n ∘ e) ∘ c.order=mu n
    rw [he,Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id]
  rw [hmcomp] at hcapture
  have hycomp : (fun n => noCollisionOrderedSlice c.order
      (polarSlice (r n ∘ e) (fun i => theta n (e i)-theta n (e 0))))=
      (fun n => polarSlice (r n) (theta n)) := by
    funext n
    rw [he,noCollisionOrderedSlice_undo e (r n) (theta n) (hzero n)]
  rw [hycomp] at hcapture
  exact hcapture

theorem normalized_noCollision_ordered_capture
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (hzero : ∀ n,theta n 0=0) (horder : ∀ n,OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (thetaLimit : Satellite → ℝ) (htt : Tendsto theta atTop (𝓝 thetaLimit))
    (hsep : Function.Injective qLimit) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) eps (fun n => polarSlice (r n) (theta n))) := by
  obtain ⟨e,_,⟨c⟩⟩ := normalized_noCollision_actual_capture eps mu x heps hepst hm hx
    r theta hr hpolar horder muLimit hmt qLimit hqt thetaLimit htt hsep
  exact c.toOriginalOrderedSlice mu eps r theta e hm hzero horder

end DominantFiveBody
