import DominantFiveBody.PairSliceConnection
import DominantFiveBody.PairActualCapture
import DominantFiveBody.NoCollisionSliceConnection

/-! # Complete-pair capture with the exact original masses and coordinates

The chart permutation is forced to undo by strict angular sorting. No
permutation is added to oriented similarity, and the current mass vector
at the endpoint is exactly the original current mass vector.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem PairCapturedBranches.toOriginalOrderedSlice
    (mu : ℕ → MassRatio) (eps : ℕ → ℝ) (r theta : ℕ → Satellite → ℝ)
    (e : Equiv.Perm Satellite) (anchor : Satellite) (heanchor : e 2=anchor)
    (psi : ℝ) (keepD : Bool)
    (c : PairCapturedBranches eps (fun n => pairPhysicalScale (mu n ∘ e))
      (fun n => pairExteriorFraction (mu n ∘ e)) (fun n => pairPhysicalFraction (mu n ∘ e))
      (fun n => pairVariablesFromPolar (pairPhysicalScale (mu n ∘ e))
        (pairPhysicalFraction (mu n ∘ e)) (r n ∘ e) (fun i => theta n (e i)-theta n anchor)) psi keepD)
    (hm : ∀ n,PositiveRatio (mu n)) (hr : ∀ n i,0<r n i)
    (hzero : ∀ n,theta n 0=0) (horder : ∀ n,OrderedSemicircle (theta n)) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) eps (fun n => polarSlice (r n) (theta n))) := by
  let sigma := pairBoundaryHullOrder psi
  have hmE (n : ℕ) := positiveRatio_satellitePermutation _ (hm n) e
  have ht (n : ℕ) := (pairPhysicalParameters_bounds (mu n ∘ e) (hmE n)).1
  have hfixed (n : ℕ) : (fun i => theta n (e i)-theta n anchor) 2=0 := by
    change theta n (e 2)-theta n anchor=0
    rw [heanchor,sub_self]
  have hradii (n : ℕ) := pairVariablesFromPolar_radii
    (pairPhysicalScale (mu n ∘ e)) (pairPhysicalFraction (mu n ∘ e)) (r n ∘ e)
    (fun i => theta n (e i)-theta n anchor) (ht n).ne'
  have hangles (n : ℕ) := pairVariablesFromPolar_angles
    (pairPhysicalScale (mu n ∘ e)) (pairPhysicalFraction (mu n ∘ e)) (r n ∘ e)
    (fun i => theta n (e i)-theta n anchor) (ht n).ne' (hfixed n)
  have hsafe := c.safe 0 (eps (c.tailStart+0))
    ⟨(c.parameters_pos 0).le,c.parameters_lt_radius 0⟩
  have hwidth := hsafe.2.1
  change ∀ i j,|pairChartAngles (pairPhysicalScale (mu (c.tailStart+0) ∘ e))
      (pairPhysicalFraction (mu (c.tailStart+0) ∘ e)) (c.branch 0 (eps (c.tailStart+0))) j-
    pairChartAngles (pairPhysicalScale (mu (c.tailStart+0) ∘ e))
      (pairPhysicalFraction (mu (c.tailStart+0) ∘ e)) (c.branch 0 (eps (c.tailStart+0))) i|<Real.pi at hwidth
  rw [c.hits,hangles] at hwidth
  have hconv := hsafe.2.2 (ht (c.tailStart+0))
  change StrictConvexInOrder sigma (liftRelative (pairChartPoints
    (pairPhysicalScale (mu (c.tailStart+0) ∘ e)) (pairPhysicalFraction (mu (c.tailStart+0) ∘ e))
    (c.branch 0 (eps (c.tailStart+0))))) at hconv
  rw [c.hits,pairVariablesFromPolar_points _ _ _ _ (ht _).ne' (hfixed _)] at hconv
  have hsort := polarStrictConvex_orderedSemicircle sigma (r (c.tailStart+0) ∘ e)
    (fun i => theta (c.tailStart+0) (e i)-theta (c.tailStart+0) anchor)
    (fun i => hr (c.tailStart+0) (e i)) hwidth hconv
  have he := orderedSemicircle_sorting_inverse (theta (c.tailStart+0)) (horder (c.tailStart+0))
    e (hullSatellitePermutation sigma) (theta (c.tailStart+0) anchor) hsort
  have hmass (n : ℕ) := pairPhysicalParameters_mass (mu n ∘ e) (hmE n)
  have hcapture := c.toOrderedSliceCapturedBranches ht (fun n => by rw [hmass n]; exact hmE n)
  have hmcomp :
      (fun n => (⟨pairChartMass (pairPhysicalScale (mu n ∘ e)) (pairExteriorFraction (mu n ∘ e))
        (pairPhysicalFraction (mu n ∘ e)) ∘ hullSatellitePermutation sigma,
        positiveRatio_satellitePermutation _ (by rw [hmass n]; exact hmE n) _⟩ : PositiveMassRatio))=
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) := by
    funext n
    apply Subtype.ext
    change pairChartMass _ _ _ ∘ hullSatellitePermutation sigma=mu n
    rw [hmass n,he,Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id]
  rw [hmcomp] at hcapture
  have hycomp :
      (fun n => pairOrderedSlice sigma (pairPhysicalScale (mu n ∘ e)) (pairPhysicalFraction (mu n ∘ e))
        (pairVariablesFromPolar (pairPhysicalScale (mu n ∘ e)) (pairPhysicalFraction (mu n ∘ e))
          (r n ∘ e) (fun i => theta n (e i)-theta n anchor)))=
      (fun n => polarSlice (r n) (theta n)) := by
    funext n
    unfold pairOrderedSlice
    rw [hradii n,hangles n]
    apply sliceCoordinates_ext
    · rw [orderedPolarSlice_radii,polarSlice_radii,he,Function.comp_assoc,
        Equiv.self_comp_symm,Function.comp_id]
    · rw [orderedPolarSlice_angles,polarSlice_angles _ _ (hzero n),he]
      funext i
      simp only [Equiv.apply_symm_apply,hzero n]
      ring
  rw [hycomp] at hcapture
  exact hcapture

theorem normalized_complete_pair_ordered_capture
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (x : ℕ → Configuration)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hm : ∀ n,PositiveRatio (mu n))
    (hx : ∀ n,NormalizedCentralConfiguration (masses (eps n) (mu n)) (x n))
    (hconv : ∀ n,StrictConvexInOrder ⟨Equiv.refl Label,rfl⟩ (x n))
    (r theta : ℕ → Satellite → ℝ) (hr : ∀ n i,0<r n i)
    (hpolar : ∀ n,satellitesRelative (x n)=polarSatellites (r n) (theta n))
    (hzero : ∀ n,theta n 0=0) (horder : ∀ n,OrderedSemicircle (theta n))
    (muLimit : MassRatio) (hmt : Tendsto mu atTop (𝓝 muLimit))
    (qLimit : SatelliteConfiguration)
    (hqt : Tendsto (fun n => satellitesRelative (x n)) atTop (𝓝 qLimit))
    (a b : Satellite) (hab : a<b) (center : Plane)
    (hpair : CompleteLimitingSatellitePair qLimit a b center)
    (theta0 : Satellite → ℝ) (hthetat : Tendsto theta atTop (𝓝 theta0))
    (u w : Satellite) (huw : u<w)
    (hu : u∈pairExteriorLabels a b) (hw : w∈pairExteriorLabels a b)
    (e : Equiv.Perm Satellite) (he0 : e 0=a) (he1 : e 1=b) (he2 : e 2=u) (he3 : e 3=w) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) eps (fun n => polarSlice (r n) (theta n))) := by
  obtain ⟨keepD,⟨c⟩⟩ := normalized_complete_pair_actual_capture eps mu x heps hepst hm hx hconv
    r theta hr hpolar horder muLimit hmt qLimit hqt a b hab center hpair theta0 hthetat
    u w huw hu hw e he0 he1 he2 he3
  exact c.toOriginalOrderedSlice mu eps r theta e u he2 _ keepD hm hr hzero horder

end DominantFiveBody
