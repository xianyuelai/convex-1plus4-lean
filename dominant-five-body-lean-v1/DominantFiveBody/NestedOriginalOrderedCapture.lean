import DominantFiveBody.NestedSliceConnection
import DominantFiveBody.NoCollisionSliceConnection

/-! # Nested capture with the exact original ordered coordinates -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem NestedCapturedBranches.toOriginalOrderedSlice
    (mu : ℕ → MassRatio) (eps : ℕ → ℝ) (r theta : ℕ → Satellite → ℝ)
    (e : Equiv.Perm Satellite) (anchor : Satellite) (heanchor : e 3=anchor)
    (tau omega : ℝ)
    (c : NestedCapturedBranches eps (fun n => nestedPhysicalScale (mu n ∘ e))
      (fun n => nestedPhysicalEta (mu n ∘ e)) (fun n => nestedPhysicalAlpha (mu n ∘ e))
      (fun n => nestedVariablesFromPolar (nestedPhysicalScale (mu n ∘ e))
        (nestedPhysicalEta (mu n ∘ e)) (nestedPhysicalAlpha (mu n ∘ e))
        (r n ∘ e) (fun i => theta n (e i)-theta n anchor)) tau omega)
    (hm : ∀ n,PositiveRatio (mu n)) (hr : ∀ n i,0<r n i)
    (hzero : ∀ n,theta n 0=0) (horder : ∀ n,OrderedSemicircle (theta n)) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) eps (fun n => polarSlice (r n) (theta n))) := by
  let sigma := nestedBoundaryHullOrder tau omega
  have hmE (n : ℕ) := positiveRatio_satellitePermutation _ (hm n) e
  have ht (n : ℕ) := (nestedPhysicalParameters_bounds (mu n ∘ e) (hmE n)).1
  have heta (n : ℕ) := (nestedPhysicalParameters_bounds (mu n ∘ e) (hmE n)).2.2.1
  have hfixed (n : ℕ) : (fun i => theta n (e i)-theta n anchor) 3=0 := by
    change theta n (e 3)-theta n anchor=0
    rw [heanchor,sub_self]
  have hradii (n : ℕ) := nestedVariablesFromPolar_radii
    (nestedPhysicalScale (mu n ∘ e)) (nestedPhysicalEta (mu n ∘ e)) (nestedPhysicalAlpha (mu n ∘ e))
    (r n ∘ e) (fun i => theta n (e i)-theta n anchor) (ht n).ne' (heta n).ne'
  have hangles (n : ℕ) := nestedVariablesFromPolar_angles
    (nestedPhysicalScale (mu n ∘ e)) (nestedPhysicalEta (mu n ∘ e)) (nestedPhysicalAlpha (mu n ∘ e))
    (r n ∘ e) (fun i => theta n (e i)-theta n anchor) (ht n).ne' (heta n).ne' (hfixed n)
  have hdomain := c.domain 0 (eps (c.tailStart+0))
    ⟨(c.parameters_pos 0).le,c.parameters_lt_radius 0⟩
  have hwidth := hdomain.2.2
  change ∀ i j,|nestedChartAngles (nestedPhysicalScale (mu (c.tailStart+0) ∘ e))
      (nestedPhysicalEta (mu (c.tailStart+0) ∘ e)) (nestedPhysicalAlpha (mu (c.tailStart+0) ∘ e))
      (c.branch 0 (eps (c.tailStart+0))) j-
    nestedChartAngles (nestedPhysicalScale (mu (c.tailStart+0) ∘ e))
      (nestedPhysicalEta (mu (c.tailStart+0) ∘ e)) (nestedPhysicalAlpha (mu (c.tailStart+0) ∘ e))
      (c.branch 0 (eps (c.tailStart+0))) i|<Real.pi at hwidth
  rw [c.hits,hangles] at hwidth
  have hconv := c.convex 0 (eps (c.tailStart+0))
    ⟨(c.parameters_pos 0).le,c.parameters_lt_radius 0⟩
  rw [c.hits,nestedVariablesFromPolar_points _ _ _ _ _ (ht _).ne' (heta _).ne' (hfixed _)] at hconv
  have hsort := polarStrictConvex_orderedSemicircle sigma (r (c.tailStart+0) ∘ e)
    (fun i => theta (c.tailStart+0) (e i)-theta (c.tailStart+0) anchor)
    (fun i => hr (c.tailStart+0) (e i)) hwidth hconv
  have he := orderedSemicircle_sorting_inverse (theta (c.tailStart+0)) (horder (c.tailStart+0))
    e (hullSatellitePermutation sigma) (theta (c.tailStart+0) anchor) hsort
  have hmass (n : ℕ) := nestedPhysicalParameters_mass (mu n ∘ e) (hmE n)
  have hcapture := c.toOrderedSliceCapturedBranches ht heta (fun n => by rw [hmass n]; exact hmE n)
  have hmcomp :
      (fun n => (⟨nestedChartMass (nestedPhysicalScale (mu n ∘ e)) (nestedPhysicalEta (mu n ∘ e))
        (nestedPhysicalAlpha (mu n ∘ e)) ∘ hullSatellitePermutation sigma,
        positiveRatio_satellitePermutation _ (by rw [hmass n]; exact hmE n) _⟩ : PositiveMassRatio))=
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) := by
    funext n
    apply Subtype.ext
    change nestedChartMass _ _ _ ∘ hullSatellitePermutation sigma=mu n
    rw [hmass n,he,Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id]
  rw [hmcomp] at hcapture
  have hycomp :
      (fun n => nestedOrderedSlice sigma (nestedPhysicalScale (mu n ∘ e)) (nestedPhysicalEta (mu n ∘ e))
        (nestedPhysicalAlpha (mu n ∘ e))
        (nestedVariablesFromPolar (nestedPhysicalScale (mu n ∘ e)) (nestedPhysicalEta (mu n ∘ e))
          (nestedPhysicalAlpha (mu n ∘ e)) (r n ∘ e) (fun i => theta n (e i)-theta n anchor)))=
      (fun n => polarSlice (r n) (theta n)) := by
    funext n
    unfold nestedOrderedSlice
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

end DominantFiveBody
