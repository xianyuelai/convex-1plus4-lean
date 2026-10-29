import DominantFiveBody.TripleSliceConnection
import DominantFiveBody.NoCollisionSliceConnection

/-! Exact original labels and current masses after triple-chart capture. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 600000

theorem TripleCapturedBranches.toOriginalOrderedSlice
    (mu : ℕ → MassRatio) (eps : ℕ → ℝ) (r theta : ℕ → Satellite → ℝ)
    (e : Equiv.Perm Satellite) (tau : ℝ)
    (hm : ∀ n,PositiveRatio (mu n)) (hzero : ∀ n,theta n 0=0)
    (horder : ∀ n,OrderedSemicircle (theta n))
    (c : TripleCapturedBranches eps (fun n => triplePhysicalScale (mu n ∘ e))
      (fun n => triplePhysicalWeights (mu n ∘ e))
      (fun n => tripleVariablesFromPolar (triplePhysicalScale (mu n ∘ e))
        (triplePhysicalWeights (mu n ∘ e)) (r n ∘ e) (fun i => theta n (e i)-theta n (e 3))) tau) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) eps (fun n => polarSlice (r n) (theta n))) := by
  let t := fun n => triplePhysicalScale (mu n ∘ e)
  let alpha := fun n => triplePhysicalWeights (mu n ∘ e)
  let v := fun n => tripleVariablesFromPolar (t n) (alpha n) (r n ∘ e)
    (fun i => theta n (e i)-theta n (e 3))
  let sigma := tripleBoundaryHullOrder tau
  have hme (n : ℕ) := positiveRatio_satellitePermutation _ (hm n) e
  have ht (n : ℕ) : 0<t n := (triplePhysicalParameters_bounds _ (hme n)).1
  have ha (n : ℕ) : ∑ i,alpha n i=1 := triplePhysicalWeights_sum _ (hme n)
  have hmass (n : ℕ) : tripleChartMass (t n) (alpha n)=mu n ∘ e := triplePhysicalParameters_mass _ (hme n)
  have hrad (n : ℕ) : tripleChartRadii (t n) (alpha n) (v n)=r n ∘ e :=
    tripleVariablesFromPolar_radii _ _ _ _ (ht n).ne' (ha n)
  have hang (n : ℕ) : tripleChartAngles (t n) (alpha n) (v n)=
      (fun i => theta n (e i)-theta n (e 3)) :=
    tripleVariablesFromPolar_angles _ _ _ _ (ht n).ne' (ha n) (sub_self _)
  let N := c.tailStart+0
  have hn : eps N∈Ico 0 c.radius := ⟨(c.parameters_pos 0).le,c.parameters_lt_radius 0⟩
  have hsafe := c.safe 0 (eps N) hn
  have hconv := c.convex 0 (eps N) hn
  rw [c.hits] at hsafe hconv
  have hrr : ∀ i,0<tripleChartRadii (t N) (alpha N) (v N) i := hsafe.1
  have hww : ∀ i j,|tripleChartAngles (t N) (alpha N) (v N) j-
      tripleChartAngles (t N) (alpha N) (v N) i|<Real.pi := hsafe.2
  have hs := polarStrictConvex_orderedSemicircle sigma _ _ hrr hww hconv
  rw [hang N] at hs
  have he : hullSatellitePermutation sigma=e.symm :=
    orderedSemicircle_sorting_inverse _ (horder N) e _ (theta N (e 3)) hs
  have hcapture := c.toOrderedSliceCapturedBranches ht ha (fun n => (hmass n).symm ▸ hme n)
  have hmcomp : (fun n => (⟨tripleChartMass (t n) (alpha n) ∘ hullSatellitePermutation sigma,
      positiveRatio_satellitePermutation _ ((hmass n).symm ▸ hme n) _⟩ : PositiveMassRatio))=
      (fun n => (⟨mu n,hm n⟩ : PositiveMassRatio)) := by
    funext n
    apply Subtype.ext
    change tripleChartMass (t n) (alpha n) ∘ hullSatellitePermutation sigma=mu n
    rw [hmass,he,Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id]
  have hycomp : (fun n => tripleOrderedSlice sigma (t n) (alpha n) (v n))=
      (fun n => polarSlice (r n) (theta n)) := by
    funext n
    unfold tripleOrderedSlice
    rw [hrad,hang]
    exact orderedPolarSlice_reindex_undo sigma e (r n) (theta n) (theta n (e 3)) he (hzero n)
  change Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
    (fun n => (⟨tripleChartMass (t n) (alpha n) ∘ hullSatellitePermutation sigma,
      positiveRatio_satellitePermutation _ ((hmass n).symm ▸ hme n) _⟩ : PositiveMassRatio)) eps
    (fun n => tripleOrderedSlice sigma (t n) (alpha n) (v n))) at hcapture
  rw [hmcomp,hycomp] at hcapture
  exact hcapture

end DominantFiveBody
