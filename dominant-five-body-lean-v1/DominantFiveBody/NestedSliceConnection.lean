import DominantFiveBody.PolarGaugeTransport
import DominantFiveBody.NestedSequenceCapture

/-! # Actual nested branches in the ordered first-angle slice

The current positive nested masses are retained at epsilon zero. This
module supplies one genuine capture type, rather than assuming the
global four-type connection property.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

def nestedOrderedSlice (sigma : HullOrder) (t eta alpha : ℝ)
    (y : NestedChartVariables) : SliceCoordinates :=
  orderedPolarSlice sigma (nestedChartRadii t eta alpha y) (nestedChartAngles t eta alpha y)

theorem nestedOrderedSlice_contDiff (n : ℕ∞ω) (sigma : HullOrder) (t eta alpha : ℝ) :
    ContDiff ℝ n (nestedOrderedSlice sigma t eta alpha) := by
  have hgraph : ContDiff ℝ n (fun y : NestedChartVariables => (nestedParameter 0 t eta alpha,y)) :=
    contDiff_const.prodMk contDiff_id
  have hr : ContDiff ℝ n (nestedChartRadii t eta alpha) := by
    apply contDiff_pi.mpr
    intro i
    exact (nestedChartRadii_joint_contDiff n i).comp hgraph
  have ha : ContDiff ℝ n (nestedChartAngles t eta alpha) := by
    apply contDiff_pi.mpr
    intro i
    exact (nestedChartAngles_joint_contDiff n i).comp hgraph
  exact (orderedPolarSlice_contDiff n sigma).comp (hr.prodMk ha)

theorem NestedCapturedBranches.orderedSlice_endpoint {eps t eta alpha : ℕ → ℝ}
    {y : ℕ → NestedChartVariables} {tau omega : ℝ}
    (c : NestedCapturedBranches eps t eta alpha y tau omega)
    (hm : ∀ n,PositiveRatio (nestedChartMass (t n) (eta n) (alpha n))) (n : ℕ) :
    nestedOrderedSlice (nestedBoundaryHullOrder tau omega) (t (c.tailStart+n))
      (eta (c.tailStart+n)) (alpha (c.tailStart+n)) (c.branch n 0)=
      coorbitalBaseSlice (nestedChartMass (t (c.tailStart+n)) (eta (c.tailStart+n))
        (alpha (c.tailStart+n)) ∘ hullSatellitePermutation (nestedBoundaryHullOrder tau omega)) := by
  have hzero : (0 : ℝ)∈Ico 0 c.radius := ⟨le_rfl,c.radius_pos⟩
  obtain ⟨hu,_,_,_,_,hco⟩ := c.endpoints n
  unfold nestedOrderedSlice
  rw [funext hu]
  apply orderedPolarSlice_endpoint _ _ _ (hm (c.tailStart+n))
    (c.domain n 0 hzero).2.2 _ hco
  simpa [nestedChartPoints,nestedParameter,funext hu] using c.convex n 0 hzero

/-- Genuine nested chart roots and their physical Hessians instantiate
the actual Section 7 capture structure in the seven-dimensional slice. -/
theorem NestedCapturedBranches.toOrderedSliceCapturedBranches {eps t eta alpha : ℕ → ℝ}
    {y : ℕ → NestedChartVariables} {tau omega : ℝ}
    (c : NestedCapturedBranches eps t eta alpha y tau omega)
    (ht : ∀ n,0<t n) (heta : ∀ n,0<eta n)
    (hm : ∀ n,PositiveRatio (nestedChartMass (t n) (eta n) (alpha n))) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n : ℕ =>
        (⟨nestedChartMass (t n) (eta n) (alpha n) ∘
          hullSatellitePermutation (nestedBoundaryHullOrder tau omega),
          positiveRatio_satellitePermutation _ (hm n) _⟩ : PositiveMassRatio)) eps
      (fun n => nestedOrderedSlice (nestedBoundaryHullOrder tau omega) (t n) (eta n) (alpha n) (y n))) := by
  let sigma := nestedBoundaryHullOrder tau omega
  let branch (n : ℕ) (s : ℝ) :=
    nestedOrderedSlice sigma (t (c.tailStart+n)) (eta (c.tailStart+n))
      (alpha (c.tailStart+n)) (c.branch n s)
  have hphysical (n : ℕ) (s : ℝ) (hs : 0<s) (hsrad : s<c.radius) :=
    nestedContinuationRoot_physical
      (nestedParameter s (t (c.tailStart+n)) (eta (c.tailStart+n)) (alpha (c.tailStart+n)))
      (c.branch n s) (c.domain n s ⟨hs.le,hsrad⟩) hs (ht (c.tailStart+n))
      (heta (c.tailStart+n)) (hm (c.tailStart+n))
      (c.regular_roots n s ⟨hs.le,hsrad⟩).2 (c.invertible n s ⟨hs.le,hsrad⟩)
  refine ⟨{
    subseq := fun n => c.tailStart+n
    subseq_strictMono := by intro i j hij; change c.tailStart+i<c.tailStart+j; omega
    radius := c.radius
    radius_pos := c.radius_pos
    parameters_lt_radius := c.parameters_lt_radius
    branch := branch
    continuous := ?_
    hits := ?_
    roots := ?_
    nondegenerate_at := ?_
    endpoints := ?_ }⟩
  · intro n
    exact (nestedOrderedSlice_contDiff 0 sigma _ _ _).continuous.comp_continuousOn (c.continuous n)
  · intro n
    change nestedOrderedSlice sigma _ _ _ (c.branch n (eps (c.tailStart+n)))=_
    rw [c.hits n]
  · intro n s hs hsrad
    exact orderedPolarSlice_root_of_normalized s _ sigma _ _ (hm (c.tailStart+n)) hs
      (c.domain n s ⟨hs.le,hsrad⟩).2.1 (c.domain n s ⟨hs.le,hsrad⟩).2.2
      (c.convex n s ⟨hs.le,hsrad⟩) (hphysical n s hs hsrad).1
  · intro n s hs hsrad
    exact orderedPolarSlice_nondegenerate_of_normalized s _ sigma _ _ (hm (c.tailStart+n))
      (c.domain n s ⟨hs.le,hsrad⟩).2.1 (hphysical n s hs hsrad).1 (hphysical n s hs hsrad).2
  · intro n
    exact c.orderedSlice_endpoint hm n

end DominantFiveBody
