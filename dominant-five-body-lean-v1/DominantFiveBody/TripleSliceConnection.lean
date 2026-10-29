import DominantFiveBody.PolarGaugeTransport
import DominantFiveBody.TripleSequenceCapture

/-! # Genuine regular-triple branches in the ordered first-angle slice -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

def tripleOrderedSlice (sigma : HullOrder) (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) : SliceCoordinates :=
  orderedPolarSlice sigma (tripleChartRadii t alpha y) (tripleChartAngles t alpha y)

theorem tripleOrderedSlice_contDiff (n : ℕ∞ω) (sigma : HullOrder) (t : ℝ) (alpha : TripleVector) :
    ContDiff ℝ n (tripleOrderedSlice sigma t alpha) := by
  have hgraph : ContDiff ℝ n (fun y : TripleChartVariables => (tripleParameter 0 t alpha,y)) :=
    contDiff_const.prodMk contDiff_id
  have hr : ContDiff ℝ n (tripleChartRadii t alpha) := by
    apply contDiff_pi.mpr
    intro i
    simpa only [Function.comp_def,tripleParameter_alpha,tripleParameter_scale] using
      (tripleChartRadii_joint_contDiff n i).comp hgraph
  have ha : ContDiff ℝ n (tripleChartAngles t alpha) := by
    apply contDiff_pi.mpr
    intro i
    simpa only [Function.comp_def,tripleParameter_alpha,tripleParameter_scale] using
      (tripleChartAngles_joint_contDiff n i).comp hgraph
  exact (orderedPolarSlice_contDiff n sigma).comp (hr.prodMk ha)

theorem TripleCapturedBranches.orderedSlice_endpoint {eps t : ℕ → ℝ}
    {alpha : ℕ → TripleVector} {y : ℕ → TripleChartVariables} {tau : ℝ}
    (c : TripleCapturedBranches eps t alpha y tau)
    (hm : ∀ n,PositiveRatio (tripleChartMass (t n) (alpha n))) (n : ℕ) :
    tripleOrderedSlice (tripleBoundaryHullOrder tau) (t (c.tailStart+n))
      (alpha (c.tailStart+n)) (c.branch n 0)=
      coorbitalBaseSlice (tripleChartMass (t (c.tailStart+n)) (alpha (c.tailStart+n)) ∘
        hullSatellitePermutation (tripleBoundaryHullOrder tau)) := by
  have hz : (0 : ℝ)∈Ico 0 c.radius := ⟨le_rfl,c.radius_pos⟩
  obtain ⟨hu,_,_,hco⟩ := c.endpoints n
  unfold tripleOrderedSlice
  rw [funext hu]
  apply orderedPolarSlice_endpoint _ _ _ (hm (c.tailStart+n)) _ _ hco
  · simpa only [tripleParameter_alpha,tripleParameter_scale] using (c.safe n 0 hz).2
  · simpa only [tripleChartPoints,funext hu] using c.convex n 0 hz

theorem TripleCapturedBranches.toOrderedSliceCapturedBranches {eps t : ℕ → ℝ}
    {alpha : ℕ → TripleVector} {y : ℕ → TripleChartVariables} {tau : ℝ}
    (c : TripleCapturedBranches eps t alpha y tau)
    (ht : ∀ n,0<t n) (ha : ∀ n,∑ i,alpha n i=1)
    (hm : ∀ n,PositiveRatio (tripleChartMass (t n) (alpha n))) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n : ℕ => (⟨tripleChartMass (t n) (alpha n) ∘
        hullSatellitePermutation (tripleBoundaryHullOrder tau),
        positiveRatio_satellitePermutation _ (hm n) _⟩ : PositiveMassRatio)) eps
      (fun n => tripleOrderedSlice (tripleBoundaryHullOrder tau) (t n) (alpha n) (y n))) := by
  let sigma := tripleBoundaryHullOrder tau
  have hr (n : ℕ) (s : ℝ) (hs : s∈Ico 0 c.radius) :
      ∀ i,0<tripleChartRadii (t (c.tailStart+n)) (alpha (c.tailStart+n)) (c.branch n s) i := by
    simpa only [tripleParameter_alpha,tripleParameter_scale] using (c.safe n s hs).1
  have hw (n : ℕ) (s : ℝ) (hs : s∈Ico 0 c.radius) :
      ∀ i j,|tripleChartAngles (t (c.tailStart+n)) (alpha (c.tailStart+n)) (c.branch n s) j-
        tripleChartAngles (t (c.tailStart+n)) (alpha (c.tailStart+n)) (c.branch n s) i|<Real.pi := by
    simpa only [tripleParameter_alpha,tripleParameter_scale] using (c.safe n s hs).2
  have hx (n : ℕ) (s : ℝ) (hs : 0<s) (hsrad : s<c.radius) :=
    (tripleChartExtendedRows_zero_iff_normalized s (t (c.tailStart+n)) (alpha (c.tailStart+n))
      (c.branch n s) hs (ht (c.tailStart+n)) (ha (c.tailStart+n)) (hm (c.tailStart+n))
      (c.regular_roots n s ⟨hs.le,hsrad⟩).1 (hr n s ⟨hs.le,hsrad⟩)).mp
      (c.regular_roots n s ⟨hs.le,hsrad⟩).2
  refine ⟨{
    subseq := fun n => c.tailStart+n
    subseq_strictMono := by intro i j hij; change c.tailStart+i<c.tailStart+j; omega
    radius := c.radius
    radius_pos := c.radius_pos
    parameters_lt_radius := c.parameters_lt_radius
    branch := fun n s => tripleOrderedSlice sigma (t (c.tailStart+n)) (alpha (c.tailStart+n)) (c.branch n s)
    continuous := ?_
    hits := ?_
    roots := ?_
    nondegenerate_at := ?_
    endpoints := ?_ }⟩
  · intro n
    exact (tripleOrderedSlice_contDiff 0 sigma _ _).continuous.comp_continuousOn (c.continuous n)
  · intro n
    rw [c.hits]
  · intro n s hs hsrad
    exact orderedPolarSlice_root_of_normalized s _ sigma _ _ (hm (c.tailStart+n)) hs
      (hr n s ⟨hs.le,hsrad⟩) (hw n s ⟨hs.le,hsrad⟩)
      (c.convex n s ⟨hs.le,hsrad⟩) (hx n s hs hsrad)
  · intro n s hs hsrad
    have hn := (tripleChartJacobian_isInvertible_iff_shape s (t (c.tailStart+n))
      (alpha (c.tailStart+n)) (c.branch n s) hs (ht (c.tailStart+n)) (ha (c.tailStart+n))
      (hm (c.tailStart+n)) (c.regular_roots n s ⟨hs.le,hsrad⟩).1 (hr n s ⟨hs.le,hsrad⟩)
      (c.regular_roots n s ⟨hs.le,hsrad⟩).2).mp (c.invertible n s ⟨hs.le,hsrad⟩)
    exact orderedPolarSlice_nondegenerate_of_normalized s _ sigma _ _ (hm (c.tailStart+n))
      (hr n s ⟨hs.le,hsrad⟩) (hx n s hs hsrad) hn
  · intro n
    exact c.orderedSlice_endpoint hm n

end DominantFiveBody
