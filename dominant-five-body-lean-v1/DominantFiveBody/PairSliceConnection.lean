import DominantFiveBody.PolarGaugeTransport
import DominantFiveBody.PairSequenceCapture

/-! # Genuine complete-pair branches in the ordered first-angle slice -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem multiplier_eq_one_of_normalized (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) (lam : ℝ)
    (hlam : MultiplierEquation m x lam) : lam=1 := by
  have hcenter : massCenter m x=0 := by simp only [massCenter,hx.2.1,smul_zero]
  have hscale (i : Label) : (-lam) • x i=(-1 : ℝ) • x i := by
    simpa only [hcenter,sub_zero,neg_one_smul] using (hlam i).symm.trans (hx.2.2 i)
  have hdiff : (-lam) • (x 1-x 0)=(-1 : ℝ) • (x 1-x 0) := by
    simp only [smul_sub,hscale]
  have hneg := (smul_left_injective ℝ (sub_ne_zero.mpr (hx.1 1 0 (by decide)))) hdiff
  linarith

theorem shapeHessianNondegenerate_of_normalized_nondegenerate (m : MassVector)
    (x : Configuration) (hx : NormalizedCentralConfiguration m x)
    (hn : NondegenerateCentralConfiguration m x) : ShapeHessianNondegenerate m 1 x := by
  obtain ⟨_,lam,_,hlam,_,hshape⟩ := hn
  have h := multiplier_eq_one_of_normalized m x hx lam hlam
  simpa only [h] using hshape

def pairOrderedSlice (sigma : HullOrder) (t alpha : ℝ)
    (y : PairChartVariables) : SliceCoordinates :=
  orderedPolarSlice sigma (pairChartRadii t alpha y) (pairChartAngles t alpha y)

theorem pairOrderedSlice_contDiff (n : ℕ∞ω) (sigma : HullOrder) (t alpha : ℝ) :
    ContDiff ℝ n (pairOrderedSlice sigma t alpha) := by
  have hgraph : ContDiff ℝ n (fun y : PairChartVariables => ((![0,t,0,alpha] : PairChartParameters),y)) :=
    contDiff_const.prodMk contDiff_id
  have hr : ContDiff ℝ n (pairChartRadii t alpha) := by
    apply contDiff_pi.mpr
    intro i
    exact (pairChartRadii_joint_contDiff n i).comp hgraph
  have ha : ContDiff ℝ n (pairChartAngles t alpha) := by
    apply contDiff_pi.mpr
    intro i
    exact (pairChartAngles_joint_contDiff n i).comp hgraph
  exact (orderedPolarSlice_contDiff n sigma).comp (hr.prodMk ha)

theorem PairCapturedBranches.orderedSlice_endpoint {eps t p alpha : ℕ → ℝ}
    {y : ℕ → PairChartVariables} {psi : ℝ} {keepD : Bool}
    (c : PairCapturedBranches eps t p alpha y psi keepD)
    (ht : ∀ n,0<t n)
    (hm : ∀ n,PositiveRatio (pairChartMass (t n) (p n) (alpha n))) (n : ℕ) :
    pairOrderedSlice (pairBoundaryHullOrder psi) (t (c.tailStart+n))
      (alpha (c.tailStart+n)) (c.branch n 0)=
      coorbitalBaseSlice (pairChartMass (t (c.tailStart+n)) (p (c.tailStart+n))
        (alpha (c.tailStart+n)) ∘ hullSatellitePermutation (pairBoundaryHullOrder psi)) := by
  have hz : (0 : ℝ)∈Ico 0 c.radius := ⟨le_rfl,c.radius_pos⟩
  obtain ⟨hu,_,_,_,hco⟩ := c.endpoints n
  unfold pairOrderedSlice
  rw [funext hu]
  apply orderedPolarSlice_endpoint _ _ _ (hm (c.tailStart+n)) (c.safe n 0 hz).2.1 _ hco
  simpa [pairChartPoints,funext hu] using (c.safe n 0 hz).2.2 (ht (c.tailStart+n))

theorem PairCapturedBranches.toOrderedSliceCapturedBranches {eps t p alpha : ℕ → ℝ}
    {y : ℕ → PairChartVariables} {psi : ℝ} {keepD : Bool}
    (c : PairCapturedBranches eps t p alpha y psi keepD)
    (ht : ∀ n,0<t n)
    (hm : ∀ n,PositiveRatio (pairChartMass (t n) (p n) (alpha n))) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n : ℕ => (⟨pairChartMass (t n) (p n) (alpha n) ∘
        hullSatellitePermutation (pairBoundaryHullOrder psi),
        positiveRatio_satellitePermutation _ (hm n) _⟩ : PositiveMassRatio)) eps
      (fun n => pairOrderedSlice (pairBoundaryHullOrder psi) (t n) (alpha n) (y n))) := by
  let sigma := pairBoundaryHullOrder psi
  have hx (n : ℕ) (s : ℝ) (hs : 0<s) (hsrad : s<c.radius) :=
    (pairChartExtendedRows_zero_iff_normalized s (t (c.tailStart+n)) (p (c.tailStart+n))
      (alpha (c.tailStart+n)) keepD (c.branch n s) hs (ht (c.tailStart+n))
      (hm (c.tailStart+n)) (c.regular_roots n s ⟨hs.le,hsrad⟩).1
      (c.safe n s ⟨hs.le,hsrad⟩).1).mp (c.regular_roots n s ⟨hs.le,hsrad⟩).2
  refine ⟨{
    subseq := fun n => c.tailStart+n
    subseq_strictMono := by intro i j hij; change c.tailStart+i<c.tailStart+j; omega
    radius := c.radius
    radius_pos := c.radius_pos
    parameters_lt_radius := c.parameters_lt_radius
    branch := fun n s => pairOrderedSlice sigma (t (c.tailStart+n)) (alpha (c.tailStart+n)) (c.branch n s)
    continuous := ?_
    hits := ?_
    roots := ?_
    nondegenerate_at := ?_
    endpoints := ?_ }⟩
  · intro n
    exact (pairOrderedSlice_contDiff 0 sigma _ _).continuous.comp_continuousOn (c.continuous n)
  · intro n
    rw [c.hits]
  · intro n s hs hsrad
    exact orderedPolarSlice_root_of_normalized s _ sigma _ _ (hm (c.tailStart+n)) hs
      (c.safe n s ⟨hs.le,hsrad⟩).1 (c.safe n s ⟨hs.le,hsrad⟩).2.1
      ((c.safe n s ⟨hs.le,hsrad⟩).2.2 (ht (c.tailStart+n))) (hx n s hs hsrad)
  · intro n s hs hsrad
    have hn := shapeHessianNondegenerate_of_normalized_nondegenerate _ _ (hx n s hs hsrad)
      (c.physical n s hs hsrad).2
    exact orderedPolarSlice_nondegenerate_of_normalized s _ sigma _ _ (hm (c.tailStart+n))
      (c.safe n s ⟨hs.le,hsrad⟩).1 (hx n s hs hsrad) hn
  · intro n
    exact c.orderedSlice_endpoint ht hm n

end DominantFiveBody
