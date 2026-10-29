import DominantFiveBody.CoorbitalContinuation
import DominantFiveBody.UniformThreshold

/-! # Actual Section 7 root relation in the ordered first-angle slice

The root includes physical convexity. Positive radii and ordered angles
alone are not used as a substitute for strict convexity. Local continuation
uniqueness is proved from the actual seven-row derivative and IFT.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

abbrev PositiveMassRatio := {mu : MassRatio // PositiveRatio mu}

def orderedSliceRoot (mu : PositiveMassRatio) (eps : ℝ) (y : SliceCoordinates) : Prop :=
  SliceRegular (eps,mu.val) y ∧ OrderedSemicircle (sliceAngles y) ∧
    StrictConvexInOrder standardHullOrder (slicePhysicalConfiguration (eps,mu.val) y) ∧
    reducedResidual (eps,mu.val) y=0

def orderedSliceNondegenerate (mu : PositiveMassRatio) (eps : ℝ) (y : SliceCoordinates) : Prop :=
  ShapeHessianNondegenerate (masses eps mu.val) 1 (slicePhysicalConfiguration (eps,mu.val) y)

def orderedSliceEndpoint (mu : PositiveMassRatio) : SliceCoordinates := coorbitalBaseSlice mu.val

theorem orderedSliceContinuationRoot_actual_data (mu : PositiveMassRatio) (eps : ℝ)
    (y : SliceCoordinates)
    (h : ContinuationRoot orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint mu eps y) :
    SliceRegular (eps,mu.val) y ∧ reducedResidual (eps,mu.val) y=0 ∧
      (reducedJacobian (eps,mu.val) y).IsInvertible := by
  rcases h with ⟨he,hy⟩ | ⟨he,hroot,hnd⟩
  · simpa only [he,hy,orderedSliceEndpoint] using coorbitalBaseSlice_actual_data mu.val mu.property
  · exact ⟨hroot.1,hroot.2.2.2,
      (reducedJacobian_isInvertible_iff_shape (eps,mu.val) y hroot.1 he mu.property hroot.2.2.2).mpr hnd⟩

theorem orderedSliceContinuationRoot_residual_zero (mu : PositiveMassRatio) (eps : ℝ)
    (y : SliceCoordinates)
    (h : ContinuationRoot orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint mu eps y) :
    reducedResidual (eps,mu.val) y=0 := (orderedSliceContinuationRoot_actual_data mu eps y h).2.1

theorem orderedSlice_localContinuationUniqueness :
    LocalContinuationUniqueness orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint := by
  intro mu radius hradius t y hroot
  obtain ⟨hreg,hzero,hJ⟩ := orderedSliceContinuationRoot_actual_data mu t.val y hroot
  obtain ⟨psi,d,r,hd,hr,_,_,hlocal⟩ :=
    reducedResidual_local_product (t.val,mu.val) y hreg hzero hJ
  refine ⟨Metric.ball y r,Metric.ball_mem_nhds y hr,?_⟩
  have hnear : ∀ᶠ s : ConnectionInterval radius in 𝓝 t,dist s.val t.val<d :=
    continuous_subtype_val.continuousAt.eventually (Metric.ball_mem_nhds t.val hd)
  filter_upwards [hnear] with s hs
  intro a ha b hb hsa hsb
  obtain ⟨_,_,huniq⟩ := hlocal s.val mu.val hs (by simpa using hd)
  have hza := orderedSliceContinuationRoot_residual_zero mu s.val a hsa
  have hzb := orderedSliceContinuationRoot_residual_zero mu s.val b hsb
  exact ((huniq a ha).mp hza).symm.trans ((huniq b hb).mp hzb)

end DominantFiveBody
