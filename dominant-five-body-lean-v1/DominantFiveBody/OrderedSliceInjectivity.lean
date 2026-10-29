import DominantFiveBody.OrderedSliceApplication
import DominantFiveBody.NoCollisionContinuation

/-! The exact coordinate-representative assertion before Proposition 7.1.
This is independent of the small-parameter uniform theorem: actual ordered
polar coordinates in the first-angle gauge are injective for every regular
parameter, and each allowed similarity class has a unique representative. -/

noncomputable section
namespace DominantFiveBody

theorem orderedSliceAngles_mem_Icc (y : SliceCoordinates)
    (horder : OrderedSemicircle (sliceAngles y)) (i : Satellite) :
    sliceAngles y i ∈ Set.Icc 0 Real.pi := by
  rcases eq_or_lt_of_le (Fin.zero_le i) with hi | hi
  · rw [← hi]
    exact ⟨le_rfl, Real.pi_pos.le⟩
  · have h := horder 0 i hi
    have hzero : sliceAngles y 0 = 0 := rfl
    rw [hzero, sub_zero] at h
    exact ⟨h.1.le, h.2.le⟩

/-- Positive radii and the genuine ordered first-angle chart, rather than
the equations themselves, give injectivity of the physical coordinate map. -/
theorem ordered_slicePhysicalConfiguration_injective
    (p : ContinuationParameter) (y z : SliceCoordinates)
    (hy : SliceRegular p y) (hz : SliceRegular p z)
    (hoy : OrderedSemicircle (sliceAngles y)) (hoz : OrderedSemicircle (sliceAngles z))
    (heq : slicePhysicalConfiguration p y = slicePhysicalConfiguration p z) : y = z := by
  have hq := congrArg satellitesRelative heq
  rw [slicePhysicalConfiguration_satellitesRelative, slicePhysicalConfiguration_satellitesRelative] at hq
  have hr : sliceRadii y = sliceRadii z := by
    funext i
    have h := congrArg (fun q : Plane => ‖q‖) (congrFun hq i)
    simpa only [sliceSatellites, polarSatellites, polarPoint_norm,
      abs_of_pos (hy.2.1 i), abs_of_pos (hz.2.1 i)] using h
  have htheta : sliceAngles y = sliceAngles z := by
    funext i
    have h := congrArg (fun q : Plane => q 0) (congrFun hq i)
    change sliceRadii y i * Real.cos (sliceAngles y i) =
      sliceRadii z i * Real.cos (sliceAngles z i) at h
    rw [hr] at h
    have hcos := (mul_left_cancel₀ (ne_of_gt (hz.2.1 i))) h
    exact Real.injOn_cos (orderedSliceAngles_mem_Icc y hoy i) (orderedSliceAngles_mem_Icc z hoz i) hcos
  exact sliceCoordinates_ext y z hr htheta

theorem orderedSliceRoot_unique_coordinates_of_normalized_gauged
    (mu : PositiveMassRatio) (eps : ℝ) (heps : 0 < eps) (x : Configuration)
    (hx : NormalizedCentralConfiguration (masses eps mu.val) x)
    (hg : FirstSatelliteGauge x) (hc : StrictConvexInOrder standardHullOrder x) :
    ∃! y : SliceCoordinates, orderedSliceRoot mu eps y ∧
      slicePhysicalConfiguration (eps,mu.val) y = x := by
  obtain ⟨y,hy,hphys⟩ := orderedSliceRoot_of_normalized_gauged mu eps heps x hx hg hc
  refine ⟨y,⟨hy,hphys⟩,?_⟩
  intro z hz
  exact ordered_slicePhysicalConfiguration_injective (eps,mu.val) z y hz.1.1 hy.1
    hz.1.2.1 hy.2.1 (hz.2.trans hphys.symm)

/-- TeX line 947: every allowed oriented similarity class in standard order
has exactly one seven-coordinate multiplier-one representative, for every
positive parameter. There is no use of `main_uniform` in this statement. -/
theorem orderedSliceRoot_existsUnique_orientedSimilar
    (mu : PositiveMassRatio) (eps : ℝ) (heps : 0 < eps) (x : Configuration)
    (hx : StrictConvexCentralConfiguration (masses eps mu.val) standardHullOrder x) :
    ∃! y : SliceCoordinates, orderedSliceRoot mu eps y ∧
      OrientedSimilar x (slicePhysicalConfiguration (eps,mu.val) y) := by
  obtain ⟨q,hq,hunique⟩ := strictConvexCC_existsUnique_normalized_gauged
    (masses eps mu.val) (masses_positive eps mu.val heps mu.property) standardHullOrder x hx
  obtain ⟨y,hy,hphys⟩ := orderedSliceRoot_of_normalized_gauged mu eps heps q hq.1 hq.2.1 hq.2.2.1
  refine ⟨y,⟨hy,?_⟩,?_⟩
  · rw [hphys]
    exact hq.2.2.2
  · intro z hz
    have hp := orderedSliceRoot_physical mu eps heps z hz.1
    have hqeq := hunique (slicePhysicalConfiguration (eps,mu.val) z) ⟨hp.1,hp.2.1,hp.2.2,hz.2⟩
    exact ordered_slicePhysicalConfiguration_injective (eps,mu.val) z y hz.1.1 hy.1
      hz.1.2.1 hy.2.1 (hqeq.trans hphys.symm)

end DominantFiveBody
