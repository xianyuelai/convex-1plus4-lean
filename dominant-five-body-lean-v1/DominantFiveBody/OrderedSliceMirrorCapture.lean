import DominantFiveBody.OrderedSliceReflection
import DominantFiveBody.OrderedSliceTripleCases

/-! # Actual mirrored limits for an upper triple

The mirrored current sequence is already an actual root sequence. Its
mass, angle and physical relative-position limits are obtained by the
proved first-angle coordinate involution. Complete upper triples become
complete lower triples at the unit first satellite.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

def firstAngleMirrorAngles (theta : Satellite → ℝ) : Satellite → ℝ :=
  fun i => theta 3-theta i.rev

theorem complete_upper_triple_firstAngleMirror
    (q : SatelliteConfiguration) (theta : Satellite → ℝ)
    (hunit : ∀ i,q i=polarPoint 1 (theta i)) (hmono : Monotone theta)
    (hspan : theta 3-theta 0<Real.pi) (center : Plane)
    (htriple : CompleteLimitingSatelliteTriple q 0 center) :
    CompleteLimitingSatelliteTriple
      (polarSatellites (fun _ => 1) (firstAngleMirrorAngles theta)) 3 (polarPoint 1 0) := by
  have hq3 : q 3=center := (htriple 3).mpr (by decide)
  have hangle (i : Satellite) (hi : i≠0) : theta i=theta 3 :=
    (unit_ordered_limit_equal_iff q theta hunit hmono hspan i 3).mp
      (((htriple i).mpr hi).trans hq3.symm)
  have hsep : theta 3≠theta 0 := by
    intro he
    have hqeq := (unit_ordered_limit_equal_iff q theta hunit hmono hspan 0 3).mpr he.symm
    exact (htriple 0).mp (hqeq.trans hq3) rfl
  have hgap : theta 3-theta 0≠0 := sub_ne_zero.mpr hsep
  have hpi : |0-(theta 3-theta 0)|<Real.pi := by
    rw [zero_sub,abs_neg,abs_of_nonneg (sub_nonneg.mpr (hmono (by decide : (0 : Satellite)≤3)))]
    exact hspan
  have hpolarNe := polarUnit_ne_of_angle_ne (theta 3-theta 0) 0 hgap hpi
  intro i
  by_cases hi : i=3
  · subst i
    simp only [polarSatellites,firstAngleMirrorAngles,show Fin.rev (3 : Satellite)=0 from rfl]
    exact iff_of_false hpolarNe (by simp)
  · have hrev : i.rev≠(0 : Satellite) := by fin_cases i <;> simp_all
    simp only [polarSatellites,firstAngleMirrorAngles,hangle i.rev hrev,sub_self]
    exact iff_of_true trivial hi

theorem orderedSlice_mirror_sequence_limits
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n,orderedSliceRoot (p n) (eps n) (y n))
    (muLimit thetaLimit : MassRatio) (qLimit : SatelliteConfiguration)
    (hmt : Tendsto (fun n => (p n).val) atTop (𝓝 muLimit))
    (htt : Tendsto (fun n => sliceAngles (y n)) atTop (𝓝 thetaLimit))
    (hqt : Tendsto (fun n => sliceSatellites (y n)) atTop (𝓝 qLimit)) :
    Tendsto (fun n => (mirrorPositiveMassRatio (p n)).val) atTop (𝓝 (muLimit ∘ Fin.revPerm)) ∧
    Tendsto (fun n => sliceAngles (mirrorSlice (y n))) atTop (𝓝 (firstAngleMirrorAngles thetaLimit)) ∧
    Tendsto (fun n => sliceSatellites (mirrorSlice (y n))) atTop
      (𝓝 (polarSatellites (fun _ => 1) (firstAngleMirrorAngles thetaLimit))) ∧
    (∀ i,qLimit i=polarPoint 1 (thetaLimit i)) ∧ Monotone thetaLimit ∧
      thetaLimit 3-thetaLimit 0<Real.pi := by
  obtain ⟨hrt,hunit,hmono,_,hspan⟩ := normalized_ordered_polar_limit_geometry eps
    (fun n => (p n).val) (fun n => slicePhysicalConfiguration (eps n,(p n).val) (y n))
    heps hepst (fun n => (p n).property)
    (fun n => (orderedSliceRoot_physical (p n) (eps n) (heps n) (y n) (hy n)).1)
    (fun n => sliceRadii (y n)) (fun n => sliceAngles (y n)) (fun n => (hy n).1.2.1)
    (fun n => slicePhysicalConfiguration_satellitesRelative _ _) (fun n => (hy n).2.1)
    muLimit hmt qLimit (by simpa only [slicePhysicalConfiguration_satellitesRelative] using hqt)
    thetaLimit htt
  have hmass : Tendsto (fun n => (mirrorPositiveMassRatio (p n)).val) atTop
      (𝓝 (muLimit ∘ Fin.revPerm)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (continuous_apply i.rev).continuousAt.tendsto.comp hmt
  have hangle : Tendsto (fun n => sliceAngles (mirrorSlice (y n))) atTop
      (𝓝 (firstAngleMirrorAngles thetaLimit)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have ht3 := (continuous_apply (3 : Satellite)).continuousAt.tendsto.comp htt
    have hti := (continuous_apply i.rev).continuousAt.tendsto.comp htt
    simpa only [Function.comp_def,mirrorSlice_angles,firstAngleMirrorAngles] using ht3.sub hti
  refine ⟨hmass,hangle,?_,hunit,hmono,hspan⟩
  apply tendsto_pi_nhds.mpr
  intro i
  have hri := (continuous_apply i.rev).continuousAt.tendsto.comp hrt
  have hti := (continuous_apply i).continuousAt.tendsto.comp hangle
  have hh := (polarPoint_contDiff 0).continuous.continuousAt.tendsto.comp (hri.prodMk_nhds hti)
  simpa only [Function.comp_def,sliceSatellites,polarSatellites,mirrorSlice_radii,
    Fin.revPerm_apply] using hh

theorem orderedSlice_upper_triple_mirror_limits
    (p : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (heps : ∀ n,0<eps n) (hepst : Tendsto eps atTop (𝓝 0))
    (hy : ∀ n,orderedSliceRoot (p n) (eps n) (y n))
    (muLimit thetaLimit : MassRatio) (qLimit : SatelliteConfiguration)
    (hmt : Tendsto (fun n => (p n).val) atTop (𝓝 muLimit))
    (htt : Tendsto (fun n => sliceAngles (y n)) atTop (𝓝 thetaLimit))
    (hqt : Tendsto (fun n => sliceSatellites (y n)) atTop (𝓝 qLimit))
    (center : Plane) (htriple : CompleteLimitingSatelliteTriple qLimit 0 center) :
    (∀ n,orderedSliceRoot (mirrorPositiveMassRatio (p n)) (eps n) (mirrorSlice (y n))) ∧
    Tendsto (fun n => (mirrorPositiveMassRatio (p n)).val) atTop (𝓝 (muLimit ∘ Fin.revPerm)) ∧
    Tendsto (fun n => sliceAngles (mirrorSlice (y n))) atTop (𝓝 (firstAngleMirrorAngles thetaLimit)) ∧
    Tendsto (fun n => sliceSatellites (mirrorSlice (y n))) atTop
      (𝓝 (polarSatellites (fun _ => 1) (firstAngleMirrorAngles thetaLimit))) ∧
    CompleteLimitingSatelliteTriple
      (polarSatellites (fun _ => 1) (firstAngleMirrorAngles thetaLimit)) 3 (polarPoint 1 0) := by
  obtain ⟨hmm,hth,hqm,hunit,hmono,hspan⟩ :=
    orderedSlice_mirror_sequence_limits p eps y heps hepst hy muLimit thetaLimit qLimit hmt htt hqt
  exact ⟨fun n => orderedSliceRoot_mirror _ _ (heps n) _ (hy n),hmm,hth,hqm,
    complete_upper_triple_firstAngleMirror qLimit thetaLimit hunit hmono hspan center htriple⟩

end DominantFiveBody
