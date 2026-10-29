import DominantFiveBody.NoCollisionContinuation

/-! Explicit inverse coordinates for the first-angle slice. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody

def polarSlice (r theta : Satellite → ℝ) : SliceCoordinates :=
  Fin.append r (fun i : Fin 3 => theta i.succ)

@[simp] theorem polarSlice_radii (r theta : Satellite → ℝ) : sliceRadii (polarSlice r theta)=r := by
  funext i
  simp [sliceRadii,polarSlice]

theorem polarSlice_angles (r theta : Satellite → ℝ) (hz : theta 0=0) :
    sliceAngles (polarSlice r theta)=theta := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hz.symm
  · simp [sliceAngles,polarSlice]

theorem polarSlice_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : MassRatio × MassRatio => polarSlice p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.addCases (m := 4) (n := 3) (fun j => ?_) (fun j => ?_) i
  · simpa only [polarSlice,Fin.append_left,Function.comp_def] using
      ((contDiff_apply ℝ ℝ j).comp contDiff_fst : ContDiff ℝ n (fun p : MassRatio × MassRatio => p.1 j))
  · simpa only [polarSlice,Fin.append_right,Function.comp_def] using
      ((contDiff_apply ℝ ℝ j.succ).comp contDiff_snd : ContDiff ℝ n (fun p : MassRatio × MassRatio => p.2 j.succ))

theorem polarSlice_regular (eps : ℝ) (mu r theta : Satellite → ℝ)
    (heps : -1<eps) (hr : ∀ i,0<r i) (hz : theta 0=0)
    (hcf : RelativeCollisionFree (polarSatellites r theta)) :
    SliceRegular (eps,mu) (polarSlice r theta) := by
  refine ⟨heps,?_,?_⟩
  · simpa only [polarSlice_radii] using hr
  · simpa only [sliceSatellites,polarSlice_radii,polarSlice_angles r theta hz] using hcf.2

theorem polarSlice_residual_zero (eps : ℝ) (mu r theta : Satellite → ℝ)
    (hz : theta 0=0)
    (hR : ∀ i,radialResidual eps mu r theta i=0)
    (hT : ∀ i,angularResidual eps mu r theta i=0) :
    reducedResidual (eps,mu) (polarSlice r theta)=0 := by
  unfold reducedResidual
  rw [polarSlice_radii,polarSlice_angles r theta hz]
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left,Pi.zero_apply] using hR j
  · simpa only [Fin.append_right,Pi.zero_apply] using hT j.succ

theorem polarSlice_physical_eq (eps : ℝ) (mu r theta : Satellite → ℝ)
    (hz : theta 0=0) : slicePhysicalConfiguration (eps,mu) (polarSlice r theta)=
      centeredFromRelative eps mu (polarSatellites r theta) := by
  simp only [slicePhysicalConfiguration,sliceSatellites,polarSlice_radii,polarSlice_angles r theta hz]
  simp only [relativeCenteredContinuous_apply]

end DominantFiveBody
