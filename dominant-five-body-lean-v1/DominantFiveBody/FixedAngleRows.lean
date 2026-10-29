import DominantFiveBody.DeletedAngularRows
import DominantFiveBody.PhysicalRelabeling

/-! The actual arbitrary-fixed-angle and arbitrary-deleted-row instance
of Lemma 3.1, with labels and physical Hessians transported explicitly. -/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

def satelliteLabelPermutation (e : Equiv.Perm Satellite) : Equiv.Perm Label where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  invFun := Fin.cases 0 (fun i => (e.symm i).succ)
  left_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem satelliteLabelPermutation_zero (e : Equiv.Perm Satellite) :
    satelliteLabelPermutation e 0 = 0 := rfl

@[simp] theorem satelliteLabelPermutation_succ (e : Equiv.Perm Satellite) (i : Satellite) :
    satelliteLabelPermutation e i.succ = (e i).succ := rfl

theorem masses_satellitePermutation (ε : ℝ) (μ : MassRatio) (e : Equiv.Perm Satellite) :
    masses ε (μ ∘ e) = masses ε μ ∘ satelliteLabelPermutation e := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [masses]

theorem positiveRatio_satellitePermutation (μ : MassRatio) (hμ : PositiveRatio μ)
    (e : Equiv.Perm Satellite) : PositiveRatio (μ ∘ e) :=
  ⟨fun i => hμ.1 (e i), (Equiv.sum_comp e μ).trans hμ.2⟩

theorem polarSatellites_permutation (r θ : Satellite → ℝ) (e : Equiv.Perm Satellite) :
    polarSatellites (r ∘ e) (θ ∘ e) = polarSatellites r θ ∘ e := rfl

theorem relativeAverage_permutation (μ : MassRatio) (q : SatelliteConfiguration)
    (e : Equiv.Perm Satellite) : relativeAverage (μ ∘ e) (q ∘ e) = relativeAverage μ q :=
  Equiv.sum_comp e (fun i => μ i • q i)

theorem radialResidual_full_sum (ε : ℝ) (μ r θ : Satellite → ℝ) (i : Satellite) :
    radialResidual ε μ r θ i = r i - (r i ^ 2)⁻¹ -
      ε * (∑ j, μ j * (r i - r j * Real.cos (θ j - θ i)) /
        satelliteDistance (polarSatellites r θ) i j ^ 3) -
      ε / (1 + ε) * inner ℝ (relativeAverage μ (polarSatellites r θ)) (polarPoint 1 (θ i)) := by
  unfold radialResidual
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp

theorem angularResidual_full_sum (ε : ℝ) (μ r θ : Satellite → ℝ) (i : Satellite) :
    angularResidual ε μ r θ i = ∑ j,
      μ j * r i * r j * Real.sin (θ j - θ i) *
        ((satelliteDistance (polarSatellites r θ) i j ^ 3)⁻¹ - (1 + ε)⁻¹) := by
  unfold angularResidual
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp

theorem radialResidual_permutation (ε : ℝ) (μ r θ : Satellite → ℝ)
    (e : Equiv.Perm Satellite) (i : Satellite) :
    radialResidual ε (μ ∘ e) (r ∘ e) (θ ∘ e) i = radialResidual ε μ r θ (e i) := by
  rw [radialResidual_full_sum, radialResidual_full_sum, polarSatellites_permutation,
    relativeAverage_permutation]
  congr 2
  congr 1
  exact Equiv.sum_comp e (fun j => μ j * (r (e i) - r j * Real.cos (θ j - θ (e i))) /
    satelliteDistance (polarSatellites r θ) (e i) j ^ 3)

theorem angularResidual_permutation (ε : ℝ) (μ r θ : Satellite → ℝ)
    (e : Equiv.Perm Satellite) (i : Satellite) :
    angularResidual ε (μ ∘ e) (r ∘ e) (θ ∘ e) i = angularResidual ε μ r θ (e i) := by
  rw [angularResidual_full_sum, angularResidual_full_sum]
  exact Equiv.sum_comp e (fun j => μ j * r (e i) * r j * Real.sin (θ j - θ (e i)) *
    ((satelliteDistance (polarSatellites r θ) (e i) j ^ 3)⁻¹ - (1 + ε)⁻¹))

theorem centeredFromRelative_satellitePermutation (ε : ℝ) (μ : MassRatio)
    (q : SatelliteConfiguration) (e : Equiv.Perm Satellite) :
    centeredFromRelative ε (μ ∘ e) (q ∘ e) =
      centeredFromRelative ε μ q ∘ satelliteLabelPermutation e := by
  have havg := relativeAverage_permutation μ q e
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp only [centeredFromRelative, liftRelative, Fin.cases_zero, Fin.cases_succ,
      Function.comp_apply, satelliteLabelPermutation_zero, satelliteLabelPermutation_succ, havg]

def fixedAnglePermutation (fixed : Satellite) : Equiv.Perm Satellite := Equiv.swap 0 fixed

def fixedAngleRadii (fixed : Satellite) (y : SliceCoordinates) : Satellite → ℝ :=
  sliceRadii y ∘ (fixedAnglePermutation fixed).symm

def fixedAngleAngles (fixed : Satellite) (y : SliceCoordinates) : Satellite → ℝ :=
  sliceAngles y ∘ (fixedAnglePermutation fixed).symm

def fixedAngleSatellites (fixed : Satellite) (y : SliceCoordinates) : SatelliteConfiguration :=
  polarSatellites (fixedAngleRadii fixed y) (fixedAngleAngles fixed y)

def fixedAnglePhysicalConfiguration (p : ContinuationParameter) (fixed : Satellite)
    (y : SliceCoordinates) : Configuration :=
  centeredFromRelative p.1 p.2 (fixedAngleSatellites fixed y)

@[simp] theorem fixedAngleAngles_fixed (fixed : Satellite) (y : SliceCoordinates) :
    fixedAngleAngles fixed y fixed = 0 := by
  simp [fixedAngleAngles, fixedAnglePermutation, sliceAngles]

/-- Seven actual physical divided rows in the chart fixing `θ_fixed=0`.
The radial order and retained angular order are explicitly transported
by the displayed satellite permutation. All original labels are retained. -/
def fixedAngleDeletedResidual (p : ContinuationParameter) (fixed omitted : Satellite)
    (y : SliceCoordinates) : SliceCoordinates :=
  let e := fixedAnglePermutation fixed
  Fin.append (fun i : Satellite =>
    radialResidual p.1 p.2 (fixedAngleRadii fixed y) (fixedAngleAngles fixed y) (e i))
    (fun j : Fin 3 => angularResidual p.1 p.2 (fixedAngleRadii fixed y) (fixedAngleAngles fixed y)
      (e ((e.symm omitted).succAbove j)))

theorem fixedAngleDeletedResidual_eq (p : ContinuationParameter) (fixed omitted : Satellite) :
    fixedAngleDeletedResidual p fixed omitted =
      deletedReducedResidual (p.1, p.2 ∘ fixedAnglePermutation fixed)
        ((fixedAnglePermutation fixed).symm omitted) := by
  let e := fixedAnglePermutation fixed
  have hR (y : SliceCoordinates) (i : Satellite) :
      radialResidual p.1 (p.2 ∘ e) (sliceRadii y) (sliceAngles y) i =
        radialResidual p.1 p.2 (fixedAngleRadii fixed y) (fixedAngleAngles fixed y) (e i) := by
    simpa only [fixedAngleRadii, fixedAngleAngles, e, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id] using
      radialResidual_permutation p.1 p.2 (fixedAngleRadii fixed y) (fixedAngleAngles fixed y) e i
  have hT (y : SliceCoordinates) (i : Satellite) :
      angularResidual p.1 (p.2 ∘ e) (sliceRadii y) (sliceAngles y) i =
        angularResidual p.1 p.2 (fixedAngleRadii fixed y) (fixedAngleAngles fixed y) (e i) := by
    simpa only [fixedAngleRadii, fixedAngleAngles, e, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id] using
      angularResidual_permutation p.1 p.2 (fixedAngleRadii fixed y) (fixedAngleAngles fixed y) e i
  funext y k
  refine Fin.addCases (motive := fun k => fixedAngleDeletedResidual p fixed omitted y k =
      deletedReducedResidual (p.1, p.2 ∘ fixedAnglePermutation fixed)
        ((fixedAnglePermutation fixed).symm omitted) y k)
    (fun i : Fin 4 => ?_) (fun j : Fin 3 => ?_) k
  · simpa only [fixedAngleDeletedResidual, deletedReducedResidual, Fin.append_left] using (hR y i).symm
  · simpa only [fixedAngleDeletedResidual, deletedReducedResidual, Fin.append_right] using
      (hT y ((e.symm omitted).succAbove j)).symm

theorem fixedAnglePhysicalConfiguration_permutation (p : ContinuationParameter)
    (fixed : Satellite) (y : SliceCoordinates) :
    slicePhysicalConfiguration (p.1, p.2 ∘ fixedAnglePermutation fixed) y =
      fixedAnglePhysicalConfiguration p fixed y ∘ satelliteLabelPermutation (fixedAnglePermutation fixed) := by
  let e := fixedAnglePermutation fixed
  have hq : fixedAngleSatellites fixed y ∘ e = sliceSatellites y := by
    ext i
    simp [fixedAngleSatellites, fixedAngleRadii, fixedAngleAngles, e, sliceSatellites,
      polarSatellites]
  simpa only [slicePhysicalConfiguration, relativeCenteredContinuous_apply,
    fixedAnglePhysicalConfiguration, hq] using
      centeredFromRelative_satellitePermutation p.1 p.2 (fixedAngleSatellites fixed y) e

/-- Complete concrete fixed-angle/deleted-row instance of Lemma 3.1.
It applies in particular to fixed index 2 and deleted indices 2 or 3.
The conclusion uses the physical configuration in the original labels. -/
theorem fixedAngleDeletedJacobian_isInvertible_iff_shape (p : ContinuationParameter)
    (fixed omitted : Satellite) (y : SliceCoordinates)
    (hreg : SliceRegular (p.1, p.2 ∘ fixedAnglePermutation fixed) y)
    (hε : 0 < p.1) (hμ : PositiveRatio p.2)
    (hroot : fixedAngleDeletedResidual p fixed omitted y = 0) :
    (fderiv ℝ (fixedAngleDeletedResidual p fixed omitted) y).IsInvertible ↔
      ShapeHessianNondegenerate (masses p.1 p.2) 1 (fixedAnglePhysicalConfiguration p fixed y) := by
  let e := fixedAnglePermutation fixed
  let E := satelliteLabelPermutation e
  let p' : ContinuationParameter := (p.1, p.2 ∘ e)
  have hμ' := positiveRatio_satellitePermutation p.2 hμ e
  have hroot' : deletedReducedResidual p' (e.symm omitted) y = 0 := by
    rwa [fixedAngleDeletedResidual_eq] at hroot
  have hfull := (deletedReducedResidual_zero_iff p' (e.symm omitted)
    (ne_of_gt (hμ'.1 0)) (ne_of_gt (hμ'.1 (e.symm omitted))) y).mp hroot'
  have hx' := normalizedCC_of_reducedResidual_zero p' y hreg hε hμ' hfull
  have hm : masses p'.1 p'.2 = masses p.1 p.2 ∘ E := masses_satellitePermutation p.1 p.2 e
  have hconfig : slicePhysicalConfiguration p' y = fixedAnglePhysicalConfiguration p fixed y ∘ E :=
    fixedAnglePhysicalConfiguration_permutation p fixed y
  have hx : NormalizedCentralConfiguration (masses p.1 p.2) (fixedAnglePhysicalConfiguration p fixed y) := by
    rw [hm, hconfig] at hx'
    have h := normalizedCC_permutation _ _ hx' E.symm
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using h
  rw [fixedAngleDeletedResidual_eq]
  exact (deletedReducedJacobian_isInvertible_iff_shape p' (e.symm omitted) y hreg hε hμ' hroot').trans
    (by rw [hm, hconfig]; exact shapeHessianNondegenerate_permutation_iff _ _ hx E)

end DominantFiveBody
