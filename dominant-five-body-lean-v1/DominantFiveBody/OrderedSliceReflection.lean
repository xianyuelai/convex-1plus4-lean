import DominantFiveBody.ReflectionHessianTransport
import DominantFiveBody.NoCollisionSliceConnection
import DominantFiveBody.OrderedSliceApplication

/-! # Reflection and exact first-angle slice capture

The first-angle reflection is a linear involution. It transports roots,
the actual shape Hessian and the current-mass coorbital endpoint. Applying
it to a captured branch returns the original ordered slice exactly.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

@[simp] theorem hullSatellitePermutation_standardHullOrder :
    hullSatellitePermutation standardHullOrder=Equiv.refl Satellite := by
  apply Equiv.ext
  intro i
  fin_cases i <;> rfl

def mirrorPositiveMassRatio (mu : PositiveMassRatio) : PositiveMassRatio :=
  ⟨mu.val ∘ Fin.revPerm,positiveRatio_satellitePermutation _ mu.property Fin.revPerm⟩

@[simp] theorem mirrorPositiveMassRatio_twice (mu : PositiveMassRatio) :
    mirrorPositiveMassRatio (mirrorPositiveMassRatio mu)=mu := by
  apply Subtype.ext
  funext i
  exact congrArg mu.val (Fin.rev_rev i)

def mirrorSlice (y : SliceCoordinates) : SliceCoordinates :=
  polarSlice (sliceRadii y ∘ Fin.revPerm)
    (fun i => sliceAngles y 3-sliceAngles y i.rev)

@[simp] theorem mirrorSlice_radii (y : SliceCoordinates) :
    sliceRadii (mirrorSlice y)=sliceRadii y ∘ Fin.revPerm := polarSlice_radii _ _

@[simp] theorem mirrorSlice_angles (y : SliceCoordinates) :
    sliceAngles (mirrorSlice y)=fun i => sliceAngles y 3-sliceAngles y i.rev := by
  exact polarSlice_angles _ _ (sub_self _)

@[simp] theorem mirrorSlice_twice (y : SliceCoordinates) : mirrorSlice (mirrorSlice y)=y := by
  apply sliceCoordinates_ext
  · simp only [mirrorSlice_radii,Function.comp_def,Fin.revPerm_apply,Fin.rev_rev]
  · simp only [mirrorSlice_angles,Fin.rev_rev,show Fin.rev (3 : Satellite)=0 from rfl]
    funext i
    change (sliceAngles y 3-0)-(sliceAngles y 3-sliceAngles y i)=sliceAngles y i
    ring

theorem mirrorSlice_contDiff (n : ℕ∞ω) : ContDiff ℝ n mirrorSlice := by
  have hr : ContDiff ℝ n (fun y : SliceCoordinates => sliceRadii y ∘ Fin.revPerm) := by
    apply contDiff_pi.mpr
    intro i
    exact sliceRadii_contDiff n i.rev
  have ht : ContDiff ℝ n (fun y : SliceCoordinates =>
      fun i : Satellite => sliceAngles y 3-sliceAngles y i.rev) := by
    apply contDiff_pi.mpr
    intro i
    exact (sliceAngles_contDiff n 3).sub (sliceAngles_contDiff n i.rev)
  exact (polarSlice_contDiff n).comp (hr.prodMk ht)

theorem mirrorSlice_eq_orderedPolarSlice (y : SliceCoordinates) : mirrorSlice y=
    orderedPolarSlice standardHullOrder (sliceRadii y ∘ Fin.revPerm)
      (fun i => -sliceAngles y i.rev) := by
  apply sliceCoordinates_ext
  · simp only [mirrorSlice_radii,orderedPolarSlice_radii,hullSatellitePermutation_standardHullOrder,
      Equiv.refl_apply,Function.comp_def]
  · simp only [mirrorSlice_angles,orderedPolarSlice_angles,hullSatellitePermutation_standardHullOrder,
      Equiv.refl_apply,show Fin.rev (0 : Satellite)=3 from rfl,neg_sub_neg]

theorem mirrorConfiguration_centeredFromRelative (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) :
    mirrorConfiguration (centeredFromRelative eps mu q)=
      centeredFromRelative eps (mu ∘ Fin.revPerm) (fun i => planeReflection (q i.rev)) := by
  change rotateConfiguration planeReflection
    (centeredFromRelative eps mu q ∘ (satelliteHullOrder Fin.revPerm).labels)=_
  rw [centeredFromRelative_hullReindex,hullSatellitePermutation_satelliteHullOrder,
    centeredFromRelative_rotate]
  rfl

theorem orderedSliceRoot_mirror (mu : PositiveMassRatio) (eps : ℝ) (heps : 0<eps)
    (y : SliceCoordinates) (hy : orderedSliceRoot mu eps y) :
    orderedSliceRoot (mirrorPositiveMassRatio mu) eps (mirrorSlice y) := by
  let r := sliceRadii y ∘ Fin.revPerm
  let theta : Satellite → ℝ := fun i => -sliceAngles y i.rev
  have hx := (orderedSliceRoot_physical mu eps heps y hy).1
  have hphys : mirrorConfiguration (slicePhysicalConfiguration (eps,mu.val) y)=
      centeredFromRelative eps (mu.val ∘ Fin.revPerm) (polarSatellites r theta) := by
    rw [slicePhysicalConfiguration,relativeCenteredContinuous_apply,mirrorConfiguration_centeredFromRelative]
    congr 1
    funext i
    exact planeReflection_polar _ _
  have hx' := mirrorConfiguration_normalized eps mu.val _ hx
  rw [hphys] at hx'
  have hc := mirrorConfiguration_strictConvex _ hy.2.2.1
  rw [hphys] at hc
  have hh := orderedPolarSlice_root_of_normalized eps (mu.val ∘ Fin.revPerm)
    standardHullOrder r theta (mirrorPositiveMassRatio mu).property heps
    (fun i => hy.1.2.1 i.rev)
    (angle_width_of_ordered_permutation theta (Equiv.refl Satellite)
      (mirrorAngles_ordered _ hy.2.1))
    ((strictConvex_centeredFromRelative_iff _ _ _ _).mp hc) hx'
  rw [←mirrorSlice_eq_orderedPolarSlice] at hh
  simpa only [hullSatellitePermutation_standardHullOrder,Equiv.refl_apply,Function.comp_def,
    mirrorPositiveMassRatio] using hh

theorem orderedSliceNondegenerate_mirror (mu : PositiveMassRatio) (eps : ℝ) (heps : 0<eps)
    (y : SliceCoordinates) (hy : orderedSliceRoot mu eps y)
    (hn : orderedSliceNondegenerate mu eps y) :
    orderedSliceNondegenerate (mirrorPositiveMassRatio mu) eps (mirrorSlice y) := by
  let r := sliceRadii y ∘ Fin.revPerm
  let theta : Satellite → ℝ := fun i => -sliceAngles y i.rev
  have hx := (orderedSliceRoot_physical mu eps heps y hy).1
  have hphys : mirrorConfiguration (slicePhysicalConfiguration (eps,mu.val) y)=
      centeredFromRelative eps (mu.val ∘ Fin.revPerm) (polarSatellites r theta) := by
    rw [slicePhysicalConfiguration,relativeCenteredContinuous_apply,mirrorConfiguration_centeredFromRelative]
    congr 1
    funext i
    exact planeReflection_polar _ _
  have hx' := mirrorConfiguration_normalized eps mu.val _ hx
  have hn' := mirrorConfiguration_shapeHessianNondegenerate eps mu.val _ hx hn
  rw [hphys] at hx' hn'
  have hh := orderedPolarSlice_nondegenerate_of_normalized eps (mu.val ∘ Fin.revPerm)
    standardHullOrder r theta (mirrorPositiveMassRatio mu).property
    (fun i => hy.1.2.1 i.rev) hx' hn'
  rw [←mirrorSlice_eq_orderedPolarSlice] at hh
  simpa only [hullSatellitePermutation_standardHullOrder,Equiv.refl_apply,Function.comp_def,
    mirrorPositiveMassRatio] using hh

theorem coorbitalResidual_neg_angles (mu theta : Satellite → ℝ) (i : Satellite) :
    coorbitalResidual mu (fun j => -theta j) i= -coorbitalResidual mu theta i := by
  unfold coorbitalResidual
  simp_rw [show ∀ j,(-theta j)-(-theta i)= -(theta j-theta i) from fun j => by ring,
    coorbitalKernel_neg,mul_neg]
  simp only [Finset.sum_neg_distrib]

theorem mirrorSlice_endpoint (mu : PositiveMassRatio) :
    mirrorSlice (orderedSliceEndpoint mu)=orderedSliceEndpoint (mirrorPositiveMassRatio mu) := by
  let theta := coorbitalRootAngles mu.val
  let thetaM : Satellite → ℝ := fun i => theta 3-theta i.rev
  have hspec := coorbitalRootAngles_spec mu.val mu.property
  have htheta0 : thetaM 0=0 := sub_self _
  have hordered : OrderedSemicircle thetaM := by
    intro i j hij
    have hh := mirrorAngles_ordered theta (orderedSemicircle_of_coorbitalAngleDomain _ hspec.1) i j hij
    change 0<thetaM j-thetaM i ∧ thetaM j-thetaM i<Real.pi
    convert! hh using 1 <;> dsimp only [thetaM] <;> ring
  have hroot (i : Satellite) : coorbitalResidual (mu.val ∘ Fin.revPerm) thetaM i=0 := by
    have hsub : thetaM=fun j => ((fun k => -theta k) ∘ Fin.revPerm) j-(-theta 3) := by
      funext j
      change theta 3-theta j.rev= -theta j.rev-(-theta 3)
      ring
    rw [hsub,coorbitalResidual_sub_constant,coorbitalResidual_reindex,coorbitalResidual_neg_angles,
      hspec.2,neg_zero]
  have heq : coorbitalRootAngles (mu.val ∘ Fin.revPerm)=thetaM :=
    coorbitalRootAngles_eq_of_root _ (mirrorPositiveMassRatio mu).property thetaM
      ⟨htheta0,fun i j hij => sub_pos.mp (hordered i j hij).1,
        by simpa only [htheta0,sub_zero] using (hordered 0 3 (by decide)).2⟩ hroot
  apply sliceCoordinates_ext
  · simp only [mirrorSlice_radii,orderedSliceEndpoint,funext (coorbitalBaseSlice_radii _)]
    rfl
  · simp only [mirrorSlice_angles,orderedSliceEndpoint,coorbitalBaseSlice_angles _ mu.property,
      coorbitalBaseSlice_angles _ (mirrorPositiveMassRatio mu).property]
    exact heq.symm

def CapturedBranches.mirrorOrderedSlice
    (mu : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (c : CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint mu eps y) :
    CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => mirrorPositiveMassRatio (mu n)) eps (fun n => mirrorSlice (y n)) where
  subseq := c.subseq
  subseq_strictMono := c.subseq_strictMono
  radius := c.radius
  radius_pos := c.radius_pos
  parameters_lt_radius := c.parameters_lt_radius
  branch := fun n s => mirrorSlice (c.branch n s)
  continuous n := (mirrorSlice_contDiff 0).continuous.comp_continuousOn (c.continuous n)
  hits n := congrArg mirrorSlice (c.hits n)
  roots n s hs hsr := orderedSliceRoot_mirror _ _ hs _ (c.roots n s hs hsr)
  nondegenerate_at n s hs hsr := orderedSliceNondegenerate_mirror _ _ hs _
    (c.roots n s hs hsr) (c.nondegenerate_at n s hs hsr)
  endpoints n := (congrArg mirrorSlice (c.endpoints n)).trans (mirrorSlice_endpoint _)

theorem captured_mirrorOrderedSlice_undo
    (mu : ℕ → PositiveMassRatio) (eps : ℕ → ℝ) (y : ℕ → SliceCoordinates)
    (c : CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint
      (fun n => mirrorPositiveMassRatio (mu n)) eps (fun n => mirrorSlice (y n))) :
    Nonempty (CapturedBranches orderedSliceRoot orderedSliceNondegenerate orderedSliceEndpoint mu eps y) := by
  have cc := c.mirrorOrderedSlice (fun n => mirrorPositiveMassRatio (mu n)) eps (fun n => mirrorSlice (y n))
  simpa only [mirrorPositiveMassRatio_twice,mirrorSlice_twice] using Nonempty.intro cc

end DominantFiveBody
