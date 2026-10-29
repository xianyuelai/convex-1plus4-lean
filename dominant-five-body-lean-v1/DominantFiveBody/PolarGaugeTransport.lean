import DominantFiveBody.FixedLabelEndpoint
import DominantFiveBody.PolarSliceCoordinates
import DominantFiveBody.SliceConnection

/-! # Exact ordered first-angle coordinates and physical Hessian transport -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology
namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem polarPoint_det (r s a b : ℝ) :
    det2 (polarPoint r a) (polarPoint s b)=r*s*Real.sin (b-a) := by
  simp [det2,polarPoint,point,Real.sin_sub]
  ring

theorem polarPoint_inner (r s a b : ℝ) :
    inner ℝ (polarPoint r a) (polarPoint s b)=r*s*Real.cos (a-b) := by
  rw [plane_inner_coordinates]
  simp [polarPoint,point,Real.cos_sub]
  ring

theorem orientedIsometry_polar_shift (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hdet : LinearMap.det R.toLinearEquiv.toLinearMap=1)
    (ra a : ℝ) (hra : 0<ra) (hanchor : R (polarPoint ra a)=polarPoint ra 0)
    (r b : ℝ) : R (polarPoint r b)=polarPoint r (b-a) := by
  apply plane_ext_of_inner_det (polarPoint ra 0) _ _
  · apply norm_ne_zero_iff.mp
    rw [polarPoint_norm,abs_of_pos hra]
    exact hra.ne'
  · rw [← hanchor,R.inner_map_map,hanchor,polarPoint_inner,polarPoint_inner]
    simp only [zero_sub,Real.cos_neg]
    rw [show a-b=-(b-a) by ring,Real.cos_neg]
  · rw [← hanchor,det2_linearIsometryEquiv,hdet,one_mul,hanchor,polarPoint_det,polarPoint_det]
    simp

theorem centeredFromRelative_rotate (R : Plane ≃ₗᵢ[ℝ] Plane) (eps : ℝ)
    (mu : MassRatio) (q : SatelliteConfiguration) :
    rotateConfiguration R (centeredFromRelative eps mu q)=
      centeredFromRelative eps mu (fun i => R (q i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  all_goals simp [rotateConfiguration,centeredFromRelative,liftRelative,relativeAverage,map_sub,map_sum,map_smul]

theorem centeredFromRelative_hullReindex (eps : ℝ) (mu : MassRatio)
    (q : SatelliteConfiguration) (sigma : HullOrder) :
    centeredFromRelative eps mu q ∘ sigma.labels=
      centeredFromRelative eps (mu ∘ hullSatellitePermutation sigma) (q ∘ hullSatellitePermutation sigma) := by
  have havg : relativeAverage (mu ∘ hullSatellitePermutation sigma) (q ∘ hullSatellitePermutation sigma)=
      relativeAverage mu q := Equiv.sum_comp (hullSatellitePermutation sigma) (fun i => mu i • q i)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Function.comp_apply,centeredFromRelative,sigma.primary_first,liftRelative,havg]
  · simp only [Function.comp_apply,centeredFromRelative,hullOrder_label_succ,liftRelative,
      Fin.cases_succ,havg]

def orderedPolarSlice (sigma : HullOrder) (r theta : Satellite → ℝ) : SliceCoordinates :=
  let e := hullSatellitePermutation sigma
  polarSlice (r ∘ e) (fun i => theta (e i)-theta (e 0))

@[simp] theorem orderedPolarSlice_radii (sigma : HullOrder) (r theta : Satellite → ℝ) :
    sliceRadii (orderedPolarSlice sigma r theta)=r ∘ hullSatellitePermutation sigma := by
  simp only [orderedPolarSlice,polarSlice_radii]

@[simp] theorem orderedPolarSlice_angles (sigma : HullOrder) (r theta : Satellite → ℝ) :
    sliceAngles (orderedPolarSlice sigma r theta)=
      fun i => theta (hullSatellitePermutation sigma i)-theta (hullSatellitePermutation sigma 0) := by
  unfold orderedPolarSlice
  exact polarSlice_angles _ _ (sub_self _)

theorem orderedPolarSlice_contDiff (n : ℕ∞ω) (sigma : HullOrder) :
    ContDiff ℝ n (fun p : MassRatio × MassRatio => orderedPolarSlice sigma p.1 p.2) := by
  let e := hullSatellitePermutation sigma
  have hr : ContDiff ℝ n (fun p : MassRatio × MassRatio => p.1 ∘ e) := by
    apply contDiff_pi.mpr
    intro i
    exact (contDiff_apply ℝ ℝ (e i)).comp contDiff_fst
  have ht : ContDiff ℝ n (fun p : MassRatio × MassRatio =>
      fun i => p.2 (e i)-p.2 (e 0)) := by
    apply contDiff_pi.mpr
    intro i
    exact ((contDiff_apply ℝ ℝ (e i)).comp contDiff_snd).sub
      ((contDiff_apply ℝ ℝ (e 0)).comp contDiff_snd)
  exact (polarSlice_contDiff n).comp (hr.prodMk ht)

theorem orderedPolarSlice_physical_eq_rotation (eps : ℝ) (mu : MassRatio)
    (sigma : HullOrder) (r theta : Satellite → ℝ) (hr : ∀ i,0<r i) :
    slicePhysicalConfiguration (eps,mu ∘ hullSatellitePermutation sigma) (orderedPolarSlice sigma r theta)=
      rotateConfiguration (firstSatelliteRotation
        (centeredFromRelative eps mu (polarSatellites r theta) ∘ sigma.labels))
        (centeredFromRelative eps mu (polarSatellites r theta) ∘ sigma.labels) := by
  let e := hullSatellitePermutation sigma
  let x := centeredFromRelative eps mu (polarSatellites r theta) ∘ sigma.labels
  let R := firstSatelliteRotation x
  have hx : x=centeredFromRelative eps (mu ∘ e) (polarSatellites (r ∘ e) (theta ∘ e)) :=
    centeredFromRelative_hullReindex eps mu (polarSatellites r theta) sigma
  have hrel : satellitesRelative x 0=polarPoint (r (e 0)) (theta (e 0)) := by
    rw [hx,satellitesRelative_centeredFromRelative]
    rfl
  have ha : R (polarPoint (r (e 0)) (theta (e 0)))=polarPoint (r (e 0)) 0 := by
    have hh := firstSatelliteRotation_anchor x
    rw [hrel,polarPoint_norm,abs_of_pos (hr (e 0))] at hh
    simpa [R,polarPoint,point] using hh
  have hpolar : (fun i => R (polarSatellites (r ∘ e) (theta ∘ e) i))=
      polarSatellites (r ∘ e) (fun i => theta (e i)-theta (e 0)) := by
    funext i
    exact orientedIsometry_polar_shift R (firstSatelliteRotation_det x)
      (r (e 0)) (theta (e 0)) (hr (e 0)) ha (r (e i)) (theta (e i))
  rw [orderedPolarSlice,polarSlice_physical_eq _ _ _ _ (sub_self _)]
  change _=rotateConfiguration R x
  rw [hx,centeredFromRelative_rotate,hpolar]

theorem polarStrictConvex_orderedSemicircle (sigma : HullOrder) (r theta : Satellite → ℝ)
    (hr : ∀ i,0<r i) (hwidth : ∀ i j,|theta j-theta i|<Real.pi)
    (hconv : StrictConvexInOrder sigma (liftRelative (polarSatellites r theta))) :
    OrderedSemicircle (theta ∘ hullSatellitePermutation sigma) := by
  let e := hullSatellitePermutation sigma
  have hadj (i : Fin 3) : theta (e i.castSucc)<theta (e i.succ) := by
    let k : Label := i.castSucc.succ
    have harea := hconv k 0 (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    have hkplus : k+1=i.succ.succ := by fin_cases i <;> rfl
    rw [hkplus,orientedArea_cyclic,orientedArea_cyclic,sigma.primary_first,
      hullOrder_label_succ sigma i.castSucc,hullOrder_label_succ sigma i.succ] at harea
    change 0<det2 (polarPoint (r (e i.castSucc)) (theta (e i.castSucc))-0)
      (polarPoint (r (e i.succ)) (theta (e i.succ))-0) at harea
    rw [sub_zero,sub_zero,polarPoint_det] at harea
    have hsin := (mul_pos_iff_of_pos_left (mul_pos (hr (e i.castSucc)) (hr (e i.succ)))).mp harea
    apply sub_pos.mp
    by_contra hn
    have hsle := Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hn)
      (abs_lt.mp (hwidth (e i.castSucc) (e i.succ))).1.le
    exact (not_lt_of_ge hsle) hsin
  have hmono : StrictMono (theta ∘ e) := Fin.strictMono_iff_lt_succ.mpr hadj
  intro i j hij
  exact ⟨sub_pos.mpr (hmono hij),lt_of_le_of_lt (le_abs_self _) (hwidth (e i) (e j))⟩

theorem orderedPolarSlice_ordered (sigma : HullOrder) (r theta : Satellite → ℝ)
    (hr : ∀ i,0<r i) (hwidth : ∀ i j,|theta j-theta i|<Real.pi)
    (hconv : StrictConvexInOrder sigma (liftRelative (polarSatellites r theta))) :
    OrderedSemicircle (sliceAngles (orderedPolarSlice sigma r theta)) := by
  have hs := polarStrictConvex_orderedSemicircle sigma r theta hr hwidth hconv
  rw [orderedPolarSlice,polarSlice_angles _ _ (sub_self _)]
  intro i j hij
  convert! hs i j hij using 1 <;> dsimp [Function.comp_apply] <;> ring

theorem orderedPolarSlice_endpoint (mu : MassRatio) (sigma : HullOrder)
    (theta : Satellite → ℝ) (hm : PositiveRatio mu)
    (hwidth : ∀ i j,|theta j-theta i|<Real.pi)
    (hconv : StrictConvexInOrder sigma (liftRelative (polarSatellites (fun _ => 1) theta)))
    (hco : ∀ i,coorbitalResidual mu theta i=0) :
    orderedPolarSlice sigma (fun _ => 1) theta=coorbitalBaseSlice (mu ∘ hullSatellitePermutation sigma) := by
  let e := hullSatellitePermutation sigma
  have hme := positiveRatio_satellitePermutation mu hm e
  have hsorted := unitStrictConvex_orderedSemicircle sigma theta hwidth hconv
  have htheta := coorbitalRootAngles_eq_sorted_shift mu theta hm e hsorted hco
  apply sliceCoordinates_ext
  · rw [orderedPolarSlice,polarSlice_radii]
    funext i
    exact (coorbitalBaseSlice_radii _ i).symm
  · rw [orderedPolarSlice,polarSlice_angles _ _ (sub_self _),coorbitalBaseSlice_angles _ hme]
    exact htheta.symm

theorem orderedPolarSlice_normalized (eps : ℝ) (mu : MassRatio)
    (sigma : HullOrder) (r theta : Satellite → ℝ) (hr : ∀ i,0<r i)
    (hx : NormalizedCentralConfiguration (masses eps mu)
      (centeredFromRelative eps mu (polarSatellites r theta))) :
    NormalizedCentralConfiguration (masses eps (mu ∘ hullSatellitePermutation sigma))
      (slicePhysicalConfiguration (eps,mu ∘ hullSatellitePermutation sigma)
        (orderedPolarSlice sigma r theta)) := by
  have hp := normalizedCC_permutation _ _ hx sigma.labels
  have hmass : masses eps (mu ∘ hullSatellitePermutation sigma)=masses eps mu ∘ sigma.labels := by
    rw [masses_satellitePermutation,satelliteLabelPermutation_hull]
  rw [← hmass] at hp
  rw [orderedPolarSlice_physical_eq_rotation eps mu sigma r theta hr]
  exact normalizedCC_rotateConfiguration _ _ _ hp

/-- Actual normalized Newton equations in any hull order give the
literal seven-row root in the ordered first-angle slice. -/
theorem orderedPolarSlice_root_of_normalized (eps : ℝ) (mu : MassRatio)
    (sigma : HullOrder) (r theta : Satellite → ℝ)
    (hm : PositiveRatio mu) (heps : 0<eps) (hr : ∀ i,0<r i)
    (hwidth : ∀ i j,|theta j-theta i|<Real.pi)
    (hconv : StrictConvexInOrder sigma (liftRelative (polarSatellites r theta)))
    (hx : NormalizedCentralConfiguration (masses eps mu)
      (centeredFromRelative eps mu (polarSatellites r theta))) :
    orderedSliceRoot
      ⟨mu ∘ hullSatellitePermutation sigma,positiveRatio_satellitePermutation mu hm _⟩ eps
      (orderedPolarSlice sigma r theta) := by
  let e := hullSatellitePermutation sigma
  let r' := r ∘ e
  let theta' : Satellite → ℝ := fun i => theta (e i)-theta (e 0)
  have hm' := positiveRatio_satellitePermutation mu hm e
  have hr' : ∀ i,0<r' i := fun i => hr (e i)
  have hz : theta' 0=0 := sub_self _
  have hp := orderedPolarSlice_normalized eps mu sigma r theta hr hx
  have hrelative : satellitesRelative (slicePhysicalConfiguration (eps,mu ∘ e)
      (orderedPolarSlice sigma r theta))=polarSatellites r' theta' := by
    rw [slicePhysicalConfiguration_satellitesRelative]
    simp only [sliceSatellites,orderedPolarSlice_radii,orderedPolarSlice_angles]
    rfl
  have hcf : RelativeCollisionFree (satellitesRelative
      (slicePhysicalConfiguration (eps,mu ∘ e) (orderedPolarSlice sigma r theta))) := by
    constructor
    · intro i
      exact sub_ne_zero.mpr (hp.1 i.succ 0 (by simp))
    · intro i j hij heq
      exact hp.1 i.succ j.succ (fun h => hij (Fin.succ_inj.mp h)) (sub_left_inj.mp heq)
  rw [hrelative] at hcf
  have hrows := polarResiduals_zero_of_normalized eps (mu ∘ e) _ hp hm' heps r' theta' hr' hrelative
  refine ⟨polarSlice_regular eps (mu ∘ e) r' theta' (by linarith) hr' hz hcf,
    orderedPolarSlice_ordered sigma r theta hr hwidth hconv,?_,
    polarSlice_residual_zero eps (mu ∘ e) r' theta' hz hrows.1 hrows.2⟩
  rw [orderedPolarSlice_physical_eq_rotation eps mu sigma r theta hr]
  apply (strictConvex_rotateConfiguration_iff _ _ _ (firstSatelliteRotation_det _)).mpr
  apply (strictConvex_hull_reindex_iff sigma _).mpr
  exact (strictConvex_centeredFromRelative_iff sigma eps mu (polarSatellites r theta)).mpr hconv

/-- The original six-dimensional shape Hessian is transported with
the same actual masses, labels and orientation-preserving rotation. -/
theorem orderedPolarSlice_nondegenerate_of_normalized (eps : ℝ) (mu : MassRatio)
    (sigma : HullOrder) (r theta : Satellite → ℝ)
    (hm : PositiveRatio mu) (hr : ∀ i,0<r i)
    (hx : NormalizedCentralConfiguration (masses eps mu)
      (centeredFromRelative eps mu (polarSatellites r theta)))
    (hn : ShapeHessianNondegenerate (masses eps mu) 1
      (centeredFromRelative eps mu (polarSatellites r theta))) :
    orderedSliceNondegenerate
      ⟨mu ∘ hullSatellitePermutation sigma,positiveRatio_satellitePermutation mu hm _⟩ eps
      (orderedPolarSlice sigma r theta) := by
  have hp := normalizedCC_permutation _ _ hx sigma.labels
  have hnp := shapeHessianNondegenerate_permutation_forward _ _ hx sigma.labels hn
  have hmass : masses eps (mu ∘ hullSatellitePermutation sigma)=masses eps mu ∘ sigma.labels := by
    rw [masses_satellitePermutation,satelliteLabelPermutation_hull]
  rw [← hmass] at hp hnp
  unfold orderedSliceNondegenerate
  rw [orderedPolarSlice_physical_eq_rotation eps mu sigma r theta hr]
  exact shapeHessianNondegenerate_rotateConfiguration_forward _ 1 _ _ hp.1
    (firstSatelliteRotation_det _) hnp

end DominantFiveBody
