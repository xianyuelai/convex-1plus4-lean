import DominantFiveBody.NoCollisionContinuation

/-! The manuscript's largest-mass gauge and full seven-row boundary matrix.
The smooth equation is defined for all nearby signed mass parameters. -/
noncomputable section
open scoped BigOperators ContDiff Matrix
namespace DominantFiveBody

theorem closedMass_exists_quarter (mu : MassRatio) (hsum : ∑ i,mu i=1) :
    ∃ p : Satellite,(1/4:ℝ)≤mu p := by
  by_contra! h
  simp only [Fin.sum_univ_four] at hsum
  linarith [h 0,h 1,h 2,h 3]

theorem fixedAngleDeletedResidual_same_eq (eps : ℝ) (mu : MassRatio) (p : Satellite) :
    fixedAngleDeletedResidual (eps,mu) p p = reducedResidual (eps,mu ∘ fixedAnglePermutation p) := by
  rw [fixedAngleDeletedResidual_eq]
  have hz : (fixedAnglePermutation p).symm p=0 := by simp [fixedAnglePermutation]
  rw [hz]
  funext y i
  refine Fin.addCases (motive := fun i =>
    deletedReducedResidual (eps,mu ∘ fixedAnglePermutation p) 0 y i=
      reducedResidual (eps,mu ∘ fixedAnglePermutation p) y i)
    (fun k : Fin 4 => ?_) (fun k : Fin 3 => ?_) i
  · rfl
  · simp [deletedReducedResidual,reducedResidual]

theorem closedCoorbital_largest_mass_gauge (mu theta : Satellite → ℝ)
    (hm : ∀ i,0≤mu i) (hsum : ∑ i,mu i=1) (hsep : SeparatedSemicircle theta)
    (hroot : ∀ i,coorbitalResidual mu theta i=0) :
    ∃ p : Satellite,∃ y : SliceCoordinates,
      (1/4:ℝ)≤mu p ∧ (∀ i,sliceRadii y i=1) ∧
      (∀ i,fixedAngleAngles p y i=theta i-theta p) ∧
      SeparatedSemicircle (sliceAngles y) ∧
      fixedAngleDeletedResidual (0,mu) p p y=0 ∧
      (fderiv ℝ (fixedAngleDeletedResidual (0,mu) p p) y).IsInvertible ∧
      ContDiffAt ℝ ∞ (fun z : ContinuationParameter × SliceCoordinates =>
        reducedResidual z.1 z.2) ((0,mu ∘ fixedAnglePermutation p),y) := by
  obtain ⟨p,hp⟩ := closedMass_exists_quarter mu hsum
  let e := fixedAnglePermutation p
  let theta' : Satellite → ℝ := fun i => theta (e i)-theta p
  let y := coorbitalSliceOfAngles theta'
  have hzero : theta' 0=0 := by simp [theta',e,fixedAnglePermutation]
  have hy : sliceAngles y=theta' := coorbitalSliceOfAngles_angles theta' hzero
  have hu : ∀ i,sliceRadii y i=1 := coorbitalSliceOfAngles_radii theta'
  have hs : SeparatedSemicircle (sliceAngles y) := by
    rw [hy]
    intro i j hij
    have h := hsep (e i) (e j) (e.injective.ne hij)
    constructor
    · dsimp [theta']; exact sub_left_inj.ne.mpr h.1
    · simpa only [theta',sub_sub_sub_cancel_right] using h.2
  have hm' : ∀ i,0≤(mu ∘ e) i := fun i => hm (e i)
  have hsum' : ∑ i,(mu ∘ e) i=1 := (Equiv.sum_comp e mu).trans hsum
  have hp' : 0<(mu ∘ e) 0 := by
    simp only [Function.comp_apply,e,fixedAnglePermutation,Equiv.swap_apply_left]
    linarith
  have hr : ∀ i,coorbitalResidual (mu ∘ e) (sliceAngles y) i=0 := by
    rw [hy]
    intro i
    rw [coorbitalResidual_sub_constant]
    change coorbitalResidual (mu ∘ e) (theta ∘ e) i=0
    rw [coorbitalResidual_reindex]
    exact hroot (e i)
  have hreg := sliceRegular_at_coorbital_separated (mu ∘ e) y hu hs
  refine ⟨p,y,hp,hu,?_,hs,?_,?_,reducedResidual_joint_contDiffAt ∞ _ y hreg⟩
  · intro i
    change sliceAngles y (e.symm i)=theta i-theta p
    rw [hy]
    simp [theta']
  · rw [fixedAngleDeletedResidual_same_eq]
    exact reducedResidual_at_coorbital_root_separated _ y hu hs hr
  · rw [fixedAngleDeletedResidual_same_eq]
    exact reducedJacobian_at_closed_separated_root_isInvertible _ y hu hm' hsum' hp' hs hr

theorem sliceAngleInjection_single (j : Fin 3) :
    sliceAngleInjection (Pi.single j (1:ℝ))=Pi.single (j.natAdd 4) 1 := by
  ext k
  refine Fin.addCases (motive := fun k =>
    sliceAngleInjection (Pi.single j (1:ℝ)) k=(Pi.single (j.natAdd 4) (1:ℝ) : SliceCoordinates) k)
    (fun i : Fin 4 => ?_) (fun i : Fin 3 => ?_) k
  · have hn : (i.castAdd 3 : Fin 7)≠j.natAdd 4 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    simp [hn]
  · have hi : (i.natAdd 4 : Fin 7)=j.natAdd 4 ↔ i=j := by
      constructor
      · intro h; exact Fin.ext (by have := congrArg Fin.val h; simpa using this)
      · exact congrArg _
    simp [Pi.single_apply,hi]

theorem reducedJacobian_zero_full_block (mu : MassRatio) (y : SliceCoordinates)
    (hreg : SliceRegular (0,mu) y) (hunit : ∀ i,sliceRadii y i=1) :
    (LinearMap.toMatrix' (reducedJacobian (0,mu) y).toLinearMap).submatrix
      finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks ((3:ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) 0
        (fun i j => reducedJacobian (0,mu) y (Pi.single (j.castAdd 3) 1) (i.natAdd 4))
        (LinearMap.toMatrix' (reducedAngularJacobian (0,mu) y).toLinearMap) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · change reducedJacobian (0,mu) y (Pi.single (j.castAdd 3) 1) (i.castAdd 3)=_
    rw [reducedJacobian_zero_radial_block mu y hreg hunit]
    change 3*(Pi.single (j.castAdd 3) (1:ℝ) : SliceCoordinates) (i.castAdd 3)=
      (3:ℝ)*(if i=j then 1 else 0)
    congr 1
    have hi : (i.castAdd 3 : Fin 7)=j.castAdd 3 ↔ i=j := by
      constructor
      · intro h
        have hv := congrArg (fun k : Fin 7 => k.val) h
        exact Fin.ext hv
      · exact congrArg _
    simp only [Pi.single_apply,hi]
  · change reducedJacobian (0,mu) y (Pi.single (j.natAdd 4) 1) (i.castAdd 3)=_
    rw [reducedJacobian_zero_radial_block mu y hreg hunit]
    have hn : (i.castAdd 3 : Fin 7)≠j.natAdd 4 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    simp [sliceRadii,Matrix.fromBlocks,hn]
  · rfl
  · change reducedJacobian (0,mu) y (Pi.single (j.natAdd 4) 1) (i.natAdd 4)=
      reducedAngularJacobian (0,mu) y (Pi.single j 1) i
    rw [← sliceAngleInjection_single]
    rfl

theorem reducedAngularJacobian_zero_full_matrix (mu : MassRatio) (y : SliceCoordinates)
    (hreg : SliceRegular (0,mu) y) (hunit : ∀ i,sliceRadii y i=1)
    (hsep : SeparatedSemicircle (sliceAngles y)) :
    LinearMap.toMatrix' (reducedAngularJacobian (0,mu) y).toLinearMap=
      deletedAngularJacobian mu (sliceAngles y) 0 0 := by
  ext i j
  rw [LinearMap.toMatrix'_apply,reducedAngularJacobian_zero_eq_separated mu y hreg hunit hsep]
  change angularDifferential mu (sliceAngles y) (coorbitalAngleInjection (Pi.single j 1)) i.succ=_
  have hinj : coorbitalAngleInjection (Pi.single j (1:ℝ))=
      Fin.insertNth (0:Satellite) 0 (Pi.single j 1) := by
    ext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp
    · simp
  rw [hinj]
  simpa [Matrix.mulVec_single] using
    (deletedAngularJacobian_action mu (sliceAngles y) 0 0 (Pi.single j 1) i).symm

theorem fixedAngle_zero_source_full_block (mu : MassRatio) (p : Satellite)
    (y : SliceCoordinates) (hunit : ∀ i,sliceRadii y i=1)
    (hsep : SeparatedSemicircle (sliceAngles y)) :
    ∃ L : Matrix (Fin 3) (Fin 4) ℝ,
      (LinearMap.toMatrix' (fderiv ℝ (fixedAngleDeletedResidual (0,mu) p p) y).toLinearMap).submatrix
        finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks ((3:ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)) 0 L
          (deletedAngularJacobian (mu ∘ fixedAnglePermutation p) (sliceAngles y) 0 0) := by
  let m := mu ∘ fixedAnglePermutation p
  have hreg := sliceRegular_at_coorbital_separated m y hunit hsep
  refine ⟨fun i j => reducedJacobian (0,m) y (Pi.single (j.castAdd 3) 1) (i.natAdd 4),?_⟩
  rw [fixedAngleDeletedResidual_same_eq]
  change (LinearMap.toMatrix' (reducedJacobian (0,m) y).toLinearMap).submatrix
    (finSumFinEquiv : (Fin 4 ⊕ Fin 3) ≃ Fin 7)
    (finSumFinEquiv : (Fin 4 ⊕ Fin 3) ≃ Fin 7) = _
  rw [reducedJacobian_zero_full_block m y hreg hunit,
    reducedAngularJacobian_zero_full_matrix m y hreg hunit hsep]

end DominantFiveBody
