import DominantFiveBody.LocalContinuation
import DominantFiveBody.RowTransform

/-! Explicit replacement of the omitted divided angular row. -/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

/-- Recover the zero-labelled divided row using the actual mass-weighted
angular identity. The other three entries are retained verbatim. -/
def restoreZeroAngularRows (μ : MassRatio) : (Fin 3 → ℝ) →L[ℝ] (Satellite → ℝ) :=
  ContinuousLinearMap.pi (fun i => Fin.cases
    ((- (μ 0)⁻¹) • ∑ j : Fin 3, μ j.succ •
      (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ))
    (fun j => ContinuousLinearMap.proj j) i)

@[simp] theorem restoreZeroAngularRows_zero (μ : MassRatio) (a : Fin 3 → ℝ) :
    restoreZeroAngularRows μ a 0 = -(μ 0)⁻¹ * ∑ j : Fin 3, μ j.succ * a j := by
  simp [restoreZeroAngularRows, smul_eq_mul]

@[simp] theorem restoreZeroAngularRows_succ (μ : MassRatio) (a : Fin 3 → ℝ) (j : Fin 3) :
    restoreZeroAngularRows μ a j.succ = a j := by simp [restoreZeroAngularRows]

theorem restoreZeroAngularRows_weighted_zero (μ : MassRatio) (hμ₀ : μ 0 ≠ 0)
    (a : Fin 3 → ℝ) : (∑ i, μ i * restoreZeroAngularRows μ a i) = 0 := by
  rw [Fin.sum_univ_succ]
  simp only [restoreZeroAngularRows_zero, restoreZeroAngularRows_succ]
  rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hμ₀]
  ring

def deletedAngularRowsProjection (q : Satellite) : (Satellite → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun j => ContinuousLinearMap.proj (q.succAbove j))

@[simp] theorem deletedAngularRowsProjection_apply (q : Satellite) (v : Satellite → ℝ) (j : Fin 3) :
    deletedAngularRowsProjection q v j = v (q.succAbove j) := rfl

/-- The actual three-by-three change from omitting row zero to omitting
row q. At zero satellite masses this map need not be invertible. -/
def deletedAngularRowsTransform (μ : MassRatio) (q : Satellite) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (deletedAngularRowsProjection q).comp (restoreZeroAngularRows μ)

theorem weighted_rows_recover (μ v : Satellite → ℝ) (q : Satellite) (hμq : μ q ≠ 0)
    (hweighted : (∑ i, μ i * v i) = 0) (hothers : ∀ i, i ≠ q → v i = 0) : v q = 0 := by
  have hsum : (∑ i, μ i * v i) = μ q * v q := by
    apply Finset.sum_eq_single q
    · intro i _ hi; rw [hothers i hi, mul_zero]
    · simp
  rw [hsum] at hweighted
  exact (mul_eq_zero.mp hweighted).resolve_left hμq

theorem deletedAngularRowsTransform_isInvertible (μ : MassRatio) (q : Satellite)
    (hμ₀ : μ 0 ≠ 0) (hμq : μ q ≠ 0) : (deletedAngularRowsTransform μ q).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro a b hab
  let v := restoreZeroAngularRows μ (a - b)
  have hrows : ∀ i : Satellite, i ≠ q → v i = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    have h := congrFun hab j
    change restoreZeroAngularRows μ a (q.succAbove j) = restoreZeroAngularRows μ b (q.succAbove j) at h
    simpa only [v, map_sub, Pi.sub_apply, sub_eq_zero] using h
  have hvq : v q = 0 := weighted_rows_recover μ v q hμq
    (restoreZeroAngularRows_weighted_zero μ hμ₀ (a - b)) hrows
  have hv : ∀ i, v i = 0 := fun i => if hi : i = q then hi ▸ hvq else hrows i hi
  funext j
  have h := hv j.succ
  simpa only [v, restoreZeroAngularRows_succ, Pi.sub_apply, sub_eq_zero] using h

def deletedReducedResidual (p : ContinuationParameter) (q : Satellite)
    (y : SliceCoordinates) : SliceCoordinates :=
  Fin.append (radialResidual p.1 p.2 (sliceRadii y) (sliceAngles y))
    (fun j : Fin 3 => angularResidual p.1 p.2 (sliceRadii y) (sliceAngles y) (q.succAbove j))

def deletedReducedRowTransform (μ : MassRatio) (q : Satellite) :
    SliceCoordinates →L[ℝ] SliceCoordinates :=
  ContinuousLinearMap.pi (fun k => Fin.addCases
    (fun i : Fin 4 => ContinuousLinearMap.proj (i.castAdd 3))
    (fun j : Fin 3 => (ContinuousLinearMap.proj j).comp
      ((deletedAngularRowsTransform μ q).comp sliceFreeAngleProjection)) k)

@[simp] theorem deletedReducedRowTransform_radial (μ : MassRatio) (q : Satellite)
    (v : SliceCoordinates) (i : Satellite) :
    deletedReducedRowTransform μ q v (i.castAdd 3) = v (i.castAdd 3) := by
  simp [deletedReducedRowTransform]

@[simp] theorem deletedReducedRowTransform_angular (μ : MassRatio) (q : Satellite)
    (v : SliceCoordinates) (j : Fin 3) :
    deletedReducedRowTransform μ q v (j.natAdd 4) =
      deletedAngularRowsTransform μ q (sliceFreeAngleProjection v) j := by
  simp [deletedReducedRowTransform]

theorem deletedReducedRowTransform_isInvertible (μ : MassRatio) (q : Satellite)
    (hμ₀ : μ 0 ≠ 0) (hμq : μ q ≠ 0) : (deletedReducedRowTransform μ q).IsInvertible := by
  apply euclidean_clm_isInvertible_of_injective
  intro a b hab
  have hangle : sliceFreeAngleProjection a = sliceFreeAngleProjection b := by
    apply (deletedAngularRowsTransform_isInvertible μ q hμ₀ hμq).injective
    funext j
    have h := congrFun hab (j.natAdd 4)
    simpa only [deletedReducedRowTransform_angular] using h
  funext k
  refine Fin.addCases (motive := fun k => a k = b k)
    (fun i : Fin 4 => ?_) (fun j : Fin 3 => ?_) k
  · have h := congrFun hab (i.castAdd 3)
    simpa only [deletedReducedRowTransform_radial] using h
  · exact congrFun hangle j

theorem restoreZeroAngularRows_actual (p : ContinuationParameter) (y : SliceCoordinates)
    (hμ₀ : p.2 0 ≠ 0) :
    restoreZeroAngularRows p.2 (fun j : Fin 3 =>
      angularResidual p.1 p.2 (sliceRadii y) (sliceAngles y) j.succ) =
        (fun i => angularResidual p.1 p.2 (sliceRadii y) (sliceAngles y) i) := by
  let t : Satellite → ℝ := fun i => angularResidual p.1 p.2 (sliceRadii y) (sliceAngles y) i
  let a : Fin 3 → ℝ := fun j => t j.succ
  have hdweighted : (∑ i, p.2 i * (restoreZeroAngularRows p.2 a i - t i)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, restoreZeroAngularRows_weighted_zero p.2 hμ₀ a,
      weighted_angularResidual_zero]
    simp
  have hdothers : ∀ i : Satellite, i ≠ 0 → restoreZeroAngularRows p.2 a i - t i = 0 := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    simp [a]
  have hd0 := weighted_rows_recover p.2 (fun i => restoreZeroAngularRows p.2 a i - t i)
    0 hμ₀ hdweighted hdothers
  funext i
  by_cases hi : i = 0
  · subst i; exact sub_eq_zero.mp hd0
  · exact sub_eq_zero.mp (hdothers i hi)

theorem deletedReducedResidual_eq_row_transform (p : ContinuationParameter)
    (q : Satellite) (hμ₀ : p.2 0 ≠ 0) (y : SliceCoordinates) :
    deletedReducedResidual p q y = deletedReducedRowTransform p.2 q (reducedResidual p y) := by
  funext k
  refine Fin.addCases (motive := fun k => deletedReducedResidual p q y k =
      deletedReducedRowTransform p.2 q (reducedResidual p y) k)
    (fun i : Fin 4 => ?_) (fun j : Fin 3 => ?_) k
  · simp [deletedReducedResidual, reducedResidual]
  · simp only [deletedReducedResidual, Fin.append_right, deletedReducedRowTransform_angular]
    have ha : sliceFreeAngleProjection (reducedResidual p y) =
        fun j : Fin 3 => angularResidual p.1 p.2 (sliceRadii y) (sliceAngles y) j.succ := by
      ext j
      simp only [sliceFreeAngleProjection_apply, reducedResidual, Fin.append_right]
    simp only [deletedAngularRowsTransform, ContinuousLinearMap.comp_apply, ha,
      restoreZeroAngularRows_actual p y hμ₀, deletedAngularRowsProjection_apply]

theorem deletedReducedResidual_zero_iff (p : ContinuationParameter) (q : Satellite)
    (hμ₀ : p.2 0 ≠ 0) (hμq : p.2 q ≠ 0) (y : SliceCoordinates) :
    deletedReducedResidual p q y = 0 ↔ reducedResidual p y = 0 := by
  rw [deletedReducedResidual_eq_row_transform p q hμ₀ y]
  exact (deletedReducedRowTransform_isInvertible p.2 q hμ₀ hμq).injective.eq_iff' (map_zero _)

theorem deletedReducedResidual_fderiv (p : ContinuationParameter) (q : Satellite)
    (y : SliceCoordinates) (hreg : SliceRegular p y) (hμ₀ : p.2 0 ≠ 0) :
    fderiv ℝ (deletedReducedResidual p q) y =
      (deletedReducedRowTransform p.2 q).comp (reducedJacobian p y) := by
  have heq : deletedReducedResidual p q =
      fun z => deletedReducedRowTransform p.2 q (reducedResidual p z) :=
    funext (deletedReducedResidual_eq_row_transform p q hμ₀)
  rw [heq]
  have hdiff : DifferentiableAt ℝ (reducedResidual p) y := by
    have hc : ContDiff ℝ 1 (fun z : SliceCoordinates => (p, z)) := contDiff_const.prodMk contDiff_id
    exact ((reducedResidual_joint_contDiffAt 1 p y hreg).comp y hc.contDiffAt).differentiableAt
      (by norm_num)
  exact ((deletedReducedRowTransform p.2 q).hasFDerivAt.comp y hdiff.hasFDerivAt).fderiv

/-- Concrete arbitrary omitted-row instance of Lemma 3.1. The row map is
the explicitly constructed actual weighted recovery map above. -/
theorem deletedReducedJacobian_isInvertible_iff_shape (p : ContinuationParameter)
    (q : Satellite) (y : SliceCoordinates) (hreg : SliceRegular p y) (hε : 0 < p.1)
    (hμ : PositiveRatio p.2) (hroot : deletedReducedResidual p q y = 0) :
    (fderiv ℝ (deletedReducedResidual p q) y).IsInvertible ↔
      ShapeHessianNondegenerate (masses p.1 p.2) 1 (slicePhysicalConfiguration p y) := by
  have hm0 : p.2 0 ≠ 0 := ne_of_gt (hμ.1 0)
  have hmq : p.2 q ≠ 0 := ne_of_gt (hμ.1 q)
  have hzero := (deletedReducedResidual_zero_iff p q hm0 hmq y).mp hroot
  rw [deletedReducedResidual_fderiv p q y hreg hm0]
  obtain ⟨e, he⟩ := deletedReducedRowTransform_isInvertible p.2 q hm0 hmq
  rw [← he, ContinuousLinearMap.isInvertible_equiv_comp]
  exact reducedJacobian_isInvertible_iff_shape p y hreg hε hμ hzero

end DominantFiveBody
