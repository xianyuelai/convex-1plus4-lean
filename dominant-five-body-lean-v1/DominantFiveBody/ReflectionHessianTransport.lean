import DominantFiveBody.CollisionReflection

/-! Reflection transports the actual shape space and Hessian.  Its sign
on the infinitesimal rotation direction leaves the orthogonality equation
unchanged. It is used for proof transport only.
-/

noncomputable section
open scoped BigOperators
namespace DominantFiveBody

@[simp] theorem planeReflection_twice (v : Plane) : planeReflection (planeReflection v)=v := by
  ext i
  fin_cases i <;> simp [planeReflection,point]

theorem rotateConfiguration_planeReflection_twice (x : Configuration) :
    rotateConfiguration planeReflection (rotateConfiguration planeReflection x)=x := by
  funext i
  exact planeReflection_twice _

theorem massInner_rotation_planeReflection (m : MassVector) (v w : Configuration) :
    massInner m (rotationDirection (rotateConfiguration planeReflection v))
      (rotateConfiguration planeReflection w)= -massInner m (rotationDirection v) w := by
  simp only [massInner,rotationDirection,rotateConfiguration,quarterTurn_inner_eq_det2,
    planeReflection_det2,mul_neg,Finset.sum_neg_distrib]

theorem shapeSpace_planeReflection_mem_iff (m : MassVector) (x v : Configuration) :
    rotateConfiguration planeReflection v ∈ shapeSpace m (rotateConfiguration planeReflection x) ↔
      v∈shapeSpace m x := by
  rw [mem_shapeSpace_iff,mem_shapeSpace_iff,centered_rotateConfiguration,
    weightedPosition_rotateConfiguration,massInner_rotateConfiguration,
    massInner_rotation_planeReflection,planeReflection.map_eq_zero_iff,neg_eq_zero]

theorem shapeHessianNondegenerate_planeReflection_forward (m : MassVector) (lam : ℝ)
    (x : Configuration) (hx : CollisionFree x) (hn : ShapeHessianNondegenerate m lam x) :
    ShapeHessianNondegenerate m lam (rotateConfiguration planeReflection x) := by
  intro v hv hk
  let u := rotateConfiguration planeReflection v
  have hrecover : rotateConfiguration planeReflection u=v := rotateConfiguration_planeReflection_twice v
  have hu : u∈shapeSpace m x := by
    apply (shapeSpace_planeReflection_mem_iff m x u).mp
    rwa [hrecover]
  have hz := hn u hu (by
    intro w hw
    have hh := hk (rotateConfiguration planeReflection w)
      ((shapeSpace_planeReflection_mem_iff m x w).mpr hw)
    rw [←hrecover,physicalHessian_rotateConfiguration m lam planeReflection x hx u w] at hh
    exact hh)
  rw [←hrecover,hz]
  funext i
  exact planeReflection.map_zero

theorem mirrorConfiguration_shapeHessianNondegenerate (eps : ℝ) (mu : MassRatio)
    (x : Configuration) (hx : NormalizedCentralConfiguration (masses eps mu) x)
    (hn : ShapeHessianNondegenerate (masses eps mu) 1 x) :
    ShapeHessianNondegenerate (masses eps (mu ∘ Fin.revPerm)) 1 (mirrorConfiguration x) := by
  rw [masses_satellitePermutation]
  apply shapeHessianNondegenerate_planeReflection_forward _ 1 _
    (normalizedCC_permutation _ _ hx reversedSatelliteLabels).1
  exact shapeHessianNondegenerate_permutation_forward _ _ hx reversedSatelliteLabels hn

end DominantFiveBody
