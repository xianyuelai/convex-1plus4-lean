import DominantFiveBody.Similarity
import DominantFiveBody.ConvexContinuation
import DominantFiveBody.ShapeDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Genuine normalization of the original geometric central configuration

Only a positive scale and a translation are used.  The original labels
and hull order are preserved, and the actual second derivative is
transported to the multiplier-one representative.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace DominantFiveBody

def positiveAffineConfiguration (a : ℝ) (b : Plane) (x : Configuration) : Configuration :=
  fun i => a • (x i-b)

theorem positiveAffineConfiguration_orientedSimilar (a : ℝ) (b : Plane)
    (x : Configuration) (ha : 0<a) : OrientedSimilar x (positiveAffineConfiguration a b x) := by
  refine ⟨-(a • b),a,LinearIsometryEquiv.refl ℝ Plane,ha,by simp,?_⟩
  intro i
  change a • (x i-b)=-(a • b)+a • x i
  rw [smul_sub]
  abel

theorem positiveAffineConfiguration_distance (a : ℝ) (b : Plane) (x : Configuration)
    (ha : 0<a) (i j : Label) :
    pairDistance (positiveAffineConfiguration a b x) i j=a*pairDistance x i j := by
  unfold pairDistance positiveAffineConfiguration
  rw [←smul_sub]
  have hd : (x i-b)-(x j-b)=x i-x j := by abel
  rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos ha]

theorem positiveAffineConfiguration_acceleration (m : MassVector) (a : ℝ) (b : Plane)
    (x : Configuration) (ha : 0<a) (hx : CollisionFree x) (i : Label) :
    acceleration m (positiveAffineConfiguration a b x) i=a⁻¹^2 • acceleration m x i := by
  unfold acceleration
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i≠j := (Finset.mem_erase.mp hj).1.symm
  have hd := collision_distance_cube_ne_zero x hx i j hij
  rw [positiveAffineConfiguration_distance a b x ha]
  have hv : positiveAffineConfiguration a b x j-positiveAffineConfiguration a b x i=
      a • (x j-x i) := by simp only [positiveAffineConfiguration,←smul_sub]; congr 1; abel
  rw [hv,smul_smul,smul_smul]
  congr 1
  field_simp [ha.ne',hd]

theorem weightedPosition_positiveAffineConfiguration (m : MassVector) (a : ℝ)
    (b : Plane) (x : Configuration) :
    weightedPosition m (positiveAffineConfiguration a b x)=
      a • (weightedPosition m x-totalMass m • b) := by
  unfold positiveAffineConfiguration
  have he : weightedPosition m (fun i => a • (x i-b))=
      a • weightedPosition m (fun i => x i-b) := by
    simp only [weightedPosition,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul,smul_smul,mul_comm]
  rw [he,weightedPosition_translate]

theorem massCenter_positiveAffineConfiguration (m : MassVector) (a : ℝ)
    (b : Plane) (x : Configuration) (hM : totalMass m≠0) :
    massCenter m (positiveAffineConfiguration a b x)=a • (massCenter m x-b) := by
  rw [massCenter,weightedPosition_positiveAffineConfiguration]
  simp only [smul_sub,smul_smul,massCenter]
  simp [mul_comm,hM]

theorem centered_positiveAffineConfiguration (m : MassVector) (a : ℝ)
    (b : Plane) (x : Configuration) (hM : totalMass m≠0) :
    centered m (positiveAffineConfiguration a b x)=a • centered m x := by
  funext i
  change a • (x i-b)-massCenter m (positiveAffineConfiguration a b x)=
    a • (x i-massCenter m x)
  rw [massCenter_positiveAffineConfiguration m a b x hM]
  module
theorem orientedArea_positiveAffineConfiguration (a : ℝ) (b : Plane)
    (x : Configuration) (i j k : Label) :
    orientedArea (positiveAffineConfiguration a b x) i j k=a^2*orientedArea x i j k := by
  simp only [orientedArea,positiveAffineConfiguration,det2,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  ring

theorem strictConvex_positiveAffineConfiguration_iff (σ : HullOrder) (a : ℝ)
    (b : Plane) (x : Configuration) (ha : 0<a) :
    StrictConvexInOrder σ (positiveAffineConfiguration a b x) ↔ StrictConvexInOrder σ x := by
  simp only [StrictConvexInOrder,orientedArea_positiveAffineConfiguration,
    mul_pos_iff_of_pos_left (sq_pos_of_pos ha)]

theorem normalizedCC_of_positiveAffine_multiplier (m : MassVector) (x : Configuration)
    (hx : CollisionFree x) (lam a : ℝ) (ha : 0<a) (hscale : a^3=lam)
    (hM : totalMass m≠0) (hroot : MultiplierEquation m x lam) :
    NormalizedCentralConfiguration m (positiveAffineConfiguration a (massCenter m x) x) := by
  have hsimilar := positiveAffineConfiguration_orientedSimilar a (massCenter m x) x ha
  refine ⟨collisionFree_of_orientedSimilar hx hsimilar,?_,?_⟩
  · rw [weightedPosition_positiveAffineConfiguration]
    simp only [massCenter,smul_smul,mul_inv_cancel₀ hM,one_smul,sub_self,smul_zero]
  · intro i
    rw [positiveAffineConfiguration_acceleration m a (massCenter m x) x ha hx i,hroot i]
    rw [smul_smul]
    change (a⁻¹^2*(-lam)) • (x i-massCenter m x)=- (a • (x i-massCenter m x))
    rw [←hscale]
    have hc : a⁻¹^2*(-a^3)=-a := by field_simp [ha.ne']
    rw [hc,neg_smul]

theorem centralConfiguration_has_normalized_representative (m : MassVector)
    (hm : PositiveMasses m) (x : Configuration) (hx : CentralConfiguration m x) :
    ∃ y, NormalizedCentralConfiguration m y ∧ OrientedSimilar x y := by
  obtain ⟨hcollision,lam,hlam,hroot⟩ := hx
  let a := Real.rpow lam (1/3)
  have ha : 0<a := Real.rpow_pos_of_pos hlam _
  have hscale : a^3=lam := by
    simpa [a,one_div] using Real.rpow_inv_natCast_pow hlam.le (by decide : (3 : ℕ)≠0)
  exact ⟨positiveAffineConfiguration a (massCenter m x) x,
    normalizedCC_of_positiveAffine_multiplier m x hcollision lam a ha hscale
      (ne_of_gt (totalMass_pos m hm)) hroot,
    positiveAffineConfiguration_orientedSimilar a (massCenter m x) x ha⟩

theorem strictConvexCC_has_normalized_representative (m : MassVector)
    (hm : PositiveMasses m) (σ : HullOrder) (x : Configuration)
    (hx : StrictConvexCentralConfiguration m σ x) :
    ∃ y, NormalizedCentralConfiguration m y ∧ StrictConvexInOrder σ y ∧ OrientedSimilar x y := by
  obtain ⟨hcollision,lam,hlam,hroot⟩ := hx.1
  let a := Real.rpow lam (1/3)
  have ha : 0<a := Real.rpow_pos_of_pos hlam _
  have hscale : a^3=lam := by
    simpa [a,one_div] using Real.rpow_inv_natCast_pow hlam.le (by decide : (3 : ℕ)≠0)
  exact ⟨positiveAffineConfiguration a (massCenter m x) x,
    normalizedCC_of_positiveAffine_multiplier m x hcollision lam a ha hscale
      (ne_of_gt (totalMass_pos m hm)) hroot,
    (strictConvex_positiveAffineConfiguration_iff σ a (massCenter m x) x ha).mpr hx.2,
    positiveAffineConfiguration_orientedSimilar a (massCenter m x) x ha⟩

theorem positiveAffineConfiguration_sub (a : ℝ) (b : Plane) (x : Configuration) (i j : Label) :
    positiveAffineConfiguration a b x i-positiveAffineConfiguration a b x j=a • (x i-x j) := by
  simp only [positiveAffineConfiguration,←smul_sub]
  congr 1; abel

/-- The actual nested second derivative has the Newtonian scale factor
`a⁻³`, provided its multiplier is scaled by the same factor. -/
theorem physicalHessian_positiveAffineConfiguration (m : MassVector) (lam a : ℝ)
    (b : Plane) (x : Configuration) (ha : 0<a) (hx : CollisionFree x) (v w : Configuration) :
    physicalHessian m (lam/a^3) (positiveAffineConfiguration a b x) v w=
      a⁻¹^3*physicalHessian m lam x v w := by
  have hy := collisionFree_of_orientedSimilar hx (positiveAffineConfiguration_orientedSimilar a b x ha)
  rw [physicalHessian_explicit m (lam/a^3) _ hy,physicalHessian_explicit m lam x hx,
    mul_add,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    have hij : p.1≠p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
    have hd : pairDistance x p.1 p.2≠0 := ne_of_gt (collision_distance_pos x hx p.1 p.2 hij)
    rw [positiveAffineConfiguration_distance a b x ha,
      positiveAffineConfiguration_sub,real_inner_smul_left,real_inner_smul_left]
    field_simp [ha.ne',hd]
  · field_simp [ha.ne']

theorem massInner_smul_left (m : MassVector) (u v : Configuration) (a : ℝ) :
    massInner m (a • u) v=a*massInner m u v := by
  rw [massInner_comm,massInner_smul_right,massInner_comm]

theorem rotationDirection_smul (a : ℝ) (x : Configuration) :
    rotationDirection (a • x)=a • rotationDirection x := by
  funext i
  exact quarterTurnLinear.map_smul a (x i)

theorem shapeSpace_positiveAffineConfiguration (m : MassVector) (a : ℝ)
    (b : Plane) (x : Configuration) (ha : 0<a) (hM : totalMass m≠0) :
    shapeSpace m (positiveAffineConfiguration a b x)=shapeSpace m x := by
  ext v
  rw [mem_shapeSpace_iff,mem_shapeSpace_iff,centered_positiveAffineConfiguration m a b x hM,
    rotationDirection_smul,massInner_smul_left,massInner_smul_left]
  simp only [mul_eq_zero,ha.ne',false_or]

theorem shapeHessianNondegenerate_positiveAffineConfiguration_iff (m : MassVector)
    (lam a : ℝ) (b : Plane) (x : Configuration) (ha : 0<a)
    (hM : totalMass m≠0) (hx : CollisionFree x) :
    ShapeHessianNondegenerate m (lam/a^3) (positiveAffineConfiguration a b x) ↔
      ShapeHessianNondegenerate m lam x := by
  unfold ShapeHessianNondegenerate
  simp only [shapeSpace_positiveAffineConfiguration m a b x ha hM,
    physicalHessian_positiveAffineConfiguration m lam a b x ha hx,
    mul_eq_zero,pow_ne_zero 3 (inv_ne_zero ha.ne'),false_or]

/-- Nondegeneracy at the normalized representative recovers the original
geometric multiplier and the genuine six-dimensional shape Hessian. -/
theorem nondegenerateCC_of_normalized_positiveAffine (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : CollisionFree x) (lam a : ℝ) (hlam : 0<lam) (ha : 0<a)
    (hscale : a^3=lam) (hroot : MultiplierEquation m x lam)
    (hn : ShapeHessianNondegenerate m 1 (positiveAffineConfiguration a (massCenter m x) x)) :
    NondegenerateCentralConfiguration m x := by
  have hc : lam/a^3=1 := by rw [←hscale]; exact div_self (pow_ne_zero 3 ha.ne')
  have hiff := shapeHessianNondegenerate_positiveAffineConfiguration_iff m lam a (massCenter m x) x
    ha (ne_of_gt (totalMass_pos m hm)) hx
  rw [hc] at hiff
  exact ⟨hx,lam,hlam,hroot,finrank_shapeSpace m hm x hx,hiff.mp hn⟩

end DominantFiveBody



