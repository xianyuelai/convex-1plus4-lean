import DominantFiveBody.Coordinates

/-! # The label-preserving oriented similarity relation is an equivalence

These elementary statements concern the exact equivalence relation of Theorem
1.1. They do not yet prove covariance of the equations or normalization of an
arbitrary geometric central configuration.
-/

noncomputable section

namespace DominantFiveBody

theorem orientedSimilar_refl (x : Configuration) : OrientedSimilar x x := by
  refine ⟨0, 1, LinearIsometryEquiv.refl ℝ Plane, by norm_num, ?_, ?_⟩
  · simp
  · intro i
    simp

theorem orientedSimilar_symm {x y : Configuration} (h : OrientedSimilar x y) :
    OrientedSimilar y x := by
  rcases h with ⟨b, a, R, ha, hdet, heq⟩
  have hane : a ≠ 0 := ne_of_gt ha
  refine ⟨-(a⁻¹ • R.symm b), a⁻¹, R.symm, inv_pos.mpr ha, ?_, ?_⟩
  · have hprod := LinearEquiv.det_mul_det_symm R.toLinearEquiv
    rw [hdet, one_mul] at hprod
    exact hprod
  · intro i
    rw [heq i, map_add, map_smul, R.symm_apply_apply]
    simp [smul_add, smul_smul, hane]

theorem orientedSimilar_trans {x y z : Configuration}
    (hxy : OrientedSimilar x y) (hyz : OrientedSimilar y z) : OrientedSimilar x z := by
  rcases hxy with ⟨b, a, R, ha, hR, hxy⟩
  rcases hyz with ⟨c, d, S, hd, hS, hyz⟩
  refine ⟨c + d • S b, d * a, R.trans S, mul_pos hd ha, ?_, ?_⟩
  · change LinearMap.det (S.toLinearEquiv.toLinearMap.comp
      R.toLinearEquiv.toLinearMap) = 1
    rw [LinearMap.det_comp, hS, hR]
    norm_num
  · intro i
    rw [hyz i, hxy i, map_add, map_smul]
    simp only [smul_add, smul_smul, LinearIsometryEquiv.trans_apply]
    abel

/-- Thus the specified similarity classes use an actual equivalence relation. -/
theorem orientedSimilar_equivalence : Equivalence OrientedSimilar :=
  ⟨orientedSimilar_refl, orientedSimilar_symm, orientedSimilar_trans⟩

/-- A positive similarity scales every physical mutual distance by its scale. -/
theorem pairDistance_of_similarity_data (x y : Configuration)
    (b : Plane) (a : ℝ) (R : Plane ≃ₗᵢ[ℝ] Plane) (ha : 0 < a)
    (heq : ∀ i, y i = b + a • R (x i)) (i j : Label) :
    pairDistance y i j = a * pairDistance x i j := by
  unfold pairDistance
  rw [heq i, heq j]
  have hsub : b + a • R (x i) - (b + a • R (x j)) = a • R (x i - x j) := by
    rw [map_sub, smul_sub]
    abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ha, R.norm_map]

theorem collisionFree_of_orientedSimilar {x y : Configuration}
    (hx : CollisionFree x) (hxy : OrientedSimilar x y) : CollisionFree y := by
  rcases hxy with ⟨b, a, R, ha, _, heq⟩
  intro i j hij hy
  have hdist := pairDistance_of_similarity_data x y b a R ha heq i j
  have hyzero : pairDistance y i j = 0 := by simp [pairDistance, hy]
  rw [hyzero] at hdist
  have hpos := mul_pos ha (collision_distance_pos x hx i j hij)
  exact (ne_of_gt hpos) hdist.symm

end DominantFiveBody
