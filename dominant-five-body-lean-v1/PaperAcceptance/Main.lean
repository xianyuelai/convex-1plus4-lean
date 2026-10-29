import DominantFiveBody

/-! Whole-paper acceptance is intentionally separate from development builds.
This module must fail until an unconditional proof of the faithful specification
exists. It has no section variables or unimplemented analytical assumptions.
-/

example : DominantFiveBody.MainUniformStatement := DominantFiveBody.main_uniform

#check @DominantFiveBody.main_uniform
#print DominantFiveBody.main_uniform
#print axioms DominantFiveBody.main_uniform

-- The expanded target has no analytical assumptions or extra typeclasses.
example : ∃ δ : ℝ, 0 < δ ∧
    ∀ μ : DominantFiveBody.MassRatio, DominantFiveBody.PositiveRatio μ →
    ∀ ε : ℝ, 0 < ε → ε < δ →
    ∀ σ : DominantFiveBody.HullOrder,
      ∃ x : DominantFiveBody.Configuration,
        DominantFiveBody.StrictConvexCentralConfiguration (DominantFiveBody.masses ε μ) σ x ∧
        (∀ y : DominantFiveBody.Configuration,
          DominantFiveBody.StrictConvexCentralConfiguration (DominantFiveBody.masses ε μ) σ y →
            DominantFiveBody.OrientedSimilar x y) ∧
        (∀ y : DominantFiveBody.Configuration,
          DominantFiveBody.StrictConvexCentralConfiguration (DominantFiveBody.masses ε μ) σ y →
            DominantFiveBody.NondegenerateCentralConfiguration (DominantFiveBody.masses ε μ) y) :=
  DominantFiveBody.main_uniform

#print DominantFiveBody.MainUniformStatement
#print DominantFiveBody.PositiveRatio
#print DominantFiveBody.masses
#print DominantFiveBody.HullOrder
#print DominantFiveBody.StrictConvexInOrder
#print DominantFiveBody.OrientedSimilar
#print DominantFiveBody.NondegenerateCentralConfiguration
#print DominantFiveBody.shapeSpace
#print DominantFiveBody.ShapeHessianNondegenerate
#print DominantFiveBody.physicalHessian
#print DominantFiveBody.augmentedPotential
#print DominantFiveBody.potential
#print DominantFiveBody.inertia
#print DominantFiveBody.CentralConfiguration
#print DominantFiveBody.MultiplierEquation

example : ∃ μ : DominantFiveBody.MassRatio, DominantFiveBody.PositiveRatio μ := by
  refine ⟨fun _ => 1/4,?_,?_⟩
  · intro i
    norm_num
  · norm_num [Fin.sum_univ_four]

example : Nonempty DominantFiveBody.HullOrder := ⟨⟨Equiv.refl _,rfl⟩⟩

example (x y : DominantFiveBody.Configuration) :
    DominantFiveBody.OrientedSimilar x y ↔
      ∃ (b : DominantFiveBody.Plane) (a : ℝ)
        (R : DominantFiveBody.Plane ≃ₗᵢ[ℝ] DominantFiveBody.Plane),
        0<a ∧ LinearMap.det R.toLinearEquiv.toLinearMap=1 ∧
          ∀ i,y i=b+a • R (x i) := Iff.rfl
