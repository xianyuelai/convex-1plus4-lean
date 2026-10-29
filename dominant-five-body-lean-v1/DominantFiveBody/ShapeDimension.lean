import DominantFiveBody.Coordinates
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod

/-!
# The actual six-dimensional shape space

Source: §3, `lem:hessian` and its center/fixed-inertia/rotation spaces.
The existing geometric `shapeSpace` is used unchanged.  Its four scalar
constraints are proved independent from positive masses and collision
freedom alone, by explicitly exhibiting preimages of the two translation,
one radial, and one rotational outputs.

The proof organization follows elementary mass-orthogonal splitting; all
positions are the five-body positions in `Definitions.lean`. No four-body
theorem or external project is imported.
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

theorem totalMass_ne_zero (m : MassVector) (hm : PositiveMasses m) : totalMass m ≠ 0 :=
  ne_of_gt (totalMass_pos m hm)

theorem massInner_comm (m : MassVector) (v w : Configuration) :
    massInner m v w = massInner m w v := by
  unfold massInner
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm]

/-- §3 `lem:hessian`: the mass metric is nonnegative for positive masses. -/
theorem massInner_self_nonneg (m : MassVector) (hm : PositiveMasses m)
    (v : Configuration) : 0 ≤ massInner m v v := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le real_inner_self_nonneg

/-- §3 `lem:hessian`: positivity of the physical mass metric is proved,
including its exact nonzero-vector hypothesis. -/
theorem massInner_self_pos (m : MassVector) (hm : PositiveMasses m)
    (v : Configuration) (hv : v ≠ 0) : 0 < massInner m v v := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hn
    apply hv
    funext i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  exact Finset.sum_pos'
    (fun j _ => mul_nonneg (hm j).le real_inner_self_nonneg)
    ⟨i, Finset.mem_univ i, mul_pos (hm i) (real_inner_self_pos.mpr hi)⟩

theorem massInner_self_eq_zero_iff (m : MassVector) (hm : PositiveMasses m)
    (v : Configuration) : massInner m v v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact (ne_of_gt (massInner_self_pos m hm v hv)) h
  · rintro rfl
    simp [massInner]

theorem massInner_self_eq_inertia (m : MassVector) (x : Configuration) :
    massInner m x x = inertia m x := by
  simp only [massInner, inertia, real_inner_self_eq_norm_sq]

theorem plane_inner_coordinates (v w : Plane) :
    inner ℝ v w = v 0 * w 0 + v 1 * w 1 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]

/-- The existing physical quarter turn is a real linear map. -/
def quarterTurnLinear : Plane →ₗ[ℝ] Plane where
  toFun := quarterTurn
  map_add' v w := by
    ext k
    fin_cases k <;> simp [quarterTurn, point, add_comm]
  map_smul' a v := by
    ext k
    fin_cases k <;> simp [quarterTurn, point]

@[simp] theorem quarterTurnLinear_apply (v : Plane) :
    quarterTurnLinear v = quarterTurn v := rfl

theorem quarterTurn_inner_self (v : Plane) : inner ℝ v (quarterTurn v) = 0 := by
  rw [plane_inner_coordinates]
  simp [quarterTurn, point]
  ring

theorem quarterTurn_inner_quarterTurn (v w : Plane) :
    inner ℝ (quarterTurn v) (quarterTurn w) = inner ℝ v w := by
  simp [plane_inner_coordinates, quarterTurn, point, add_comm]

/-- §3 `lem:hessian`: rotation is mass-orthogonal to the radial direction. -/
theorem massInner_rotation_self (m : MassVector) (q : Configuration) :
    massInner m q (rotationDirection q) = 0 := by
  simp [massInner, rotationDirection, quarterTurn_inner_self]

theorem massInner_rotation_rotation (m : MassVector) (v w : Configuration) :
    massInner m (rotationDirection v) (rotationDirection w) = massInner m v w := by
  simp [massInner, rotationDirection, quarterTurn_inner_quarterTurn]

theorem weightedPosition_rotation (m : MassVector) (q : Configuration) :
    weightedPosition m (rotationDirection q) = quarterTurn (weightedPosition m q) := by
  change (∑ i, m i • quarterTurnLinear (q i)) =
    quarterTurnLinear (∑ i, m i • q i)
  simp only [map_sum, map_smul]

theorem weightedPosition_rotation_eq_zero (m : MassVector) (q : Configuration)
    (hq : weightedPosition m q = 0) : weightedPosition m (rotationDirection q) = 0 := by
  rw [weightedPosition_rotation, hq]
  exact map_zero quarterTurnLinear

/-- The two common translation directions, without changing any labels. -/
def translationConfiguration (b : Plane) : Configuration := fun _ => b

theorem weightedPosition_translation (m : MassVector) (b : Plane) :
    weightedPosition m (translationConfiguration b) = totalMass m • b := by
  simp only [weightedPosition, translationConfiguration, totalMass, Finset.sum_smul]

theorem massInner_translation_right (m : MassVector) (q : Configuration) (b : Plane) :
    massInner m q (translationConfiguration b) = inner ℝ (weightedPosition m q) b := by
  simp only [massInner, translationConfiguration, weightedPosition, sum_inner,
    real_inner_smul_left]

theorem centered_collisionFree (m : MassVector) (x : Configuration)
    (hx : CollisionFree x) : CollisionFree (centered m x) := by
  intro i j hij heq
  exact hx i j hij (by simpa only [centered, sub_left_inj] using heq)

theorem collisionFree_ne_zero (x : Configuration) (hx : CollisionFree x) : x ≠ 0 := by
  intro hzero
  exact hx 0 1 (by decide) (by simp [hzero])

/-- A collision-free configuration cannot become the zero configuration
by subtracting its center of mass. -/
theorem centered_ne_zero (m : MassVector) (x : Configuration) (hx : CollisionFree x) :
    centered m x ≠ 0 :=
  collisionFree_ne_zero _ (centered_collisionFree m x hx)

/-- The fixed-inertia radial denominator is positive for every actual
positive-mass collision-free configuration, without a CC hypothesis. -/
theorem centered_massInner_pos (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : CollisionFree x) :
    0 < massInner m (centered m x) (centered m x) :=
  massInner_self_pos m hm _ (centered_ne_zero m x hx)

/-- The actual centered inertia is positive, so removing its radial
direction never divides by a zero normalization denominator. -/
theorem centered_inertia_pos (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : CollisionFree x) : 0 < inertia m (centered m x) := by
  rw [← massInner_self_eq_inertia]
  exact centered_massInner_pos m hm x hx

theorem finrank_plane : Module.finrank ℝ Plane = 2 :=
  finrank_euclideanSpace_fin

/-- Five labeled two-dimensional positions give ten ambient coordinates. -/
theorem finrank_configuration : Module.finrank ℝ Configuration = 10 := by
  simp [Configuration, Label, Plane, Module.finrank_pi_fintype]

/-- §3 `lem:hessian`: the exact existing shape-space equations assembled
as a linear map with two-plus-one-plus-one real outputs. -/
def shapeConstraints (m : MassVector) (x : Configuration) :
    Configuration →ₗ[ℝ] Plane × (ℝ × ℝ) :=
  (weightedPositionLinear m).prod
    ((massInnerRight m (centered m x)).prod
      (massInnerRight m (rotationDirection (centered m x))))

theorem shapeConstraints_apply (m : MassVector) (x w : Configuration) :
    shapeConstraints m x w =
      (weightedPosition m w,
        (massInner m (centered m x) w, massInner m (rotationDirection (centered m x)) w)) := by
  simp only [shapeConstraints, LinearMap.prod_apply, Function.prod_apply,
    weightedPositionLinear_apply, massInnerRight_apply]

/-- Equality with the original geometric shape space, not a redefinition. -/
theorem ker_shapeConstraints (m : MassVector) (x : Configuration) :
    LinearMap.ker (shapeConstraints m x) = shapeSpace m x := by
  simp only [shapeConstraints, LinearMap.ker_prod, shapeSpace]

theorem shapeConstraints_translation (m : MassVector) (x : Configuration)
    (hM : totalMass m ≠ 0) (b : Plane) :
    shapeConstraints m x (translationConfiguration b) = (totalMass m • b, (0, 0)) := by
  have hc := centered_weightedPosition_zero m x hM
  simp only [shapeConstraints_apply, weightedPosition_translation, massInner_translation_right,
    hc, weightedPosition_rotation_eq_zero m (centered m x) hc, inner_zero_left]

theorem shapeConstraints_radial (m : MassVector) (x : Configuration)
    (hM : totalMass m ≠ 0) :
    shapeConstraints m x (centered m x) =
      (0, (massInner m (centered m x) (centered m x), 0)) := by
  rw [shapeConstraints_apply, centered_weightedPosition_zero m x hM,
    massInner_comm m (rotationDirection (centered m x)) (centered m x),
    massInner_rotation_self]

theorem shapeConstraints_rotation (m : MassVector) (x : Configuration)
    (hM : totalMass m ≠ 0) :
    shapeConstraints m x (rotationDirection (centered m x)) =
      (0, (0, massInner m (centered m x) (centered m x))) := by
  rw [shapeConstraints_apply,
    weightedPosition_rotation_eq_zero m (centered m x) (centered_weightedPosition_zero m x hM),
    massInner_rotation_self, massInner_rotation_rotation]

/-- §3 `lem:hessian`: all four constraint outputs occur, with explicitly
proved nonzero total mass and radial denominators. -/
theorem shapeConstraints_surjective (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : CollisionFree x) :
    Function.Surjective (shapeConstraints m x) := by
  have hM := totalMass_ne_zero m hm
  have hI := ne_of_gt (centered_massInner_pos m hm x hx)
  rintro ⟨b, t, s⟩
  refine ⟨translationConfiguration ((totalMass m)⁻¹ • b) +
    ((massInner m (centered m x) (centered m x))⁻¹ * t) • centered m x +
    ((massInner m (centered m x) (centered m x))⁻¹ * s) • rotationDirection (centered m x), ?_⟩
  simp [map_add, map_smul, shapeConstraints_translation m x hM,
    shapeConstraints_radial m x hM, shapeConstraints_rotation m x hM,
    smul_smul, hM, hI, mul_comm]

theorem finrank_range_shapeConstraints (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : CollisionFree x) :
    Module.finrank ℝ (LinearMap.range (shapeConstraints m x)) = 4 := by
  rw [LinearMap.range_eq_top.mpr (shapeConstraints_surjective m hm x hx), finrank_top]
  simp [Module.finrank_prod]

/-- §3 `lem:hessian`: the actual shape space has dimension six, obtained
as ten ambient coordinates minus four independent symmetry constraints.
No central equation, strict convexity, or nondegeneracy is assumed. -/
theorem finrank_shapeSpace (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) (hx : CollisionFree x) :
    Module.finrank ℝ (shapeSpace m x) = 6 := by
  have h := (shapeConstraints m x).finrank_range_add_finrank_ker
  rw [finrank_range_shapeConstraints m hm x hx, ker_shapeConstraints,
    finrank_configuration] at h
  omega

/-- §3 `lem:hessian`: for positive masses the six-dimensional clause in
the physical nondegeneracy predicate is automatic, not an extra research
assumption. The actual Hessian condition remains unchanged. -/
theorem nondegenerateCentralConfiguration_iff (m : MassVector) (hm : PositiveMasses m)
    (x : Configuration) :
    NondegenerateCentralConfiguration m x ↔
      CollisionFree x ∧ ∃ lam : ℝ, 0 < lam ∧ MultiplierEquation m x lam ∧
        ShapeHessianNondegenerate m lam x := by
  constructor
  · rintro ⟨hx, lam, hpos, heq, _, hnd⟩
    exact ⟨hx, lam, hpos, heq, hnd⟩
  · rintro ⟨hx, lam, hpos, heq, hnd⟩
    exact ⟨hx, lam, hpos, heq, finrank_shapeSpace m hm x hx, hnd⟩

end DominantFiveBody
