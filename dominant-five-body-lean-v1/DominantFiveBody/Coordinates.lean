import DominantFiveBody.Definitions
import Mathlib.Tactic

/-! # Verified mass, coordinate, and denominator identities

These statements cover the coordinate transition in §3, before `eq:G`.
They do not assert any collision classification or implicit continuation.
-/

noncomputable section
open scoped BigOperators

namespace DominantFiveBody

@[simp] theorem masses_primary (ε : ℝ) (μ : MassRatio) : masses ε μ 0 = 1 := rfl

@[simp] theorem masses_satellite (ε : ℝ) (μ : MassRatio) (i : Satellite) :
    masses ε μ i.succ = ε * μ i := rfl

/-- Equation `eq:masses`: every mass is positive, with no lower bound on ratios. -/
theorem masses_positive (ε : ℝ) (μ : MassRatio) (hε : 0 < ε)
    (hμ : PositiveRatio μ) : PositiveMasses (masses ε μ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · norm_num
  · exact mul_pos hε (hμ.1 j)

theorem totalMass_masses (ε : ℝ) (μ : MassRatio) (hμ : PositiveRatio μ) :
    totalMass (masses ε μ) = 1 + ε := by
  simp [totalMass, Fin.sum_univ_succ, ← Finset.mul_sum, hμ.2]

theorem totalMass_pos (m : MassVector) (hm : PositiveMasses m) : 0 < totalMass m := by
  exact Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty

theorem parameter_denominator_pos (ε : ℝ) (hε : -1 < ε) : 0 < 1 + ε := by
  linarith

theorem parameter_denominator_ne_zero (ε : ℝ) (hε : -1 < ε) : 1 + ε ≠ 0 :=
  ne_of_gt (parameter_denominator_pos ε hε)

theorem collision_distance_pos (x : Configuration) (hx : CollisionFree x)
    (i j : Label) (hij : i ≠ j) : 0 < pairDistance x i j := by
  exact norm_pos_iff.mpr (sub_ne_zero.mpr (hx i j hij))

theorem collision_distance_cube_ne_zero (x : Configuration) (hx : CollisionFree x)
    (i j : Label) (hij : i ≠ j) : pairDistance x i j ^ 3 ≠ 0 :=
  pow_ne_zero _ (ne_of_gt (collision_distance_pos x hx i j hij))

@[simp] theorem primaryRelative_primary (x : Configuration) : primaryRelative x 0 = 0 := by
  simp [primaryRelative]

theorem relative_distance_eq (x : Configuration) (i j : Label) :
    pairDistance (primaryRelative x) i j = pairDistance x i j := by
  unfold pairDistance primaryRelative
  congr 1
  abel

theorem weightedPosition_translate (m : MassVector) (x : Configuration) (b : Plane) :
    weightedPosition m (fun i => x i - b) =
      weightedPosition m x - totalMass m • b := by
  simp [weightedPosition, totalMass, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]

/-- Centering really imposes the two center-of-mass conditions; denominator checked. -/
theorem centered_weightedPosition_zero (m : MassVector) (x : Configuration)
    (hm : totalMass m ≠ 0) : weightedPosition m (centered m x) = 0 := by
  change weightedPosition m (fun i => x i - massCenter m x) = 0
  rw [weightedPosition_translate]
  simp [massCenter, smul_smul, hm]

theorem weightedPositionLinear_apply (m : MassVector) (v : Configuration) :
    weightedPositionLinear m v = weightedPosition m v := by
  simp [weightedPositionLinear, weightedPosition]

theorem massInnerRight_apply (m : MassVector) (v w : Configuration) :
    massInnerRight m v w = massInner m v w := by
  simp [massInnerRight, massInner, innerₗ]
  rfl

/-- Exact tangent-space conditions of §3 `lem:hessian`; no dimension assertion. -/
theorem mem_shapeSpace_iff (m : MassVector) (x v : Configuration) :
    v ∈ shapeSpace m x ↔ weightedPosition m v = 0 ∧
      massInner m (centered m x) v = 0 ∧
      massInner m (rotationDirection (centered m x)) v = 0 := by
  simp [shapeSpace, weightedPositionLinear_apply, massInnerRight_apply]

theorem weightedPosition_liftRelative (ε : ℝ) (μ : MassRatio)
    (q : SatelliteConfiguration) :
    weightedPosition (masses ε μ) (liftRelative q) = ε • relativeAverage μ q := by
  simp [weightedPosition, Fin.sum_univ_succ, liftRelative,
    relativeAverage, mul_smul]

/-- The primary-relative formula is exactly ordinary center-of-mass centering. -/
theorem centered_liftRelative (ε : ℝ) (μ : MassRatio) (hμ : PositiveRatio μ)
    (q : SatelliteConfiguration) :
    centered (masses ε μ) (liftRelative q) = centeredFromRelative ε μ q := by
  funext i
  simp [centered, massCenter, totalMass_masses ε μ hμ,
    weightedPosition_liftRelative, centeredFromRelative, div_eq_mul_inv,
    smul_smul, mul_comm]

theorem centeredFromRelative_weightedPosition_zero (ε : ℝ) (μ : MassRatio)
    (hμ : PositiveRatio μ) (hε : -1 < ε) (q : SatelliteConfiguration) :
    weightedPosition (masses ε μ) (centeredFromRelative ε μ q) = 0 := by
  rw [← centered_liftRelative ε μ hμ]
  exact centered_weightedPosition_zero _ _
    (by rw [totalMass_masses ε μ hμ]; exact parameter_denominator_ne_zero ε hε)

/-- Both coordinate conversions preserve the actual satellite-relative positions. -/
theorem satellitesRelative_centeredFromRelative (ε : ℝ) (μ : MassRatio)
    (q : SatelliteConfiguration) :
    satellitesRelative (centeredFromRelative ε μ q) = q := by
  funext i
  simp [satellitesRelative, primaryRelative, centeredFromRelative, liftRelative]

/-- The normalization is part of the central-configuration equation, not an axiom. -/
theorem normalized_is_central (m : MassVector) (x : Configuration)
    (hx : NormalizedCentralConfiguration m x) : CentralConfiguration m x := by
  refine ⟨hx.1, 1, by norm_num, ?_⟩
  intro i
  simpa [massCenter, hx.2.1] using hx.2.2 i

end DominantFiveBody
