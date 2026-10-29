import DominantFiveBody.TripleSlowCoordinates
import DominantFiveBody.BackgroundSlow
import DominantFiveBody.TripleSlowExterior

/-! # Actual zero-scale triple vector equations

Source §6.1. Internal rows are actual Newton-force projections. The
slow-eigenvector candidate is substituted into these retained probe rows.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

local instance tripleSlowPlaneAddCommGroup : AddCommGroup Plane :=
  (inferInstance : NormedAddCommGroup Plane).toAddCommGroup
local instance tripleSlowPlaneModule : Module ℝ Plane :=
  (inferInstance : NormedSpace ℝ Plane).toModule

def tripleBoundaryDisplacement (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : Plane :=
  tripleChartRadialPositions alpha y i • polarPoint 1 (y 4) +
    tripleChartAngularPositions alpha y i • quarterTurn (polarPoint (y 1) (y 4))

theorem tripleBoundaryDisplacement_radial (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) :
    inner ℝ (tripleBoundaryDisplacement alpha y i) (polarPoint 1 (y 4)) =
      tripleChartRadialPositions alpha y i := by
  have hself : inner ℝ (polarPoint 1 (y 4)) (polarPoint 1 (y 4)) = 1 := by
    rw [real_inner_self_eq_norm_sq, polarPoint_norm]
    norm_num
  rw [tripleBoundaryDisplacement, polarPoint_rotation_smul]
  simp only [inner_add_left, real_inner_smul_left, hself, mul_one, smul_smul]
  have horth : inner ℝ (quarterTurn (polarPoint 1 (y 4))) (polarPoint 1 (y 4)) = 0 := by
    rw [real_inner_comm, quarterTurn_inner_self]
  rw [horth]
  ring

theorem tripleBoundaryDisplacement_angular (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) :
    inner ℝ (tripleBoundaryDisplacement alpha y i) (quarterTurn (polarPoint (y 1) (y 4))) =
      y 1 ^ 2 * tripleChartAngularPositions alpha y i := by
  have hself : inner ℝ (polarPoint (y 1) (y 4)) (polarPoint (y 1) (y 4)) = y 1 ^ 2 := by
    rw [real_inner_self_eq_norm_sq, polarPoint_norm, sq_abs]
  have horth : inner ℝ (polarPoint 1 (y 4)) (quarterTurn (polarPoint (y 1) (y 4))) = 0 := by
    rw [polarPoint_rotation_smul]
    simp only [real_inner_smul_right, quarterTurn_inner_self, mul_zero]
  rw [tripleBoundaryDisplacement]
  simp only [inner_add_left, real_inner_smul_left, horth, mul_zero, zero_add,
    quarterTurn_inner_quarterTurn, hself]
  ring

theorem tripleBoundaryDisplacement_difference (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) :
    tripleBoundaryDisplacement alpha y j - tripleBoundaryDisplacement alpha y i =
      triplePointDirection 0 alpha y i j := by
  rw [triplePointDirection_at_zero, polarPointDerivative_apply, tripleBoundaryDisplacement,
    tripleBoundaryDisplacement]
  module

theorem tripleBoundaryDisplacement_distance (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) :
    ‖tripleBoundaryDisplacement alpha y i - tripleBoundaryDisplacement alpha y j‖ =
      tripleChartW 0 alpha y i j := by
  have hself : inner ℝ (polarPoint 1 (y 4)) (polarPoint 1 (y 4)) = 1 := by
    rw [real_inner_self_eq_norm_sq, polarPoint_norm]
    norm_num
  have hrot : inner ℝ (quarterTurn (polarPoint (y 1) (y 4)))
      (quarterTurn (polarPoint (y 1) (y 4))) = y 1 ^ 2 := by
    rw [quarterTurn_inner_quarterTurn, real_inner_self_eq_norm_sq, polarPoint_norm, sq_abs]
  have horth : inner ℝ (polarPoint 1 (y 4)) (quarterTurn (polarPoint (y 1) (y 4))) = 0 := by
    rw [polarPoint_rotation_smul]
    simp only [real_inner_smul_right, quarterTurn_inner_self, mul_zero]
  have horth' : inner ℝ (quarterTurn (polarPoint (y 1) (y 4))) (polarPoint 1 (y 4)) = 0 := by
    rw [real_inner_comm, horth]
  have hv : tripleBoundaryDisplacement alpha y i - tripleBoundaryDisplacement alpha y j =
      (tripleChartRadialPositions alpha y i - tripleChartRadialPositions alpha y j) •
        polarPoint 1 (y 4) +
      (tripleChartAngularPositions alpha y i - tripleChartAngularPositions alpha y j) •
        quarterTurn (polarPoint (y 1) (y 4)) := by
    simp only [tripleBoundaryDisplacement]
    module
  have hn : ‖tripleBoundaryDisplacement alpha y i - tripleBoundaryDisplacement alpha y j‖ ^ 2 =
      tripleChartWSq 0 alpha y i j := by
    rw [← real_inner_self_eq_norm_sq, hv, tripleChartWSq_at_zero]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hself, hrot, horth, horth', mul_one, mul_zero, zero_add, add_zero]
    ring
  rw [tripleChartW, ← hn, Real.sqrt_sq (norm_nonneg _)]

def tripleBoundaryInternalForce (alpha : TripleVector) (y : TripleChartVariables)
    (i : TripleLabel) : Plane :=
  ∑ j ∈ Finset.univ.erase i, alpha j •
    newtonTargetField (tripleBoundaryDisplacement alpha y i) (tripleBoundaryDisplacement alpha y j)

theorem tripleInternalRadialReduced_vector_projection (eps : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) :
    tripleInternalRadialReduced eps 0 alpha y i =
      -eps * inner ℝ (tripleBoundaryInternalForce alpha y i) (polarPoint 1 (y 4)) := by
  simp only [tripleInternalRadialReduced, singleScaleChi, zero_mul, zero_div, mul_zero, add_zero,
    tripleBoundaryInternalForce, sum_inner, real_inner_smul_left]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [newtonTargetField]
  simp only [real_inner_smul_left, inner_sub_left, tripleBoundaryDisplacement_radial]
  rw [tripleBoundaryDisplacement_distance]
  ring

theorem tripleInternalAngularReduced_vector_projection (eps : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (i : TripleLabel) :
    tripleInternalAngularReduced eps 0 alpha y i =
      -inner ℝ (tripleBoundaryInternalForce alpha y i) (quarterTurn (polarPoint (y 1) (y 4))) := by
  simp only [tripleInternalAngularReduced, tripleChartRadii_cluster, singleScaleRadius,
    zero_mul, add_zero, Real.sinc_zero, mul_one, zero_pow (by decide : 3 ≠ 0), zero_div,
    sub_zero, tripleBoundaryInternalForce, sum_inner, real_inner_smul_left]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [newtonTargetField]
  simp only [real_inner_smul_left, inner_sub_left, tripleBoundaryDisplacement_angular]
  rw [tripleBoundaryDisplacement_distance]
  ring

theorem tripleSlowPoint_displacement (eps tau : ℝ) (alpha : TripleVector) (g : TripleGaps)
    (he : 0 < 1 + eps) (i : TripleLabel) :
    tripleBoundaryDisplacement alpha (tripleSlowPoint eps tau g) i =
      backgroundScalarLift eps tau ((tripleCenteringMatrix alpha *ᵥ g) i) := by
  rw [tripleBoundaryDisplacement, tripleSlowPoint_radialPositions, tripleSlowPoint_angularPositions]
  change (_ * _ * _ * _) • backgroundE0 tau +
    (_ * _) • quarterTurn (polarPoint (backgroundRadius eps) (tau * h)) = _
  rw [polarPoint_rotation_smul, smul_smul]
  change (_ * _ * _ * _) • backgroundE0 tau +
    (_ * _ * _) • quarterTurn (backgroundE0 tau) = _
  convert! backgroundSlow_polar_displacement eps tau ((tripleCenteringMatrix alpha *ᵥ g) i) he using 1
  congr 1 <;> congr 1 <;> ring

theorem tripleSlowPoint_vector_balance (eps tau : ℝ) (alpha : TripleVector) (g : TripleGaps)
    (he : |eps| < 1 / 4) (ht : tau = 1 ∨ tau = -1)
    (hroot : ∀ i, tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ g) i = 0)
    (i : TripleLabel) :
    backgroundOperator eps tau (tripleBoundaryDisplacement alpha (tripleSlowPoint eps tau g) i) -
      eps • tripleBoundaryInternalForce alpha (tripleSlowPoint eps tau g) i = 0 := by
  have hp := backgroundSmall_one_add_pos eps he
  simpa only [tripleBoundaryInternalForce, tripleSlowPoint_displacement eps tau alpha g hp] using
    backgroundScalarLift_vector_balance eps tau alpha (tripleCenteringMatrix alpha *ᵥ g) he ht hroot i

theorem tripleSlowPoint_regular (eps tau : ℝ) (alpha : TripleVector) (g : TripleGaps)
    (he : 0 < 1 + eps) (ht : tau = 1 ∨ tau = -1)
    (hdist : ∀ i j, i ≠ j → (tripleCenteringMatrix alpha *ᵥ g) i ≠
      (tripleCenteringMatrix alpha *ᵥ g) j) :
    TripleChartRegular eps 0 alpha (tripleSlowPoint eps tau g) := by
  have ha := backgroundRadius_pos eps he
  refine ⟨he.ne', ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [tripleChartRadii, tripleSlowPoint, ha.ne']
  · intro i j hij
    have hW : 0 < tripleChartW 0 alpha (tripleSlowPoint eps tau g) i j := by
      rw [tripleSlowPoint_W eps tau alpha g he i j]
      exact mul_pos (backgroundSlowLength_pos eps he.ne')
        (abs_pos.mpr (sub_ne_zero.mpr (hdist i j hij)))
    exact Real.sqrt_pos.mp hW
  · intro i
    rw [tripleChartPoints_zero_exterior, tripleChartPoints_zero_cluster]
    change polarPoint (backgroundRadius eps) 0 ≠ polarPoint (backgroundRadius eps) (tau * h)
    intro heq
    have hdiff : polarPoint (backgroundRadius eps) 0 - polarPoint (backgroundRadius eps) (tau * h) =
        backgroundRadius eps • backgroundW0 tau := by
      rw [polarPoint_smul_one (backgroundRadius eps) 0,
        polarPoint_smul_one (backgroundRadius eps) (tau * h)]
      simp only [backgroundW0, backgroundE0, smul_sub]
    have hn := congrArg norm hdiff
    rw [heq, sub_self, norm_zero, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
      backgroundW0_norm tau ht, mul_one] at hn
    linarith

/-- Source `eq:regular-slow`: the displayed candidate is proved to solve
all seven actual extended rows. The ε=0 face uses its genuine extension,
and the tangential ε division is used only when ε is nonzero. -/
theorem tripleSlowPoint_root (eps tau : ℝ) (alpha : TripleVector) (g : TripleGaps)
    (he : |eps| < 1 / 4) (ht : tau = 1 ∨ tau = -1) (ha : ∑ i, alpha i = 1)
    (hroot : ∀ i, tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ g) i = 0) :
    tripleChartExtendedRows eps 0 alpha (tripleSlowPoint eps tau g) = 0 := by
  by_cases he0 : eps = 0
  · subst eps
    rw [tripleSlowPoint_zero]
    apply tripleChartExtendedRows_unit_root alpha ha (tau * h) _ g hroot
    rcases ht with rfl | rfl
    · rw [one_mul, abs_of_pos (by unfold h; positivity)]
    · rw [neg_one_mul, abs_neg, abs_of_pos (by unfold h; positivity)]
  have hp := backgroundSmall_one_add_pos eps he
  let y := tripleSlowPoint eps tau g
  have hy0 : y 0 = backgroundRadius eps := rfl
  have hy1 : y 1 = backgroundRadius eps := rfl
  have hy4 : y 4 = tau * h := rfl
  have hB (i : TripleLabel) : backgroundOperator eps tau (tripleBoundaryDisplacement alpha y i) =
      eps • tripleBoundaryInternalForce alpha y i :=
    sub_eq_zero.mp (tripleSlowPoint_vector_balance eps tau alpha g he ht hroot i)
  have hR (k : Fin 2) : tripleRadialDifference eps 0 alpha y k = 0 := by
    rw [tripleRadialDifference, tripleRadialExteriorDifference_background eps tau alpha y hp ht hy0 hy1 hy4,
      tripleInternalRadialDifference, tripleGapMatrix_mulVec_entry,
      tripleInternalRadialReduced_vector_projection, tripleInternalRadialReduced_vector_projection,
      ← tripleBoundaryDisplacement_difference, map_sub, hB, hB]
    change inner ℝ (_ - _) (backgroundE0 tau) +
      (-eps * inner ℝ _ (backgroundE0 tau) - -eps * inner ℝ _ (backgroundE0 tau)) = 0
    simp only [inner_sub_left, real_inner_smul_left]
    ring
  have hT (k : Fin 2) : tripleAngularDifference eps 0 alpha y k = 0 := by
    apply (mul_eq_zero.mp (show eps * tripleAngularDifference eps 0 alpha y k = 0 from ?_)).resolve_left he0
    rw [tripleAngularDifference, mul_add,
      tripleAngularExteriorDifference_background eps tau alpha y hp ht hy0 hy1 hy4,
      tripleInternalAngularDifference, tripleGapMatrix_mulVec_entry,
      tripleInternalAngularReduced_vector_projection, tripleInternalAngularReduced_vector_projection,
      ← tripleBoundaryDisplacement_difference, map_sub, hB, hB]
    have hq : polarPoint (y 1) (y 4) = backgroundProbeCenter eps tau := by
      rw [hy1, hy4, polarPoint_smul_one]
      rfl
    rw [hq]
    simp only [inner_sub_left, real_inner_smul_left]
    ring
  have hAR := tripleRadialMean_background_zero eps tau alpha y hp ht hy0 hy1 hy4
  have hAT := tripleAngularMean_background_zero eps tau alpha y hp ht hy0 hy1 hy4
  have hRp := tripleExteriorRadialRow_background_zero eps alpha y hp hy0
  ext i
  fin_cases i
  · exact hRp
  · exact hAR
  · exact hR 0
  · exact hR 1
  · exact hAT
  · exact hT 0
  · exact hT 1

end DominantFiveBody
