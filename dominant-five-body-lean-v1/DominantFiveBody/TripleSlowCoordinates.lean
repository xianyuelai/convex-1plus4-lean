import DominantFiveBody.BackgroundSpectrum
import DominantFiveBody.TripleAreas

/-! # The actual regular-triple slow boundary coordinates

Source `eq:regular-slow` and `eq:regular-parallel`. All three centering
positions are computed from the same full scalar root, including probes.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def tripleSlowPoint (eps tau : ℝ) (g : TripleGaps) : TripleChartVariables :=
  let a := backgroundRadius eps
  let b := backgroundAngularScale eps tau
  let k := backgroundSlowK eps tau
  ![a, a, a * k * b * g 0, a * k * b * g 1, tau * h, b * g 0, b * g 1]

theorem tripleSlowPoint_zero (tau : ℝ) (g : TripleGaps) :
    tripleSlowPoint 0 tau g = tripleUnitPoint (tau * h) g := by
  ext i
  fin_cases i <;> simp [tripleSlowPoint, tripleUnitPoint]

theorem tripleSlowPoint_radialPositions (eps tau : ℝ) (alpha : TripleVector) (g : TripleGaps)
    (i : TripleLabel) :
    tripleChartRadialPositions alpha (tripleSlowPoint eps tau g) i =
      backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau *
        (tripleCenteringMatrix alpha *ᵥ g) i := by
  fin_cases i
  all_goals simp [tripleChartRadialPositions, tripleChartRadialGaps, tripleSlowPoint,
    tripleCenteringMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

theorem tripleSlowPoint_angularPositions (eps tau : ℝ) (alpha : TripleVector) (g : TripleGaps)
    (i : TripleLabel) :
    tripleChartAngularPositions alpha (tripleSlowPoint eps tau g) i =
      backgroundAngularScale eps tau * (tripleCenteringMatrix alpha *ᵥ g) i := by
  fin_cases i
  all_goals simp [tripleChartAngularPositions, tripleChartAngularGaps, tripleSlowPoint,
    tripleCenteringMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

/-- Exact collinearity, with no asymptotic ε/t restriction. -/
theorem tripleSlowPoint_parallel (eps tau : ℝ) (alpha : TripleVector) (g : TripleGaps)
    (i : TripleLabel) :
    tripleChartRadialPositions alpha (tripleSlowPoint eps tau g) i =
      (backgroundRadius eps * backgroundSlowK eps tau) *
        tripleChartAngularPositions alpha (tripleSlowPoint eps tau g) i := by
  rw [tripleSlowPoint_radialPositions, tripleSlowPoint_angularPositions]
  ring

theorem tripleSlowPoint_internalArea_zero (eps tau : ℝ) (alpha : TripleVector) (g : TripleGaps) :
    tripleInternalAreaQuotient 0 alpha (tripleSlowPoint eps tau g) = 0 :=
  tripleInternalAreaQuotient_zero_of_parallel alpha (tripleSlowPoint eps tau g)
    (backgroundRadius eps * backgroundSlowK eps tau) (tripleSlowPoint_parallel eps tau alpha g)

theorem backgroundAngularScale_norm_identity (eps tau : ℝ) (he : 0 < 1 + eps) :
    (backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau) ^ 2 +
      backgroundRadius eps ^ 2 * backgroundAngularScale eps tau ^ 2 =
      backgroundSlowLength eps ^ 2 := by
  have ha := (backgroundRadius_pos eps he).ne'
  have hs : 0 < 1 + backgroundSlowK eps tau ^ 2 := by positivity
  have hn := (Real.sqrt_pos.mpr hs).ne'
  have hsq := Real.sq_sqrt hs.le
  unfold backgroundAngularScale
  field_simp
  nlinarith

theorem tripleSlowPoint_W (eps tau : ℝ) (alpha : TripleVector) (g : TripleGaps)
    (he : 0 < 1 + eps) (i j : TripleLabel) :
    tripleChartW 0 alpha (tripleSlowPoint eps tau g) i j =
      backgroundSlowLength eps * |(tripleCenteringMatrix alpha *ᵥ g) i -
        (tripleCenteringMatrix alpha *ᵥ g) j| := by
  rw [tripleChartW, tripleChartWSq_at_zero, tripleSlowPoint_radialPositions,
    tripleSlowPoint_radialPositions, tripleSlowPoint_angularPositions,
    tripleSlowPoint_angularPositions]
  change Real.sqrt ((_ * _ * _ * _ - _ * _ * _ * _) ^ 2 +
    backgroundRadius eps ^ 2 * (_ * _ - _ * _) ^ 2) = _
  have hs := backgroundAngularScale_norm_identity eps tau he
  have heq : (backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau *
        (tripleCenteringMatrix alpha *ᵥ g) i -
      backgroundRadius eps * backgroundSlowK eps tau * backgroundAngularScale eps tau *
        (tripleCenteringMatrix alpha *ᵥ g) j) ^ 2 + backgroundRadius eps ^ 2 *
      (backgroundAngularScale eps tau * (tripleCenteringMatrix alpha *ᵥ g) i -
        backgroundAngularScale eps tau * (tripleCenteringMatrix alpha *ᵥ g) j) ^ 2 =
      (backgroundSlowLength eps * ((tripleCenteringMatrix alpha *ᵥ g) i -
        (tripleCenteringMatrix alpha *ᵥ g) j)) ^ 2 := by
    linear_combination ((tripleCenteringMatrix alpha *ᵥ g) i -
      (tripleCenteringMatrix alpha *ᵥ g) j) ^ 2 * hs
  rw [heq, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (backgroundSlowLength_pos eps he.ne')]

theorem tripleSlowPoint_contDiffAt (n : ℕ∞ω) (eps tau : ℝ) (g : TripleGaps)
    (he : |eps| < 1 / 4) : ContDiffAt ℝ n (fun e => tripleSlowPoint e tau g) eps := by
  apply contDiffAt_pi.mpr
  intro i
  have ha := backgroundRadius_contDiffAt n eps (backgroundSmall_one_add_pos eps he).ne'
  have hb := backgroundAngularScale_contDiffAt n eps tau he
  have hk := backgroundSlowK_contDiffAt n eps tau he
  fin_cases i
  all_goals simp [tripleSlowPoint]
  all_goals first
    | exact ha
    | exact ((ha.mul hk).mul hb).mul contDiffAt_const
    | exact hb.mul contDiffAt_const
    | exact contDiffAt_const

theorem tripleSlowPoint_joint_contDiffAt (n : ℕ∞ω) (eps tau : ℝ) (g : TripleGaps)
    (he : |eps| < 1 / 4) :
    ContDiffAt ℝ n (fun p : ℝ × TripleGaps => tripleSlowPoint p.1 tau p.2) (eps, g) := by
  have ha := (backgroundRadius_contDiffAt n eps
    (backgroundSmall_one_add_pos eps he).ne').comp (eps, g) contDiffAt_fst
  have hb := (backgroundAngularScale_contDiffAt n eps tau he).comp (eps, g) contDiffAt_fst
  have hk := (backgroundSlowK_contDiffAt n eps tau he).comp (eps, g) contDiffAt_fst
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  all_goals simp [tripleSlowPoint]
  all_goals first
    | exact ha
    | exact ((ha.mul hk).mul hb).mul ((contDiffAt_pi.mp contDiffAt_snd) _)
    | exact hb.mul ((contDiffAt_pi.mp contDiffAt_snd) _)
    | exact contDiffAt_const

end DominantFiveBody
