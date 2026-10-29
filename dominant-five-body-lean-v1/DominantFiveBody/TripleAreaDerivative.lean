import DominantFiveBody.TripleAreas

/-! # The full-root derivative of the regular-triple area at the base

Source §6.2. The radii and radial gaps are derived from the actual
ε=0 root equations. All angular coordinates may vary with the branch.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem tripleCircleAreaCoefficient_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : ℝ × TripleGaps => tripleCircleAreaCoefficient p.1 p.2) := by
  simp only [tripleCircleAreaCoefficient]
  fun_prop

/-- The entire root dependence is differentiated. The term containing
the derivative of the changing angular gaps vanishes only at t=0. -/
theorem tripleAreaAlongZeroRoot_hasDerivAt (alpha : TripleVector)
    (ha : ∑ i, alpha i = 1) (branch : ℝ → TripleChartVariables)
    (hsmooth : ContDiffAt ℝ 1 branch 0)
    (hroots : ∀ᶠ t in 𝓝 (0 : ℝ), tripleChartExtendedRows 0 t alpha (branch t) = 0)
    (hradii : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < tripleChartRadii t alpha (branch t) i) :
    HasDerivAt (fun t => tripleInternalAreaQuotient t alpha (branch t))
      ((branch 0) 5 * (branch 0) 6 * ((branch 0) 5 + (branch 0) 6) / 2) 0 := by
  have hg : ContDiffAt ℝ 1 (fun t => tripleChartAngularGaps (branch t)) 0 := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (contDiffAt_pi.mp hsmooth) 5
    · exact (contDiffAt_pi.mp hsmooth) 6
  have hc := ((tripleCircleAreaCoefficient_contDiff 1).contDiffAt.comp 0
    (contDiffAt_id.prodMk hg)).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hd := (hasDerivAt_id (0 : ℝ)).mul hc.hasDerivAt
  have heq : (fun t => tripleInternalAreaQuotient t alpha (branch t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => t * tripleCircleAreaCoefficient t (tripleChartAngularGaps (branch t))) := by
    filter_upwards [hroots, hradii] with t hroot hr
    have hu := tripleChart_zero_eps_all_scale_faces t alpha (branch t) ha hr hroot
    exact tripleInternalAreaQuotient_eq_circle t alpha (branch t) ha hu.2.1 hu.1
  have hd' := hd.congr_of_eventuallyEq heq
  simpa only [tripleCircleAreaCoefficient_zero, tripleChartAngularGaps,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul, add_zero,
    Function.comp_apply, id_eq] using hd'

theorem tripleAreaAlongZeroRoot_deriv_pos (alpha : TripleVector)
    (ha : ∑ i, alpha i = 1) (branch : ℝ → TripleChartVariables)
    (hsmooth : ContDiffAt ℝ 1 branch 0)
    (hroots : ∀ᶠ t in 𝓝 (0 : ℝ), tripleChartExtendedRows 0 t alpha (branch t) = 0)
    (hradii : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < tripleChartRadii t alpha (branch t) i)
    (hg0 : 0 < (branch 0) 5) (hg1 : 0 < (branch 0) 6) :
    0 < deriv (fun t => tripleInternalAreaQuotient t alpha (branch t)) 0 := by
  rw [(tripleAreaAlongZeroRoot_hasDerivAt alpha ha branch hsmooth hroots hradii).deriv]
  positivity

end DominantFiveBody
