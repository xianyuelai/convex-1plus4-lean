import DominantFiveBody.TripleZeroEndpoint
import DominantFiveBody.PairAreas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Exact regular-triple signed-area factors

Source `eq:regular-area`. The integrated derivative below is the
derivative of the entire composition with the actual root branch.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem det2_smul_right (t : ℝ) (v w : Plane) : det2 v (t • w) = t * det2 v w := by
  simp only [det2, PiLp.smul_apply, smul_eq_mul]
  ring

theorem det2_quarterTurn (v w : Plane) : det2 (quarterTurn v) (quarterTurn w) = det2 v w := by
  simp [det2, quarterTurn, point]
  ring

def tripleExternalAreaQuotient (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) (k : Label) : ℝ :=
  det2 (triplePointDirection t alpha y i j)
    (liftRelative (tripleChartPoints t alpha y) k - tripleChartPoints t alpha y i.castSucc)

theorem tripleExternalArea_factor (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables)
    (i j : TripleLabel) (k : Label) :
    orientedArea (liftRelative (tripleChartPoints t alpha y)) i.castSucc.succ j.castSucc.succ k =
      t * tripleExternalAreaQuotient t alpha y i j k := by
  change det2 (tripleChartPoints t alpha y j.castSucc - tripleChartPoints t alpha y i.castSucc) _ = _
  rw [triplePointDirection_identity, det2_smul_left]
  rfl

def tripleInternalAreaQuotient (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) : ℝ :=
  det2 (triplePointDirection t alpha y 0 1) (triplePointDirection t alpha y 0 2)

theorem tripleInternalArea_factor_square (t : ℝ) (alpha : TripleVector) (y : TripleChartVariables) :
    orientedArea (liftRelative (tripleChartPoints t alpha y)) 1 2 3 =
      t ^ 2 * tripleInternalAreaQuotient t alpha y := by
  change det2 (tripleChartPoints t alpha y 1 - tripleChartPoints t alpha y 0)
    (tripleChartPoints t alpha y 2 - tripleChartPoints t alpha y 0) = _
  have h01 : tripleChartPoints t alpha y 1 - tripleChartPoints t alpha y 0 =
      t • triplePointDirection t alpha y 0 1 := triplePointDirection_identity t alpha y 0 1
  have h02 : tripleChartPoints t alpha y 2 - tripleChartPoints t alpha y 0 =
      t • triplePointDirection t alpha y 0 2 := triplePointDirection_identity t alpha y 0 2
  rw [h01, h02,
    det2_smul_left, det2_smul_right]
  rw [tripleInternalAreaQuotient]
  ring

/-- Exact zero-face collinearity algebra. The common slope is allowed to
depend on all independent parameters. -/
theorem tripleInternalAreaQuotient_zero_of_parallel (alpha : TripleVector)
    (y : TripleChartVariables) (c : ℝ)
    (hparallel : ∀ i, tripleChartRadialPositions alpha y i =
      c * tripleChartAngularPositions alpha y i) :
    tripleInternalAreaQuotient 0 alpha y = 0 := by
  rw [tripleInternalAreaQuotient, triplePointDirection_at_zero,
    triplePointDirection_at_zero, polarPointDerivative_apply, polarPointDerivative_apply,
    hparallel 0, hparallel 1, hparallel 2]
  simp only [det2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem tripleInternalAreaQuotient_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleInternalAreaQuotient (v.1 1) (tripleJointAlpha v.1) v.2) := by
  have ha := triplePointDirection_joint_contDiff n 0 1
  have hb := triplePointDirection_joint_contDiff n 0 2
  simp only [tripleInternalAreaQuotient, det2]
  exact ((((contDiff_piLp 2).mp ha) 0).mul (((contDiff_piLp 2).mp hb) 1)).sub
    ((((contDiff_piLp 2).mp ha) 1).mul (((contDiff_piLp 2).mp hb) 0))

theorem tripleAngularPositions_gap (alpha : TripleVector) (y : TripleChartVariables)
    (ha : ∑ i, alpha i = 1) (k : Fin 2) :
    tripleChartAngularPositions alpha y k.succ - tripleChartAngularPositions alpha y k.castSucc =
      tripleChartAngularGaps y k := by
  have h := congrFun (congrArg (fun A => A *ᵥ tripleChartAngularGaps y)
    (tripleGapMatrix_centeringMatrix alpha ha)) k
  rw [← Matrix.mulVec_mulVec] at h
  simpa only [Matrix.one_mulVec, tripleGapMatrix_mulVec_entry, tripleChartAngularPositions] using h

def tripleCircleAreaCoefficient (t : ℝ) (g : TripleGaps) : ℝ :=
  (g 0 * g 1 * (g 0 + g 1) / 2) * Real.sinc (t * g 0 / 2) *
    Real.sinc (t * g 1 / 2) * Real.sinc (t * (g 0 + g 1) / 2)

theorem tripleCircleAreaCoefficient_zero (g : TripleGaps) :
    tripleCircleAreaCoefficient 0 g = g 0 * g 1 * (g 0 + g 1) / 2 := by
  simp [tripleCircleAreaCoefficient]

theorem tripleCircleAreaCoefficient_zero_pos (g : TripleGaps) (hg0 : 0 < g 0) (hg1 : 0 < g 1) :
    0 < tripleCircleAreaCoefficient 0 g := by
  rw [tripleCircleAreaCoefficient_zero]
  positivity

theorem triplePointDirection_unit_at_zero (alpha : TripleVector) (psi : ℝ) (g : TripleGaps)
    (i j : TripleLabel) :
    triplePointDirection 0 alpha (tripleUnitPoint psi g) i j =
      ((tripleCenteringMatrix alpha *ᵥ g) j - (tripleCenteringMatrix alpha *ᵥ g) i) •
        quarterTurn (polarPoint 1 psi) := by
  rw [triplePointDirection_at_zero, polarPointDerivative_apply]
  have hu : tripleChartRadialGaps (tripleUnitPoint psi g) = 0 := by ext k; fin_cases k <;> rfl
  have hv : tripleChartAngularGaps (tripleUnitPoint psi g) = g := by ext k; fin_cases k <;> rfl
  simp only [tripleChartRadialPositions, tripleChartAngularPositions, hu, hv,
    Matrix.mulVec_zero, Pi.zero_apply, sub_self, zero_smul, zero_add]
  simp [tripleUnitPoint]

theorem tripleExternalAreaQuotient_primary_boundary (alpha : TripleVector) (psi : ℝ) (g : TripleGaps)
    (i j : TripleLabel) :
    tripleExternalAreaQuotient 0 alpha (tripleUnitPoint psi g) i j 0 =
      (tripleCenteringMatrix alpha *ᵥ g) j - (tripleCenteringMatrix alpha *ᵥ g) i := by
  unfold tripleExternalAreaQuotient
  rw [triplePointDirection_unit_at_zero, tripleChartPoints_zero_cluster]
  have h := Real.sin_sq_add_cos_sq psi
  simp [liftRelative, tripleUnitPoint, det2, quarterTurn, polarPoint, point, PiLp.smul_apply, smul_eq_mul]
  linear_combination ((tripleCenteringMatrix alpha *ᵥ g) j -
    (tripleCenteringMatrix alpha *ᵥ g) i) * h

theorem tripleExternalAreaQuotient_exterior_boundary (alpha : TripleVector) (psi : ℝ) (g : TripleGaps)
    (i j : TripleLabel) :
    tripleExternalAreaQuotient 0 alpha (tripleUnitPoint psi g) i j 4 =
      ((tripleCenteringMatrix alpha *ᵥ g) j - (tripleCenteringMatrix alpha *ᵥ g) i) *
        (1 - Real.cos psi) := by
  unfold tripleExternalAreaQuotient
  rw [triplePointDirection_unit_at_zero, tripleChartPoints_zero_cluster]
  have hp : liftRelative (tripleChartPoints 0 alpha (tripleUnitPoint psi g)) 4 = polarPoint 1 0 := by
    exact tripleChartPoints_zero_exterior alpha (tripleUnitPoint psi g)
  rw [hp]
  change det2 (_ • quarterTurn (polarPoint 1 psi)) (polarPoint 1 0 - polarPoint 1 psi) = _
  rw [det2_quarterTurn_unit_sub]
  simp

/-- The exact circle factor holds for varying root coordinates. Thus its
zero-scale value will retain the dependence of the root on t. -/
theorem tripleInternalAreaQuotient_eq_circle (t : ℝ) (alpha : TripleVector)
    (y : TripleChartVariables) (ha : ∑ i, alpha i = 1)
    (hu : tripleChartRadialGaps y = 0) (hr : ∀ i, tripleChartRadii t alpha y i = 1) :
    tripleInternalAreaQuotient t alpha y =
      t * tripleCircleAreaCoefficient t (tripleChartAngularGaps y) := by
  have hw : tripleChartRadialPositions alpha y = 0 := by
    rw [tripleChartRadialPositions, hu, Matrix.mulVec_zero]
  have hg01 : tripleChartAngularPositions alpha y 1 - tripleChartAngularPositions alpha y 0 = y 5 :=
    tripleAngularPositions_gap alpha y ha 0
  have hg12 : tripleChartAngularPositions alpha y 2 - tripleChartAngularPositions alpha y 1 = y 6 :=
    tripleAngularPositions_gap alpha y ha 1
  have hg02 : tripleChartAngularPositions alpha y 2 - tripleChartAngularPositions alpha y 0 = y 5 + y 6 := by
    linarith
  have hd (i j : TripleLabel) : triplePointDirection t alpha y i j = tripleUnitDirection t alpha y i j := by
    simp [triplePointDirection, hw, hr]
  rw [tripleInternalAreaQuotient, hd, hd]
  unfold tripleUnitDirection
  rw [hg01, hg02, det2_smul_left, det2_smul_right, det2_quarterTurn, unit_polar_det]
  have hm : (y 4 + t * (tripleChartAngularPositions alpha y 0 +
      tripleChartAngularPositions alpha y 2) / 2) -
      (y 4 + t * (tripleChartAngularPositions alpha y 0 +
        tripleChartAngularPositions alpha y 1) / 2) = t * y 6 / 2 := by
    linear_combination (t / 2) * hg12
  rw [hm, ← sinc_mul_argument]
  simp [tripleCircleAreaCoefficient, tripleChartAngularGaps]
  ring

theorem tripleExternalAreaQuotient_joint_contDiff (n : ℕ∞ω)
    (i j : TripleLabel) (k : Label) :
    ContDiff ℝ n (fun v : TripleJointVariables =>
      tripleExternalAreaQuotient (v.1 1) (tripleJointAlpha v.1) v.2 i j k) := by
  have hq : ContDiff ℝ n (fun v : TripleJointVariables =>
      liftRelative (tripleChartPoints (v.1 1) (tripleJointAlpha v.1) v.2) k) := by
    refine Fin.cases ?_ (fun a => ?_) k
    · exact contDiff_const
    · exact tripleChartPoints_joint_contDiff n a
  have hv := triplePointDirection_joint_contDiff n i j
  have ha := tripleChartPoints_joint_contDiff n i.castSucc
  simp only [tripleExternalAreaQuotient, det2, PiLp.sub_apply]
  exact ((((contDiff_piLp 2).mp hv) 0).mul
    ((((contDiff_piLp 2).mp hq) 1).sub (((contDiff_piLp 2).mp ha) 1))).sub
    ((((contDiff_piLp 2).mp hv) 1).mul
      ((((contDiff_piLp 2).mp hq) 0).sub (((contDiff_piLp 2).mp ha) 0)))

def tripleParameter (eps t : ℝ) (alpha : TripleVector) : TripleChartParameters :=
  ![eps, t, alpha 0, alpha 1, alpha 2]

def tripleAreaAlongRoot (branch : TripleChartParameters → TripleChartVariables)
    (eps : ℝ) (alpha : TripleVector) (t : ℝ) : ℝ :=
  tripleInternalAreaQuotient t alpha (branch (tripleParameter eps t alpha))

def tripleAreaCoefficientAlongRoot (branch : TripleChartParameters → TripleChartVariables)
    (eps t : ℝ) (alpha : TripleVector) : ℝ :=
  ∫ s in (0 : ℝ)..1, deriv (tripleAreaAlongRoot branch eps alpha) (s * t)

/-- Source `eq:regular-area`, with differentiation of the full implicit
root composition. No root coordinate is frozen in the integrand. -/
theorem tripleInternalArea_factor_cubic_along_root
    (branch : TripleChartParameters → TripleChartVariables) (eps t : ℝ) (alpha : TripleVector)
    (hzero : tripleAreaAlongRoot branch eps alpha 0 = 0)
    (hderiv : ∀ s ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (tripleAreaAlongRoot branch eps alpha) (s * t))
    (hcont : ContinuousOn (fun s : ℝ => deriv (tripleAreaAlongRoot branch eps alpha) (s * t))
      (Icc 0 1)) :
    orientedArea (liftRelative (tripleChartPoints t alpha (branch (tripleParameter eps t alpha))))
      1 2 3 = t ^ 3 * tripleAreaCoefficientAlongRoot branch eps t alpha := by
  have hFTC := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (z₀ := (0 : ℝ)) (z₁ := t) (f := tripleAreaAlongRoot branch eps alpha)
    (f' := deriv (tripleAreaAlongRoot branch eps alpha))
    (by simpa only [smul_eq_mul, zero_add] using hcont)
    (by intro s hs; simpa only [smul_eq_mul, zero_add] using (hderiv s hs).hasDerivAt)
  simp only [smul_eq_mul, zero_add, hzero, sub_zero] at hFTC
  rw [tripleInternalArea_factor_square]
  change t ^ 2 * tripleAreaAlongRoot branch eps alpha t = _
  rw [← hFTC]
  change t ^ 2 * (t * tripleAreaCoefficientAlongRoot branch eps t alpha) = _
  ring

end DominantFiveBody
