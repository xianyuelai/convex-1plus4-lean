import DominantFiveBody.NestedBoundary
import DominantFiveBody.TripleAreas

/-! # Exact nested signed-area factors

Source `eq:nest-area`. Divided edges are the actual smooth edges of the
physical coordinates. The FTC integrand differentiates the entire root
composition, including its dependence on all four independent parameters.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
set_option maxHeartbeats 800000

theorem nestedInnerDirection_at_zero (eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInnerDirection 0 eta alpha y = polarPointDerivative (y 1,y 4) (y 3,y 6) := by
  simp [nestedInnerDirection,nestedInnerVariables,pairPointDirection_at_zero]

theorem nestedOuterDirection_at_zero (eta alpha : ℝ) (y : NestedChartVariables) (i : Fin 2) :
    nestedOuterDirection 0 eta alpha y i = polarPointDerivative (y 1,y 4)
      (nestedOuterRadialGaps eta alpha y i,nestedOuterAngularGaps eta alpha y i) := by
  simp [nestedOuterDirection,nestedOuterVariables,pairPointDirection_at_zero,
    nestedChartRadii,nestedChartAngles,nestedCoordinates]
  fin_cases i <;> rfl

def nestedExternalAreaQuotient (t eta alpha : ℝ) (y : NestedChartVariables)
    (k : NestedEdge) (j : Label) : ℝ :=
  det2 (nestedEdgeDirection t eta alpha y k)
    (liftRelative (nestedChartPoints t eta alpha y) j -
      nestedChartPoints t eta alpha y (nestedEdgeSource k))

theorem nestedExternalArea_factor (t eta alpha : ℝ) (y : NestedChartVariables)
    (k : NestedEdge) (j : Label) :
    orientedArea (liftRelative (nestedChartPoints t eta alpha y))
      (nestedEdgeSource k).succ (nestedEdgeTarget k).succ j =
        nestedEdgeScale t eta k * nestedExternalAreaQuotient t eta alpha y k j := by
  change det2 (nestedChartPoints t eta alpha y (nestedEdgeTarget k) -
    nestedChartPoints t eta alpha y (nestedEdgeSource k)) _ = _
  rw [nestedEdge_direction_identity,det2_smul_left]
  rfl

def nestedInternalAreaQuotient (t eta alpha : ℝ) (y : NestedChartVariables) : ℝ :=
  det2 (nestedInnerDirection t eta alpha y) (nestedOuterDirection t eta alpha y 0)

theorem nestedInternalArea_factor_square (t eta alpha : ℝ) (y : NestedChartVariables) :
    orientedArea (liftRelative (nestedChartPoints t eta alpha y)) 1 2 3 =
      t^2*eta*nestedInternalAreaQuotient t eta alpha y := by
  change det2 (nestedChartPoints t eta alpha y 1-nestedChartPoints t eta alpha y 0)
    (nestedChartPoints t eta alpha y 2-nestedChartPoints t eta alpha y 0) = _
  have h02 := nestedOuterDirection_identity t eta alpha y 0
  change nestedChartPoints t eta alpha y 2-nestedChartPoints t eta alpha y 0 =
    t • nestedOuterDirection t eta alpha y 0 at h02
  rw [nestedInnerDirection_identity,h02,det2_smul_left,det2_smul_right,
    nestedInternalAreaQuotient]
  ring

theorem det2_polarPointDerivative (R psi : ℝ) (u v : ℝ×ℝ) :
    det2 (polarPointDerivative (R,psi) u) (polarPointDerivative (R,psi) v) =
      R*(u.1*v.2-u.2*v.1) := by
  have h := Real.sin_sq_add_cos_sq psi
  simp [polarPointDerivative_apply,det2,quarterTurn,polarPoint,point]
  linear_combination R*(u.1*v.2-u.2*v.1)*h

theorem nestedInternalAreaQuotient_zero_formula (eta alpha : ℝ) (y : NestedChartVariables) :
    nestedInternalAreaQuotient 0 eta alpha y = y 1*(y 3*y 5-y 2*y 6) := by
  rw [nestedInternalAreaQuotient,nestedInnerDirection_at_zero,nestedOuterDirection_at_zero,
    det2_polarPointDerivative]
  dsimp [nestedOuterRadialGaps,nestedOuterAngularGaps]
  ring

theorem nestedInternalAreaQuotient_zero_of_parallel (eta alpha : ℝ)
    (y : NestedChartVariables) (hparallel : y 3*y 5-y 2*y 6=0) :
    nestedInternalAreaQuotient 0 eta alpha y=0 := by
  rw [nestedInternalAreaQuotient_zero_formula,hparallel,mul_zero]

theorem nestedInternalAreaQuotient_joint_contDiff (n : ℕ∞ω) :
    ContDiff ℝ n (fun v : NestedJointVariables =>
      nestedInternalAreaQuotient (v.1 1) (v.1 2) (v.1 3) v.2) := by
  have ha := nestedInnerDirection_joint_contDiff n
  have hb := nestedOuterDirection_joint_contDiff n 0
  simp only [nestedInternalAreaQuotient,det2]
  exact ((((contDiff_piLp 2).mp ha) 0).mul (((contDiff_piLp 2).mp hb) 1)).sub
    ((((contDiff_piLp 2).mp ha) 1).mul (((contDiff_piLp 2).mp hb) 0))

theorem nestedExternalAreaQuotient_joint_contDiff (n : ℕ∞ω) (k : NestedEdge) (j : Label) :
    ContDiff ℝ n (fun v : NestedJointVariables =>
      nestedExternalAreaQuotient (v.1 1) (v.1 2) (v.1 3) v.2 k j) := by
  have hq : ContDiff ℝ n (fun v : NestedJointVariables =>
      liftRelative (nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2) j) := by
    refine Fin.cases ?_ (fun a => ?_) j
    · exact contDiff_const
    · exact nestedChartPoints_joint_contDiff n a
  have hv : ContDiff ℝ n (fun v : NestedJointVariables =>
      nestedEdgeDirection (v.1 1) (v.1 2) (v.1 3) v.2 k) := by
    fin_cases k
    · exact nestedOuterDirection_joint_contDiff n 0
    · exact nestedOuterDirection_joint_contDiff n 1
    · exact nestedInnerDirection_joint_contDiff n
  have ha := nestedChartPoints_joint_contDiff n (nestedEdgeSource k)
  simp only [nestedExternalAreaQuotient,det2,PiLp.sub_apply]
  exact ((((contDiff_piLp 2).mp hv) 0).mul
    ((((contDiff_piLp 2).mp hq) 1).sub (((contDiff_piLp 2).mp ha) 1))).sub
    ((((contDiff_piLp 2).mp hv) 1).mul
      ((((contDiff_piLp 2).mp hq) 0).sub (((contDiff_piLp 2).mp ha) 0)))

def nestedParameter (eps t eta alpha : ℝ) : NestedChartParameters := ![eps,t,eta,alpha]

def nestedAreaAlongRoot (branch : NestedChartParameters → NestedChartVariables)
    (eps eta alpha t : ℝ) : ℝ :=
  nestedInternalAreaQuotient t eta alpha (branch (nestedParameter eps t eta alpha))

def nestedAreaCoefficientAlongRoot (branch : NestedChartParameters → NestedChartVariables)
    (eps t eta alpha : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, deriv (nestedAreaAlongRoot branch eps eta alpha) (s*t)

theorem nestedInternalArea_factor_cubic_along_root
    (branch : NestedChartParameters → NestedChartVariables) (eps t eta alpha : ℝ)
    (hzero : nestedAreaAlongRoot branch eps eta alpha 0=0)
    (hderiv : ∀ s∈Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (nestedAreaAlongRoot branch eps eta alpha) (s*t))
    (hcont : ContinuousOn (fun s : ℝ => deriv (nestedAreaAlongRoot branch eps eta alpha) (s*t))
      (Icc 0 1)) :
    orientedArea (liftRelative (nestedChartPoints t eta alpha
      (branch (nestedParameter eps t eta alpha)))) 1 2 3 =
        t^3*eta*nestedAreaCoefficientAlongRoot branch eps t eta alpha := by
  have hFTC := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (z₀ := (0 : ℝ)) (z₁ := t) (f := nestedAreaAlongRoot branch eps eta alpha)
    (f' := deriv (nestedAreaAlongRoot branch eps eta alpha))
    (by simpa only [smul_eq_mul,zero_add] using hcont)
    (by intro s hs; simpa only [smul_eq_mul,zero_add] using (hderiv s hs).hasDerivAt)
  simp only [smul_eq_mul,zero_add,hzero,sub_zero] at hFTC
  rw [nestedInternalArea_factor_square]
  change t^2*eta*nestedAreaAlongRoot branch eps eta alpha t = _
  rw [← hFTC]
  change t^2*eta*(t*nestedAreaCoefficientAlongRoot branch eps t eta alpha) = _
  ring

end DominantFiveBody
