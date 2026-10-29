import DominantFiveBody.PairUnitBoundary
import DominantFiveBody.ConvexContinuation
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! # Exact signed-area factors for the complete-pair chart

The factors are smooth functions of every parameter and of the unknowns.
Consequently their composition with an actual implicit root includes all
dependence of that root; no frozen-root differentiation is used.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody

theorem det2_smul_left (t : ℝ) (v w : Plane) : det2 (t • v) w=t*det2 v w := by
  simp only [det2,PiLp.smul_apply,smul_eq_mul]
  ring

def pairAreaQuotient (t alpha : ℝ) (y : PairChartVariables) (j : Label) : ℝ :=
  det2 (pairPointDirection t alpha y)
    (liftRelative (pairChartPoints t alpha y) j-pairChartPoints t alpha y 0)

/-- Exact factorization, including the signed extension t=0. -/
theorem pairArea_factor (t alpha : ℝ) (y : PairChartVariables) (j : Label) :
    orientedArea (liftRelative (pairChartPoints t alpha y)) 1 2 j=
      t*pairAreaQuotient t alpha y j := by
  change det2 (pairChartPoints t alpha y 1-pairChartPoints t alpha y 0)
    (liftRelative (pairChartPoints t alpha y) j-pairChartPoints t alpha y 0)=_
  have hv : pairChartPoints t alpha y 1-pairChartPoints t alpha y 0=t • pairPointDirection t alpha y :=
    pairPointDirection_identity t alpha y
  rw [hv,det2_smul_left]
  rfl

theorem det2_quarterTurn_unit_sub (theta phi z : ℝ) :
    det2 (z • quarterTurn (polarPoint 1 theta))
      (polarPoint 1 phi-polarPoint 1 theta)=z*(1-Real.cos (phi-theta)) := by
  rw [det2_smul_left]
  congr 1
  have h := Real.sin_sq_add_cos_sq theta
  simp [det2,quarterTurn,polarPoint,point,PiLp.sub_apply,Real.cos_sub]
  nlinarith

theorem pairPointDirection_unit_at_zero (alpha omega psi z : ℝ) :
    pairPointDirection 0 alpha (pairUnitPoint omega psi z)=z • quarterTurn (polarPoint 1 psi) := by
  rw [pairPointDirection_at_zero]
  change polarPointDerivative (1,psi) (0,z)=_
  rw [polarPointDerivative_apply]
  simp

theorem pairAreaQuotient_primary_boundary (alpha omega psi z : ℝ) :
    pairAreaQuotient 0 alpha (pairUnitPoint omega psi z) 0=z := by
  unfold pairAreaQuotient
  rw [pairPointDirection_unit_at_zero,pairChartPoints_at_zero]
  have h := Real.sin_sq_add_cos_sq psi
  simp [liftRelative,pairUnitPoint,det2,quarterTurn,polarPoint,point,PiLp.smul_apply,smul_eq_mul]
  linear_combination z*h

theorem pairAreaQuotient_c_boundary (alpha omega psi z : ℝ) :
    pairAreaQuotient 0 alpha (pairUnitPoint omega psi z) 3=z*(1-Real.cos psi) := by
  unfold pairAreaQuotient
  rw [pairPointDirection_unit_at_zero,pairChartPoints_at_zero]
  change det2 (z • quarterTurn (polarPoint 1 psi)) (polarPoint 1 0-polarPoint 1 psi)=_
  rw [det2_quarterTurn_unit_sub]
  simp

theorem pairAreaQuotient_d_boundary (alpha omega psi z : ℝ) :
    pairAreaQuotient 0 alpha (pairUnitPoint omega psi z) 4=z*(1-Real.cos (omega-psi)) := by
  unfold pairAreaQuotient
  rw [pairPointDirection_unit_at_zero,pairChartPoints_at_zero]
  change det2 (z • quarterTurn (polarPoint 1 psi)) (polarPoint 1 omega-polarPoint 1 psi)=_
  exact det2_quarterTurn_unit_sub psi omega z

theorem pairAreaQuotient_joint_contDiff (n : ℕ∞ω) (j : Label) :
    ContDiff ℝ n (fun v : PairJointVariables => pairAreaQuotient (v.1 1) (v.1 3) v.2 j) := by
  have hq : ContDiff ℝ n (fun v : PairJointVariables => liftRelative (pairChartPoints (v.1 1) (v.1 3) v.2) j) := by
    refine Fin.cases ?_ (fun i => ?_) j
    · exact contDiff_const
    · exact pairChartPoints_joint_contDiff n i
  have hv := pairPointDirection_joint_contDiff n
  have ha := pairChartPoints_joint_contDiff n 0
  simp only [pairAreaQuotient,det2,PiLp.sub_apply]
  exact ((((contDiff_piLp 2).mp hv) 0).mul ((((contDiff_piLp 2).mp hq) 1).sub (((contDiff_piLp 2).mp ha) 1))).sub
    ((((contDiff_piLp 2).mp hv) 1).mul ((((contDiff_piLp 2).mp hq) 0).sub (((contDiff_piLp 2).mp ha) 0)))

theorem one_sub_cos_pos_of_ne_zero (x : ℝ) (hx : x≠0) (hpi : |x|<Real.pi) :
    0<1-Real.cos x := by
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := |x|)
    (by norm_num) hpi.le (abs_pos.mpr hx)
  simpa only [Real.cos_zero,Real.cos_abs] using sub_pos.mpr hc

/-- The three factors containing the colliding pair are strictly positive
at every separated unit boundary root, uniformly allowing α endpoints. -/
theorem pairAreaQuotient_boundary_positive (alpha omega psi z : ℝ)
    (hz : 0<z) (hpsi0 : psi≠0) (hpsiw : psi≠omega)
    (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi) :
    ∀ j∈({0,3,4} : Finset Label), 0<pairAreaQuotient 0 alpha (pairUnitPoint omega psi z) j := by
  intro j hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · simpa only [pairAreaQuotient_primary_boundary] using hz
  · rw [pairAreaQuotient_c_boundary]
    exact mul_pos hz (one_sub_cos_pos_of_ne_zero psi hpsi0 hpi0)
  · rw [pairAreaQuotient_d_boundary]
    exact mul_pos hz (one_sub_cos_pos_of_ne_zero (omega-psi) (sub_ne_zero.mpr hpsiw.symm)
      (by simpa only [abs_sub_comm] using hpiw))

/-- Factor positivity persists on an ambient neighborhood, before any
choice of a root branch or relation between ε and t. -/
theorem pairArea_positive_neighborhood (p alpha omega psi z : ℝ)
    (hz : 0<z) (hpsi0 : psi≠0) (hpsiw : psi≠omega)
    (hpi0 : |psi|<Real.pi) (hpiw : |psi-omega|<Real.pi) :
    ∀ᶠ v : PairJointVariables in 𝓝 ((![0,0,p,alpha] : Fin 4 → ℝ),pairUnitPoint omega psi z),
      ∀ j∈({0,3,4} : Finset Label),
        0<v.1 1 → 0<orientedArea (liftRelative (pairChartPoints (v.1 1) (v.1 3) v.2)) 1 2 j := by
  apply Filter.eventually_all.mpr
  intro j
  by_cases hj : j∈({0,3,4} : Finset Label)
  · have hp := pairAreaQuotient_boundary_positive alpha omega psi z hz hpsi0 hpsiw hpi0 hpiw j hj
    have hc := (pairAreaQuotient_joint_contDiff 0 j).continuous.continuousAt
      (x := ((![0,0,p,alpha] : Fin 4 → ℝ),pairUnitPoint omega psi z))
    have he : ∀ᶠ v : PairJointVariables in 𝓝 ((![0,0,p,alpha] : Fin 4 → ℝ),pairUnitPoint omega psi z),
        0<pairAreaQuotient (v.1 1) (v.1 3) v.2 j :=
      hc.eventually (Ioi_mem_nhds hp)
    filter_upwards [he] with v hv
    intro _ ht
    rw [pairArea_factor]
    exact mul_pos ht hv
  · exact Filter.Eventually.of_forall (fun _ h => (hj h).elim)

end DominantFiveBody
