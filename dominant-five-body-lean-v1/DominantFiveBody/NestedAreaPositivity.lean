import DominantFiveBody.NestedContinuation
import DominantFiveBody.NestedAreaDerivative
import DominantFiveBody.TripleConvexity

/-! # Nested exterior area values and the full-root cubic coefficient

The outer divided areas are signed by omega; the inner divided areas
have positive orientation. Every derivative below is taken after
composition with the whole implicit root in independent parameters.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def nestedEdgeBoundaryGap (Z z : ℝ) : NestedEdge → ℝ := ![Z,Z,z]
def nestedEdgeOrientation (omega : ℝ) : NestedEdge → ℝ := ![omega,omega,1]

theorem nestedEdgeDirection_unit_boundary (alpha psi Z z : ℝ) (k : NestedEdge) :
    nestedEdgeDirection 0 0 alpha (nestedUnitPoint psi Z z) k =
      nestedEdgeBoundaryGap Z z k • quarterTurn (polarPoint 1 psi) := by
  rw [nestedEdgeDirection_at_boundary,polarPointDerivative_apply]
  fin_cases k <;> simp [nestedUnitPoint,nestedBoundaryDisplacement,nestedEdgeBoundaryGap]

theorem nestedChartPoints_unit_boundary_cluster (alpha psi Z z : ℝ) (i : Fin 3) :
    nestedChartPoints 0 0 alpha (nestedUnitPoint psi Z z) i.castSucc=polarPoint 1 psi := by
  simpa [nestedUnitPoint] using nestedChartPoints_zero_cluster 0 alpha (nestedUnitPoint psi Z z) i

theorem nestedChartPoints_unit_boundary_source (alpha psi Z z : ℝ) (k : NestedEdge) :
    nestedChartPoints 0 0 alpha (nestedUnitPoint psi Z z) (nestedEdgeSource k)=polarPoint 1 psi := by
  fin_cases k
  · exact nestedChartPoints_unit_boundary_cluster alpha psi Z z 0
  · exact nestedChartPoints_unit_boundary_cluster alpha psi Z z 1
  · exact nestedChartPoints_unit_boundary_cluster alpha psi Z z 0

theorem nestedExternalAreaQuotient_primary_boundary (alpha psi Z z : ℝ) (k : NestedEdge) :
    nestedExternalAreaQuotient 0 0 alpha (nestedUnitPoint psi Z z) k 0=
      nestedEdgeBoundaryGap Z z k := by
  rw [nestedExternalAreaQuotient,nestedEdgeDirection_unit_boundary,
    nestedChartPoints_unit_boundary_source]
  have h := Real.sin_sq_add_cos_sq psi
  simp [liftRelative,det2,quarterTurn,polarPoint,point,PiLp.smul_apply,smul_eq_mul]
  linear_combination nestedEdgeBoundaryGap Z z k*h

theorem nestedExternalAreaQuotient_exterior_boundary (alpha psi Z z : ℝ) (k : NestedEdge) :
    nestedExternalAreaQuotient 0 0 alpha (nestedUnitPoint psi Z z) k 4=
      nestedEdgeBoundaryGap Z z k*(1-Real.cos psi) := by
  rw [nestedExternalAreaQuotient,nestedEdgeDirection_unit_boundary,
    nestedChartPoints_unit_boundary_source]
  have hp : liftRelative (nestedChartPoints 0 0 alpha (nestedUnitPoint psi Z z)) 4=polarPoint 1 0 := by
    change nestedChartPoints 0 0 alpha (nestedUnitPoint psi Z z) 3=polarPoint 1 0
    simpa [nestedUnitPoint] using nestedChartPoints_zero_exterior 0 0 alpha (nestedUnitPoint psi Z z)
  rw [hp,det2_quarterTurn_unit_sub]
  simp

theorem nestedEdge_signed_base_gap_pos (omega : ℝ) (hw : omega=1 ∨ omega=-1) (k : NestedEdge) :
    0<nestedEdgeOrientation omega k*
      nestedEdgeBoundaryGap (omega*pairBoundaryScale tripleD0) (pairBoundaryScale (3*tripleD0)) k := by
  have hZ := pairBoundaryScale_pos tripleD0 tripleD0_pos
  have hz := pairBoundaryScale_pos (3*tripleD0) (mul_pos (by norm_num) tripleD0_pos)
  rcases hw with rfl | rfl <;> fin_cases k
  all_goals first
    | simpa [nestedEdgeOrientation,nestedEdgeBoundaryGap] using hZ
    | simpa [nestedEdgeOrientation,nestedEdgeBoundaryGap] using hz

theorem nestedExternalAreaQuotient_base_signed_positive (alpha tau omega : ℝ)
    (htau : tau=1 ∨ tau=-1) (hw : omega=1 ∨ omega=-1)
    (k : NestedEdge) (j : Label) (hj : j∈({0,4} : Finset Label)) :
    0<nestedEdgeOrientation omega k*nestedExternalAreaQuotient 0 0 alpha
      (nestedBasePoint (tau*h) omega) k j := by
  have hgap := nestedEdge_signed_base_gap_pos omega hw k
  have hh : 0<h := by unfold h; positivity
  have hangle : |tau*h|=h := by rcases htau with rfl | rfl <;> simp [abs_of_pos hh]
  obtain ⟨hne,hpi,_,_⟩ := tripleBoundaryAngle_facts (tau*h) hangle
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · simpa only [nestedBasePoint,nestedExternalAreaQuotient_primary_boundary] using hgap
  · rw [nestedBasePoint,nestedExternalAreaQuotient_exterior_boundary,← mul_assoc]
    exact mul_pos hgap (one_sub_cos_pos_of_ne_zero (tau*h) hne hpi)

theorem nestedMacroArea_unit_boundary (alpha psi Z z tau : ℝ)
    (htau : tau=1 ∨ tau=-1) (hpsi : psi=tau*h) (i : TripleLabel) :
    tripleMacroArea tau (liftRelative (nestedChartPoints 0 0 alpha (nestedUnitPoint psi Z z))) i=
      Real.sin h := by
  subst psi
  have hq := nestedChartPoints_unit_boundary_cluster alpha (tau*h) Z z i
  have hp := nestedChartPoints_zero_exterior 0 0 alpha (nestedUnitPoint (tau*h) Z z)
  rcases htau with rfl | rfl
  · rw [tripleMacroArea,if_pos (by norm_num)]
    change det2 (nestedChartPoints 0 0 alpha (nestedUnitPoint (1*h) Z z) 3-0)
      (nestedChartPoints 0 0 alpha (nestedUnitPoint (1*h) Z z) i.castSucc-0)=_
    rw [sub_zero,sub_zero,hp,hq]
    simp [nestedUnitPoint,unit_polar_det]
  · rw [tripleMacroArea,if_neg (by norm_num)]
    change det2 (nestedChartPoints 0 0 alpha (nestedUnitPoint (-1*h) Z z) i.castSucc-0)
      (nestedChartPoints 0 0 alpha (nestedUnitPoint (-1*h) Z z) 3-0)=_
    rw [sub_zero,sub_zero,hp,hq]
    simp [nestedUnitPoint,unit_polar_det]

theorem nestedChartArea_joint_continuous (i j k : Label) :
    Continuous (fun v : NestedJointVariables =>
      orientedArea (liftRelative (nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2)) i j k) :=
  (orientedArea_continuous i j k).comp (liftRelative_continuous.comp
    (continuous_pi (fun l => (nestedChartPoints_joint_contDiff 0 l).continuous)))

theorem nestedMacroArea_joint_continuous (tau : ℝ) (i : TripleLabel) :
    Continuous (fun v : NestedJointVariables =>
      tripleMacroArea tau (liftRelative (nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2)) i) := by
  unfold tripleMacroArea
  split_ifs
  · exact nestedChartArea_joint_continuous 0 4 i.castSucc.succ
  · exact nestedChartArea_joint_continuous 0 i.castSucc.succ 4

theorem nestedExteriorAreas_positive_neighborhood (alpha tau omega : ℝ)
    (htau : tau=1 ∨ tau=-1) (hw : omega=1 ∨ omega=-1) :
    ∀ᶠ v : NestedJointVariables in 𝓝 (nestedParameter 0 0 0 alpha,nestedBasePoint (tau*h) omega),
      (∀ k : NestedEdge,∀ j∈({0,4} : Finset Label),
        0<nestedEdgeOrientation omega k*nestedExternalAreaQuotient (v.1 1) (v.1 2) (v.1 3) v.2 k j) ∧
      ∀ i : TripleLabel,
        0<tripleMacroArea tau (liftRelative (nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2)) i := by
  have he : ∀ᶠ v : NestedJointVariables in 𝓝 (nestedParameter 0 0 0 alpha,nestedBasePoint (tau*h) omega),
      ∀ (k : NestedEdge) (j : Label),j∈({0,4} : Finset Label) →
        0<nestedEdgeOrientation omega k*nestedExternalAreaQuotient (v.1 1) (v.1 2) (v.1 3) v.2 k j := by
    apply Filter.eventually_all.mpr
    intro k
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j∈({0,4} : Finset Label)
    · have hpos := nestedExternalAreaQuotient_base_signed_positive alpha tau omega htau hw k j hj
      have hc := ((continuous_const : Continuous (fun _ : NestedJointVariables => nestedEdgeOrientation omega k)).mul
        (nestedExternalAreaQuotient_joint_contDiff 0 k j).continuous).continuousAt
        (x := (nestedParameter 0 0 0 alpha,nestedBasePoint (tau*h) omega))
      have hp := hc.eventually (Ioi_mem_nhds hpos)
      filter_upwards [hp] with v hv
      exact fun _ => hv
    · exact Filter.Eventually.of_forall (fun _ h => (hj h).elim)
  have hm : ∀ᶠ v : NestedJointVariables in 𝓝 (nestedParameter 0 0 0 alpha,nestedBasePoint (tau*h) omega),
      ∀ i : TripleLabel,
        0<tripleMacroArea tau (liftRelative (nestedChartPoints (v.1 1) (v.1 2) (v.1 3) v.2)) i := by
    apply Filter.eventually_all.mpr
    intro i
    have hh : 0<h := by unfold h; positivity
    have hpi : h<Real.pi := by unfold h; linarith [Real.pi_pos]
    have hpos : 0<tripleMacroArea tau (liftRelative (nestedChartPoints 0 0 alpha (nestedBasePoint (tau*h) omega))) i := by
      rw [nestedBasePoint,nestedMacroArea_unit_boundary alpha _ _ _ tau htau rfl i]
      exact Real.sin_pos_of_pos_of_lt_pi hh hpi
    exact (nestedMacroArea_joint_continuous tau i).continuousAt.eventually (Ioi_mem_nhds hpos)
  exact he.and hm

end DominantFiveBody
