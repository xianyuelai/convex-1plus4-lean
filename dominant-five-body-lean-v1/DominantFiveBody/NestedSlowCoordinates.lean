import DominantFiveBody.NestedTripleBoundary
import DominantFiveBody.NestedUnitBoundary
import DominantFiveBody.TripleSlowBoundary

/-! # Nested slow-vector candidates in the actual coordinates

Both angular gaps have the same scale b; their radial gaps are a k times
those angular gaps. The bridge uses all three scalar probe equations,
including zero individual weights at alpha=0 and alpha=1.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology
namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 1000000

def nestedSlowPoint (eps tau Z z : ℝ) : NestedChartVariables :=
  tripleSlowPoint eps tau ![Z,z]

theorem nestedSlowPoint_zero (tau Z z : ℝ) :
    nestedSlowPoint 0 tau Z z=nestedUnitPoint (tau*h) Z z := by
  rw [nestedSlowPoint,tripleSlowPoint_zero]
  rfl

theorem nestedSlowPoint_parallel (eps tau Z z : ℝ) :
    nestedSlowPoint eps tau Z z 3*nestedSlowPoint eps tau Z z 5-
      nestedSlowPoint eps tau Z z 2*nestedSlowPoint eps tau Z z 6=0 := by
  dsimp [nestedSlowPoint,tripleSlowPoint]
  ring

theorem nestedSlowPoint_area_zero (eps tau eta alpha Z z : ℝ) :
    nestedInternalAreaQuotient 0 eta alpha (nestedSlowPoint eps tau Z z)=0 :=
  nestedInternalAreaQuotient_zero_of_parallel eta alpha _ (nestedSlowPoint_parallel eps tau Z z)

theorem nestedSlowPoint_joint_contDiffAt (n : ℕ∞ω) (eps tau Z z : ℝ) (he : |eps|<1/4) :
    ContDiffAt ℝ n (fun p : ℝ × (Fin 2 → ℝ) => nestedSlowPoint p.1 tau (p.2 0) (p.2 1))
      (eps,![Z,z]) := by
  have heq : (fun p : ℝ × (Fin 2 → ℝ) => nestedSlowPoint p.1 tau (p.2 0) (p.2 1))=
      (fun p : ℝ × TripleGaps => tripleSlowPoint p.1 tau p.2) := by
    funext p
    unfold nestedSlowPoint
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [heq]
  exact tripleSlowPoint_joint_contDiffAt n eps tau ![Z,z] he

theorem nestedToTriple_slowPoint (eps tau eta alpha Z z : ℝ) :
    nestedToTripleVariables eta alpha (nestedSlowPoint eps tau Z z)=
      tripleSlowPoint eps tau ![eta*z,Z-alpha*eta*z] := by
  ext i
  fin_cases i <;> dsimp [nestedToTripleVariables,nestedSlowPoint,tripleSlowPoint] <;> ring

theorem nestedToTriple_unitPoint (eta alpha psi Z z : ℝ) :
    nestedToTripleVariables eta alpha (nestedUnitPoint psi Z z)=
      tripleUnitPoint psi ![eta*z,Z-alpha*eta*z] := by
  ext i
  fin_cases i <;> simp [nestedToTripleVariables,nestedUnitPoint,tripleUnitPoint]

theorem nestedTripleWeights_nonneg (eta alpha : ℝ) (he : 0≤eta) (he1 : eta≤1)
    (ha : 0≤alpha) (ha1 : alpha≤1) : ∀ i,0≤nestedTripleWeights eta alpha i := by
  have he3 : eta^3≤1 := by nlinarith [sq_nonneg (eta-1)]
  intro i
  fin_cases i
  · change 0≤eta^3*alpha; positivity
  · change 0≤eta^3*(1-alpha); positivity
  · change 0≤1-eta^3; linarith

theorem nestedUnitPoint_scalar_root (eta alpha psi Z z : ℝ)
    (he : 0<eta) (he1 : eta≤1) (ha : 0≤alpha) (ha1 : alpha≤1) (hangle : |psi|=h)
    (hreg : NestedChartRegular 0 0 eta alpha (nestedUnitPoint psi Z z))
    (hroot : nestedChartExtendedRows 0 0 eta alpha (nestedUnitPoint psi Z z)=0) :
    ∀ i,tripleScalarResidual (nestedTripleWeights eta alpha)
      (tripleCenteringMatrix (nestedTripleWeights eta alpha) *ᵥ ![eta*z,Z-alpha*eta*z]) i=0 := by
  have ht := (nestedToTriple_boundary_root_iff 0 eta alpha _ he hreg).mp hroot
  rw [nestedToTriple_unitPoint] at ht
  obtain ⟨hpsi,hpi,_,hD⟩ := tripleBoundaryAngle_facts psi hangle
  apply tripleScalar_centered_gap_root_recovery _ _
    ⟨nestedTripleWeights_nonneg eta alpha he.le he1 ha ha1,nestedTripleWeights_sum eta alpha⟩
  rw [← tripleAngularDifference_unit_scalar _ psi _ hpsi hpi hD]
  ext k
  fin_cases k
  · exact congrFun ht 5
  · exact congrFun ht 6

theorem nestedSlowPoint_regular (eps tau eta alpha Z z : ℝ)
    (heps : 0<1+eps) (htau : tau=1 ∨ tau= -1)
    (hz : z≠0) (hZ0 : Z+(1-alpha)*eta*z≠0) (hZ1 : Z-alpha*eta*z≠0) :
    NestedChartRegular eps 0 eta alpha (nestedSlowPoint eps tau Z z) := by
  have ha := backgroundRadius_pos eps heps
  have hb := backgroundAngularScale_pos eps tau heps
  have hr (j : Satellite) : nestedChartRadii 0 eta alpha (nestedSlowPoint eps tau Z z) j=backgroundRadius eps := by
    fin_cases j <;> simp [nestedChartRadii,nestedCoordinates,nestedSlowPoint,tripleSlowPoint]
  refine ⟨heps.ne',?_,?_,?_,?_⟩
  · intro i
    rw [hr]
    exact ha.ne'
  · rw [nestedInnerWSq_formula,hr,hr]
    change 0<(backgroundRadius eps*backgroundSlowK eps tau*backgroundAngularScale eps tau*z)^2+
      backgroundRadius eps*backgroundRadius eps*(backgroundAngularScale eps tau*z)^2*
        Real.sinc (0*eta*(backgroundAngularScale eps tau*z)/2)^2
    simp only [zero_mul,zero_div,Real.sinc_zero,one_pow,mul_one]
    have hp : 0<(backgroundRadius eps)^2*(backgroundAngularScale eps tau*z)^2 :=
      mul_pos (sq_pos_of_ne_zero ha.ne') (sq_pos_of_ne_zero (mul_ne_zero hb.ne' hz))
    nlinarith [sq_nonneg (backgroundRadius eps*backgroundSlowK eps tau*backgroundAngularScale eps tau*z)]
  · intro i
    rw [nestedOuterWSq_formula]
    have hgap : nestedOuterAngularGaps eta alpha (nestedSlowPoint eps tau Z z) i=
        backgroundAngularScale eps tau*nestedOuterAngularGaps eta alpha (nestedUnitPoint 0 Z z) i := by
      fin_cases i <;> dsimp [nestedOuterAngularGaps,nestedSlowPoint,tripleSlowPoint,nestedUnitPoint] <;> ring
    have hgn : nestedOuterAngularGaps eta alpha (nestedUnitPoint 0 Z z) i≠0 := by
      fin_cases i
      · exact hZ0
      · exact hZ1
    rw [hr,hr,hgap]
    simp only [zero_mul,zero_div,Real.sinc_zero,one_pow,mul_one]
    have hp : 0<(backgroundRadius eps)^2*(backgroundAngularScale eps tau*
        nestedOuterAngularGaps eta alpha (nestedUnitPoint 0 Z z) i)^2 :=
      mul_pos (sq_pos_of_ne_zero ha.ne') (sq_pos_of_ne_zero (mul_ne_zero hb.ne' hgn))
    nlinarith [sq_nonneg (nestedOuterRadialGaps eta alpha (nestedSlowPoint eps tau Z z) i)]
  · intro i
    rw [nestedChartPoints_zero_exterior,nestedChartPoints_zero_cluster]
    change polarPoint (backgroundRadius eps) 0≠polarPoint (backgroundRadius eps) (tau*h)
    intro heq
    have hdiff : polarPoint (backgroundRadius eps) 0-polarPoint (backgroundRadius eps) (tau*h)=
        backgroundRadius eps • backgroundW0 tau := by
      rw [polarPoint_smul_one (backgroundRadius eps) 0,polarPoint_smul_one (backgroundRadius eps) (tau*h)]
      simp only [backgroundW0,backgroundE0,smul_sub]
    have hn := congrArg norm hdiff
    rw [heq,sub_self,norm_zero,norm_smul,Real.norm_eq_abs,abs_of_pos ha,
      backgroundW0_norm tau htau,mul_one] at hn
    linarith

theorem nestedSlowPoint_root (eps tau eta alpha Z z : ℝ)
    (heps : |eps|<1/4) (htau : tau=1 ∨ tau= -1) (he : 0<eta)
    (hz : z≠0) (hZ0 : Z+(1-alpha)*eta*z≠0) (hZ1 : Z-alpha*eta*z≠0)
    (hscalar : ∀ i,tripleScalarResidual (nestedTripleWeights eta alpha)
      (tripleCenteringMatrix (nestedTripleWeights eta alpha) *ᵥ ![eta*z,Z-alpha*eta*z]) i=0) :
    nestedChartExtendedRows eps 0 eta alpha (nestedSlowPoint eps tau Z z)=0 := by
  have hreg := nestedSlowPoint_regular eps tau eta alpha Z z
    (backgroundSmall_one_add_pos eps heps) htau hz hZ0 hZ1
  apply (nestedToTriple_boundary_root_iff eps eta alpha _ he hreg).mpr
  rw [nestedToTriple_slowPoint]
  exact tripleSlowPoint_root eps tau _ _ heps htau (nestedTripleWeights_sum eta alpha) hscalar

end DominantFiveBody
