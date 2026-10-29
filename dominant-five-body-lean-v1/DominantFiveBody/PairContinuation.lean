import DominantFiveBody.PairBoundaryInvertibility
import DominantFiveBody.CompactImplicit
import DominantFiveBody.PairRecovery

/-! # Independent-parameter continuation of the complete-pair boundary roots

The compact base set ranges over all α∈[0,1].  The unknowns and the actual
extended equations are the same as in the physical recovery theorem.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital

abbrev PairChartParameters := Fin 4 → ℝ

def pairBoundaryScale (D : ℝ) : ℝ := D ^ (-(1 : ℝ)/3)

theorem pairBoundaryScale_pos (D : ℝ) (hD : 0<D) : 0<pairBoundaryScale D :=
  Real.rpow_pos_of_pos hD _

theorem pairBoundaryScale_equation (D : ℝ) (hD : 0<D) : D*pairBoundaryScale D^3=1 := by
  have he : pairBoundaryScale D^3=D⁻¹ := by
    unfold pairBoundaryScale
    rw [←Real.rpow_mul_natCast hD.le]
    norm_num [Real.rpow_neg_one]
  rw [he,mul_inv_cancel₀ hD.ne']

def pairChartParameterRows (keepD : Bool) (q : PairChartParameters) :
    PairChartVariables → PairChartVariables :=
  pairChartExtendedRows (q 0) (q 1) (q 2) (q 3) keepD

/-- The actual common product neighborhood required in §5.2.  In the
sup norm, the parameter ball allows ε,t,p,α to vary independently.
The base hypotheses specify an actual separated two-source probe root;
all smoothness, scale, regularity and invertibility facts are proved. -/
theorem pairChart_compact_boundary_continuation (p psi : ℝ) (keepD : Bool)
    (hp : 0≤p) (hp1 : p≤1) (hkeep : if keepD then 0<p else p<1)
    (hpsi0 : psi≠0) (hpsih : psi≠h) (hspan : twoSourceSpan psi<Real.pi)
    (hroot : p*coorbitalKernel psi+(1-p)*coorbitalKernel (psi-h)=0)
    (tau : ℝ) (htau : 0<tau) :
    let y0 := pairUnitPoint h psi (pairBoundaryScale (pairProbeDerivative p h psi))
    ∃ eta r C : ℝ, 0<eta ∧ 0<r ∧ 0<C ∧ r≤tau ∧ eta≤r ∧
      ∀ alpha ∈ Icc (0 : ℝ) 1, ∃ branch : PairChartParameters → PairChartVariables,
        branch ![0,0,p,alpha]=y0 ∧
        ContDiffOn ℝ ∞ branch (Metric.ball ![0,0,p,alpha] eta) ∧
        ∀ q, dist q ![0,0,p,alpha]<eta →
          dist (branch q) y0<r/2 ∧ PairChartRegular (q 0) (q 1) (q 3) (branch q) ∧
          (pairChartJacobian (q 0) (q 1) (q 2) (q 3) keepD (branch q)).IsInvertible ∧
          ‖(pairChartJacobian (q 0) (q 1) (q 2) (q 3) keepD (branch q)).inverse‖≤C ∧
          pairChartParameterRows keepD q (branch q)=0 ∧
          (∀ y, dist y y0<r → (pairChartParameterRows keepD q y=0 ↔ branch q=y)) := by
  let z0 := pairBoundaryScale (pairProbeDerivative p h psi)
  let y0 := pairUnitPoint h psi z0
  let domain : Set PairJointVariables := {v | PairChartRegular (v.1 0) (v.1 1) (v.1 3) v.2}
  let K : Set PairJointVariables := (fun a : ℝ => ((![0,0,p,a] : PairChartParameters),y0)) '' Icc 0 1
  have hD : 0<pairProbeDerivative p h psi :=
    twoSourceProbe hp (by linarith) (by ring) hpsi0 hpsih hspan hroot
  have hz : 0<z0 := pairBoundaryScale_pos _ hD
  have hscale : pairProbeDerivative p h psi*z0^3=1 := pairBoundaryScale_equation _ hD
  have hhpos : 0<h := by unfold h; positivity
  have hhpi : |h|<Real.pi := by rw [abs_of_pos hhpos]; unfold h; linarith [Real.pi_pos]
  have hsep := probe_separations_lt_pi hspan
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hdata : ∀ a ∈ K, a ∈ domain ∧ pairChartParameterRows keepD a.1 a.2=0 ∧
      (CompactImplicit.jacobian (pairChartParameterRows keepD) a.1 a.2).IsInvertible := by
    rintro a ⟨alpha,_,rfl⟩
    refine ⟨?_,?_,?_⟩
    · exact pairUnitPoint_regular alpha h psi z0 hz hhpos.ne' hhpi hpsi0 hpsih hsep.1 hsep.2
    · exact pairChartExtendedRows_unit_root p alpha psi z0 keepD hz hpsi0 hpsih hsep.1 hsep.2 hroot hscale
    · exact pairChartJacobian_boundary_isInvertible p alpha psi z0 keepD hp hp1 hkeep hz hpsi0 hpsih hspan hroot hscale
  obtain ⟨eta,r,C,heta,hr,hC,hrt,her,hbranch⟩ :=
    CompactImplicit.compact_product (pairChartParameterRows keepD) domain K pairChartRegular_isOpen
      (pairChartExtendedRows_joint_contDiffOn ∞ keepD) hK hdata tau htau
  refine ⟨eta,r,C,heta,hr,hC,hrt,her,?_⟩
  intro alpha halpha
  exact hbranch ((![0,0,p,alpha] : PairChartParameters),y0) ⟨alpha,halpha,rfl⟩

end DominantFiveBody
