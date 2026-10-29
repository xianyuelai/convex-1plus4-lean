import DominantFiveBody.NestedJacobian
import DominantFiveBody.CompactImplicit

/-! # Actual independent two-scale continuation, uniformly in alpha

The compact base contains every alpha in [0,1]. Positive radii and the
open semicircle width are verified parts of the continuation domain.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital

def nestedChartParameterRows (q : NestedChartParameters) : NestedChartVariables → NestedChartVariables :=
  nestedChartExtendedRows (q 0) (q 1) (q 2) (q 3)

def NestedContinuationDomain (v : NestedJointVariables) : Prop :=
  NestedChartRegular (v.1 0) (v.1 1) (v.1 2) (v.1 3) v.2 ∧
    (∀ i,0<nestedChartRadii (v.1 1) (v.1 2) (v.1 3) v.2 i) ∧
    ∀ i j,|nestedChartAngles (v.1 1) (v.1 2) (v.1 3) v.2 j-
      nestedChartAngles (v.1 1) (v.1 2) (v.1 3) v.2 i|<Real.pi

theorem nestedContinuationDomain_isOpen : IsOpen {v : NestedJointVariables | NestedContinuationDomain v} := by
  have hr : IsOpen {v : NestedJointVariables | ∀ i,0<nestedChartRadii (v.1 1) (v.1 2) (v.1 3) v.2 i} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const (nestedChartRadii_joint_contDiff 0 i).continuous
  have hw : IsOpen {v : NestedJointVariables | ∀ i j,
      |nestedChartAngles (v.1 1) (v.1 2) (v.1 3) v.2 j-
        nestedChartAngles (v.1 1) (v.1 2) (v.1 3) v.2 i|<Real.pi} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (continuous_abs.comp ((nestedChartAngles_joint_contDiff 0 j).continuous.sub
      (nestedChartAngles_joint_contDiff 0 i).continuous)) continuous_const
  exact nestedChartRegular_isOpen.inter (hr.inter hw)

theorem nestedChartParameterRows_joint_contDiffOn (n : ℕ∞ω) :
    ContDiffOn ℝ n (fun v : NestedJointVariables => nestedChartParameterRows v.1 v.2)
      {v | NestedContinuationDomain v} := by
  intro v hv
  exact (nestedChartExtendedRows_joint_contDiffAt n v hv.1).contDiffWithinAt

theorem nestedBasePoint_continuationDomain (alpha psi omega : ℝ)
    (hangle : |psi|=h) (hw : |omega|=1) :
    NestedContinuationDomain ((![0,0,0,alpha] : NestedChartParameters),nestedBasePoint psi omega) := by
  obtain ⟨_,hpi,_,_⟩ := tripleBoundaryAngle_facts psi hangle
  refine ⟨nestedBasePoint_regular alpha psi omega hangle hw,?_,?_⟩
  · intro i
    change 0<nestedChartRadii 0 0 alpha (nestedBasePoint psi omega) i
    rw [nestedBasePoint,nestedUnitPoint_radii]
    norm_num
  · intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | simpa [nestedBasePoint,nestedUnitPoint,nestedChartAngles,nestedCoordinates] using hpi
      | simpa [nestedBasePoint,nestedUnitPoint,nestedChartAngles,nestedCoordinates] using Real.pi_pos

/-- The same root ball and inverse bound work for all alpha in [0,1].
Each parameter ball is a genuine independent epsilon,t,eta,alpha product
in the sup norm. The boundary root is proved, not assumed. -/
theorem nestedChart_compact_boundary_continuation (psi omega : ℝ)
    (hangle : |psi|=h) (hw : |omega|=1) (tolerance : ℝ) (htol : 0<tolerance) :
    ∃ delta r C : ℝ,0<delta ∧ 0<r ∧ 0<C ∧ r≤tolerance ∧ delta≤r ∧
      ∀ alpha ∈ Icc (0 : ℝ) 1,∃ branch : NestedChartParameters → NestedChartVariables,
        branch ![0,0,0,alpha]=nestedBasePoint psi omega ∧
        ContDiffOn ℝ ∞ branch (Metric.ball ![0,0,0,alpha] delta) ∧
        ∀ q,dist q ![0,0,0,alpha]<delta →
          dist (branch q) (nestedBasePoint psi omega)<r/2 ∧
          NestedContinuationDomain (q,branch q) ∧
          (nestedChartJacobian (q 0) (q 1) (q 2) (q 3) (branch q)).IsInvertible ∧
          ‖(nestedChartJacobian (q 0) (q 1) (q 2) (q 3) (branch q)).inverse‖≤C ∧
          nestedChartParameterRows q (branch q)=0 ∧
          (∀ y,dist y (nestedBasePoint psi omega)<r →
            (nestedChartParameterRows q y=0 ↔ branch q=y)) := by
  let y0 := nestedBasePoint psi omega
  let domain : Set NestedJointVariables := {v | NestedContinuationDomain v}
  let K : Set NestedJointVariables :=
    (fun alpha : ℝ => ((![0,0,0,alpha] : NestedChartParameters),y0)) '' Icc 0 1
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hdata : ∀ a ∈ K,a ∈ domain ∧ nestedChartParameterRows a.1 a.2=0 ∧
      (CompactImplicit.jacobian nestedChartParameterRows a.1 a.2).IsInvertible := by
    rintro a ⟨alpha,_,rfl⟩
    refine ⟨?_,?_,?_⟩
    · exact nestedBasePoint_continuationDomain alpha psi omega hangle hw
    · exact nestedChartExtendedRows_base_root alpha psi omega hangle hw
    · exact nestedChartJacobian_boundary_isInvertible alpha psi omega hangle hw
  obtain ⟨delta,r,C,hd,hr,hC,hrt,hdr,hbranch⟩ :=
    CompactImplicit.compact_product nestedChartParameterRows domain K nestedContinuationDomain_isOpen
      (nestedChartParameterRows_joint_contDiffOn ∞) hK hdata tolerance htol
  refine ⟨delta,r,C,hd,hr,hC,hrt,hdr,?_⟩
  intro alpha halpha
  exact hbranch ((![0,0,0,alpha] : NestedChartParameters),y0) ⟨alpha,halpha,rfl⟩

/-- A positive physical root supplied by the actual continuation has the
original normalized central configuration and original shape Hessian. -/
theorem nestedContinuationRoot_physical (q : NestedChartParameters) (y : NestedChartVariables)
    (hdomain : NestedContinuationDomain (q,y))
    (heps : 0<q 0) (ht : 0<q 1) (he : 0<q 2)
    (hm : PositiveRatio (nestedChartMass (q 1) (q 2) (q 3)))
    (hroot : nestedChartParameterRows q y=0)
    (hJ : (nestedChartJacobian (q 0) (q 1) (q 2) (q 3) y).IsInvertible) :
    NormalizedCentralConfiguration (masses (q 0) (nestedChartMass (q 1) (q 2) (q 3)))
      (centeredFromRelative (q 0) (nestedChartMass (q 1) (q 2) (q 3))
        (nestedChartPoints (q 1) (q 2) (q 3) y)) ∧
      ShapeHessianNondegenerate (masses (q 0) (nestedChartMass (q 1) (q 2) (q 3))) 1
        (centeredFromRelative (q 0) (nestedChartMass (q 1) (q 2) (q 3))
          (nestedChartPoints (q 1) (q 2) (q 3) y)) := by
  constructor
  · exact (nestedChartExtendedRows_zero_iff_normalized _ _ _ _ _ heps ht he hm hdomain.1 hdomain.2.1).mp hroot
  · exact (nestedChartJacobian_isInvertible_iff_shape _ _ _ _ _ heps ht he hm hdomain.1 hdomain.2.1 hroot).mp hJ

theorem nestedContinuationRoot_fixed_mass_endpoint (t eta alpha : ℝ) (y : NestedChartVariables)
    (ht : 0<t) (he : 0<eta) (hm : PositiveRatio (nestedChartMass t eta alpha))
    (hdomain : NestedContinuationDomain ((![0,t,eta,alpha] : NestedChartParameters),y))
    (hroot : nestedChartExtendedRows 0 t eta alpha y=0) :
    (∀ i,nestedChartRadii t eta alpha y i=1) ∧ y 2=0 ∧ y 3=0 ∧
      RelativeCollisionFree (nestedChartPoints t eta alpha y) ∧
      SeparatedSemicircle (nestedChartAngles t eta alpha y) ∧
      ∀ i,coorbitalResidual (nestedChartMass t eta alpha) (nestedChartAngles t eta alpha y) i=0 :=
  nestedChart_fixed_mass_zero_endpoint t eta alpha y ht he hm hdomain.1 hdomain.2.1 hdomain.2.2 hroot

end DominantFiveBody
