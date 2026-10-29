import DominantFiveBody.TripleZeroEndpoint
import DominantFiveBody.TripleHessian

/-! # Physical regular-triple continuation and fixed-mass zero endpoints

Source §5.3 and the nondegeneracy and endpoint assertions of
Proposition `prop:chart-interface`. Strict convexity is proved separately
from the exact three-cluster area factor; it is not included in this
regularity predicate.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

def tripleChartConfiguration (q : TripleChartParameters) (y : TripleChartVariables) : Configuration :=
  centeredFromRelative (q 0) (tripleChartMass (q 1) (tripleJointAlpha q))
    (tripleChartPoints (q 1) (tripleJointAlpha q) y)

def triplePhysicalRegularSet : Set TripleJointVariables :=
  {v | (∀ i, 0 < tripleChartRadii (v.1 1) (tripleJointAlpha v.1) v.2 i) ∧
    ∀ i j, |tripleChartAngles (v.1 1) (tripleJointAlpha v.1) v.2 j -
      tripleChartAngles (v.1 1) (tripleJointAlpha v.1) v.2 i| < Real.pi}

theorem tripleChartPositiveRadii_isOpen : IsOpen {v : TripleJointVariables |
    ∀ i, 0 < tripleChartRadii (v.1 1) (tripleJointAlpha v.1) v.2 i} := by
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt continuous_const (tripleChartRadii_joint_contDiff 0 i).continuous

theorem triplePhysicalRegularSet_isOpen : IsOpen triplePhysicalRegularSet :=
  tripleChartPositiveRadii_isOpen.inter tripleChartWidth_isOpen

theorem triplePhysicalRegularSet_unit_boundary (alpha : TripleVector) (psi : ℝ)
    (g : TripleGaps) (hangle : |psi| = h) :
    (tripleBoundaryParameter alpha, tripleUnitPoint psi g) ∈ triplePhysicalRegularSet := by
  obtain ⟨_, hpi, _, _⟩ := tripleBoundaryAngle_facts psi hangle
  constructor
  · intro i
    fin_cases i <;> norm_num [triplePhysicalRegularSet, tripleChartRadii,
      tripleBoundaryParameter, tripleUnitPoint]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [tripleChartAngles, tripleBoundaryParameter, tripleUnitPoint, Real.pi_pos]

theorem tripleChart_regular_root_physical (q : TripleChartParameters)
    (y : TripleChartVariables) (heps : 0 < q 0) (ht : 0 < q 1)
    (ha : ∑ i, tripleJointAlpha q i = 1)
    (hm : PositiveRatio (tripleChartMass (q 1) (tripleJointAlpha q)))
    (hreg : TripleChartRegular (q 0) (q 1) (tripleJointAlpha q) y)
    (hr : ∀ i, 0 < tripleChartRadii (q 1) (tripleJointAlpha q) y i)
    (hroot : tripleChartParameterRows q y = 0)
    (hJ : (tripleChartJacobian (q 0) (q 1) (tripleJointAlpha q) y).IsInvertible) :
    NormalizedCentralConfiguration (masses (q 0) (tripleChartMass (q 1) (tripleJointAlpha q)))
      (tripleChartConfiguration q y) ∧
    NondegenerateCentralConfiguration (masses (q 0) (tripleChartMass (q 1) (tripleJointAlpha q)))
      (tripleChartConfiguration q y) := by
  have hx := (tripleChartExtendedRows_zero_iff_normalized (q 0) (q 1) (tripleJointAlpha q) y
    heps ht ha hm hreg hr).mp hroot
  have hnd := (tripleChartJacobian_isInvertible_iff_shape (q 0) (q 1) (tripleJointAlpha q) y
    heps ht ha hm hreg hr hroot).mp hJ
  refine ⟨hx, hx.1, 1, by norm_num, ?_, ?_, hnd⟩
  · intro i
    simpa [tripleChartConfiguration, massCenter, hx.2.1] using hx.2.2 i
  · exact finrank_shapeSpace _ (masses_positive _ _ heps hm) _ hx.1

/-- Independent-parameter IFT with the actual physical equations,
six-dimensional Hessian, and same-positive-mass zero endpoint. -/
theorem tripleChart_physical_continuation (alpha : TripleVector) (ha : TripleWeights alpha)
    (psi : ℝ) (hangle : |psi| = h) (g : TripleGaps)
    (hdist : ∀ i j, i ≠ j → (tripleCenteringMatrix alpha *ᵥ g) i ≠
      (tripleCenteringMatrix alpha *ᵥ g) j)
    (hroot : ∀ i, tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ g) i = 0)
    (tau : ℝ) (htau : 0 < tau) :
    ∃ eta r C : ℝ, 0 < eta ∧ 0 < r ∧ 0 < C ∧ r ≤ tau ∧ eta ≤ r ∧
      ∃ branch : TripleChartParameters → TripleChartVariables,
        branch (tripleBoundaryParameter alpha) = tripleUnitPoint psi g ∧
        ContDiffOn ℝ ∞ branch (Metric.ball (tripleBoundaryParameter alpha) eta) ∧
        ∀ q, dist q (tripleBoundaryParameter alpha) < eta →
          dist (branch q) (tripleUnitPoint psi g) < r / 2 ∧
          TripleChartRegular (q 0) (q 1) (tripleJointAlpha q) (branch q) ∧
          (q, branch q) ∈ triplePhysicalRegularSet ∧
          (tripleChartJacobian (q 0) (q 1) (tripleJointAlpha q) (branch q)).IsInvertible ∧
          ‖(tripleChartJacobian (q 0) (q 1) (tripleJointAlpha q) (branch q)).inverse‖ ≤ C ∧
          tripleChartParameterRows q (branch q) = 0 ∧
          (∀ y, dist y (tripleUnitPoint psi g) < r →
            (tripleChartParameterRows q y = 0 ↔ branch q = y)) ∧
          (0 < q 0 → 0 < q 1 → (∑ i, tripleJointAlpha q i = 1) →
            PositiveRatio (tripleChartMass (q 1) (tripleJointAlpha q)) →
            NormalizedCentralConfiguration (masses (q 0) (tripleChartMass (q 1) (tripleJointAlpha q)))
              (tripleChartConfiguration q (branch q)) ∧
            NondegenerateCentralConfiguration (masses (q 0) (tripleChartMass (q 1) (tripleJointAlpha q)))
              (tripleChartConfiguration q (branch q))) ∧
          (q 0 = 0 → 0 < q 1 → (∑ i, tripleJointAlpha q i = 1) →
            PositiveRatio (tripleChartMass (q 1) (tripleJointAlpha q)) →
            (∀ i, tripleChartRadii (q 1) (tripleJointAlpha q) (branch q) i = 1) ∧
              RelativeCollisionFree (tripleChartPoints (q 1) (tripleJointAlpha q) (branch q)) ∧
              SeparatedSemicircle (tripleChartAngles (q 1) (tripleJointAlpha q) (branch q)) ∧
              ∀ i, coorbitalResidual (tripleChartMass (q 1) (tripleJointAlpha q))
                (tripleChartAngles (q 1) (tripleJointAlpha q) (branch q)) i = 0) := by
  let p0 := tripleBoundaryParameter alpha
  let y0 := tripleUnitPoint psi g
  let domain : Set TripleJointVariables := {v |
    TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2} ∩ triplePhysicalRegularSet
  let K : Set TripleJointVariables := {(p0, y0)}
  obtain ⟨hpsi, hpi, _, _⟩ := tripleBoundaryAngle_facts psi hangle
  have hdata : ∀ a ∈ K, a ∈ domain ∧ tripleChartParameterRows a.1 a.2 = 0 ∧
      (CompactImplicit.jacobian tripleChartParameterRows a.1 a.2).IsInvertible := by
    intro a haK
    have heq : a = (p0, y0) := haK
    subst a
    refine ⟨⟨?_, triplePhysicalRegularSet_unit_boundary alpha psi g hangle⟩, ?_, ?_⟩
    · change TripleChartRegular 0 0 (tripleJointAlpha (tripleBoundaryParameter alpha)) y0
      rw [tripleBoundaryParameter_alpha]
      exact tripleUnitPoint_regular alpha psi g hpsi hpi hdist
    · change tripleChartExtendedRows 0 0 (tripleJointAlpha (tripleBoundaryParameter alpha)) y0 = 0
      rw [tripleBoundaryParameter_alpha]
      exact tripleChartExtendedRows_unit_root alpha ha.2 psi hangle g hroot
    · change (tripleChartJacobian 0 0 (tripleJointAlpha (tripleBoundaryParameter alpha)) y0).IsInvertible
      rw [tripleBoundaryParameter_alpha]
      exact tripleChartJacobian_boundary_isInvertible alpha ha psi hangle g hdist
  obtain ⟨eta, r, C, heta, hr, hC, hrt, her, hbranch⟩ :=
    CompactImplicit.compact_product tripleChartParameterRows domain K
      (tripleChartRegular_isOpen.inter triplePhysicalRegularSet_isOpen)
      ((tripleChartExtendedRows_joint_contDiffOn ∞).mono (fun _ hv => hv.1))
      isCompact_singleton hdata tau htau
  obtain ⟨branch, hbase, hsmooth, hbranch⟩ := hbranch (p0, y0) (Set.mem_singleton _)
  refine ⟨eta, r, C, heta, hr, hC, hrt, her, branch, hbase, hsmooth, ?_⟩
  intro q hq
  obtain ⟨hd, hdom, hJ, hinv, hrootq, huniq⟩ := hbranch q hq
  refine ⟨hd, hdom.1, hdom.2, hJ, hinv, hrootq, huniq, ?_, ?_⟩
  · intro heps ht haq hm
    exact tripleChart_regular_root_physical q (branch q) heps ht haq hm hdom.1 hdom.2.1 hrootq hJ
  · intro heps ht haq hm
    have hreg : TripleChartRegular 0 (q 1) (tripleJointAlpha q) (branch q) := by
      have hg : TripleChartRegular (q 0) (q 1) (tripleJointAlpha q) (branch q) := hdom.1
      simpa only [heps] using hg
    have hzero : tripleChartExtendedRows 0 (q 1) (tripleJointAlpha q) (branch q) = 0 := by
      simpa only [tripleChartParameterRows, heps] using hrootq
    obtain ⟨hu, _, hcf, hsep, hco⟩ := tripleChart_fixed_mass_zero_endpoint (q 1) (tripleJointAlpha q)
      (branch q) ht haq hm hreg hdom.2.1 hdom.2.2 hzero
    exact ⟨hu, hcf, hsep, hco⟩

end DominantFiveBody
