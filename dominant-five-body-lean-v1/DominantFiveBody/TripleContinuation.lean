import DominantFiveBody.TripleJacobian
import DominantFiveBody.TripleRecovery
import DominantFiveBody.CompactImplicit

/-! # Actual independent-parameter continuation of a regular triple seed

Boundary weights may vanish, but each seed is an actual distinct ordered
root. Positive-weight existence is supplied by the proved scalar seed.
The parameter ball permits ε,t,α₁,α₂,α₃ to vary independently.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

abbrev TripleChartParameters := Fin 5 → ℝ

def tripleChartParameterRows (q : TripleChartParameters) : TripleChartVariables → TripleChartVariables :=
  tripleChartExtendedRows (q 0) (q 1) (tripleJointAlpha q)

def tripleBoundaryParameter (alpha : TripleVector) : TripleChartParameters :=
  ![0, 0, alpha 0, alpha 1, alpha 2]

@[simp] theorem tripleBoundaryParameter_alpha (alpha : TripleVector) :
    tripleJointAlpha (tripleBoundaryParameter alpha) = alpha := by
  ext i
  fin_cases i <;> rfl

theorem tripleScalar_root_gap_recovery (alpha z : TripleVector) (ha : ∑ i, alpha i = 1)
    (hr : ∀ i, tripleScalarResidual alpha z i = 0) :
    tripleCenteringMatrix alpha *ᵥ (tripleGapMatrix *ᵥ z) = z := by
  have hc := tripleScalar_root_weighted_center alpha z hr
  have he := tripleCentering_gap_decomposition alpha z ha
  rw [hc] at he
  change z = (0 : TripleVector) + tripleCenteringMatrix alpha *ᵥ (tripleGapMatrix *ᵥ z) at he
  simpa only [zero_add] using he.symm

/-- Source §5.3: a genuine product neighborhood and a unique smooth
regular-triple root, from an actual boundary seed with no extra estimates. -/
theorem tripleChart_boundary_continuation (alpha : TripleVector) (ha : TripleWeights alpha)
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
          (tripleChartJacobian (q 0) (q 1) (tripleJointAlpha q) (branch q)).IsInvertible ∧
          ‖(tripleChartJacobian (q 0) (q 1) (tripleJointAlpha q) (branch q)).inverse‖ ≤ C ∧
          tripleChartParameterRows q (branch q) = 0 ∧
          (∀ y, dist y (tripleUnitPoint psi g) < r →
            (tripleChartParameterRows q y = 0 ↔ branch q = y)) := by
  let p0 := tripleBoundaryParameter alpha
  let y0 := tripleUnitPoint psi g
  let domain : Set TripleJointVariables := {v |
    TripleChartRegular (v.1 0) (v.1 1) (tripleJointAlpha v.1) v.2}
  let K : Set TripleJointVariables := {(p0, y0)}
  obtain ⟨hpsi, hpi, _, _⟩ := tripleBoundaryAngle_facts psi hangle
  have hdata : ∀ a ∈ K, a ∈ domain ∧ tripleChartParameterRows a.1 a.2 = 0 ∧
      (CompactImplicit.jacobian tripleChartParameterRows a.1 a.2).IsInvertible := by
    intro a haK
    have heq : a = (p0, y0) := haK
    subst a
    refine ⟨?_, ?_, ?_⟩
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
    CompactImplicit.compact_product tripleChartParameterRows domain K tripleChartRegular_isOpen
      (tripleChartExtendedRows_joint_contDiffOn ∞) isCompact_singleton hdata tau htau
  refine ⟨eta, r, C, heta, hr, hC, hrt, her, ?_⟩
  exact hbranch (p0, y0) (Set.mem_singleton _)

/-- Every actual distinct ordered scalar root, including a zero-weight
capture limit, supplies the proved regular-triple chart. -/
theorem tripleChart_boundary_continuation_of_scalar_root (alpha z : TripleVector)
    (ha : TripleWeights alpha) (hz : TripleOrdered z)
    (hroot : ∀ i, tripleScalarResidual alpha z i = 0)
    (psi : ℝ) (hangle : |psi| = h) (tau : ℝ) (htau : 0 < tau) :
    ∃ eta r C : ℝ, 0 < eta ∧ 0 < r ∧ 0 < C ∧ r ≤ tau ∧ eta ≤ r ∧
      ∃ branch : TripleChartParameters → TripleChartVariables,
        branch (tripleBoundaryParameter alpha) = tripleUnitPoint psi (tripleGapMatrix *ᵥ z) ∧
        ContDiffOn ℝ ∞ branch (Metric.ball (tripleBoundaryParameter alpha) eta) ∧
        ∀ q, dist q (tripleBoundaryParameter alpha) < eta →
          dist (branch q) (tripleUnitPoint psi (tripleGapMatrix *ᵥ z)) < r / 2 ∧
          TripleChartRegular (q 0) (q 1) (tripleJointAlpha q) (branch q) ∧
          (tripleChartJacobian (q 0) (q 1) (tripleJointAlpha q) (branch q)).IsInvertible ∧
          ‖(tripleChartJacobian (q 0) (q 1) (tripleJointAlpha q) (branch q)).inverse‖ ≤ C ∧
          tripleChartParameterRows q (branch q) = 0 ∧
          (∀ y, dist y (tripleUnitPoint psi (tripleGapMatrix *ᵥ z)) < r →
            (tripleChartParameterRows q y = 0 ↔ branch q = y)) := by
  have heq := tripleScalar_root_gap_recovery alpha z ha.2 hroot
  apply tripleChart_boundary_continuation alpha ha psi hangle (tripleGapMatrix *ᵥ z)
  · simpa only [heq] using tripleOrdered_distinct hz
  · simpa only [heq] using hroot
  · exact htau

end DominantFiveBody
