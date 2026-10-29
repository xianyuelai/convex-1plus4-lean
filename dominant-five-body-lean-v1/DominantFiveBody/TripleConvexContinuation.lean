import DominantFiveBody.TripleConvexity

/-! # The implemented regular-triple physical chart

Source §5.3 and Proposition `prop:chart-interface`. The actual scalar
seed, true derivative, smooth extension, convexity and physical Hessian
are assembled without additional geometric or spectral assumptions.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

theorem tripleChart_convex_physical_continuation (alpha z : TripleVector)
    (ha : TripleWeights alpha) (hz : TripleOrdered z)
    (hscalar : ∀ i, tripleScalarResidual alpha z i = 0)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1) (bound : ℝ) (hbound : 0 < bound) :
    ∃ eta r C : ℝ, 0 < eta ∧ 0 < r ∧ 0 < C ∧ r ≤ bound ∧ eta ≤ r ∧
      ∃ branch : TripleChartParameters → TripleChartVariables,
        branch (tripleBoundaryParameter alpha) = tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z) ∧
        ContDiffOn ℝ ∞ branch (Metric.ball (tripleBoundaryParameter alpha) eta) ∧
        ∀ q, dist q (tripleBoundaryParameter alpha) < eta →
          dist (branch q) (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z)) < r / 2 ∧
          TripleChartRegular (q 0) (q 1) (tripleJointAlpha q) (branch q) ∧
          (q, branch q) ∈ triplePhysicalRegularSet ∧
          (tripleChartJacobian (q 0) (q 1) (tripleJointAlpha q) (branch q)).IsInvertible ∧
          ‖(tripleChartJacobian (q 0) (q 1) (tripleJointAlpha q) (branch q)).inverse‖ ≤ C ∧
          tripleChartParameterRows q (branch q) = 0 ∧
          (∀ y, dist y (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z)) < r →
            (tripleChartParameterRows q y = 0 ↔ branch q = y)) ∧
          (0 < q 1 → (∑ i, tripleJointAlpha q i = 1) →
            StrictConvexInOrder (tripleBoundaryHullOrder tau)
              (liftRelative (tripleChartPoints (q 1) (tripleJointAlpha q) (branch q)))) ∧
          (0 < q 0 → 0 < q 1 → (∑ i, tripleJointAlpha q i = 1) →
            PositiveRatio (tripleChartMass (q 1) (tripleJointAlpha q)) →
            StrictConvexCentralConfiguration (masses (q 0) (tripleChartMass (q 1) (tripleJointAlpha q)))
              (tripleBoundaryHullOrder tau) (tripleChartConfiguration q (branch q)) ∧
            NondegenerateCentralConfiguration (masses (q 0) (tripleChartMass (q 1) (tripleJointAlpha q)))
              (tripleChartConfiguration q (branch q))) ∧
          (q 0 = 0 → 0 < q 1 → (∑ i, tripleJointAlpha q i = 1) →
            PositiveRatio (tripleChartMass (q 1) (tripleJointAlpha q)) →
            (∀ i, tripleChartRadii (q 1) (tripleJointAlpha q) (branch q) i = 1) ∧
              RelativeCollisionFree (tripleChartPoints (q 1) (tripleJointAlpha q) (branch q)) ∧
              SeparatedSemicircle (tripleChartAngles (q 1) (tripleJointAlpha q) (branch q)) ∧
              ∀ i, coorbitalResidual (tripleChartMass (q 1) (tripleJointAlpha q))
                (tripleChartAngles (q 1) (tripleJointAlpha q) (branch q)) i = 0) := by
  have hrec := tripleScalar_root_gap_recovery alpha z ha.2 hscalar
  have hh : 0 < h := by unfold h; positivity
  have hangle : |tau * h| = h := by
    rcases htau with rfl | rfl <;> simp [abs_of_pos hh]
  obtain ⟨eta, r, C, heta, hr, hC, hrbound, hetar, branch, hbase, hsmooth, hdata⟩ :=
    tripleChart_physical_continuation alpha ha (tau * h) hangle (tripleGapMatrix *ᵥ z)
      (by simpa only [hrec] using tripleOrdered_distinct hz)
      (by simpa only [hrec] using hscalar) bound hbound
  obtain ⟨delta, hdelta, hdeltaeta, hconv⟩ := tripleChart_strictConvex_neighborhood
    alpha z ha hz hscalar tau htau eta r heta hr branch hbase hsmooth
    (fun q hq => (hdata q hq).2.2.2.2.2.1)
    (fun q hq => (hdata q hq).2.2.1.1)
    (fun q hq => (hdata q hq).2.2.2.2.2.2.1)
  refine ⟨delta, r, C, hdelta, hr, hC, hrbound, hdeltaeta.trans hetar, branch, hbase,
    hsmooth.mono (Metric.ball_subset_ball hdeltaeta), ?_⟩
  intro q hq
  obtain ⟨hd, hreg, hsafe, hJ, hinv, hroot, huniq, hphys, hend⟩ :=
    hdata q (lt_of_lt_of_le hq hdeltaeta)
  have hconvq (ht : 0 < q 1) (hasum : ∑ i, tripleJointAlpha q i = 1) :
      StrictConvexInOrder (tripleBoundaryHullOrder tau)
        (liftRelative (tripleChartPoints (q 1) (tripleJointAlpha q) (branch q))) := by
    have heq : tripleParameter (q 0) (q 1) (tripleJointAlpha q) = q := by
      ext i
      fin_cases i <;> rfl
    simpa only [heq] using hconv (q 0) (q 1) (tripleJointAlpha q) (by simpa only [heq] using hq) hasum ht
  refine ⟨hd, hreg, hsafe, hJ, hinv, hroot, huniq, hconvq, ?_, hend⟩
  intro heps ht hasum hm
  obtain ⟨hx, hnd⟩ := hphys heps ht hasum hm
  have hc := (strictConvex_centeredFromRelative_iff (tripleBoundaryHullOrder tau)
    (q 0) (tripleChartMass (q 1) (tripleJointAlpha q))
    (tripleChartPoints (q 1) (tripleJointAlpha q) (branch q))).mpr (hconvq ht hasum)
  exact ⟨⟨normalized_is_central _ _ hx, hc⟩, hnd⟩

end DominantFiveBody
