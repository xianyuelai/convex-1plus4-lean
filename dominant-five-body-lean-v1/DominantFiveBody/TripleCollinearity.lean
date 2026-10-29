import DominantFiveBody.TripleSlowBoundary
import DominantFiveBody.TriplePhysicalContinuation

/-! # Exact collinearity of the actual implicit regular-triple root

Source `eq:regular-parallel`. The scalar root for changing normalized
weights is itself produced by the proved scalar implicit function theorem.
The displayed slow candidate is then identified with the actual chart
root by the latter's genuine common-ball uniqueness.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

/-- Every actual local regular-triple IFT branch has an exact parallel
zero-scale face on an independent epsilon/weight neighborhood. -/
theorem tripleChart_zero_face_parallel_of_local_uniqueness
    (alpha0 z0 : TripleVector) (ha : TripleWeights alpha0) (hz : TripleOrdered z0)
    (hscalar : ∀ i, tripleScalarResidual alpha0 z0 i = 0)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (eta r : ℝ) (heta : 0 < eta) (hr : 0 < r)
    (branch : TripleChartParameters → TripleChartVariables)
    (huniq : ∀ q, dist q (tripleBoundaryParameter alpha0) < eta →
      ∀ y, dist y (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0)) < r →
        (tripleChartParameterRows q y = 0 ↔ branch q = y)) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ eps alpha, |eps| < delta → dist alpha alpha0 < delta → (∑ i, alpha i = 1) →
        ∀ i, tripleChartRadialPositions alpha (branch (tripleParameter eps 0 alpha)) i =
          (backgroundRadius eps * backgroundSlowK eps tau) *
            tripleChartAngularPositions alpha (branch (tripleParameter eps 0 alpha)) i := by
  obtain ⟨scalarBranch, hscalarBase, hscalarSmooth, hscalarRoots, _⟩ :=
    tripleScalar_root_local_implicitFunction alpha0 z0 ha.1 hz hscalar
  let g (alpha : TripleVector) : TripleGaps := tripleGapMatrix *ᵥ scalarBranch alpha
  let y0 := tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0)
  let candidate (p : ℝ × TripleVector) := tripleSlowPoint p.1 tau (g p.2)
  have hg : ContinuousAt g alpha0 := by
    exact tripleGapLinear.continuous.continuousAt.comp hscalarSmooth.continuousAt
  have hfst : ContinuousAt (fun p : ℝ × TripleVector => p.1) (0, alpha0) := continuousAt_fst
  have hsnd : ContinuousAt (fun p : ℝ × TripleVector => p.2) (0, alpha0) := continuousAt_snd
  have hslow : ContinuousAt (fun p : ℝ × TripleGaps => tripleSlowPoint p.1 tau p.2)
      (0, g alpha0) :=
    (tripleSlowPoint_joint_contDiffAt 0 0 tau (g alpha0) (by norm_num)).continuousAt
  have hmap : ContinuousAt (fun p : ℝ × TripleVector => (p.1, g p.2)) (0, alpha0) :=
    hfst.prodMk (ContinuousAt.comp' (f := fun p : ℝ × TripleVector => p.2) hg hsnd)
  have hc : ContinuousAt candidate (0, alpha0) := by
    exact ContinuousAt.comp' (f := fun p : ℝ × TripleVector => (p.1, g p.2))
      (g := fun p : ℝ × TripleGaps => tripleSlowPoint p.1 tau p.2) hslow hmap
  have hbase : candidate (0, alpha0) = y0 := by
    simp only [candidate, g, hscalarBase, tripleSlowPoint_zero, y0]
  have hcnear : ∀ᶠ p : ℝ × TripleVector in 𝓝 (0, alpha0), dist (candidate p) y0 < r := by
    rw [← hbase]
    exact hc.eventually (Metric.ball_mem_nhds _ hr)
  have hqcont : Continuous (fun p : ℝ × TripleVector => tripleParameter p.1 0 p.2) := by
    simp only [tripleParameter]
    fun_prop
  have hqnear : ∀ᶠ p : ℝ × TripleVector in 𝓝 (0, alpha0),
      dist (tripleParameter p.1 0 p.2) (tripleBoundaryParameter alpha0) < eta :=
    hqcont.continuousAt.eventually (Metric.ball_mem_nhds _ heta)
  have hene : ∀ᶠ p : ℝ × TripleVector in 𝓝 (0, alpha0), |p.1| < 1 / 4 :=
    continuousAt_fst.abs.eventually (Iio_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 4))
  have hsnear : ∀ᶠ p : ℝ × TripleVector in 𝓝 (0, alpha0),
      ∀ i, tripleScalarResidual p.2 (scalarBranch p.2) i = 0 :=
    hsnd.eventually hscalarRoots
  have hnear := hene.and (hsnear.and (hqnear.and hcnear))
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨delta, hdelta, ?_⟩
  intro eps alpha heps halpha hasum i
  have hd : dist (eps, alpha) (0, alpha0) < delta := by
    rw [Prod.dist_eq]
    simpa only [Real.dist_eq, sub_zero] using max_lt heps halpha
  obtain ⟨he, hs, hq, hcy⟩ := hball hd
  have hgroot : ∀ j, tripleScalarResidual alpha (tripleCenteringMatrix alpha *ᵥ g alpha) j = 0 := by
    have hrec := tripleScalar_root_gap_recovery alpha (scalarBranch alpha) hasum hs
    simpa only [g, hrec] using hs
  have hcroot : tripleChartParameterRows (tripleParameter eps 0 alpha) (candidate (eps, alpha)) = 0 := by
    have halphaq : tripleJointAlpha (tripleParameter eps 0 alpha) = alpha := by
      ext j
      fin_cases j <;> rfl
    simp only [tripleChartParameterRows, halphaq]
    exact tripleSlowPoint_root eps tau alpha (g alpha) he htau hasum hgroot
  have heq := (huniq (tripleParameter eps 0 alpha) hq (candidate (eps, alpha)) hcy).mp hcroot
  rw [heq]
  exact tripleSlowPoint_parallel eps tau alpha (g alpha) i

theorem tripleChart_zero_face_area_zero_of_local_uniqueness
    (alpha0 z0 : TripleVector) (ha : TripleWeights alpha0) (hz : TripleOrdered z0)
    (hscalar : ∀ i, tripleScalarResidual alpha0 z0 i = 0)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (eta r : ℝ) (heta : 0 < eta) (hr : 0 < r)
    (branch : TripleChartParameters → TripleChartVariables)
    (huniq : ∀ q, dist q (tripleBoundaryParameter alpha0) < eta →
      ∀ y, dist y (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z0)) < r →
        (tripleChartParameterRows q y = 0 ↔ branch q = y)) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ eps alpha, |eps| < delta → dist alpha alpha0 < delta → (∑ i, alpha i = 1) →
        tripleAreaAlongRoot branch eps alpha 0 = 0 := by
  obtain ⟨delta, hdelta, hparallel⟩ := tripleChart_zero_face_parallel_of_local_uniqueness
    alpha0 z0 ha hz hscalar tau htau eta r heta hr branch huniq
  refine ⟨delta, hdelta, ?_⟩
  intro eps alpha heps halpha hasum
  exact tripleInternalAreaQuotient_zero_of_parallel alpha (branch (tripleParameter eps 0 alpha))
    (backgroundRadius eps * backgroundSlowK eps tau) (hparallel eps alpha heps halpha hasum)

end DominantFiveBody
