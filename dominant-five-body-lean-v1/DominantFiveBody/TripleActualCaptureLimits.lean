import DominantFiveBody.TripleSequenceCapture

/-! # Scalar seeds obtained from actual regular-triple limits

The divided equations converge on the proved regular domain. Their
limiting difference rows give the genuine scalar equations, including
all zero-weight probe rows. No scalar equation is assumed in the physical
capture theorem below.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

theorem tripleParameter_tendsto (eps t : ℕ → ℝ) (alpha : ℕ → TripleVector)
    (alpha0 : TripleVector)
    (heps : Tendsto eps atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0))
    (ha : Tendsto alpha atTop (𝓝 alpha0)) :
    Tendsto (fun n => tripleParameter (eps n) (t n) (alpha n)) atTop
      (𝓝 (tripleBoundaryParameter alpha0)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact heps
  · exact ht
  · exact (continuous_apply (0 : TripleLabel)).tendsto alpha0 |>.comp ha
  · exact (continuous_apply (1 : TripleLabel)).tendsto alpha0 |>.comp ha
  · exact (continuous_apply (2 : TripleLabel)).tendsto alpha0 |>.comp ha

theorem tripleChart_limit_root (alpha0 : TripleVector) (y0 : TripleChartVariables)
    (hreg : TripleChartRegular 0 0 alpha0 y0)
    (eps t : ℕ → ℝ) (alpha : ℕ → TripleVector) (y : ℕ → TripleChartVariables)
    (heps : Tendsto eps atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0))
    (ha : Tendsto alpha atTop (𝓝 alpha0)) (hy : Tendsto y atTop (𝓝 y0))
    (hroots : ∀ n, tripleChartExtendedRows (eps n) (t n) (alpha n) (y n) = 0) :
    tripleChartExtendedRows 0 0 alpha0 y0 = 0 := by
  let p0 := tripleBoundaryParameter alpha0
  have hreg0 : TripleChartRegular (p0 0) (p0 1) (tripleJointAlpha p0) y0 := by
    change TripleChartRegular 0 0 (tripleJointAlpha (tripleBoundaryParameter alpha0)) y0
    simpa only [tripleBoundaryParameter_alpha] using hreg
  have hct := (tripleChartExtendedRows_joint_contDiffAt 0 (p0, y0) hreg0).continuousAt
  have hparam := (tripleParameter_tendsto eps t alpha alpha0 heps ht ha).prodMk_nhds hy
  have hlim : Tendsto (fun n => tripleChartExtendedRows (eps n) (t n) (alpha n) (y n))
      atTop (𝓝 (tripleChartExtendedRows 0 0 alpha0 y0)) := by
    simpa only [Function.comp_def, p0, tripleParameter_eps, tripleParameter_scale,
      tripleParameter_alpha, tripleBoundaryParameter_alpha,
      show tripleBoundaryParameter alpha0 0 = 0 from rfl,
      show tripleBoundaryParameter alpha0 1 = 0 from rfl] using hct.tendsto.comp hparam
  have hzero : Tendsto (fun n => tripleChartExtendedRows (eps n) (t n) (alpha n) (y n))
      atTop (𝓝 (0 : TripleChartVariables)) := by
    simp_rw [hroots]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hzero

theorem tripleScalar_seed_of_regular_scaled_limits (alpha0 : TripleVector)
    (ha0 : TripleWeights alpha0) (g : TripleGaps) (hg0 : 0 < g 0) (hg1 : 0 < g 1)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (eps t : ℕ → ℝ) (alpha : ℕ → TripleVector) (y : ℕ → TripleChartVariables)
    (heps : Tendsto eps atTop (𝓝 0)) (ht : Tendsto t atTop (𝓝 0))
    (ha : Tendsto alpha atTop (𝓝 alpha0))
    (hy : Tendsto y atTop (𝓝 (tripleUnitPoint (tau * h) g)))
    (hroots : ∀ n, tripleChartExtendedRows (eps n) (t n) (alpha n) (y n) = 0) :
    TripleOrdered (tripleCenteringMatrix alpha0 *ᵥ g) ∧
      ∀ i, tripleScalarResidual alpha0 (tripleCenteringMatrix alpha0 *ᵥ g) i = 0 := by
  have hz := tripleCentered_positions_ordered alpha0 g ha0.2 hg0 hg1
  have hh : 0 < h := by unfold h; positivity
  have hangle : |tau * h| = h := by
    rcases htau with rfl | rfl <;> simp [abs_of_pos hh]
  obtain ⟨hpsi, hpi, _, hD⟩ := tripleBoundaryAngle_facts (tau * h) hangle
  have hreg := tripleUnitPoint_regular alpha0 (tau * h) g hpsi hpi (tripleOrdered_distinct hz)
  have hroot := tripleChart_limit_root alpha0 (tripleUnitPoint (tau * h) g) hreg
    eps t alpha y heps ht ha hy hroots
  refine ⟨hz, tripleScalar_centered_gap_root_recovery alpha0 g ha0 ?_⟩
  rw [← tripleAngularDifference_unit_scalar alpha0 (tau * h) g hpsi hpi hD]
  ext k
  rw [← tripleChartExtendedRows_angularDifference, hroot]
  rfl

/-- Actual physical capture needs only the classified regular scale
limits. The scalar seed is a proved consequence of the real equations. -/
theorem triplePhysical_capture_of_regular_scaled_limits (alpha0 : TripleVector)
    (ha0 : TripleWeights alpha0) (g : TripleGaps) (hg0 : 0 < g 0) (hg1 : 0 < g 1)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (r theta : ℕ → Satellite → ℝ)
    (heps : ∀ n, 0 < eps n) (hm : ∀ n, PositiveRatio (mu n))
    (hr : ∀ n i, 0 < r n i) (hfixed : ∀ n, theta n 3 = 0)
    (hcf : ∀ n, RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hphysical : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n))
      (centeredFromRelative (eps n) (mu n) (polarSatellites (r n) (theta n))))
    (hepslim : Tendsto eps atTop (𝓝 0))
    (htlim : Tendsto (fun n => triplePhysicalScale (mu n)) atTop (𝓝 0))
    (halim : Tendsto (fun n => triplePhysicalWeights (mu n)) atTop (𝓝 alpha0))
    (hylim : Tendsto (fun n => tripleVariablesFromPolar (triplePhysicalScale (mu n))
      (triplePhysicalWeights (mu n)) (r n) (theta n)) atTop
      (𝓝 (tripleUnitPoint (tau * h) g))) :
    Nonempty (TripleCapturedBranches eps (fun n => triplePhysicalScale (mu n))
      (fun n => triplePhysicalWeights (mu n))
      (fun n => tripleVariablesFromPolar (triplePhysicalScale (mu n))
        (triplePhysicalWeights (mu n)) (r n) (theta n)) tau) := by
  have hroots (n : ℕ) := triplePhysicalCoordinates_root (eps n) (mu n) (heps n) (hm n)
    (r n) (theta n) (hr n) (hfixed n) (hcf n) (hphysical n)
  obtain ⟨hz, hscalar⟩ := tripleScalar_seed_of_regular_scaled_limits alpha0 ha0 g hg0 hg1 tau htau
    eps (fun n => triplePhysicalScale (mu n)) (fun n => triplePhysicalWeights (mu n))
    (fun n => tripleVariablesFromPolar (triplePhysicalScale (mu n))
      (triplePhysicalWeights (mu n)) (r n) (theta n)) hepslim htlim halim hylim hroots
  have hgap : tripleGapMatrix *ᵥ (tripleCenteringMatrix alpha0 *ᵥ g) = g := by
    rw [Matrix.mulVec_mulVec, tripleGapMatrix_centeringMatrix alpha0 ha0.2, Matrix.one_mulVec]
  apply triplePhysical_sequence_capture_of_scaled_limits alpha0 (tripleCenteringMatrix alpha0 *ᵥ g)
    ha0 hz hscalar tau htau eps mu r theta heps hm hr hfixed hcf hphysical hepslim htlim halim
  simpa only [hgap] using hylim

end DominantFiveBody
