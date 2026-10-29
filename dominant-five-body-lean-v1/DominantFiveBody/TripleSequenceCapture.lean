import DominantFiveBody.TripleConvexContinuation
import DominantFiveBody.TriplePhysicalCoordinates

/-! # Capture of real regular-triple sequences

The physical entry point derives the extended chart equations from the
original normalized Newton equations. Its remaining hypotheses are the
classified scaled limits, including an actual distinct ordered scalar
limit; no chart entry or boundary-weight existence is assumed.
-/

noncomputable section
open scoped BigOperators Matrix ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital
set_option maxHeartbeats 800000

@[simp] theorem tripleParameter_eps (eps t : ℝ) (alpha : TripleVector) :
    tripleParameter eps t alpha 0 = eps := rfl

@[simp] theorem tripleParameter_scale (eps t : ℝ) (alpha : TripleVector) :
    tripleParameter eps t alpha 1 = t := rfl

structure TripleCapturedBranches (eps t : ℕ → ℝ) (alpha : ℕ → TripleVector)
    (y : ℕ → TripleChartVariables) (tau : ℝ) where
  tailStart : ℕ
  radius : ℝ
  radius_pos : 0 < radius
  inverseBound : ℝ
  inverseBound_pos : 0 < inverseBound
  branch : ℕ → ℝ → TripleChartVariables
  parameters_pos : ∀ n, 0 < eps (tailStart + n)
  parameters_lt_radius : ∀ n, eps (tailStart + n) < radius
  continuous : ∀ n, ContinuousOn (branch n) (Ico 0 radius)
  hits : ∀ n, branch n (eps (tailStart + n)) = y (tailStart + n)
  regular_roots : ∀ n s, s ∈ Ico 0 radius →
    TripleChartRegular s (t (tailStart + n)) (alpha (tailStart + n)) (branch n s) ∧
    tripleChartExtendedRows s (t (tailStart + n)) (alpha (tailStart + n)) (branch n s) = 0
  safe : ∀ n s, s ∈ Ico 0 radius →
    (tripleParameter s (t (tailStart + n)) (alpha (tailStart + n)), branch n s) ∈
      triplePhysicalRegularSet
  invertible : ∀ n s, s ∈ Ico 0 radius →
    (tripleChartJacobian s (t (tailStart + n)) (alpha (tailStart + n)) (branch n s)).IsInvertible
  inverse_norm : ∀ n s, s ∈ Ico 0 radius →
    ‖(tripleChartJacobian s (t (tailStart + n)) (alpha (tailStart + n)) (branch n s)).inverse‖ ≤ inverseBound
  convex : ∀ n s, s ∈ Ico 0 radius →
    StrictConvexInOrder (tripleBoundaryHullOrder tau)
      (liftRelative (tripleChartPoints (t (tailStart + n)) (alpha (tailStart + n)) (branch n s)))
  physical : ∀ n s, 0 < s → s < radius →
    StrictConvexCentralConfiguration (masses s (tripleChartMass (t (tailStart + n)) (alpha (tailStart + n))))
      (tripleBoundaryHullOrder tau)
      (tripleChartConfiguration (tripleParameter s (t (tailStart + n)) (alpha (tailStart + n))) (branch n s)) ∧
    NondegenerateCentralConfiguration (masses s (tripleChartMass (t (tailStart + n)) (alpha (tailStart + n))))
      (tripleChartConfiguration (tripleParameter s (t (tailStart + n)) (alpha (tailStart + n))) (branch n s))
  endpoints : ∀ n,
    (∀ i, tripleChartRadii (t (tailStart + n)) (alpha (tailStart + n)) (branch n 0) i = 1) ∧
    RelativeCollisionFree (tripleChartPoints (t (tailStart + n)) (alpha (tailStart + n)) (branch n 0)) ∧
    SeparatedSemicircle (tripleChartAngles (t (tailStart + n)) (alpha (tailStart + n)) (branch n 0)) ∧
    ∀ i, coorbitalResidual (tripleChartMass (t (tailStart + n)) (alpha (tailStart + n)))
      (tripleChartAngles (t (tailStart + n)) (alpha (tailStart + n)) (branch n 0)) i = 0

theorem tripleChart_sequence_capture_of_scaled_limits (alpha0 z : TripleVector)
    (ha0 : TripleWeights alpha0) (hz : TripleOrdered z)
    (hscalar : ∀ i, tripleScalarResidual alpha0 z i = 0)
    (tau : ℝ) (htau : tau = 1 ∨ tau = -1)
    (eps t : ℕ → ℝ) (alpha : ℕ → TripleVector) (y : ℕ → TripleChartVariables)
    (heps : ∀ n, 0 < eps n) (ht : ∀ n, 0 < t n)
    (ha : ∀ n, ∑ i, alpha n i = 1)
    (hm : ∀ n, PositiveRatio (tripleChartMass (t n) (alpha n)))
    (hepslim : Tendsto eps atTop (𝓝 0)) (htlim : Tendsto t atTop (𝓝 0))
    (halim : Tendsto alpha atTop (𝓝 alpha0))
    (hylim : Tendsto y atTop (𝓝 (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z))))
    (hroots : ∀ n, tripleChartExtendedRows (eps n) (t n) (alpha n) (y n) = 0) :
    Nonempty (TripleCapturedBranches eps t alpha y tau) := by
  classical
  obtain ⟨eta, r, C, heta, hr, hC, _, _, B, _, hBsmooth, hB⟩ :=
    tripleChart_convex_physical_continuation alpha0 z ha0 hz hscalar tau htau 1 (by norm_num)
  have hεnear : ∀ᶠ n in atTop, |eps n| < eta := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      hepslim.eventually (Metric.ball_mem_nhds (0 : ℝ) heta)
  have htnear : ∀ᶠ n in atTop, |t n| < eta := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      htlim.eventually (Metric.ball_mem_nhds (0 : ℝ) heta)
  have hanear : ∀ᶠ n in atTop, dist (alpha n) alpha0 < eta :=
    halim.eventually (Metric.ball_mem_nhds alpha0 heta)
  have hynear : ∀ᶠ n in atTop, dist (y n) (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z)) < r :=
    hylim.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hεnear.and (htnear.and (hanear.and hynear)))
  have htail (n : ℕ) := hN (N + n) (Nat.le_add_right N n)
  let q (n : ℕ) (s : ℝ) := tripleParameter s (t (N + n)) (alpha (N + n))
  let branch (n : ℕ) (s : ℝ) := B (q n s)
  have hdist (n : ℕ) (s : ℝ) (hs : |s| < eta) :
      dist (q n s) (tripleBoundaryParameter alpha0) < eta := by
    have halpha := (dist_pi_lt_iff heta).mp (htail n).2.2.1
    apply (dist_pi_lt_iff heta).mpr
    intro i
    fin_cases i
    · simpa [q, tripleParameter, tripleBoundaryParameter, Real.dist_eq] using hs
    · simpa [q, tripleParameter, tripleBoundaryParameter, Real.dist_eq] using (htail n).2.1
    · exact halpha 0
    · exact halpha 1
    · exact halpha 2
  have hdata (n : ℕ) (s : ℝ) (hs : |s| < eta) := hB (q n s) (hdist n s hs)
  refine ⟨{
    tailStart := N
    radius := eta
    radius_pos := heta
    inverseBound := C
    inverseBound_pos := hC
    branch := branch
    parameters_pos := fun n => heps (N + n)
    parameters_lt_radius := fun n => lt_of_le_of_lt (le_abs_self _) (htail n).1
    continuous := ?_
    hits := ?_
    regular_roots := ?_
    safe := ?_
    invertible := ?_
    inverse_norm := ?_
    convex := ?_
    physical := ?_
    endpoints := ?_ }⟩
  · intro n
    apply hBsmooth.continuousOn.comp (show Continuous (q n) by
      unfold q tripleParameter
      fun_prop).continuousOn
    intro s hs
    exact hdist n s (by simpa only [abs_of_nonneg hs.1] using hs.2)
  · intro n
    obtain ⟨_, _, _, _, _, _, huniq, _⟩ := hdata n (eps (N + n)) (htail n).1
    apply (huniq (y (N + n)) (htail n).2.2.2).mp
    simpa only [q, branch, tripleChartParameterRows, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using hroots (N + n)
  · intro n s hs
    obtain ⟨_, hreg, _, _, _, hroot, _⟩ := hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)
    simpa only [q, branch, tripleChartParameterRows, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using And.intro hreg hroot
  · intro n s hs
    exact (hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)).2.2.1
  · intro n s hs
    simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using
      (hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)).2.2.2.1
  · intro n s hs
    simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using
      (hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)).2.2.2.2.1
  · intro n s hs
    obtain ⟨_, _, _, _, _, _, _, hconv, _⟩ := hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)
    simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using hconv (ht (N + n)) (by simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using ha (N + n))
  · intro n s hs hsη
    obtain ⟨_, _, _, _, _, _, _, _, hphys, _⟩ := hdata n s (by simpa only [abs_of_pos hs] using hsη)
    simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using hphys hs (ht (N + n))
      (by simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using ha (N + n))
      (by simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using hm (N + n))
  · intro n
    obtain ⟨_, _, _, _, _, _, _, _, _, hend⟩ := hdata n 0 (by simpa using heta)
    simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using hend rfl (ht (N + n))
      (by simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using ha (N + n))
      (by simpa only [q, branch, tripleParameter_alpha, tripleParameter_eps, tripleParameter_scale] using hm (N + n))

/-- Actual normalized physical solutions enter the regular-triple chart
through explicit inverse coordinates. -/
theorem triplePhysical_sequence_capture_of_scaled_limits (alpha0 z : TripleVector)
    (ha0 : TripleWeights alpha0) (hz : TripleOrdered z)
    (hscalar : ∀ i, tripleScalarResidual alpha0 z i = 0)
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
      (𝓝 (tripleUnitPoint (tau * h) (tripleGapMatrix *ᵥ z)))) :
    Nonempty (TripleCapturedBranches eps (fun n => triplePhysicalScale (mu n))
      (fun n => triplePhysicalWeights (mu n))
      (fun n => tripleVariablesFromPolar (triplePhysicalScale (mu n))
        (triplePhysicalWeights (mu n)) (r n) (theta n)) tau) := by
  apply tripleChart_sequence_capture_of_scaled_limits alpha0 z ha0 hz hscalar tau htau
    eps _ _ _ heps (fun n => (triplePhysicalParameters_bounds (mu n) (hm n)).1)
    (fun n => triplePhysicalWeights_sum (mu n) (hm n))
    (fun n => by rw [triplePhysicalParameters_mass _ (hm n)]; exact hm n)
    hepslim htlim halim hylim
  intro n
  exact triplePhysicalCoordinates_root (eps n) (mu n) (heps n) (hm n) (r n) (theta n)
    (hr n) (hfixed n) (hcf n) (hphysical n)

end DominantFiveBody
