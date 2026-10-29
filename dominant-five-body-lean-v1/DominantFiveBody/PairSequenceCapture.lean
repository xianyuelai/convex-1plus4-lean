import DominantFiveBody.PairPhysicalContinuation
import DominantFiveBody.PairPhysicalCoordinates

/-! # Capture in the actual pair chart from the classified scale limits

The compact fraction is never assumed to converge.  The physical version
below derives the chart root from the original normalized equations and
the explicit inverse coordinates.  The scale-limit hypotheses are the
remaining inputs of Proposition 4.2, not a chart-capture assumption.
-/

noncomputable section
open scoped BigOperators ContDiff
open Filter Set Topology

namespace DominantFiveBody
open Coorbital

structure PairCapturedBranches (eps t p alpha : ℕ → ℝ) (y : ℕ → PairChartVariables)
    (psi : ℝ) (keepD : Bool) where
  tailStart : ℕ
  radius : ℝ
  radius_pos : 0<radius
  branch : ℕ → ℝ → PairChartVariables
  parameters_pos : ∀ n, 0<eps (tailStart+n)
  parameters_lt_radius : ∀ n, eps (tailStart+n)<radius
  continuous : ∀ n, ContinuousOn (branch n) (Ico 0 radius)
  hits : ∀ n, branch n (eps (tailStart+n))=y (tailStart+n)
  regular_roots : ∀ n s, s∈Ico 0 radius →
    PairChartRegular s (t (tailStart+n)) (alpha (tailStart+n)) (branch n s) ∧
    pairChartExtendedRows s (t (tailStart+n)) (p (tailStart+n)) (alpha (tailStart+n)) keepD (branch n s)=0
  safe : ∀ n s, s∈Ico 0 radius →
    ((![s,t (tailStart+n),p (tailStart+n),alpha (tailStart+n)] : PairChartParameters),branch n s) ∈
      pairPhysicalSafeSet (pairBoundaryHullOrder psi)
  physical : ∀ n s, 0<s → s<radius →
    StrictConvexCentralConfiguration (masses s (pairChartMass (t (tailStart+n)) (p (tailStart+n)) (alpha (tailStart+n))))
      (pairBoundaryHullOrder psi)
      (pairChartConfiguration ![s,t (tailStart+n),p (tailStart+n),alpha (tailStart+n)] (branch n s)) ∧
    NondegenerateCentralConfiguration (masses s (pairChartMass (t (tailStart+n)) (p (tailStart+n)) (alpha (tailStart+n))))
      (pairChartConfiguration ![s,t (tailStart+n),p (tailStart+n),alpha (tailStart+n)] (branch n s))
  endpoints : ∀ n,
    (∀ i, pairChartRadii (t (tailStart+n)) (alpha (tailStart+n)) (branch n 0) i=1) ∧
    (branch n 0) 3=0 ∧
    RelativeCollisionFree (pairChartPoints (t (tailStart+n)) (alpha (tailStart+n)) (branch n 0)) ∧
    SeparatedSemicircle (pairChartAngles (t (tailStart+n)) (alpha (tailStart+n)) (branch n 0)) ∧
    ∀ i, coorbitalResidual (pairChartMass (t (tailStart+n)) (p (tailStart+n)) (alpha (tailStart+n)))
      (pairChartAngles (t (tailStart+n)) (alpha (tailStart+n)) (branch n 0)) i=0

theorem pairChart_sequence_capture_of_scaled_limits (p0 psi : ℝ) (keepD : Bool)
    (hp0 : 0≤p0) (hp01 : p0≤1) (hkeep : if keepD then 0<p0 else p0<1)
    (hpsi0 : psi≠0) (hpsih : psi≠h) (hspan : twoSourceSpan psi<Real.pi)
    (hprobe : p0*coorbitalKernel psi+(1-p0)*coorbitalKernel (psi-h)=0)
    (eps t p alpha : ℕ → ℝ) (y : ℕ → PairChartVariables)
    (heps : ∀ n, 0<eps n) (ht : ∀ n, 0<t n) (ha : ∀ n, alpha n∈Icc (0 : ℝ) 1)
    (hm : ∀ n, PositiveRatio (pairChartMass (t n) (p n) (alpha n)))
    (hepslim : Tendsto eps atTop (𝓝 0)) (htlim : Tendsto t atTop (𝓝 0))
    (hplim : Tendsto p atTop (𝓝 p0))
    (hylim : Tendsto y atTop (𝓝 (pairUnitPoint h psi (pairBoundaryScale (pairProbeDerivative p0 h psi)))))
    (hroots : ∀ n, pairChartExtendedRows (eps n) (t n) (p n) (alpha n) keepD (y n)=0) :
    Nonempty (PairCapturedBranches eps t p alpha y psi keepD) := by
  classical
  obtain ⟨eta,r,C,heta,hr,_,_,_,hbranches⟩ :=
    pairChart_compact_physical_continuation p0 psi keepD hp0 hp01 hkeep hpsi0 hpsih hspan hprobe 1 (by norm_num)
  choose B hBbase hBsmooth hB using fun n => hbranches (alpha n) (ha n)
  have hεnear : ∀ᶠ n in atTop, |eps n|<eta := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hepslim.eventually (Metric.ball_mem_nhds (0 : ℝ) heta)
  have htnear : ∀ᶠ n in atTop, |t n|<eta := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using htlim.eventually (Metric.ball_mem_nhds (0 : ℝ) heta)
  have hpnear : ∀ᶠ n in atTop, dist (p n) p0<eta := hplim.eventually (Metric.ball_mem_nhds p0 heta)
  have hynear : ∀ᶠ n in atTop, dist (y n) (pairUnitPoint h psi (pairBoundaryScale (pairProbeDerivative p0 h psi)))<r :=
    hylim.eventually (Metric.ball_mem_nhds _ hr)
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (hεnear.and (htnear.and (hpnear.and hynear)))
  have htail (n : ℕ) := hN (N+n) (Nat.le_add_right N n)
  let q (n : ℕ) (s : ℝ) : PairChartParameters := ![s,t (N+n),p (N+n),alpha (N+n)]
  let branch (n : ℕ) (s : ℝ) := B (N+n) (q n s)
  have hdist (n : ℕ) (s : ℝ) (hs : |s|<eta) : dist (q n s) ![0,0,p0,alpha (N+n)]<eta := by
    apply (dist_pi_lt_iff heta).mpr
    intro i
    fin_cases i
    · simpa [q,Real.dist_eq] using hs
    · simpa [q,Real.dist_eq] using (htail n).2.1
    · exact (htail n).2.2.1
    · simpa [q] using heta
  have hdata (n : ℕ) (s : ℝ) (hs : |s|<eta) := hB (N+n) (q n s) (hdist n s hs)
  refine ⟨{
    tailStart := N
    radius := eta
    radius_pos := heta
    branch := branch
    parameters_pos := fun n => heps (N+n)
    parameters_lt_radius := fun n => lt_of_le_of_lt (le_abs_self _) (htail n).1
    continuous := ?_
    hits := ?_
    regular_roots := ?_
    safe := ?_
    physical := ?_
    endpoints := ?_ }⟩
  · intro n
    apply (hBsmooth (N+n)).continuousOn.comp (show Continuous (q n) by fun_prop).continuousOn
    intro s hs
    exact hdist n s (by simpa only [abs_of_nonneg hs.1] using hs.2)
  · intro n
    obtain ⟨_,_,_,_,_,_,huniq,_⟩ := hdata n (eps (N+n)) (htail n).1
    exact (huniq (y (N+n)) (htail n).2.2.2).mp (hroots (N+n))
  · intro n s hs
    obtain ⟨_,hreg,_,_,_,hroot,_,_⟩ := hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)
    exact ⟨hreg,hroot⟩
  · intro n s hs
    exact (hdata n s (by simpa only [abs_of_nonneg hs.1] using hs.2)).2.2.1
  · intro n s hs hsη
    obtain ⟨_,_,_,_,_,_,_,hphys⟩ := hdata n s (by simpa only [abs_of_pos hs] using hsη)
    exact hphys hs (ht (N+n)) (hm (N+n))
  · intro n
    obtain ⟨_,hreg,hsafe,_,_,hroot,_,_⟩ := hdata n 0 (by simpa using heta)
    exact pairChart_fixed_mass_zero_endpoint (t (N+n)) (p (N+n)) (alpha (N+n)) keepD
      (branch n 0) (ht (N+n)) (hm (N+n)) hreg hsafe.1 hsafe.2.1 hroot

/-- Physical sequence entry point: the chart equations and regularity are
derived from real normalized configurations.  Only the classified scale
limits remain as explicit hypotheses, and α is allowed to oscillate. -/
theorem pairPhysical_sequence_capture_of_scaled_limits (p0 psi : ℝ) (keepD : Bool)
    (hp0 : 0≤p0) (hp01 : p0≤1) (hkeep : if keepD then 0<p0 else p0<1)
    (hpsi0 : psi≠0) (hpsih : psi≠h) (hspan : twoSourceSpan psi<Real.pi)
    (hprobe : p0*coorbitalKernel psi+(1-p0)*coorbitalKernel (psi-h)=0)
    (eps : ℕ → ℝ) (mu : ℕ → MassRatio) (r theta : ℕ → Satellite → ℝ)
    (heps : ∀ n, 0<eps n) (hm : ∀ n, PositiveRatio (mu n))
    (hr : ∀ n i, 0<r n i) (hfixed : ∀ n, theta n 2=0)
    (hcf : ∀ n, RelativeCollisionFree (polarSatellites (r n) (theta n)))
    (hphysical : ∀ n, NormalizedCentralConfiguration (masses (eps n) (mu n))
      (centeredFromRelative (eps n) (mu n) (polarSatellites (r n) (theta n))))
    (hepslim : Tendsto eps atTop (𝓝 0))
    (htlim : Tendsto (fun n => pairPhysicalScale (mu n)) atTop (𝓝 0))
    (hplim : Tendsto (fun n => pairExteriorFraction (mu n)) atTop (𝓝 p0))
    (hylim : Tendsto (fun n => pairVariablesFromPolar (pairPhysicalScale (mu n)) (pairPhysicalFraction (mu n)) (r n) (theta n))
      atTop (𝓝 (pairUnitPoint h psi (pairBoundaryScale (pairProbeDerivative p0 h psi))))) :
    Nonempty (PairCapturedBranches eps (fun n => pairPhysicalScale (mu n))
      (fun n => pairExteriorFraction (mu n)) (fun n => pairPhysicalFraction (mu n))
      (fun n => pairVariablesFromPolar (pairPhysicalScale (mu n)) (pairPhysicalFraction (mu n)) (r n) (theta n)) psi keepD) := by
  apply pairChart_sequence_capture_of_scaled_limits p0 psi keepD hp0 hp01 hkeep hpsi0 hpsih hspan hprobe
    eps _ _ _ _ heps (fun n => (pairPhysicalParameters_bounds (mu n) (hm n)).1)
    (fun n => ⟨(pairPhysicalParameters_bounds (mu n) (hm n)).2.2.1.le,
      (pairPhysicalParameters_bounds (mu n) (hm n)).2.2.2.1.le⟩)
    (fun n => by rw [pairPhysicalParameters_mass _ (hm n)]; exact hm n) hepslim htlim hplim hylim
  intro n
  exact pairPhysicalCoordinates_root (eps n) (mu n) (heps n) (hm n) (r n) (theta n)
    (hr n) (hfixed n) (hcf n) (hphysical n) keepD

end DominantFiveBody
